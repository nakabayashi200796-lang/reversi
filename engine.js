/* リバーシの頭脳（盤の計算とAI）
   盤は64マスを「32マス×2本」の数（下半分 l・上半分 h）で持つ。マスの番号は 行*8+列（左上が0、右下が63）
   画面からは普通の script として読み込み、AIの読みは同じファイルを Worker（裏で動く別の作業員）として動かす */
'use strict';

const M7E = 0x7e7e7e7e;           // 左右の端の列を除いたマス
const NOT_A = 0xfefefefe | 0;     // 左端の列を除いたマス
const NOT_H = 0x7f7f7f7f;         // 右端の列を除いたマス

function pc(x) {
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return Math.imul((x + (x >>> 4)) & 0x0f0f0f0f, 0x01010101) >>> 24;
}
function bitAt(l, h, i) { return i < 32 ? (l >>> i) & 1 : (h >>> (i - 32)) & 1; }

/* ---------- 打てる場所（手番側 P、相手 O）。結果は ML / MH に入る ---------- */
let ML = 0, MH = 0;
function genMoves(pl, ph, ol, oh) {
  const el = ~(pl | ol), eh = ~(ph | oh);
  const al = ol & M7E, ah = oh & M7E;
  let rl = 0, rh = 0, tl, th, nl, nh, k;

  // 右（+1）
  tl = (pl << 1) & al; th = ((ph << 1) | (pl >>> 31)) & ah;
  for (k = 0; k < 5; k++) { nl = tl << 1; nh = (th << 1) | (tl >>> 31); tl |= nl & al; th |= nh & ah; }
  rl |= (tl << 1) & el; rh |= ((th << 1) | (tl >>> 31)) & eh;
  // 左（-1）
  tl = ((pl >>> 1) | (ph << 31)) & al; th = (ph >>> 1) & ah;
  for (k = 0; k < 5; k++) { nl = (tl >>> 1) | (th << 31); nh = th >>> 1; tl |= nl & al; th |= nh & ah; }
  rl |= ((tl >>> 1) | (th << 31)) & el; rh |= (th >>> 1) & eh;
  // 下（+8）
  tl = (pl << 8) & ol; th = ((ph << 8) | (pl >>> 24)) & oh;
  for (k = 0; k < 5; k++) { nl = tl << 8; nh = (th << 8) | (tl >>> 24); tl |= nl & ol; th |= nh & oh; }
  rl |= (tl << 8) & el; rh |= ((th << 8) | (tl >>> 24)) & eh;
  // 上（-8）
  tl = ((pl >>> 8) | (ph << 24)) & ol; th = (ph >>> 8) & oh;
  for (k = 0; k < 5; k++) { nl = (tl >>> 8) | (th << 24); nh = th >>> 8; tl |= nl & ol; th |= nh & oh; }
  rl |= ((tl >>> 8) | (th << 24)) & el; rh |= (th >>> 8) & eh;
  // 右下（+9）
  tl = (pl << 9) & al; th = ((ph << 9) | (pl >>> 23)) & ah;
  for (k = 0; k < 5; k++) { nl = tl << 9; nh = (th << 9) | (tl >>> 23); tl |= nl & al; th |= nh & ah; }
  rl |= (tl << 9) & el; rh |= ((th << 9) | (tl >>> 23)) & eh;
  // 左上（-9）
  tl = ((pl >>> 9) | (ph << 23)) & al; th = (ph >>> 9) & ah;
  for (k = 0; k < 5; k++) { nl = (tl >>> 9) | (th << 23); nh = th >>> 9; tl |= nl & al; th |= nh & ah; }
  rl |= ((tl >>> 9) | (th << 23)) & el; rh |= (th >>> 9) & eh;
  // 左下（+7）
  tl = (pl << 7) & al; th = ((ph << 7) | (pl >>> 25)) & ah;
  for (k = 0; k < 5; k++) { nl = tl << 7; nh = (th << 7) | (tl >>> 25); tl |= nl & al; th |= nh & ah; }
  rl |= (tl << 7) & el; rh |= ((th << 7) | (tl >>> 25)) & eh;
  // 右上（-7）
  tl = ((pl >>> 7) | (ph << 25)) & al; th = (ph >>> 7) & ah;
  for (k = 0; k < 5; k++) { nl = (tl >>> 7) | (th << 25); nh = th >>> 7; tl |= nl & al; th |= nh & ah; }
  rl |= ((tl >>> 7) | (th << 25)) & el; rh |= (th >>> 7) & eh;

  ML = rl; MH = rh;
}
function countMoves(pl, ph, ol, oh) { genMoves(pl, ph, ol, oh); return pc(ML) + pc(MH); }

/* ---------- 返る石。マス sq に P が打ったとき返る石を FL / FH に入れる ---------- */
const RAY = new Int8Array(64 * 8 * 8).fill(-1);   // [マス][向き][歩数] → マス番号（端で -1）
(function () {
  const D = [[0, 1], [0, -1], [1, 0], [-1, 0], [1, 1], [-1, -1], [1, -1], [-1, 1]];
  for (let sq = 0; sq < 64; sq++) {
    for (let d = 0; d < 8; d++) {
      let r = sq >> 3, c = sq & 7, n = 0;
      for (;;) {
        r += D[d][0]; c += D[d][1];
        if (r < 0 || r > 7 || c < 0 || c > 7) break;
        RAY[(sq * 8 + d) * 8 + n++] = r * 8 + c;
      }
    }
  }
})();
let FL = 0, FH = 0;
function getFlips(sq, pl, ph, ol, oh) {
  let gl = 0, gh = 0;
  const base = sq * 64;
  for (let d = 0; d < 8; d++) {
    let fl = 0, fh = 0, j = base + d * 8;
    const end = j + 8;
    for (; j < end; j++) {
      const t = RAY[j];
      if (t < 0) break;
      if (t < 32) {
        const b = 1 << t;
        if (ol & b) { fl |= b; continue; }
        if (pl & b) { gl |= fl; gh |= fh; }
        break;
      } else {
        const b = 1 << (t - 32);
        if (oh & b) { fh |= b; continue; }
        if (ph & b) { gl |= fl; gh |= fh; }
        break;
      }
    }
  }
  FL = gl; FH = gh;
}

/* ---------- 形勢の見立て（手番側から見た点数。だいたい「最後の石差」の目安） ---------- */
const CORNERS = [0, 7, 56, 63];
const XSQ = [9, 14, 49, 54];
const CSQ = [[1, 8], [6, 15], [48, 57], [55, 62]];
// 角から2本の辺に沿って並ぶマス（確定石の数え上げ用）
const EDGE_RUNS = [
  [[1, 2, 3, 4, 5, 6, 7], [8, 16, 24, 32, 40, 48, 56]],
  [[6, 5, 4, 3, 2, 1, 0], [15, 23, 31, 39, 47, 55, 63]],
  [[57, 58, 59, 60, 61, 62, 63], [48, 40, 32, 24, 16, 8, 0]],
  [[62, 61, 60, 59, 58, 57, 56], [55, 47, 39, 31, 23, 15, 7]],
];
const W = {
  corner: 11, xsq: 5, csq: 1.6, mob: 1.0, mobLate: 0.6, front: 0.45, stable: 1.1, disc: 0.0, discLate: 0.25,
};

function stableEdge(pl, ph, ol, oh) {
  // 角から辺に沿って同じ色が続く石と、埋まりきった辺の石を「動かない石」として数える（重複は1つにまとめる）
  let sl = 0, sh = 0, tl = 0, th = 0; // s: P の確定石, t: O の確定石
  for (let k = 0; k < 4; k++) {
    const c = CORNERS[k];
    const cp = bitAt(pl, ph, c), co = bitAt(ol, oh, c);
    if (!cp && !co) continue;
    if (cp) { if (c < 32) sl |= 1 << c; else sh |= 1 << (c - 32); }
    else { if (c < 32) tl |= 1 << c; else th |= 1 << (c - 32); }
    for (const run of EDGE_RUNS[k]) {
      for (const sq of run) {
        const mine = cp ? bitAt(pl, ph, sq) : bitAt(ol, oh, sq);
        if (!mine) break;
        if (cp) { if (sq < 32) sl |= 1 << sq; else sh |= 1 << (sq - 32); }
        else { if (sq < 32) tl |= 1 << sq; else th |= 1 << (sq - 32); }
      }
    }
  }
  return pc(sl) + pc(sh) - pc(tl) - pc(th);
}

function evaluate(pl, ph, ol, oh) {
  const nP = pc(pl) + pc(ph), nO = pc(ol) + pc(oh);
  const empties = 64 - nP - nO;
  const el = ~(pl | ol), eh = ~(ph | oh);

  // 空きマスの隣（ここにある石は返されやすい）
  let nl = (el << 8) | (el >>> 8) | (eh << 24);
  let nh = (eh << 8) | (el >>> 24) | (eh >>> 8);
  let xl = (el << 1) | (el << 9) | (el >>> 7) | (eh << 25);
  let xh = (eh << 1) | (el >>> 31) | (eh << 9) | (el >>> 23) | (eh >>> 7);
  nl |= xl & NOT_A; nh |= xh & NOT_A;
  xl = (el >>> 1) | (eh << 31) | (el >>> 9) | (eh << 23) | (el << 7);
  xh = (eh >>> 1) | (eh >>> 9) | (eh << 7) | (el >>> 25);
  nl |= xl & NOT_H; nh |= xh & NOT_H;
  const fP = pc(pl & nl) + pc(ph & nh), fO = pc(ol & nl) + pc(oh & nh);

  const mP = countMoves(pl, ph, ol, oh), mO = countMoves(ol, oh, pl, ph);

  let corner = 0, xs = 0, cs = 0;
  for (let k = 0; k < 4; k++) {
    const c = CORNERS[k];
    const cp = bitAt(pl, ph, c), co = bitAt(ol, oh, c);
    corner += cp - co;
    if (!cp && !co) {
      xs += bitAt(pl, ph, XSQ[k]) - bitAt(ol, oh, XSQ[k]);
      cs += bitAt(pl, ph, CSQ[k][0]) - bitAt(ol, oh, CSQ[k][0]) + bitAt(pl, ph, CSQ[k][1]) - bitAt(ol, oh, CSQ[k][1]);
    }
  }
  const late = empties < 20 ? (20 - empties) / 20 : 0;   // 終盤ほど 1 に近づく
  let s = W.corner * corner - W.xsq * xs - W.csq * cs;
  s += (W.mob * (1 - late) + W.mobLate * late) * (mP - mO);
  s += W.front * (fO - fP) * (1 - late * 0.5);
  s += W.stable * stableEdge(pl, ph, ol, oh);
  s += (W.disc * (1 - late) + W.discLate * late) * (nP - nO);
  if (mP === 0 && mO > 0) s -= 3;                        // 手番なのに打てない＝パスは苦しい
  return Math.round(s * 4) / 4;
}

/* ---------- 学んだ点数表による見立て（神が使う） ----------
   eval.bin に、盤の形（端の列・角の周り・斜めの列など）ごとの「並び→点数」の表が段階別に入っている。
   src\train\train.py が Edax の採点を手本に作る */
let PAT = null;
const PST = new Int8Array(64);
function loadEval(buf) {
  const dv = new DataView(buf instanceof ArrayBuffer ? buf : buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength));
  const tag = String.fromCharCode(dv.getUint8(0), dv.getUint8(1), dv.getUint8(2), dv.getUint8(3));
  if (tag !== 'RVE1') throw new Error('eval.bin の形式が違う');
  let o = 4;
  const nph = dv.getInt32(o, true); o += 4;
  const nt = dv.getInt32(o, true); o += 4;
  const scale = dv.getInt32(o, true); o += 4;
  const sq = [], len = [], typ = [], tsize = [];
  for (let t = 0; t < nt; t++) {
    const n = dv.getInt32(o, true), k = dv.getInt32(o + 4, true); o += 8;
    tsize.push(Math.pow(3, n));
    for (let i = 0; i < k; i++) { for (let j = 0; j < n; j++) sq.push(dv.getUint8(o++)); len.push(n); typ.push(t); }
  }
  // 段階ごとに、全部の表を1本の配列に並べる（形 t の表は toff[t] から）
  const toff = [];
  let tot = 0;
  for (let t = 0; t < nt; t++) { toff.push(tot); tot += tsize[t]; }
  const tabs = [], bias = [];
  for (let ph = 0; ph < nph; ph++) {
    const tab = new Int16Array(tot);
    for (let t = 0; t < nt; t++) {
      for (let i = 0; i < tsize[t]; i++) { tab[toff[t] + i] = dv.getInt16(o, true); o += 2; }
    }
    tabs.push(tab);
    bias.push(dv.getInt16(o, true)); o += 2;
  }
  const ioff = new Int32Array(typ.length);
  for (let i = 0; i < typ.length; i++) ioff[i] = toff[typ[i]];
  PAT = { nph, scale, sq: Int8Array.from(sq), len: Int8Array.from(len), ioff, tabs, bias, n: typ.length };
  return PAT;
}
function evaluateP(pl, ph, ol, oh) {
  PST.fill(0);
  let x;
  x = pl; while (x) { const b = x & -x; PST[31 - Math.clz32(b)] = 1; x ^= b; }
  x = ph; while (x) { const b = x & -x; PST[63 - Math.clz32(b)] = 1; x ^= b; }
  x = ol; while (x) { const b = x & -x; PST[31 - Math.clz32(b)] = 2; x ^= b; }
  x = oh; while (x) { const b = x & -x; PST[63 - Math.clz32(b)] = 2; x ^= b; }
  const empties = 64 - pc(pl) - pc(ph) - pc(ol) - pc(oh);
  let phs = Math.floor((59 - empties) / 5);
  if (phs < 0) phs = 0; else if (phs >= PAT.nph) phs = PAT.nph - 1;
  const tab = PAT.tabs[phs], sqs = PAT.sq, lens = PAT.len, ioff = PAT.ioff;
  let s = PAT.bias[phs], k = 0;
  for (let i = 0, n = PAT.n; i < n; i++) {
    let idx = 0;
    for (let j = lens[i]; j > 0; j--) idx = idx * 3 + PST[sqs[k++]];
    s += tab[ioff[i] + idx];
  }
  return Math.round(s / PAT.scale * 4) / 4;
}
let EVAL = evaluate;
let evalMode = 'hand';
function useEval(mode) {
  const m = mode === 'pattern' && PAT ? 'pattern' : 'hand';
  if (m !== evalMode) { ttClear(); evalMode = m; }   // 見立てが変わったら、前の見立てで読んだメモは捨てる
  EVAL = m === 'pattern' ? evaluateP : evaluate;
  return m;
}

/* ---------- 読み ---------- */
const WIN = 1000;               // 勝ち負けが読み切れたときは見立てより必ず大きくする
const INF = 100000;
const ABORT = { abort: true };
let nodes = 0, deadline = Infinity;

function finalScore(pl, ph, ol, oh) {
  const a = pc(pl) + pc(ph), b = pc(ol) + pc(oh);
  const e = 64 - a - b;
  if (a > b) return a - b + e;
  if (a < b) return a - b - e;
  return 0;
}

// 置換表（同じ盤面を何度も読まないためのメモ）
const TT_BITS = 19, TT_SIZE = 1 << TT_BITS, TT_MASK = TT_SIZE - 1;
const ttK = new Int32Array(TT_SIZE * 4);
const ttV = new Float32Array(TT_SIZE);
const ttD = new Int8Array(TT_SIZE).fill(-1);   // 読んだ深さ（-1 は空き）
const ttF = new Int8Array(TT_SIZE);            // 0=ちょうど 1=これ以上 2=これ以下
const ttM = new Int8Array(TT_SIZE);            // いちばん良かった手
function ttIndex(pl, ph, ol, oh) {
  let h = Math.imul(pl ^ 0x2545f491, 0x9e3779b1);
  h ^= Math.imul(ph ^ 0x6c8e9cf5, 0x85ebca77);
  h = (h << 13) | (h >>> 19);
  h ^= Math.imul(ol ^ 0x1b873593, 0xc2b2ae3d);
  h ^= Math.imul(oh ^ 0x7fb5d329, 0x27d4eb2f);
  h ^= h >>> 15; h = Math.imul(h, 0x2c1b3c6d); h ^= h >>> 12;
  return h & TT_MASK;
}
function ttClear() { ttD.fill(-1); }

// 角・辺を先に、X打ち（角の斜め隣）を後に読む並び順
const SQ_ORDER = new Int8Array([
  20, -8, 8, 6, 6, 8, -8, 20,
  -8, -12, -2, -1, -1, -2, -12, -8,
  8, -2, 3, 2, 2, 3, -2, 8,
  6, -1, 2, 0, 0, 2, -1, 6,
  6, -1, 2, 0, 0, 2, -1, 6,
  8, -2, 3, 2, 2, 3, -2, 8,
  -8, -12, -2, -1, -1, -2, -12, -8,
  20, -8, 8, 6, 6, 8, -8, 20,
]);

function listMoves(l, h, out) {
  let n = 0;
  while (l) { const b = l & -l; out[n++] = 31 - Math.clz32(b); l ^= b; }
  while (h) { const b = h & -h; out[n++] = 63 - Math.clz32(b); h ^= b; }
  return n;
}

const MOVEBUF = [], KEYBUF = [];
for (let i = 0; i < 96; i++) { MOVEBUF.push(new Int8Array(32)); KEYBUF.push(new Float64Array(32)); }

function search(pl, ph, ol, oh, depth, alpha, beta, passed, ply) {
  if ((++nodes & 2047) === 0 && Date.now() > deadline) throw ABORT;
  if (depth <= 0) return EVAL(pl, ph, ol, oh);

  genMoves(pl, ph, ol, oh);
  let ml = ML, mh = MH;
  if (!(ml | mh)) {
    if (passed) { const f = finalScore(pl, ph, ol, oh); return f > 0 ? WIN + f : f < 0 ? -WIN + f : 0; }
    return -search(ol, oh, pl, ph, depth, -beta, -alpha, true, ply + 1);
  }

  const idx = ttIndex(pl, ph, ol, oh), k4 = idx * 4;
  let ttMove = -1;
  if (ttD[idx] >= 0 && ttK[k4] === pl && ttK[k4 + 1] === ph && ttK[k4 + 2] === ol && ttK[k4 + 3] === oh) {
    ttMove = ttM[idx];
    if (ttD[idx] >= depth) {
      const v = ttV[idx], f = ttF[idx];
      if (f === 0) return v;
      if (f === 1 && v >= beta) return v;
      if (f === 2 && v <= alpha) return v;
    }
  }

  const mv = MOVEBUF[ply], key = KEYBUF[ply];
  const n = listMoves(ml, mh, mv);
  for (let i = 0; i < n; i++) {
    const sq = mv[i];
    let kk = SQ_ORDER[sq];
    if (sq === ttMove) kk += 10000;
    else if (depth >= 3) {
      getFlips(sq, pl, ph, ol, oh);
      const npl = pl | FL | (sq < 32 ? 1 << sq : 0), nph = ph | FH | (sq >= 32 ? 1 << (sq - 32) : 0);
      kk -= 4 * countMoves(ol & ~FL, oh & ~FH, npl, nph);
    }
    key[i] = kk;
  }
  // 並べ替え（数が少ないので挿入ソート）
  for (let i = 1; i < n; i++) {
    const m = mv[i], kv = key[i];
    let j = i - 1;
    while (j >= 0 && key[j] < kv) { mv[j + 1] = mv[j]; key[j + 1] = key[j]; j--; }
    mv[j + 1] = m; key[j + 1] = kv;
  }

  const a0 = alpha;
  let best = -INF, bestMove = mv[0];
  for (let i = 0; i < n; i++) {
    const sq = mv[i];
    getFlips(sq, pl, ph, ol, oh);
    const npl = pl | FL | (sq < 32 ? 1 << sq : 0), nph = ph | FH | (sq >= 32 ? 1 << (sq - 32) : 0);
    const nol = ol & ~FL, noh = oh & ~FH;
    let v;
    if (i === 0) v = -search(nol, noh, npl, nph, depth - 1, -beta, -alpha, false, ply + 1);
    else {
      v = -search(nol, noh, npl, nph, depth - 1, -alpha - 0.25, -alpha, false, ply + 1);
      if (v > alpha && v < beta) v = -search(nol, noh, npl, nph, depth - 1, -beta, -v, false, ply + 1);
    }
    if (v > best) { best = v; bestMove = sq; if (v > alpha) { alpha = v; if (alpha >= beta) break; } }
  }

  ttK[k4] = pl; ttK[k4 + 1] = ph; ttK[k4 + 2] = ol; ttK[k4 + 3] = oh;
  ttV[idx] = best; ttD[idx] = depth; ttM[idx] = bestMove;
  ttF[idx] = best <= a0 ? 2 : best >= beta ? 1 : 0;
  return best;
}

/* ---------- 終盤の読み切り（最後の石差をぴったり出す） ---------- */
// 終盤の読み切り専用の置換表（深さの代わりに「読み切り済み」を印にする）
const etK = new Int32Array(TT_SIZE * 4);
const etL = new Int8Array(TT_SIZE), etU = new Int8Array(TT_SIZE), etM = new Int8Array(TT_SIZE);
const etOn = new Uint8Array(TT_SIZE);
function etClear() { etOn.fill(0); }

// 残り数マス用：打てる場所を一括で数えず、空きマスを1つずつ試す（このほうが速い）
// 4つの区画のうち空きが奇数の区画から先に打つ（最後の1手を自分が打てる形を作りやすい）
function quadParityFirst(el, eh, out) {
  let n = 0, odd = 0;
  const qs = [0x0f0f0f0f & el, 0xf0f0f0f0 & el, 0x0f0f0f0f & eh, 0xf0f0f0f0 & eh];
  for (let q = 0; q < 4; q++) if (pc(qs[q]) & 1) odd |= 1 << q;
  for (let pass = 0; pass < 2; pass++) {
    for (let q = 0; q < 4; q++) {
      if (((odd >> q) & 1) !== (pass === 0 ? 1 : 0)) continue;
      let b = qs[q];
      const off = q >= 2 ? 32 : 0;
      while (b) { const x = b & -b; out[n++] = off + 31 - Math.clz32(x); b ^= x; }
    }
  }
  return n;
}
const SMALL = 6;
let ORDER_SEARCH = 16;   // 残りがこれ以上なら、浅く読んだ見立てで並べる
function solveSmall(pl, ph, ol, oh, alpha, beta, passed, empties, ply) {
  ++nodes;
  if (empties === 0) return pc(pl) + pc(ph) - pc(ol) - pc(oh);
  const el = ~(pl | ol), eh = ~(ph | oh);
  if (empties === 1) {
    const sq = el ? 31 - Math.clz32(el) : 63 - Math.clz32(eh);
    const d = pc(pl) + pc(ph) - pc(ol) - pc(oh);
    getFlips(sq, pl, ph, ol, oh);
    let f = pc(FL) + pc(FH);
    if (f) return d + 2 * f + 1;
    getFlips(sq, ol, oh, pl, ph);
    f = pc(FL) + pc(FH);
    if (f) return d - 2 * f - 1;
    return d > 0 ? d + 1 : d < 0 ? d - 1 : 0;
  }
  const mv = MOVEBUF[ply];
  const n = quadParityFirst(el, eh, mv);
  let best = -INF, any = false;
  for (let i = 0; i < n; i++) {
    const sq = mv[i];
    getFlips(sq, pl, ph, ol, oh);
    if (!(FL | FH)) continue;
    any = true;
    const npl = pl | FL | (sq < 32 ? 1 << sq : 0), nph = ph | FH | (sq >= 32 ? 1 << (sq - 32) : 0);
    const v = -solveSmall(ol & ~FL, oh & ~FH, npl, nph, -beta, -alpha, false, empties - 1, ply + 1);
    if (v > best) { best = v; if (v > alpha) { alpha = v; if (alpha >= beta) return best; } }
  }
  if (!any) {
    if (passed) return finalScore(pl, ph, ol, oh);
    return -solveSmall(ol, oh, pl, ph, -beta, -alpha, true, empties, ply + 1);
  }
  return best;
}

function solve(pl, ph, ol, oh, alpha, beta, passed, empties, ply) {
  if (empties <= SMALL) return solveSmall(pl, ph, ol, oh, alpha, beta, passed, empties, ply);
  if ((++nodes & 2047) === 0 && Date.now() > deadline) throw ABORT;

  genMoves(pl, ph, ol, oh);
  let ml = ML, mh = MH;
  if (!(ml | mh)) {
    if (passed) return finalScore(pl, ph, ol, oh);
    return -solve(ol, oh, pl, ph, -beta, -alpha, true, empties, ply + 1);
  }

  let idx = -1, k4 = 0, ttMove = -1;
  if (empties >= 9) {
    idx = ttIndex(pl, ph, ol, oh); k4 = idx * 4;
    if (etOn[idx] && etK[k4] === pl && etK[k4 + 1] === ph && etK[k4 + 2] === ol && etK[k4 + 3] === oh) {
      const lo = etL[idx], up = etU[idx];
      if (lo >= beta) return lo;
      if (up <= alpha) return up;
      if (lo === up) return lo;
      if (lo > alpha) alpha = lo;
      if (up < beta) beta = up;
      ttMove = etM[idx];
    }
  }

  const mv = MOVEBUF[ply], key = KEYBUF[ply];
  const n = listMoves(ml, mh, mv);
  if (empties >= 6) {
    // 相手の打てる場所が少なくなる手から読む（早く結論が出やすい）
    for (let i = 0; i < n; i++) {
      const sq = mv[i];
      if (sq === ttMove) { key[i] = 1e6; continue; }
      getFlips(sq, pl, ph, ol, oh);
      const npl = pl | FL | (sq < 32 ? 1 << sq : 0), nph = ph | FH | (sq >= 32 ? 1 << (sq - 32) : 0);
      const nol = ol & ~FL, noh = oh & ~FH;
      if (empties >= ORDER_SEARCH) key[i] = -search(nol, noh, npl, nph, empties >= ORDER_SEARCH + 4 ? 2 : 1, -INF, INF, false, ply + 1);
      else {
        genMoves(nol, noh, npl, nph);
        // 相手の打てる場所の数（角は3つ分に数える）
        key[i] = SQ_ORDER[sq] * 0.1 - 10 * (pc(ML) + pc(MH) + 2 * (pc(ML & 0x81) + pc(MH & 0x81000000)));
      }
    }
  } else {
    for (let i = 0; i < n; i++) key[i] = SQ_ORDER[mv[i]];
  }
  for (let i = 1; i < n; i++) {
    const m = mv[i], kv = key[i];
    let j = i - 1;
    while (j >= 0 && key[j] < kv) { mv[j + 1] = mv[j]; key[j + 1] = key[j]; j--; }
    mv[j + 1] = m; key[j + 1] = kv;
  }

  const a0 = alpha, b0 = beta;
  let best = -INF, bestMove = mv[0];
  for (let i = 0; i < n; i++) {
    const sq = mv[i];
    getFlips(sq, pl, ph, ol, oh);
    const npl = pl | FL | (sq < 32 ? 1 << sq : 0), nph = ph | FH | (sq >= 32 ? 1 << (sq - 32) : 0);
    const nol = ol & ~FL, noh = oh & ~FH;
    let v;
    if (i === 0) v = -solve(nol, noh, npl, nph, -beta, -alpha, false, empties - 1, ply + 1);
    else {
      v = -solve(nol, noh, npl, nph, -alpha - 1, -alpha, false, empties - 1, ply + 1);
      if (v > alpha && v < beta) v = -solve(nol, noh, npl, nph, -beta, -v, false, empties - 1, ply + 1);
    }
    if (v > best) { best = v; bestMove = sq; if (v > alpha) { alpha = v; if (alpha >= beta) break; } }
  }

  if (idx >= 0) {
    if (!(etOn[idx] && etK[k4] === pl && etK[k4 + 1] === ph && etK[k4 + 2] === ol && etK[k4 + 3] === oh)) {
      etK[k4] = pl; etK[k4 + 1] = ph; etK[k4 + 2] = ol; etK[k4 + 3] = oh;
      etL[idx] = -64; etU[idx] = 64; etOn[idx] = 1;
    }
    if (best <= a0) etU[idx] = Math.min(etU[idx], best);
    else if (best >= b0) etL[idx] = Math.max(etL[idx], best);
    else { etL[idx] = best; etU[idx] = best; }
    etM[idx] = bestMove;
  }
  return best;
}

/* ---------- いちばん上（根）の読み。手ごとの点数を返す ---------- */
function applyMove(pl, ph, ol, oh, sq) {
  getFlips(sq, pl, ph, ol, oh);
  return [pl | FL | (sq < 32 ? 1 << sq : 0), ph | FH | (sq >= 32 ? 1 << (sq - 32) : 0), ol & ~FL, oh & ~FH];
}

// 決まった深さで根を読む。order は前の深さでの良い順。ret: {move, score, scores}
function rootSearch(pl, ph, ol, oh, depth, order, exactAll) {
  let alpha = -INF, best = -INF, bestMove = order[0];
  const scores = {};
  for (let i = 0; i < order.length; i++) {
    const sq = order[i];
    const [a, b, c, d] = applyMove(pl, ph, ol, oh, sq);
    let v;
    if (i === 0 || exactAll) v = -search(c, d, a, b, depth - 1, -INF, exactAll ? INF : -alpha, false, 1);
    else {
      v = -search(c, d, a, b, depth - 1, -alpha - 0.25, -alpha, false, 1);
      if (v > alpha) v = -search(c, d, a, b, depth - 1, -INF, -v, false, 1);
    }
    scores[sq] = v;
    if (v > best) { best = v; bestMove = sq; }
    if (v > alpha) alpha = v;
  }
  return { move: bestMove, score: best, scores };
}

function solveRoot(pl, ph, ol, oh, order, empties) {
  let alpha = -65, best = -65, bestMove = order[0];
  for (let i = 0; i < order.length; i++) {
    const sq = order[i];
    const [a, b, c, d] = applyMove(pl, ph, ol, oh, sq);
    let v;
    if (i === 0) v = -solve(c, d, a, b, -65, 65, false, empties - 1, 1);
    else {
      v = -solve(c, d, a, b, -alpha - 1, -alpha, false, empties - 1, 1);
      if (v > alpha) v = -solve(c, d, a, b, -65, -v, false, empties - 1, 1);
    }
    if (v > best) { best = v; bestMove = sq; }
    if (v > alpha) alpha = v;
  }
  return { move: bestMove, score: best };
}

// 勝ち・引き分け・負けだけを読み切る（石差まで出すより速い）。勝てる手が見つかればすぐ返す
function wldRoot(pl, ph, ol, oh, order, empties) {
  let best = -2, bestMove = order[0];
  for (const sq of order) {
    const [a, b, c, d] = applyMove(pl, ph, ol, oh, sq);
    const v = -solve(c, d, a, b, -1, 1, false, empties - 1, 1);
    const k = v > 0 ? 1 : v < 0 ? -1 : 0;
    if (k > best) { best = k; bestMove = sq; if (k === 1) break; }
  }
  return { move: bestMove, wld: best };
}

function sortByScores(order, scores) {
  return order.slice().sort((x, y) => scores[y] - scores[x]);
}

/* ---------- 段ごとの打ち方 ----------
   depth: 読む手数 / end: 残り何マスから最後まで読み切るか / time: 考える時間の上限(ミリ秒) / noise: 序盤のゆらぎ */
const LEVELS = [
  null,
  { name: 'ひよこ', kind: 'random' },
  { name: '見習い', kind: 'greedy' },
  { name: '門番', kind: 'shallow', noise: 3 },
  { name: '達人', depth: 3, end: 8, time: 3000, noise: 3 },
  { name: '竜王', depth: 5, end: 12, time: 5000, noise: 1.5 },
  { name: '鬼神', depth: 7, end: 16, time: 6000, noise: 0 },
  { name: "覇王", depth: 30, end: 20, time: 2500, endTime: 6500, wldTime: 3500, noise: 0 },
  { name: "神", depth: 40, end: 22, time: 5000, endTime: 10000, wldTime: 5500, noise: 0, pattern: true, endMid: 1000 },
];

const TABLE = [
  100, -25, 10, 5, 5, 10, -25, 100,
  -25, -45, 1, 1, 1, 1, -45, -25,
  10, 1, 3, 2, 2, 3, 1, 10,
  5, 1, 2, 1, 1, 2, 1, 5,
  5, 1, 2, 1, 1, 2, 1, 5,
  10, 1, 3, 2, 2, 3, 1, 10,
  -25, -45, 1, 1, 1, 1, -45, -25,
  100, -25, 10, 5, 5, 10, -25, 100,
];

function pick(arr) { return arr[Math.floor(Math.random() * arr.length)]; }

// P が手番の盤面で、段 lv の手を選ぶ。打てる場所が無いときは -1
function think(pl, ph, ol, oh, lv, opts) {
  opts = opts || {};
  genMoves(pl, ph, ol, oh);
  const moves = [];
  const buf = new Int8Array(32);
  const n = listMoves(ML, MH, buf);
  for (let i = 0; i < n; i++) moves.push(buf[i]);
  if (!moves.length) return { move: -1 };
  if (moves.length === 1) return { move: moves[0], forced: true };
  const L = LEVELS[lv];
  const mode = useEval(L.pattern ? 'pattern' : 'hand');

  if (L.kind === 'random') return { move: pick(moves) };
  if (L.kind === 'greedy') {
    let bestN = -1, cand = [];
    for (const sq of moves) {
      getFlips(sq, pl, ph, ol, oh);
      const f = pc(FL) + pc(FH);
      if (f > bestN) { bestN = f; cand = [sq]; } else if (f === bestN) cand.push(sq);
    }
    return { move: pick(cand) };
  }
  if (L.kind === 'table') {
    let best = -1e9, cand = [];
    for (const sq of moves) {
      const v = TABLE[sq] + Math.random() * 4;
      if (v > best) { best = v; cand = [sq]; }
    }
    return { move: cand[0] };
  }
  if (L.kind === 'shallow') {
    // 1手だけ見て、角・角の隣・打てる場所の数で決める。毎回少しゆらぐ
    let best = -1e9, bm = moves[0];
    for (const sq of moves) {
      const [a, b, c, d] = applyMove(pl, ph, ol, oh, sq);
      const v = -evaluate(c, d, a, b) + (Math.random() * 2 - 1) * L.noise;
      if (v > best) { best = v; bm = sq; }
    }
    return { move: bm };
  }

  const empties = 64 - pc(pl) - pc(ph) - pc(ol) - pc(oh);
  const t0 = Date.now();
  nodes = 0;
  let order = moves.slice().sort((a, b) => SQ_ORDER[b] - SQ_ORDER[a]);
  let res = null, depthDone = 0;

  // 中盤：浅い深さから順に読み、時間切れなら最後に読み終えた深さの手を使う
  const maxDepth = Math.min(L.depth, empties);
  const midTime = empties <= L.end ? Math.min(L.time, L.endMid || 500) : L.time;
  deadline = t0 + midTime;
  try {
    for (let d = 1; d <= maxDepth; d++) {
      const useNoise = L.noise > 0 && empties >= 50 && d === maxDepth;
      const r = rootSearch(pl, ph, ol, oh, d, order, useNoise);
      res = r; depthDone = d;
      order = sortByScores(order, r.scores);
      if (Math.abs(r.score) >= WIN - 64 && d >= 4) break;    // 勝ち負けが見えたら終わり
      if (lv >= 7 && Date.now() - t0 > midTime * 0.45) break; // 次の深さは時間内に終わらない見込み
    }
  } catch (e) { if (e !== ABORT) throw e; }
  deadline = Infinity;
  if (!res) res = { move: order[0], score: 0, scores: {} };

  // 序盤だけ、ほぼ同じ点数の手からランダムに選んで毎回同じ展開にならないようにする
  if (L.noise > 0 && empties >= 50 && depthDone === maxDepth) {
    const near = order.filter(sq => res.scores[sq] >= res.score - L.noise);
    res = { move: pick(near), score: res.score };
  }

  // 終盤：読み切り。石差まで読み切れないときは、勝てるかどうかだけ読み切る
  if (empties <= L.end) {
    const endTime = L.endTime || L.time;
    deadline = Date.now() + (L.wldTime ? endTime - L.wldTime : endTime);
    try {
      const r = solveRoot(pl, ph, ol, oh, order, empties);
      res = { move: r.move, score: r.score, exact: true };
    } catch (e) {
      if (e !== ABORT) throw e;
      if (L.wldTime) {
        deadline = Date.now() + L.wldTime;
        try {
          const r = wldRoot(pl, ph, ol, oh, order, empties);
          if (r.wld >= 0 || !res) res = { move: r.move, score: r.wld, wld: r.wld };
        } catch (e2) { if (e2 !== ABORT) throw e2; }
      }
    }
    deadline = Infinity;
  }
  res.depth = depthDone; res.nodes = nodes; res.ms = Date.now() - t0; res.eval = mode;
  return res;
}

/* ---------- 講座の問題づくり用：すべての手の点数（手番側から見た石差の目安） ---------- */
function scoreMoves(pl, ph, ol, oh, depth, exactEmpties) {
  const moves = movesOf(pl, ph, ol, oh);
  const empties = 64 - pc(pl) - pc(ph) - pc(ol) - pc(oh);
  const out = {};
  for (const sq of moves) {
    const [a, b, c, d] = applyMove(pl, ph, ol, oh, sq);
    let v;
    if (empties - 1 <= exactEmpties) v = -solve(c, d, a, b, -65, 65, false, empties - 1, 1);
    else {
      v = -search(c, d, a, b, depth - 1, -INF, INF, false, 1);
      if (v >= WIN - 64) v -= WIN; else if (v <= -WIN + 64) v += WIN;
    }
    out[sq] = v;
  }
  return out;
}

/* ---------- 振り返り用：盤面の見立て（手番側から見た点数と、いちばん良い手） ---------- */
function analyzePosition(pl, ph, ol, oh) {
  genMoves(pl, ph, ol, oh);
  const buf = new Int8Array(32);
  const n = listMoves(ML, MH, buf);
  const empties = 64 - pc(pl) - pc(ph) - pc(ol) - pc(oh);
  if (n === 0) {
    genMoves(ol, oh, pl, ph);
    if (!(ML | MH)) return { value: finalScore(pl, ph, ol, oh), best: -1, exact: true };
    const r = analyzePosition(ol, oh, pl, ph);
    return { value: -r.value, best: -1, exact: r.exact };
  }
  let order = [];
  for (let i = 0; i < n; i++) order.push(buf[i]);
  order.sort((a, b) => SQ_ORDER[b] - SQ_ORDER[a]);
  if (empties <= 14) {
    deadline = Date.now() + 4000;
    try { const r = solveRoot(pl, ph, ol, oh, order, empties); deadline = Infinity; return { value: r.score, best: r.move, exact: true }; }
    catch (e) { if (e !== ABORT) throw e; }
    deadline = Infinity;
  }
  let res = null;
  deadline = Date.now() + 1500;
  try {
    for (let d = 1; d <= Math.min(6, empties); d++) {
      res = rootSearch(pl, ph, ol, oh, d, order, false);
      order = sortByScores(order, res.scores);
    }
  } catch (e) { if (e !== ABORT) throw e; }
  deadline = Infinity;
  let v = res ? res.score : 0;
  if (v >= WIN - 64) v = v - WIN; else if (v <= -WIN + 64) v = v + WIN;
  return { value: v, best: res ? res.move : order[0], exact: false };
}

/* ---------- 画面側でも使う小さな道具 ---------- */
const START = { bl: (1 << 28) | 0, bh: 1 << (35 - 32), wl: 1 << 27, wh: 1 << (36 - 32) };
function movesOf(pl, ph, ol, oh) {
  genMoves(pl, ph, ol, oh);
  const buf = new Int8Array(32), n = listMoves(ML, MH, buf), out = [];
  for (let i = 0; i < n; i++) out.push(buf[i]);
  return out;
}
function flipsOf(sq, pl, ph, ol, oh) {
  getFlips(sq, pl, ph, ol, oh);
  const buf = new Int8Array(32), out = [];
  const n = listMoves(FL, FH, buf);
  for (let i = 0; i < n; i++) out.push(buf[i]);
  return out;
}

const Engine = { setOrderSearch(v) { ORDER_SEARCH = v; }, loadEval, useEval, evaluateP, get hasPattern() { return !!PAT; }, scoreMoves, pc, genMoves, movesOf, flipsOf, applyMove, think, analyzePosition, evaluate, finalScore, solve, search, LEVELS, START, W, ttClear, etClear, get nodes() { return nodes; } };

/* ---------- Worker として動いているときの受け口 ---------- */
if (typeof WorkerGlobalScope !== 'undefined' && self instanceof WorkerGlobalScope) {
  // 神の点数表は起動したらすぐ読み込みはじめる。読み終わる前に神の番が来たら待つ
  const evalReady = fetch('eval.bin').then(r => (r.ok ? r.arrayBuffer() : null)).then(b => { if (b) loadEval(b); }).catch(() => {});
  self.onmessage = async (ev) => {
    const m = ev.data;
    if ((m.cmd === 'think' && LEVELS[m.level] && LEVELS[m.level].pattern) || m.cmd === 'analyze') await evalReady;
    if (m.cmd === 'think') {
      const [pl, ph, ol, oh] = m.board;
      const r = think(pl, ph, ol, oh, m.level);
      self.postMessage({ id: m.id, cmd: 'think', move: r.move, info: r });
    } else if (m.cmd === 'analyze') {
      // m.positions: [{p:[pl,ph,ol,oh]}...]（それぞれの手番側から見た盤）
      const out = [];
      useEval('pattern');     // 振り返りは、いちばん良い見立てで調べる
      for (let i = 0; i < m.positions.length; i++) {
        out.push(analyzePosition(...m.positions[i]));
        self.postMessage({ id: m.id, cmd: 'progress', done: i + 1, total: m.positions.length });
      }
      self.postMessage({ id: m.id, cmd: 'analyze', result: out });
    }
  };
} else if (typeof module !== 'undefined') {
  module.exports = Engine;
} else {
  self.Engine = Engine;
}
