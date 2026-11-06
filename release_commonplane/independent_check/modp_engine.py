"""D2 (Stiefel rows) and D3 (cut-(3,) blocks) at every B_i, modulo a prime p (or with absolute values for bounds).

For B_i (variable block v, coordinate j) and every ordering lam of st_v, the Gram-coordinate tensor of the block is
the factor-permuted H_j = W S_j W^T, paired per factor: (f_0^2, ..., f_3^2, a^2).  Then:
  Stiefel  S_0(B_i) = sum_lam ((x)_l tr0_l[lam_l] (x) st_aux)(gten_lam)  -> (6,6,6,6,70); sorted S3 tuples kept;
  cut (3,) H'_{st',ai'}(B_i) = sum_lam ((x)_l T3[st'_l <- lam_l] (x) aux transfer)(gten_lam) -> F_b = V_b^T H' V_b.
Scalings: tr0 x 192, T3 x 192, aux Stiefel x 2 (all integral), so
  St_mine = 192^4 * 2 * coefficient,   F3_mine = 192^4 * V^T H' V  (= the producer's stored scaling for cut (3,)).
usage: modp_engine.py MODE CHUNK NCHUNK OUT    (MODE = prime p, or 'abs')"""
import sys
import time
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload
from aud_common import *

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
mode = sys.argv[1]
chunk, nchunk = int(sys.argv[2]), int(sys.argv[3])
outpath = sys.argv[4]
ABS = mode == 'abs'
p = None if ABS else int(mode)
S = safeload.load(W_ + 'pkt/struct_k4d3_min.pkl')
LOC = pickle.load(open(W_ + 'work/local.pkl', 'rb'))
f0 = [LOC['site'][((), l)]['f'] for l in range(4)]
f3 = [LOC['site'][((3,), l)]['f'] for l in range(4)]
ab0, ab3 = LOC['aux']['blocks'][()], LOC['aux']['blocks'][(3,)]
a0, a3 = [len(b) for b in ab0], [len(b) for b in ab3]
offs = LOC['offs']


def integral(M, scale):
    out = np.zeros(M.shape, dtype=object)
    for idx, x in np.ndenumerate(M):
        y = Fraction(x) * scale
        assert y.denominator == 1
        out[idx] = int(y)
    return out


def to_field(A):
    """object/int array -> float64 array (mod p, or absolute values)."""
    A = np.asarray(A, dtype=object)
    if ABS:
        return np.array([abs(int(x)) for x in A.ravel()], dtype=np.float64).reshape(A.shape)
    return np.array([int(x) % p for x in A.ravel()], dtype=np.float64).reshape(A.shape)


def red(X):
    if not ABS:
        np.fmod(X, p, out=X)
    return X


# local maps restricted to label blocks: (out x f^2)
tr0 = integral(LOC['maps']['tr0'], 192)                        # 6 x 23
T3 = {l: integral(LOC['maps'][('cut3', l)], 192) for l in (2, 3)}
tr0_lab = {lam: to_field(tr0[:, offs[lam]:offs[lam] + f0[lam] ** 2]) for lam in range(4)}
T3_lab = {(lp, lam): to_field(T3[lp][:, offs[lam]:offs[lam] + f0[lam] ** 2]) for lp in (2, 3) for lam in range(4)}
# aux Stiefel restricted to weight block ai: (70 x a^2), scaled x 2
aux_coord = LOC['aux']['coord']
st_aux = integral(LOC['aux']['st'], 2)
st_aux_blk = {}
t3_src = {}
for ai in range(5):
    ks = [k for k, (w, i, j) in enumerate(aux_coord) if w == ai]
    assert [aux_coord[k][1] * a0[ai] + aux_coord[k][2] for k in ks] == list(range(a0[ai] ** 2))
    st_aux_blk[ai] = to_field(st_aux[:, ks])
    for k_loc, k in enumerate(ks):
        c, i1, i2 = LOC['aux']['t3'][k]
        t3_src.setdefault((ai, c), ([], []))
        t3_src[(ai, c)][0].append(k_loc)
        t3_src[(ai, c)][1].append(i1 * a3[c] + i2)
sorted_tuples = [q for q in itertools.product(range(6), repeat=4) if list(q) == sorted(q)]
assert len(sorted_tuples) == 126
sorted_flat = np.array([((q[0] * 6 + q[1]) * 6 + q[2]) * 6 + q[3] for q in sorted_tuples])

outs3 = [(bi, o) for bi, o in enumerate(S['outputs']) if o['cut'] == (3,)]
by3 = {}
for bi, o in outs3:
    by3.setdefault((tuple(o['st']), o['ai']), []).append((bi, to_field(o['V'])))
classes3 = sorted(by3)


def mode_mul(X, M, axis):
    """Mode product: contract axis `axis` of X (absolute index, length n) with M (r x n); result has length r there."""
    Xm = np.moveaxis(X, axis, -1)
    shp = Xm.shape
    R = Xm.reshape(-1, shp[-1]) @ M.T
    red(R)
    return np.moveaxis(R.reshape(shp[:-1] + (M.shape[0],)), -1, axis)


variables = S['variables']
mine = [vi for vi in range(len(variables)) if vi % nchunk == chunk]
F3 = {bi: {} for bi, _ in outs3}
ST = {}
for vi in mine:
    v = variables[vi]
    st, ai, off = tuple(v['st']), v['ai'], v['off']
    W = np.array(v['W'], dtype=object)
    Hs = []
    for B in v['basis']:
        H = W.dot(np.array(B, dtype=object)).dot(W.T)
        Hs.append(H)
    mb = len(Hs)
    shape = [f0[x] for x in st] + [a0[ai]]
    nH = int(np.prod(shape))
    Hst = to_field(np.array(Hs, dtype=object)).reshape([mb] + shape + shape)
    # pair row/col per factor: (mb, f0,f0, f1,f1, ..., a,a) -> (mb, f0^2, ..., a^2)
    order = [0]
    for l in range(5):
        order += [1 + l, 6 + l]
    base = np.ascontiguousarray(Hst.transpose(order)).reshape([mb] + [s * s for s in shape])
    st_acc = np.zeros((mb, 126, 70))
    f3_acc = {}
    for lam in sorted(set(itertools.permutations(st))):
        # site permutation pi with lam_l = st_{pi^-1(l)}: take the axes of base in that order
        used = [False] * 4
        src = []
        for l in range(4):
            for s_ in range(4):
                if not used[s_] and st[s_] == lam[l]:
                    used[s_] = True
                    src.append(s_)
                    break
        g = np.ascontiguousarray(np.transpose(base, [0] + [1 + s_ for s_ in src] + [5]))
        # ---- Stiefel
        X = mode_mul(g, st_aux_blk[ai], 5)
        for l in sorted(range(4), key=lambda l: -f0[lam[l]]):
            X = mode_mul(X, tr0_lab[lam[l]], 1 + l)
        X = X.reshape(mb, 6 ** 4, 70)[:, sorted_flat, :]
        st_acc += X
        red(st_acc)
        # ---- cut (3,)
        for (st2, ai2) in classes3:
            key = (ai, ai2)
            if key not in t3_src:
                continue
            sidx, tidx = t3_src[key]
            Y = np.zeros(g.shape[:5] + (a3[ai2] ** 2,))
            Y[..., tidx] = g[..., sidx]
            for l in sorted(range(4), key=lambda l: -f0[lam[l]]):
                Y = mode_mul(Y, T3_lab[(st2[l], lam[l])], 1 + l)
            f3_acc[(st2, ai2)] = f3_acc.get((st2, ai2), 0) + Y
            red(f3_acc[(st2, ai2)])
    for j in range(mb):
        ST[off + j] = st_acc[j]
    for (st2, ai2), Y in f3_acc.items():
        shape2 = [f3[x] for x in st2] + [a3[ai2]]
        n2 = int(np.prod(shape2))
        Yt = Y.reshape([mb] + [s for x in shape2 for s in (x, x)])
        inv_order = [0] + [1 + 2 * l for l in range(5)] + [2 + 2 * l for l in range(5)]
        Hp = np.ascontiguousarray(Yt.transpose(inv_order)).reshape(mb, n2, n2)
        for bi, V in by3[(st2, ai2)]:
            for j in range(mb):
                A = V.T @ Hp[j]
                red(A)
                Fb = A @ V
                red(Fb)
                F3[bi][off + j] = Fb
    log('variable %d st=%s ai=%d mb=%d orderings=%d done' % (vi, st, ai, mb, len(set(itertools.permutations(st)))))
pickle.dump({'mode': mode, 'vars': mine, 'F3': F3, 'ST': ST}, open(outpath, 'wb'), protocol=4)
log('saved %s' % outpath)
