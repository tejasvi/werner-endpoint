"""D2 (Stiefel rows) and D3 (cut-(3,) S2 blocks) at every B_i of the S2 coordinate system, at dimension d (or the s = 0 limit),
modulo a prime p (or with absolute values for bounds).  Same assembly as ../modp_engine.py (d = 3 audit), with the local maps of
local4.py evaluated at d:
  cut (3,) site maps x 576 (integral), tr0 x 576, aux Stiefel x 2.
  DSPEC = integer d >= 4: maps at d;  DSPEC = 'inf': top-degree coefficients (d^2 for f = 1 labels, d^0 for f = 0 labels,
  d^1 for tr0), i.e. the s = 0 limit of the scaled data d^-deg F_b(d), d^-4 E_r(d).
  F3_mine = 576^4 V_b^T H'(B_i) V_b (at d), St_mine = 576^4 * 2 * Stiefel coefficient (sorted S3-word tuple, aux unit).
usage: engine4.py MODE DSPEC CHUNK NCHUNK OUT    (MODE = prime p or 'abs')"""
import os
import sys
import time
import itertools
import pickle
from fractions import Fraction
W_ = os.environ.get('AUDIT_W', '<ROOT>/independent_check/')
sys.path.insert(0, W_)
import numpy as np
import safeload

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
mode, dspec = sys.argv[1], sys.argv[2]
chunk, nchunk = int(sys.argv[3]), int(sys.argv[4])
outpath = sys.argv[5]
ABS = mode == 'abs'
p = None if ABS else int(mode)
S = safeload.load(W_ + 'alld/bundle/struct_k4d4_s2.pkl')
LOC = pickle.load(open(W_ + 'alld/work/local4.pkl', 'rb'))
f0, f3, offs = LOC['f0'], LOC['f3'], LOC['offs']
LAB3 = LOC['LAB3']
ab0, ab3 = LOC['aux']['blocks'][()], LOC['aux']['blocks'][(3,)]
a0, a3 = [len(b) for b in ab0], [len(b) for b in ab3]


def poly_at(key, top):
    co = LOC['poly'][key]
    if dspec == 'inf':
        return co[top] if top < len(co) else np.zeros_like(co[0])
    d = int(dspec)
    if ABS:                       # entrywise sum_e |c_e| d^e: a bound valid for every d' <= d
        return sum(np.vectorize(lambda x: abs(Fraction(x)), otypes=[object])(c) * d ** e for e, c in enumerate(co))
    return sum(c * d ** e for e, c in enumerate(co))


def integral(M, scale):
    out = np.zeros(M.shape, dtype=object)
    for idx, x in np.ndenumerate(M):
        y = Fraction(x) * scale
        assert y.denominator == 1
        out[idx] = int(y)
    return out


def to_field(A):
    A = np.asarray(A, dtype=object)
    if ABS:
        return np.array([abs(int(x)) for x in A.ravel()], dtype=np.float64).reshape(A.shape)
    return np.array([int(x) % p for x in A.ravel()], dtype=np.float64).reshape(A.shape)


def red(X):
    if not ABS:
        np.fmod(X, p, out=X)          # values stay in (-p, p)
    return X


MAPMAX = {'site': 0, 'aux': 0, 'V': 0}


def map_field(A, kind='site'):
    """Small integer maps are kept SIGNED and unreduced (exact in float64); abs values in the bound pass."""
    A = np.asarray(A, dtype=object)
    mx = max([abs(int(x)) for x in A.ravel()] + [0])
    MAPMAX[kind] = max(MAPMAX[kind], mx)
    if ABS:
        return np.array([abs(int(x)) for x in A.ravel()], dtype=np.float64).reshape(A.shape)
    return np.array([int(x) for x in A.ravel()], dtype=np.float64).reshape(A.shape)


T3 = {l: integral(poly_at(('cut3', l), 2 * LAB3[l][0]), 576) for l in (2, 3, 4)}
tr0 = integral(poly_at('tr0', 1), 576)
tr0_lab = {lam: map_field(tr0[:, offs[lam]:offs[lam] + f0[lam] ** 2]) for lam in range(5)}
T3_lab = {(lp, lam): map_field(T3[lp][:, offs[lam]:offs[lam] + f0[lam] ** 2]) for lp in (2, 3, 4) for lam in range(5)}
aux_coord = LOC['aux']['coord']
st_aux = integral(LOC['aux']['st'], 2)
st_aux_blk, t3_src = {}, {}
for ai in range(5):
    ks = [k for k, (w, i, j) in enumerate(aux_coord) if w == ai]
    assert [aux_coord[k][1] * a0[ai] + aux_coord[k][2] for k in ks] == list(range(a0[ai] ** 2))
    st_aux_blk[ai] = map_field(st_aux[:, ks], 'aux')
    for k_loc, k in enumerate(ks):
        c, i1, i2 = LOC['aux']['t3'][k]
        t3_src.setdefault((ai, c), ([], []))
        t3_src[(ai, c)][0].append(k_loc)
        t3_src[(ai, c)][1].append(i1 * a3[c] + i2)
sorted_tuples = [q for q in itertools.product(range(6), repeat=4) if list(q) == sorted(q)]
sorted_flat = np.array([((q[0] * 6 + q[1]) * 6 + q[2]) * 6 + q[3] for q in sorted_tuples])
outs3 = [(bi, o) for bi, o in enumerate(S['outputs']) if o['cut'] == (3,)]
by3 = {}
for bi, o in outs3:
    assert all(x in (2, 3, 4) for x in o['st'])
    by3.setdefault((tuple(o['st']), o['ai']), []).append((bi, map_field(o['V'], 'V')))
classes3 = sorted(by3)
NOST = len(sys.argv) > 6 and sys.argv[6] == 'nost'
if not ABS:
    # exactness of every float64 step: |sum| <= (contraction length) * max|map| * p < 2^53
    nmax = max(np.prod([f3[x] for x in st2]) * a3[ai2] for (st2, ai2) in classes3)
    # site modes: length <= 9; aux Stiefel: length <= 36; V^T H' and (.) V: length <= nmax with |V| small
    assert 9 * MAPMAX['site'] * p < 2 ** 53, ('prime too large (site)', MAPMAX)
    assert 36 * MAPMAX['aux'] * p < 2 ** 53 and nmax * MAPMAX['V'] * p < 2 ** 53, ('prime too large (aux/V)', MAPMAX)
log('maps built: max |map entries| %s, prime %s, dspec %s' % (MAPMAX, mode, dspec))


def mode_mul(X, M, axis):
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
    Hs = [W.dot(np.array(B, dtype=object)).dot(W.T) for B in v['basis']]
    mb = len(Hs)
    shape = [f0[x] for x in st] + [a0[ai]]
    Hst = to_field(np.array(Hs, dtype=object)).reshape([mb] + shape + shape)
    order = [0]
    for l in range(5):
        order += [1 + l, 6 + l]
    base = np.ascontiguousarray(Hst.transpose(order)).reshape([mb] + [s * s for s in shape])
    st_acc = np.zeros((mb, 126, 70))
    f3_acc = {}
    for lam in sorted(set(itertools.permutations(st))):
        used, src = [False] * 4, []
        for l in range(4):
            for s_ in range(4):
                if not used[s_] and st[s_] == lam[l]:
                    used[s_] = True
                    src.append(s_)
                    break
        g = np.ascontiguousarray(np.transpose(base, [0] + [1 + s_ for s_ in src] + [5]))
        if not NOST:
            X = mode_mul(g, st_aux_blk[ai], 5)
            for l in sorted(range(4), key=lambda l: -f0[lam[l]]):
                X = mode_mul(X, tr0_lab[lam[l]], 1 + l)
            st_acc += X.reshape(mb, 6 ** 4, 70)[:, sorted_flat, :]
            red(st_acc)
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
log('d=%s mode=%s chunk %d/%d: %d variables done' % (dspec, mode, chunk, nchunk, len(mine)))
pickle.dump({'mode': mode, 'd': dspec, 'vars': mine, 'F3': F3, 'ST': ST}, open(outpath, 'wb'), protocol=4)
log('saved %s' % outpath)
