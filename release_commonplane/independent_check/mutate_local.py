"""M6: the cut-(3,) comparison must fail if my local transfer is wrong.  Mini-engine (cut (3,) only, prime 1048573)
for a few variable blocks with (a) the correct local maps (control: expect 0 mismatches) and (b) mutated maps:
partial transpose on site slot 2 instead of 3 (expect mismatches), (c) aux transfer without the aux transpose.
Also a unit test of the exact LDL positivity routine on an indefinite matrix."""
import sys
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload
from aud_common import *

W_ = '<ROOT>/independent_check/'
S = safeload.load(W_ + 'pkt/struct_k4d3_min.pkl')
Dat = safeload.load(W_ + 'p1x/slice/xk4_min.pkl')
LOC = pickle.load(open(W_ + 'work/local.pkl', 'rb'))
p = 1048573
d = 3
f0 = [LOC['site'][((), l)]['f'] for l in range(4)]
f3 = [LOC['site'][((3,), l)]['f'] for l in range(4)]
ab0, ab3 = LOC['aux']['blocks'][()], LOC['aux']['blocks'][(3,)]
a0, a3 = [len(b) for b in ab0], [len(b) for b in ab3]
offs = LOC['offs']
iota = np.array(LOC['iota'], dtype=object)
VP = [perm_matrix(d, q) for q in PERMS]


def site_T3(slot):
    out = {}
    for l in (2, 3):
        J3 = LOC['site'][((3,), l)]['J']
        Lmat = np.array([(J3.T @ partial_transpose(VP[q], d, (slot,)) @ J3).ravel() for q in range(24)], dtype=object)
        Lt = Lmat.T.dot(iota)                     # (9 x 23), Fractions
        out[l] = np.array([[int(Fraction(x) * 192) for x in row] for row in Lt], dtype=object)
    return out


def aux_t3(transpose_aux):
    src = {}
    where3 = {}
    for c, blk in enumerate(ab3):
        for i, s in enumerate(blk):
            where3[tuple(s)] = (c, i)
    for ai in range(5):
        blk = [tuple(b) for b in ab0[ai]]
        for i, r in enumerate(blk):
            for j, s in enumerate(blk):
                if transpose_aux:
                    rr, ss = (r[0], r[1], r[2], s[3]), (s[0], s[1], s[2], r[3])
                else:
                    rr, ss = r, s
                (c1, i1), (c2, i2) = where3[rr], where3[ss]
                if c1 != c2:
                    continue
                src.setdefault((ai, c1), ([], []))
                src[(ai, c1)][0].append(i * a0[ai] + j)
                src[(ai, c1)][1].append(i1 * a3[c1] + i2)
    return src


def mm(X, M, axis):
    Xm = np.moveaxis(X, axis, -1)
    shp = Xm.shape
    R = np.fmod(Xm.reshape(-1, shp[-1]) @ M.T, p)
    return np.moveaxis(R.reshape(shp[:-1] + (M.shape[0],)), -1, axis)


def run(T3, t3src, vlist):
    T3l = {(lp, lam): np.array([[int(x) % p for x in row] for row in T3[lp][:, offs[lam]:offs[lam] + f0[lam] ** 2]], dtype=np.float64)
           for lp in (2, 3) for lam in range(4)}
    outs = {}
    for bi, o in enumerate(S['outputs']):
        if o['cut'] == (3,):
            outs.setdefault((tuple(o['st']), o['ai']), []).append((bi, np.array([[int(x) % p for x in r] for r in o['V']], dtype=np.float64)))
    nbad = ncmp = 0
    for vi in vlist:
        v = S['variables'][vi]
        st, ai, off = tuple(v['st']), v['ai'], v['off']
        W = np.array(v['W'], dtype=object)
        Hs = [W.dot(np.array(B, dtype=object)).dot(W.T) for B in v['basis']]
        mb = len(Hs)
        shape = [f0[x] for x in st] + [a0[ai]]
        Hst = np.array([[int(x) % p for x in H.ravel()] for H in Hs], dtype=np.float64).reshape([mb] + shape + shape)
        order = [0] + [a for l in range(5) for a in (1 + l, 6 + l)]
        base = np.ascontiguousarray(Hst.transpose(order)).reshape([mb] + [s * s for s in shape])
        acc = {}
        for lam in sorted(set(itertools.permutations(st))):
            used, src = [False] * 4, []
            for l in range(4):
                for s_ in range(4):
                    if not used[s_] and st[s_] == lam[l]:
                        used[s_] = True
                        src.append(s_)
                        break
            g = np.transpose(base, [0] + [1 + s_ for s_ in src] + [5])
            for (st2, ai2) in outs:
                if (ai, ai2) not in t3src:
                    continue
                si, ti = t3src[(ai, ai2)]
                Y = np.zeros(g.shape[:5] + (a3[ai2] ** 2,))
                Y[..., ti] = g[..., si]
                for l in range(4):
                    Y = mm(Y, T3l[(st2[l], lam[l])], 1 + l)
                acc[(st2, ai2)] = np.fmod(acc.get((st2, ai2), 0) + Y, p)
        for (st2, ai2), lst in outs.items():
            Y = acc.get((st2, ai2))
            shape2 = [f3[x] for x in st2] + [a3[ai2]]
            n2 = int(np.prod(shape2))
            if Y is not None:
                Yt = Y.reshape([mb] + [s for x in shape2 for s in (x, x)])
                Hp = np.ascontiguousarray(Yt.transpose([0] + [1 + 2 * l for l in range(5)] + [2 + 2 * l for l in range(5)])).reshape(mb, n2, n2)
            for bi, V in lst:
                F = Dat['blocks'][bi]['F']
                for j in range(mb):
                    mine = np.fmod(np.fmod(V.T @ Hp[j], p) @ V, p).astype(np.int64) if Y is not None else np.zeros((V.shape[1],) * 2, dtype=np.int64)
                    prod = np.array([int(x) % p for x in F[off + j].ravel()], dtype=np.int64).reshape(mine.shape)
                    ncmp += 1
                    nbad += not np.array_equal(mine, prod)
    return ncmp, nbad


vlist = [147, 140, 100, 60]
print('variables tested:', [(vi, tuple(S['variables'][vi]['st']), S['variables'][vi]['ai']) for vi in vlist])
for name, T3, src in (('control (correct maps)', site_T3(3), aux_t3(True)),
                      ('site partial transpose on slot 2', site_T3(2), aux_t3(True)),
                      ('no aux partial transpose', site_T3(3), aux_t3(False))):
    ncmp, nbad = run(T3, src, vlist)
    print('M6 %s: %d (output block, coordinate) pairs, %d mismatches' % (name, ncmp, nbad))


def ldl_pos(Mq):
    n = Mq.nrows()
    A = [[Mq[i, j] for j in range(n)] for i in range(n)]
    for k in range(n):
        piv = A[k][k]
        if piv <= 0:
            return False
        for i in range(k + 1, n):
            if A[i][k] != 0:
                f = A[i][k] / piv
                for j in range(k, n):
                    A[i][j] -= f * A[k][j]
    return True


rng = np.random.default_rng(1)
B = rng.integers(-5, 6, size=(12, 12))
Mpd = B @ B.T + np.eye(12, dtype=np.int64)
lm = float(np.linalg.eigvalsh(Mpd.astype(float)).min())
for shift, expect in ((lm / 2, True), (lm + 1e-3, False)):
    sh = Fraction(shift).limit_denominator(10 ** 6)
    Mq = flint.fmpq_mat(12, 12, [flint.fmpq(int(Mpd[i, j])) - (flint.fmpq(sh.numerator, sh.denominator) if i == j else 0) for i in range(12) for j in range(12)])
    print('LDL unit test shift %.4f (lambda_min %.4f): positive = %s (expect %s)' % (float(sh), lm, ldl_pos(Mq), expect))
