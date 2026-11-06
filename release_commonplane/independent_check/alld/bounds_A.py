"""Verdict 4, step A (own code).  Exact assembly, from the polynomial data (xpoly4.pkl) and the limit certificate
(xcert4inf.pkl: x0, column set S = sel_info, row set R = rows), of
   A_RS,j  (rows R, columns S, order j in s)   and   r_j = c_j - A_j x0  (all 3N rows),  j = 0..16.
Unknowns: ('lam', c, e): lambda_c of equality row erows[e];  ('Y', b, a, bb): Yhat_b[a,bb] (= [bb,a]), Z_b = N_b Yhat_b N_b^T.
Row (c, i) = c*N + i;  target (c_a, c_b, 2 c_ab).  Coefficient of Yhat_b[a,bb] in row (c,i): <Fhat_b[i](s), M_c> with
M_a = N1 S N1^T, M_b = N2 S N2^T, M_ab = N1 S N2^T + N2 S N1^T, S = E_{a,bb} + E_{bb,a} (a != bb) or E_aa.
Exact integer arithmetic with flint (D x0 is integral).  Usage: bounds_A.py ORDERS OUT   (ORDERS e.g. '0' or '1-8')."""
import sys
import time
import math
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
a_, b_ = (sys.argv[1].split('-') + [None])[:2]
orders = list(range(int(a_), int(b_ if b_ is not None else a_) + 1))
out = sys.argv[2]
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
Linf = safeload.load('<ROOT>/certificates/alld/xk4dinf_s2.pkl')
C = safeload.load(W_ + 'alld/bundle/xcert4inf.pkl')
N = P['N']
D = int(C['D'])
erows = [int(e) for e in C['erows']]
sel = C['sel_info']
R = [int(r) for r in C['rows']]
rowpos = {r: k for k, r in enumerate(R)}
assert len(sel) == len(R) == 4780 and len(set(R)) == 4780
tk = lambda t: None if t is None else tuple(t)
pk = {(b['cut'], tuple(b['st']), b['ai'], tk(b['tau'])): b for b in P['blocks']}


def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


def ent(Mf):
    return np.array([int(x) for x in Mf.entries()], dtype=object).reshape(Mf.nrows(), Mf.ncols())


# D x0
lamD = [[int(x) for x in C['lam_n'][c]] for c in range(3)]
YD = {}
for b in C['N']:
    Yi, s = C['Yq'][b]
    assert D % (1 << int(s)) == 0
    YD[b] = np.asarray(Yi, dtype=object) * (D >> int(s)) + np.asarray(C['dYn'][b], dtype=object)
# unknowns by block
ycols = {}
lamcols = []
for k, u in enumerate(sel):
    if u[0] == 'Y':
        ycols.setdefault(u[1], []).append((k, int(u[2]), int(u[3])))
    else:
        assert u[0] == 'lam'
        lamcols.append((k, int(u[1]), int(u[2])))
assert all(b in C['N'] for b in ycols)
# targets
tgt = [[Fraction(x) for x in c] for c in P['c']['ca']], [[Fraction(x) for x in c] for c in P['c']['cb']], \
      [[2 * Fraction(x) for x in c] for c in P['c']['cab']]
res = {'orders': orders, 'At': {}, 'rD': {}}
for j in orders:
    At = {}                      # (rowpos, col) -> int
    AxD = [[0] * N for _ in range(3)]     # D * (A_j x0) rows (c, i)
    for b, Nb in C['N'].items():
        lb = Linf['blocks'][b]
        pb = pk[(lb['cut'], tuple(lb['st']), lb['ai'], tk(lb['tau']))]
        if j >= len(pb['coef']):
            continue
        m = pb['m']
        Nb = np.asarray(Nb, dtype=object)
        N1, N2 = Nb[:m], Nb[m:]
        Fj = fz(np.asarray(pb['coef'][j], dtype=object).reshape(N, m * m))
        # x0 part: P_c(Z0) with Z0 = N YD N^T
        Z = Nb.dot(YD[b]).dot(Nb.T)
        Pm = [Z[:m, :m], Z[m:, m:], Z[:m, m:] + Z[m:, :m].T]
        Pv = fz(np.array([M.ravel() for M in Pm], dtype=object).T)              # m^2 x 3
        X = ent(Fj * Pv)                                                         # N x 3
        for c in range(3):
            for i in range(N):
                AxD[c][i] += int(X[i, c])
        if b in ycols:
            cols = []
            for (k, a, bb) in ycols[b]:
                Sm = np.zeros((Nb.shape[1], Nb.shape[1]), dtype=object)
                Sm[a, bb] = 1
                Sm[bb, a] = 1
                Ms = [N1.dot(Sm).dot(N1.T), N2.dot(Sm).dot(N2.T), N1.dot(Sm).dot(N2.T) + N2.dot(Sm).dot(N1.T)]
                for c in range(3):
                    cols.append(Ms[c].ravel())
            G = fz(np.array(cols, dtype=object).T)                               # m^2 x 3k
            K = ent(Fj * G)                                                      # N x 3k
            for t, (k, a, bb) in enumerate(ycols[b]):
                for c in range(3):
                    colv = K[:, 3 * t + c]
                    for i in np.flatnonzero(colv != 0):
                        r = c * N + int(i)
                        if r in rowpos:
                            At[(rowpos[r], k)] = int(colv[i])
    # equality rows
    if j < len(P['Ecoef']):
        Ej = P['Ecoef'][j]
        for c in range(3):
            for e in range(len(erows)):
                row = Ej[erows[e]]
                le = lamD[c][e]
                if le:
                    for i in range(N):
                        if row[i]:
                            AxD[c][i] += int(row[i]) * le
        for (k, c, e) in lamcols:
            row = Ej[erows[e]]
            for i in range(N):
                if row[i]:
                    r = c * N + i
                    if r in rowpos:
                        At[(rowpos[r], k)] = int(row[i])
    # r_j = target_j - A_j x0 (exact), all rows
    rD = []
    for c in range(3):
        for i in range(N):
            tj = tgt[c][j][i] if j < len(tgt[c]) else Fraction(0)
            rD.append(tj - Fraction(AxD[c][i], D))
    res['At'][j] = At
    res['rD'][j] = rD
    nzr = sum(1 for x in rD if x != 0)
    mx = max(abs(x) for x in rD)
    log('order %d: A_RS nonzeros %d; r_j nonzero rows %d, max |r_j| %.3e' % (j, len(At), nzr, float(mx)))
pickle.dump(res, open(out, 'wb'), protocol=4)
log('saved %s' % out)
