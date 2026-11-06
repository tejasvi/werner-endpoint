"""Gram matrix of the orbit sums, its exact rank, and the objective / trace functionals on orbit sums.

Objective (paper A s.3.5 with b = (I x M) a, M = sqrt2 diag(cos th, sin th), replicas 1..4 -> 0..3):
  c_th(X) = L^-1 Tr[(Z_t)_{03} M_3 X M_3],  Z_t = F_Q prod_sites (I - t F_l),  t = 1/2,  L = (2 d^k)^4.
On a word V_w x |r><s|:
  c_th = L^-1 prod_l (d^kappa(w_l) - t d^kappa((03) o w_l)) * [s = swap03(r)] * m_{r_0} m_{r_3},
  m = sqrt2 (cos th, sin th), so m_i m_j = 2 v_i v_j with v = (cos th, sin th).
  c_th = sum_ij v_i v_j K_ij,  K_ij = 2/L * S(w) [s = swap03(r)] [r_0 = i][r_3 = j].
  Symmetric 2x2: C00 = K00, C11 = K11, C01 = (K01 + K10)/2.
Trace: tau(X) = L^-1 Tr X;  Tr(V_w x |r><s|) = prod_l d^kappa(w_l) [r = s].
"""
import sys
import time
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
from aud_common import *

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W = '<ROOT>/independent_check/work/'
Z = np.load(W + 'orbits.npz')
oid, rep, size = Z['oid'], Z['rep'], Z['size']
NO = len(rep)
d = D_SITE
L = (2 * d ** K_SITES) ** 4
log('orbits %d, L = %d' % (NO, L))

# ---------------- Gram matrix G[o,o'] = Tr(V_o^T V_o') = |o| * Tr(V_rep(o)^T V_o')
oid5 = oid.reshape(NP, NP, NP, NP, NA)
dpow = np.array([d ** k for k in range(5)], dtype=np.int64)
G = np.zeros((NO, NO), dtype=object)
for o in range(NO):
    c = int(rep[o])
    uu = c % NA
    rest = c // NA
    ws = []
    for _ in range(4):
        ws.append(rest % NP)
        rest //= NP
    ws = ws[::-1]                                   # w0..w3
    vecs = [dpow[KAPPA[MUL[INV[wl], :]]] for wl in ws]   # Tr(V_wl^T V_q) = d^kappa(wl^-1 q), q = 0..23
    val = np.einsum('a,b,c,e->abce', *vecs).astype(np.float64).ravel()
    row = np.bincount(oid5[:, :, :, :, uu].ravel(), weights=val, minlength=NO)
    assert np.all(row == np.rint(row)) and row.max() < 2 ** 52
    G[o, :] = [int(x) * int(size[o]) for x in np.rint(row).astype(np.int64)]
log('Gram matrix built')
assert all(G[i, j] == G[j, i] for i in range(NO) for j in range(i))
log('Gram symmetric')
Gf = flint.fmpz_mat(NO, NO, [int(x) for x in G.ravel()])
rk = Gf.rank()
log('rank of the Gram matrix of orbit sums (d=%d): %d of %d' % (d, rk, NO))

# ---------------- objective and trace on orbit sums (exact integers / common denominators)
w0, w1, w2, w3, u = decode_all()
swap03 = PIDX[(3, 1, 2, 0)]
S2 = 2 * dpow[KAPPA] - dpow[KAPPA[MUL[swap03, :]]]     # 2 (d^kappa(p) - 1/2 d^kappa((03) p)), integer
Sw = S2[w0] * S2[w1] * S2[w2] * S2[w3]                  # = 16 S(w)
del w1, w2, w3
auxK = np.zeros((2, 2, NA), dtype=np.int64)
auxT = np.zeros(NA, dtype=np.int64)
for ui, (r, s) in enumerate(AUX):
    br, bs = BITS[r], BITS[s]
    if bs == (br[3], br[1], br[2], br[0]):
        auxK[br[0], br[3], ui] = 1
    if r == s:
        auxT[ui] = 1


def orbit_sum_int(vals):
    order = np.argsort(oid, kind='stable')
    so = oid[order]
    starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
    sums = np.add.reduceat(vals[order], starts)
    out = np.zeros(NO, dtype=object)
    for idx, v in zip(so[starts], sums):
        out[int(idx)] = int(v)
    return out


Kij = {}
for i in range(2):
    for j in range(2):
        vals = Sw * auxK[i, j][u]
        assert np.abs(vals).max() < 2 ** 62 // 30000
        Kij[(i, j)] = orbit_sum_int(vals)              # sum_w 16 S(w) [...]
# K_ij(V_o) = 2/L * (1/16) * sum = sum / (8 L)
C00 = [Fraction(int(x), 8 * L) for x in Kij[(0, 0)]]
C11 = [Fraction(int(x), 8 * L) for x in Kij[(1, 1)]]
C01 = [Fraction(int(a) + int(b), 16 * L) for a, b in zip(Kij[(0, 1)], Kij[(1, 0)])]
log('K01 == K10 on every orbit sum: %s' % all(int(a) == int(b) for a, b in zip(Kij[(0, 1)], Kij[(1, 0)])))
del Sw, w0
w0b, w1b, w2b, w3b, _ = decode_all()
tvals = dpow[KAPPA[w0b]] * dpow[KAPPA[w1b]] * dpow[KAPPA[w2b]] * dpow[KAPPA[w3b]] * auxT[u]
TR = [Fraction(int(x), L) for x in orbit_sum_int(tvals)]
log('objective nonzeros C00 %d C11 %d C01 %d; trace nonzeros %d' % (
    sum(1 for x in C00 if x), sum(1 for x in C11 if x), sum(1 for x in C01 if x), sum(1 for x in TR if x)))
import pickle
pickle.dump({'G': G, 'rank': rk, 'C00': C00, 'C11': C11, 'C01': C01, 'TR': TR, 'L': L},
            open(W + 'gram_obj.pkl', 'wb'), protocol=4)
log('saved work/gram_obj.pkl')
