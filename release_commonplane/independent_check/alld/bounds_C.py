"""Verdict 4, step C (own code): the Lemma-5.3 chain at s0 = 2^-T, in exact rationals.
  At(s) = Dr A_RS(s) Dc = At_0 + sum_{i>=1} s^i At_i;  e(s) = sum_{i>=1} s^i ||At_i||_inf;  theta0, beta from step B.
  If beta e(s) < 1:  ||At(s)^-1||_inf <= kappa(s) = beta / (1 - beta e(s)).
  delta_S = Dc At(s)^-1 Dr r_R(s),  r(s) = c(s) - A(s) x0 = sum_{j>=1} s^j r_j  (r_0 = 0 exactly, step A);
  ||At^-1 Dr r_R||_inf <= kappa(s) rho(s),  rho(s) = sum_{j>=1} s^j ||Dr (r_j)_R||_inf.
  Block b (unknowns of b in S): ||dY_b(s)||_F <= r_b * max_{S(b)} Dc * kappa rho  <  tau_b - ||dYn_b/D||_F  (lambda_min(Yhat_b(0)) >= that).
  Left kernel: rows Q (|Q| = q) with W_Q(0) invertible, T ~ W_Q(0)^-1 (dyadic):  theta_W + sum_{j>=1} s^j ||W_Q,j T||_inf < 1
  => W(s) has rank q  => rank A(s) <= 3N - q = |S|;  At(s) invertible => rank A(s) = |S| and left kernel = span W(s);
  W^T c == 0 (verdict 3) => c(s) in range A(s) => A(s)(x0 + delta(s)) = c(s)  (paper A Lemma 5.3 argument).
All bounds are polynomials in s with nonnegative coefficients (kappa increasing while beta e < 1), so s0 covers (0, s0].
Usage: bounds_C.py T"""
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
T = int(sys.argv[1])
s0 = Fraction(1, 2 ** T)
B = pickle.load(open(W_ + 'alld/work/bB.pkl', 'rb'))
f, g, theta0, beta = B['f'], B['g'], B['theta0'], B['beta']
C = safeload.load(W_ + 'alld/bundle/xcert4inf.pkl')
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
N = P['N']
R = [int(r) for r in C['rows']]
sel = C['sel_info']
n = len(sel)
D = int(C['D'])
normA, normr = {}, {}
for fn in ('bA_1_4.pkl', 'bA_5_8.pkl'):
    A = pickle.load(open(W_ + 'alld/work/' + fn, 'rb'))
    for j in A['orders']:
        rs = [0] * n                                     # row sums of |A_ik| 2^(G - g_k), integers
        G = max(g)
        for (i, k), v in A['At'][j].items():
            rs[i] += abs(v) << (G - g[k])
        normA[j] = max(Fraction(rs[i], 2 ** (G + f[i])) for i in range(n))
        rj = A['rD'][j]
        normr[j] = max(abs(rj[R[t]]) / 2 ** f[t] if f[t] >= 0 else abs(rj[R[t]]) * 2 ** (-f[t]) for t in range(n))
        log('order %d: ||At_j||_inf = %.4e, ||Dr (r_j)_R||_inf = %.4e' % (j, float(normA[j]), float(normr[j])))
    del A
# orders 9..16 of r = c (A has degree <= 8)
tgt = [[Fraction(x) for x in c] for c in P['c']['ca']], [[Fraction(x) for x in c] for c in P['c']['cb']], \
      [[2 * Fraction(x) for x in c] for c in P['c']['cab']]
assert max(b['deg'] for b in P['blocks']) <= 8 and len(P['Ecoef']) <= 9
for j in range(9, len(tgt[0])):
    vals = [tgt[r // N][j][r % N] for r in R]
    normr[j] = max(abs(v) * Fraction(2) ** (-f[t]) for t, v in enumerate(vals))
    log('order %d: ||Dr (c_j)_R||_inf = %.4e' % (j, float(normr[j])))
e0 = sum(s0 ** i * normA[i] for i in normA)
rho = sum(s0 ** j * normr[j] for j in normr)
be = beta * e0
log('theta0 %.4e, beta %.4e, e(s0) %.4e, beta*e(s0) %.4e (< 1/2: %s), rho(s0) %.4e' % (
    float(theta0), float(beta), float(e0), float(be), be < Fraction(1, 2), float(rho)))
assert be < 1
kappa = beta / (1 - be)
dnorm = kappa * rho                                       # >= ||At^-1 Dr r_R||_inf
# block margins
ys = {}
for k, u in enumerate(sel):
    if u[0] == 'Y':
        ys.setdefault(u[1], []).append(k)


def ldl_pos(Mq):
    nn = Mq.nrows()
    A_ = [[Mq[i, j] for j in range(nn)] for i in range(nn)]
    for kk in range(nn):
        piv = A_[kk][kk]
        if piv <= 0:
            return False
        for i in range(kk + 1, nn):
            if A_[i][kk] != 0:
                fct = A_[i][kk] / piv
                for j in range(kk, nn):
                    A_[i][j] -= fct * A_[kk][j]
    return True


worst = None
nfail = 0
for b, ks in ys.items():
    Yi, s = C['Yq'][b]
    Yi = np.asarray(Yi, dtype=object)
    r = Yi.shape[0]
    lm = float(np.linalg.eigvalsh(np.array(Yi, dtype=float) / 2.0 ** int(s)).min())
    kk = math.ceil(-math.log2(lm / 2))
    tau = Fraction(1, 2 ** kk)
    sh = flint.fmpq(2 ** int(s), 2 ** kk)
    Aq = flint.fmpq_mat(r, r, [flint.fmpq(int(Yi[i, j])) - (sh if i == j else 0) for i in range(r) for j in range(r)])
    assert ldl_pos(Aq), ('Yhat - tau I not PD', b)
    fro2 = sum(int(x) ** 2 for x in np.asarray(C['dYn'][b], dtype=object).ravel())
    margin = tau - Fraction(math.isqrt(fro2) + 1, D)
    need = r * max(Fraction(1, 2 ** g[k]) for k in ks) * dnorm
    ratio = need / margin
    worst = ratio if worst is None or ratio > worst else worst
    nfail += not (margin > 0 and need < margin)
log('blocks with unknowns in S: %d; failures %d; worst (needed correction bound) / margin = %.4e' % (len(ys), nfail, float(worst)))
# left kernel rank certificate
LK = safeload.load(W_ + 'alld/bundle/xlk4.pkl')
Wc = [np.asarray(Wj, dtype=object) for Wj in LK['coefs']]
q = Wc[0].shape[1]
W0 = flint.fmpq_mat(3 * N, q, [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for x in Wc[0].ravel()])
# choose q independent rows greedily via rref of W0^T
Rr, rk = W0.transpose().rref()
assert rk == q
piv = []
for i in range(q):
    for j in range(3 * N):
        if Rr[i, j] != 0:
            piv.append(j)
            break
WQ0 = np.array([[float(Fraction(int(W0[r_, c].p), int(W0[r_, c].q))) for c in range(q)] for r_ in piv])
Tf = np.linalg.inv(WQ0)
kt = 50 - int(math.ceil(math.log2(np.abs(Tf).max())))
Tq = flint.fmpq_mat(q, q, [flint.fmpq(int(x), 2 ** kt) for x in np.rint(np.ldexp(Tf, kt)).astype(np.int64).ravel()])


def subW(j):
    return flint.fmpq_mat(q, q, [flint.fmpq(int(Fraction(Wc[j][r_, c]).numerator), int(Fraction(Wc[j][r_, c]).denominator)) for r_ in piv for c in range(q)])


def ninf(M):
    return max(sum(abs(Fraction(int(M[i, j].p), int(M[i, j].q))) for j in range(M.ncols())) for i in range(M.nrows()))


I = flint.fmpq_mat(q, q, [1 if i == j else 0 for i in range(q) for j in range(q)])
thW = ninf(I - subW(0) * Tq)
pert = sum(s0 ** j * ninf(subW(j) * Tq) for j in range(1, len(Wc)) if any(x != 0 for x in Wc[j].ravel()))
log('left kernel: rows Q chosen (%d), theta_W = %.4e, sum_j s0^j ||W_Q,j T||_inf = %.4e  -> rank certificate %s' % (
    len(piv), float(thW), float(pert), thW + pert < 1))
ok = be < 1 and nfail == 0 and thW + pert < 1
print('BOUNDS_RESULT s0 = 2^-%d: %s (beta e %.3e, worst block ratio %.3e, W %.3e)' % (T, 'PASS' if ok else 'FAIL', float(be), float(worst), float(thW + pert)))
