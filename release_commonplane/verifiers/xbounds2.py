"""Rigorous bounds for the uniform-in-d certificate (paper A, Lemma 5.3 style), as xbounds.py but sized for k = 4 (rho x rho
matrices only, one order at a time, flint products) and with the final inequalities checked in exact rational arithmetic.
Scaled system A(s) x = c(s) (xpoly.py), exact limit certificate x0 with column set S and row set R (xrat4.py: sel_info, rows),
exact polynomial left-kernel certificate W(s) (xlkx.py, verified by xlkverify.py).  With At(s) = Dr A_RS(s) Dc (powers of two):
   delta_S(s) = Dc At(s)^-1 Dr r_R(s),  r(s) = c(s) - A(s) x0 = sum_{j>=1} s^j r_j        (r_0 = 0 exactly)
   ||At(s)^-1||_inf <= beta / (1 - beta e(s)),  e(s) = sum_{i>=1} s^i ||At_i||_inf,  beta = ||X||_inf / (1 - ||I - At_0 X||_inf)
   block b stays PD if r_b max_S(b) Dc ||At(s)^-1 Dr r_R(s)||_inf < tau_b - ||dY_b||_F      (Weyl, exact LDL of Yhat_b - tau_b I)
   sigma_q(W_sub(s)) >= sqrt(mu) - sum_{j>=1} s^j ||W_sub,j||_F > 0, so rank A(s) = n - q = rho and W^T c == 0 gives consistency.
Every bound is polynomial in s with nonnegative coefficients (beta(s) increasing), so the exact check at s0 = 2^-t covers (0, s0].
Usage: python xbounds2.py POLYPICKLE LIMITCERT LKPICKLE"""
import sys, os, pickle, time, math
from fractions import Fraction
import numpy as np
import flint
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xrat import ldl_pd

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)
P = pickle.load(open(sys.argv[1], 'rb')); cert = pickle.load(open(sys.argv[2], 'rb')); LK = pickle.load(open(sys.argv[3], 'rb'))
assert LK['ok']
N = P['N']; n = 3 * N
blocks = P['blocks']
sel = cert['sel_info']; rows = cert['rows']; erows = cert['erows']
rho = len(sel)
assert len(rows) == rho and n - LK['q'] == rho, 'need |S| = |R| = rho = n - q'
act = sorted(cert['N'])
JE = len(P['Ecoef'])
NORD = max(max(len(blocks[j]['coef']) for j in act), JE)
fz = lambda A: flint.fmpz_mat(A.shape[0], A.shape[1], [int(v) for v in np.asarray(A, dtype=object).ravel()])
def fz_entries(M_):
    return np.array([int(x) for x in M_.entries()], dtype=object).reshape(M_.nrows(), M_.ncols())
rowpos = np.full(n, -1); rowpos[rows] = np.arange(rho)
byb = {}
for idx, inf in enumerate(sel):
    if inf[0] == 'Y':
        byb.setdefault(inf[1], []).append((idx, inf[2], inf[3]))
Vb = {}
for j, lst in byb.items():
    m = blocks[j]['m']; Nm = cert['N'][j]
    Ms = []
    for idx, a, bb in lst:
        S = np.zeros((Nm.shape[1], Nm.shape[1]), dtype=object); S[a, bb] = 1; S[bb, a] = 1
        Z = Nm.dot(S).dot(Nm.T)
        Ms += [Z[:m, :m].ravel(), Z[m:, m:].ravel(), (Z[:m, m:] + Z[:m, m:].T).ravel()]
    Vb[j] = fz(np.stack(Ms, 1))
rN = [np.nonzero(rowpos[c * N:(c + 1) * N] >= 0)[0] for c in range(3)]     # rows of copy c inside R
def ARS_order(i):
    """A_RS,i exactly (rho x rho object array)."""
    A = np.zeros((rho, rho), dtype=object)
    for idx, inf in enumerate(sel):
        if inf[0] == 'lam' and i < JE:
            _, c, ee = inf
            col = P['Ecoef'][i][erows[ee]]
            A[rowpos[c * N + rN[c]], idx] = col[rN[c]]
    for j, lst in byb.items():
        b = blocks[j]; m = b['m']
        if i >= len(b['coef']):
            continue
        Rm = fz_entries(fz(b['coef'][i].reshape(N, m * m)) * Vb[j])
        for t, (idx, a, bb) in enumerate(lst):
            for c in range(3):
                A[rowpos[c * N + rN[c]], idx] = Rm[rN[c], 3 * t + c]
    return A
A0 = ARS_order(0)
absA0 = np.abs(A0)
lc = absA0.max(axis=0)
assert all(x > 0 for x in lc)
ec = [-(int(x).bit_length() - 1) for x in lc]                            # Dc[c] = 2^ec[c]
lr = [max(int(absA0[r, c]) * 2.0 ** ec[c] for c in range(rho)) for r in range(rho)]
er = [-int(math.floor(math.log2(x))) for x in lr]                        # Dr[r] = 2^er[r]
emin = min(ec) + min(er)
shift = np.array([[2 ** (er[r] + ec[c] - emin) for c in range(rho)] for r in range(rho)], dtype=object)
del absA0
def inf_norm_scaled(A):
    """||Dr A Dc||_inf exactly, A an exact rho x rho object array."""
    return Fraction(int((np.abs(A) * shift).sum(axis=1).max()), 2 ** (-emin))
e_i = [inf_norm_scaled(A0)]
At0 = A0 * shift                                                         # 2^-emin Dr A_RS,0 Dc, integers
del A0
for i in range(1, NORD):
    e_i.append(inf_norm_scaled(ARS_order(i)))
log('||Dr A_RS,i Dc||_inf (i = 0..%d): %s' % (NORD - 1, ['%.3e' % float(x) for x in e_i]))
# ---- beta: approximate inverse X of At_0, exact residual
Af = np.array(At0, dtype=np.float64) * 2.0 ** emin
X = np.linalg.inv(Af)
ex = int(math.ceil(-math.log2(np.abs(X).max()))) + 52
Xi = np.rint(X * 2.0 ** ex).astype(np.int64)
del Af, X
Rz = fz(At0) * flint.fmpz_mat(rho, rho, [int(v) for v in Xi.ravel()])   # = 2^(ex - emin) At_0 X
sh = ex - emin
Rint = fz_entries(Rz); del Rz
Rint[np.arange(rho), np.arange(rho)] -= 2 ** sh
theta0 = Fraction(int(np.abs(Rint).sum(axis=1).max()), 2 ** sh)
del Rint
Xnorm = Fraction(int(np.abs(Xi.astype(object)).sum(axis=1).max()), 2 ** ex)
log('At_0: theta0 = ||I - At_0 X||_inf = %.3e, ||X||_inf = %.3e' % (float(theta0), float(Xnorm)))
assert theta0 < 1
beta = Xnorm / (1 - theta0)
# ---- residual coefficients r_j = c_j - A_j x0 on the rows R (exact, common denominator L0)
Dn = int(cert['D'])
smax = max(s_ for _, s_ in cert['Yq'].values())
L0 = Dn * 2 ** smax // math.gcd(Dn, 2 ** smax)
lamz = [flint.fmpz_mat(len(erows), 1, [int(v) * (L0 // Dn) for v in cert['lam_n'][c]]) for c in range(3)]
Vx = {}
for j in act:
    m = blocks[j]['m']; Nm = cert['N'][j]
    Yi, s_ = cert['Yq'][j]
    Yint = Yi.astype(object) * (L0 // 2 ** s_) + cert['dYn'][j] * (L0 // Dn)
    Z = Nm.dot(Yint).dot(Nm.T)
    Vx[j] = fz(np.stack([Z[:m, :m].ravel(), Z[m:, m:].ravel(), (Z[:m, m:] + Z[:m, m:].T).ravel()], 1))
def Ax0_scaled(j):
    """L0 A_j x0 (all n rows, integers)."""
    acc = np.zeros(n, dtype=object)
    if j < JE:
        Et = fz(P['Ecoef'][j][erows]).transpose()
        for c in range(3):
            acc[c * N:(c + 1) * N] += fz_entries(Et * lamz[c])[:, 0]
    for jb in act:
        b = blocks[jb]; m = b['m']
        if j >= len(b['coef']):
            continue
        Rm = fz_entries(fz(b['coef'][j].reshape(N, m * m)) * Vx[jb])
        for c in range(3):
            acc[c * N:(c + 1) * N] += Rm[:, c]
    return acc
NC = len(P['c']['ca'])
cvec = lambda j: (list(P['c']['ca'][j]) + list(P['c']['cb'][j]) + [2 * v for v in P['c']['cab'][j]]) if j < NC else [Fraction(0)] * n
a0 = Ax0_scaled(0); c0 = cvec(0)
assert all(c0[r] * L0 == a0[r] for r in range(n)), 'x0 is not an exact solution at s = 0'
rho_j = []
for j in range(1, max(NORD, NC)):
    aj = Ax0_scaled(j); cj = cvec(j)
    rho_j.append(max(abs(cj[r] - Fraction(int(aj[r]), L0)) * Fraction(2) ** er[ri] for ri, r in enumerate(rows)))
log('||Dr (r_j)_R||_inf (j >= 1): %s' % ['%.3e' % float(x) for x in rho_j])
# ---- margins of x0 (exact): tau_b - (upper bound of ||dY_b||_F), relative to r_b max_S(b) Dc
dcb = {}
for idx, inf in enumerate(sel):
    if inf[0] == 'Y':
        dcb[inf[1]] = max(dcb.get(inf[1], Fraction(0)), Fraction(2) ** ec[idx])
mrel = None
for jb in act:
    Yi, s_ = cert['Yq'][jb]
    lmin = np.linalg.eigvalsh(Yi.astype(float) / 2.0 ** s_).min()
    tsh = int(math.floor(math.log2(lmin / 2))); tau = Fraction(2) ** tsh
    Mt = np.array([[Fraction(int(Yi[a, c]), 2 ** s_) - (tau if a == c else 0) for c in range(Yi.shape[1])] for a in range(Yi.shape[0])], dtype=object)
    assert ldl_pd(Mt)[0] is not None
    nrm = Fraction(math.isqrt(sum(int(x) ** 2 for x in cert['dYn'][jb].ravel())) + 1, Dn)      # >= ||dY_b||_F
    assert nrm < tau
    if jb in dcb:
        v = (tau - nrm) / (Yi.shape[0] * dcb[jb])
        mrel = v if mrel is None else min(mrel, v)
log('margins: min (tau_b - ||dY_b||_F) / (r_b max Dc) = %.3e' % float(mrel))
# ---- left kernel: q columns of W independent at s = 0, then an exact rational change of basis T (W -> W T, still a polynomial
# left-kernel basis) that makes the columns orthogonal at s = 0: G0 = W_sub(0)^T W_sub(0) = L Dg L^T (exact LDL, all Dg > 0 proves
# rank q), T = L^-T diag(c), c_i = 2^-round(log2(Dg_i)/2), so (W_sub(0) T)^T (W_sub(0) T) = diag(c_i^2 Dg_i) and sigma_q^2 = mu.
W = LK['coefs']; q = LK['q']
fq = lambda A, cols: flint.fmpq_mat(n, len(cols), [flint.fmpq(A[r, c].numerator, A[r, c].denominator) for r in range(n) for c in cols])
W0 = fq(W[0], range(W[0].shape[1]))
Rw, rkw = W0.rref()
piv = []
for r in range(rkw):
    for c in range(W0.ncols()):
        if Rw[r, c] != 0:
            piv.append(c); break
assert rkw == q
Wq = [fq(Wj, piv) for Wj in W]
G0 = Wq[0].transpose() * Wq[0]
Lm = [[flint.fmpq(0)] * q for _ in range(q)]
Dg = [flint.fmpq(0)] * q
for i in range(q):
    for j in range(i + 1):
        acc = G0[i, j]
        for k_ in range(j):
            acc -= Lm[i][k_] * Lm[j][k_] * Dg[k_]
        if i == j:
            Dg[i] = acc
        else:
            Lm[i][j] = acc / Dg[j]
    Lm[i][i] = flint.fmpq(1)
    assert Dg[i] > 0, 'W_sub(0) does not have rank q'
Lmat = flint.fmpq_mat(q, q, [Lm[i][j] for i in range(q) for j in range(q)])
cpow = [-((int(x.p).bit_length() - int(x.q).bit_length()) // 2) for x in Dg]          # any power of two is valid; mu is exact
T = Lmat.inv().transpose() * flint.fmpq_mat(q, q, [flint.fmpq(2) ** cpow[i] if i == j else flint.fmpq(0) for i in range(q) for j in range(q)])
Gd = T.transpose() * G0 * T
assert all(Gd[i, j] == 0 for i in range(q) for j in range(q) if i != j)
mu = min(Fraction(int(Gd[i, i].p), int(Gd[i, i].q)) for i in range(q))
def frob_upper(Wj):
    """rational upper bound of ||Wj T||_F."""
    Wt = Wj * T
    G = Wt.transpose() * Wt
    s2 = sum((Fraction(int(G[i, i].p), int(G[i, i].q)) for i in range(q)), Fraction(0))
    K = 2 ** 30
    return Fraction(math.isqrt(s2.numerator * K * K // s2.denominator) + 1, K)
wn = [frob_upper(Wj) for Wj in Wq[1:]]
log('left kernel (basis orthogonal at s = 0): sigma_q(W_sub(0) T)^2 = mu = %.3e; ||W_sub,j T||_F <= %s' % (float(mu), ['%.2e' % float(x) for x in wn]))
# ---- s0 = 2^-t: all conditions (each with factor 2 to spare), checked exactly
def ok(s):
    es = sum(e_i[i] * s ** i for i in range(1, len(e_i)))
    if beta * es >= Fraction(1, 2):
        return False
    bs = beta / (1 - beta * es)
    rs = sum(rho_j[j - 1] * s ** j for j in range(1, len(rho_j) + 1))
    if bs * rs >= mrel / 2:
        return False
    ws = sum(w * s ** (j + 1) for j, w in enumerate(wn))
    if ws * ws * 4 >= mu:
        return False
    return True
t = 1
while not ok(Fraction(1, 2 ** t)):
    t += 1
    assert t < 4000
log('RESULT (exact): every condition holds for s in (0, 2^-%d], i.e. for every d >= d0 = 2^%d = %.3e' % (t, t, 2.0 ** t))
