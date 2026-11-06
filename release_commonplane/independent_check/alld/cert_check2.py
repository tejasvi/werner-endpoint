"""Own exact check of the certificate in the producer's coordinates y (data file F_b, E, c_a, c_b, c_ab):
  Z_b = N_b (Yi_b / 2^s_b + dYn_b / D) N_b^T  (2m_b x 2m_b), lambda_c = lam_n[c] / D, rows E_r = E[erows];
  identity for every coordinate i (exact integers after multiplying by D and the coordinate denominators):
    c_a[i]    = sum_e E_r[e,i] lam1[e]/D + <F_b[i], Z_b[11]>
    c_b[i]    = ... lam2 ...           + <F_b[i], Z_b[22]>
    2 c_ab[i] = ... lam3 ...           + <F_b[i], Z_b[12] + Z_b[12]^T>
  PSD: M_b = Yi_b/2^s_b + dYn_b/D is positive definite (then Z_b = N_b M_b N_b^T is PSD):
    choose tau_b = 2^-k <= lambda_min(Yhat_b)/2 (float guess), prove Yhat_b - tau_b I > 0 by an exact LDL^T over Q,
    and ||dYn_b||_F^2 < (tau_b D)^2 exactly; Weyl: lambda_min(M_b) >= tau_b - ||dY_b||_2 > 0.
    Second, independent route: exact LDL^T of the full M_b over Q (all pivots > 0)."""
import sys
import time
import math
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
Dat = safeload.load(sys.argv[1])
C = safeload.load(sys.argv[2])
full_ldl = 'full' in sys.argv[3:]
MUT = [a for a in sys.argv[3:] if a.startswith('mut')]      # mutation tests only: mutlam, mutY, mutdY
MUTB = sorted(C['N'])[10]
D = int(C['D'])
N = Dat['N']
blocks = Dat['blocks']
erows = [int(e) for e in C['erows']]
assert len(set(erows)) == len(erows) and all(0 <= e < Dat['E'].shape[0] for e in erows)
lam = [[int(x) for x in C['lam_n'][c]] for c in range(3)]
if 'mutlam' in MUT:
    lam[0][3] += 1
assert all(len(l) == len(erows) for l in lam)


def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


# ---- D * Z_b as exact integer matrices
ZD = {}
Mid = {}
for b in sorted(C['N']):
    Nb = np.asarray(C['N'][b], dtype=object)
    Yi, s = C['Yq'][b]
    s = int(s)
    assert D % (1 << s) == 0
    Yi = np.asarray(Yi, dtype=object)
    dY = np.asarray(C['dYn'][b], dtype=object)
    if b == MUTB and 'mutY' in MUT:            # make Yhat indefinite: subtract (lambda_min + 2^-20) I
        lm = float(np.linalg.eigvalsh(np.array(Yi, dtype=float) / 2.0 ** s).min())
        Yi = Yi - int(round((lm + 2.0 ** -20) * 2 ** s)) * np.eye(Yi.shape[0], dtype=np.int64).astype(object)
    if b == MUTB and 'mutdY' in MUT:
        dY = dY * 10 ** 6
    r = Yi.shape[0]
    assert Yi.shape == (r, r) == dY.shape and Nb.shape == (2 * blocks[b]['m'], r)
    M = fz(Yi) * (D >> s) + fz(dY)                    # D * (Yhat + dY/D)
    assert M == M.transpose()
    Mid[b] = (M, Yi, s, dY)
    ZD[b] = fz(Nb) * M * fz(Nb).transpose()
log('built D*Z_b for %d blocks (absent blocks: Z_b = 0)' % len(ZD))

# ---- identity: accumulate integer right-hand sides  sum_b <F_b[i], D Z_b part>
rhs = [[0] * N for _ in range(3)]
for b, Z in ZD.items():
    m = blocks[b]['m']
    Zl = [[int(Z[u, v]) for v in range(2 * m)] for u in range(2 * m)]
    P11 = [Zl[u][v] for u in range(m) for v in range(m)]
    P22 = [Zl[m + u][m + v] for u in range(m) for v in range(m)]
    P12 = [Zl[u][m + v] + Zl[m + v][u] for u in range(m) for v in range(m)]       # Z12 + Z12^T, entry (u,v)
    F = blocks[b]['F']
    for i in range(N):
        Fi = [int(x) for x in F[i].ravel()]
        if not any(Fi):
            continue
        rhs[0][i] += sum(a * z for a, z in zip(Fi, P11))
        rhs[1][i] += sum(a * z for a, z in zip(Fi, P22))
        rhs[2][i] += sum(a * z for a, z in zip(Fi, P12))
log('block part done')
E = Dat['E']
for e, row in enumerate(erows):
    Er = [int(x) for x in E[row]]
    for c in range(3):
        le = lam[c][e]
        if le:
            for i in range(N):
                if Er[i]:
                    rhs[c][i] += Er[i] * le
log('equality part done')
targets = [[Fraction(x) for x in Dat['ca']], [Fraction(x) for x in Dat['cb']], [2 * Fraction(x) for x in Dat['cab']]]
nbad = [0, 0, 0]
for c in range(3):
    for i in range(N):
        t = targets[c][i]
        if t.numerator * D != t.denominator * rhs[c][i]:
            nbad[c] += 1
log('IDENTITY: mismatching coordinates (a, b, ab): %s of %d each' % (nbad, N))

# ---- PSD
def ldl_pos(Mq):
    """Exact Gaussian elimination without pivoting over Q of a symmetric fmpq_mat (its pivots are the D of
    LDL^T, and products of pivots are the leading principal minors).  True iff every pivot is > 0."""
    n = Mq.nrows()
    A = [[Mq[i, j] for j in range(n)] for i in range(n)]
    for k in range(n):
        piv = A[k][k]
        if piv <= 0:
            return False, k
        Ak = A[k]
        for i in range(k + 1, n):
            if A[i][k] != 0:
                f = A[i][k] / piv
                Ai = A[i]
                for j in range(k, n):
                    Ai[j] -= f * Ak[j]
    return True, n


npd = 0
worst = 0.0
fails = []
for b in sorted(Mid):
    M, Yi, s, dY = Mid[b]
    r = Yi.shape[0]
    Yf = np.array(Yi, dtype=float) / 2.0 ** s
    lmin = float(np.linalg.eigvalsh(Yf).min())
    if lmin <= 0:
        fails.append((b, 'Yhat not PD in float'))
        continue
    k = math.ceil(-math.log2(lmin / 2))
    tau = Fraction(1, 2 ** k)                          # tau <= lmin / 2
    # exact: Yhat - tau I > 0  <=>  Yi - tau 2^s I > 0 ; tau 2^s = 2^(s-k)
    shift = Fraction(2 ** s, 2 ** k)
    Aq = flint.fmpq_mat(r, r, [flint.fmpq(int(Yi[i, j])) - (flint.fmpq(shift.numerator, shift.denominator) if i == j else 0)
                               for i in range(r) for j in range(r)])
    ok, piv = ldl_pos(Aq)
    fro2 = sum(int(x) ** 2 for x in dY.ravel())
    ok2 = fro2 * tau.denominator ** 2 < (tau.numerator * D) ** 2
    ratio = math.sqrt(float(Fraction(fro2 * 4 ** k, D * D))) if fro2 else 0.0      # ||dY||_F / tau
    worst = max(worst, ratio) if math.isfinite(ratio) else worst
    if ok and ok2:
        npd += 1
    else:
        fails.append((b, ok, piv, ok2))
log('PSD (tau route): %d of %d blocks certified PD; worst ||dY||_F / tau = %.3e; failures %s' % (npd, len(Mid), worst, fails[:5]))
if full_ldl:
    nfull = 0
    for b in sorted(Mid):
        M = Mid[b][0]
        r = M.nrows()
        Mq = flint.fmpq_mat(r, r, [flint.fmpq(int(M[i, j])) for i in range(r) for j in range(r)])
        ok, piv = ldl_pos(Mq)
        nfull += ok
    log('PSD (full exact LDL of D*M_b): %d of %d blocks have all pivots > 0' % (nfull, len(Mid)))
print('CERT_CHECK', 'IDENTITY_OK' if nbad == [0, 0, 0] else 'IDENTITY_FAIL', 'PSD_OK' if npd == len(Mid) else 'PSD_FAIL')
