"""Independent check of an all-theta certificate (xrat2.py output) against the exact data (xbuild.py output).
With Y_b = Yi_b 2^-s_b + dYn_b / D and Z_b = N_b Y_b N_b^T it recomputes in exact integer arithmetic (flint), over the common
denominator L = lcm(D, 2^max s):
   c_a - E_r^T lam_1 - sum_b F_b^*(Z_b[11])             = 0
   c_b - E_r^T lam_2 - sum_b F_b^*(Z_b[22])             = 0
   2 c_ab - E_r^T lam_3 - sum_b F_b^*(Z_b[12] + Z_b[12]^T) = 0      (lam_c = lam_n[c] / D)
and positive definiteness of every Y_b: exact LDL of Yhat_b - tau_b I and ||dY_b||_F < tau_b (Weyl).
Then for every theta, c_theta = E^T lam(theta) + sum_b F_b^*(m^T Z_b m) with m^T Z_b m PSD (m = (cos, sin) (x) I), so
c_theta . y >= 0 for every y with E y = 0 and all blocks F_b(y) PSD.  Usage: python xverify.py XPICKLE CERT_PICKLE"""
import sys, os, math, pickle, time
from fractions import Fraction
import numpy as np
import flint
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xrat import ldl_pd

t0 = time.time()
Dex = pickle.load(open(sys.argv[1], 'rb')); cert = pickle.load(open(sys.argv[2], 'rb'))
N = Dex['N']; blocks = Dex['blocks']; E = Dex['E']
D = int(cert['D'])
smax = max(s for _, s in cert['Yq'].values())
L = D * 2 ** smax // math.gcd(D, 2 ** smax)
fzm = lambda A: flint.fmpz_mat(A.shape[0], A.shape[1], [int(v) for v in np.asarray(A, dtype=object).ravel()])
tot = [flint.fmpz_mat(N, 1) for _ in range(3)]
for j, Nm in cert['N'].items():
    m = blocks[j]['m']
    Yi, s = cert['Yq'][j]
    Yint = Yi.astype(object) * (L // 2 ** s) + cert['dYn'][j] * (L // D)              # Y_b * L, integers
    Nz = fzm(Nm)
    Z = Nz * fzm(Yint) * Nz.transpose()
    cols = []
    for a in range(m):
        for b in range(m):
            cols.append((int(Z[a, b]), int(Z[m + a, m + b]), int(Z[a, m + b]) + int(Z[b, m + a])))
    V = flint.fmpz_mat(m * m, 3, [x for c3 in cols for x in c3])
    R = fzm(blocks[j]['F'].reshape(N, -1)) * V
    for c in range(3):
        tot[c] = tot[c] + flint.fmpz_mat(N, 1, [int(R[i, c]) for i in range(N)])
er = cert['erows']
Er = E[er]
ctot = [Dex['ca'], Dex['cb'], [2 * v for v in Dex['cab']]]
ok_eq = True
for c in range(3):
    lam = cert['lam_n'][c]
    Elam = [sum(int(Er[e, i]) * int(lam[e]) for e in range(len(er))) for i in range(N)]       # (E_r^T lam_n)_i
    nz = 0
    for i in range(N):
        val = Fraction(ctot[c][i]) - Fraction(Elam[i], D) - Fraction(int(tot[c][i, 0]), L)
        nz += val != 0
    ok_eq = ok_eq and nz == 0
    print('copy %d: nonzero residual entries %d of %d (%.0fs)' % (c + 1, nz, N, time.time() - t0), flush=True)
npd = 0
for j, Nm in cert['N'].items():
    Yi, s = cert['Yq'][j]
    lmin = np.linalg.eigvalsh(Yi.astype(float) / 2.0 ** s).min()
    if lmin <= 0:
        continue
    tsh = int(math.floor(math.log2(lmin / 2)))
    tau = Fraction(2) ** tsh
    M = np.array([[Fraction(int(Yi[a, b]), 2 ** s) - (tau if a == b else 0) for b in range(Yi.shape[1])] for a in range(Yi.shape[0])], dtype=object)
    pmin, _ = ldl_pd(M)
    nrm2 = sum(int(x) * int(x) for x in cert['dYn'][j].ravel())
    ok_n = (nrm2 * 4 ** (-tsh) < D * D) if tsh < 0 else (nrm2 < D * D * 4 ** tsh)
    if pmin is not None and ok_n:
        npd += 1
print('PD blocks %d of %d; identity exact: %s; solution denominator 2^%.0f (%.0fs)' % (npd, len(cert['N']), ok_eq, math.log2(D), time.time() - t0), flush=True)
print('VERIFIED' if ok_eq and npd == len(cert['N']) else 'NOT VERIFIED')
