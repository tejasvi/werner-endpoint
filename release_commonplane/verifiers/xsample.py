"""The uniform certificate of xbounds.py, constructed exactly at a sampled dimension d = 2^e (s = 2^-e):
   x(s) = x0 + delta(s),  delta_S(s) = A_RS(s)^-1 r_R(s),  r(s) = c(s) - A(s) x0,  delta = 0 off the column set S,
with x0 the exact limit certificate and S, R its column and row sets (xrat4.py, keys sel_info / rows).  The scaled
multipliers are mapped to the data at d (xpolyeval.py): Y_b(d) = d^-deg_b Yhat_b(s), lam_r(d) = d^-deg_r lamhat_r(s).  With d a
power of two the dyadic part of the limit certificate stays dyadic, so the output is an ordinary certificate for xverify.py
(run it on xpolyeval.py data at the same d).   Usage: python xsample.py POLYPICKLE LIMITCERT e OUT.pkl"""
import sys, os, pickle, time, math
from fractions import Fraction
import numpy as np
import flint

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)
P = pickle.load(open(sys.argv[1], 'rb')); cert = pickle.load(open(sys.argv[2], 'rb'))
e = int(sys.argv[3]); out = sys.argv[4]
N = P['N']; n = 3 * N
blocks = P['blocks']
sel = cert['sel_info']; rows = cert['rows']; erows = cert['erows']
rho = len(sel)
assert len(rows) == rho
act = sorted(cert['N'])
JE = len(P['Ecoef'])
assert all(not P['Ecoef'][i][r].any() for r in erows for i in range(int(P['Edeg'][r]) + 1, JE))
assert all(len(blocks[j]['coef']) <= blocks[j]['deg'] + 1 for j in act)
IM = max(max(len(blocks[j]['coef']) for j in act), JE) - 1          # top order of A(s)
wts = [2 ** (e * (IM - i)) for i in range(IM + 1)]                   # 2^(e IM) s^i at s = 2^-e
fz = lambda A: flint.fmpz_mat(A.shape[0], A.shape[1], [int(v) for v in np.asarray(A, dtype=object).ravel()])
def wsum(lst):
    """sum_i wts[i] lst[i] (object arrays)."""
    return sum(lst[i] * wts[i] for i in range(len(lst)))
# ---- M = 2^(e IM) A_RS(s), exact integers
cols = np.zeros((n, rho), dtype=object)
byb = {}
for idx, inf in enumerate(sel):
    if inf[0] == 'lam':
        _, c, ee = inf
        cols[c * N:(c + 1) * N, idx] = wsum([P['Ecoef'][i][erows[ee]] for i in range(JE)])
    else:
        byb.setdefault(inf[1], []).append((idx, inf[2], inf[3]))
Fs = {}
for j in act:
    b = blocks[j]; m = b['m']
    Fs[j] = fz(wsum(list(b['coef'])).reshape(N, m * m))
for j, lst in byb.items():
    m = blocks[j]['m']; Nm = cert['N'][j]
    Ms = []
    for idx, a, bb in lst:
        S = np.zeros((Nm.shape[1], Nm.shape[1]), dtype=object); S[a, bb] = 1; S[bb, a] = 1
        Z = Nm.dot(S).dot(Nm.T)
        Ms += [Z[:m, :m].ravel(), Z[m:, m:].ravel(), (Z[:m, m:] + Z[:m, m:].T).ravel()]
    Rm = Fs[j] * fz(np.stack(Ms, 1))
    for t, (idx, a, bb) in enumerate(lst):
        for c in range(3):
            cols[c * N:(c + 1) * N, idx] = [int(Rm[r, 3 * t + c]) for r in range(N)]
M = fz(cols[rows])
del cols
log('M = 2^(e IM) A_RS(s) assembled (%d x %d, e = %d, IM = %d)' % (rho, rho, e, IM))
# ---- 2^(e IM) r(s) = 2^(e IM) c(s) - M_full x0, all rows, exact (common denominator L0 of x0)
Dn = int(cert['D'])
smax = max(s_ for _, s_ in cert['Yq'].values())
L0 = Dn * 2 ** smax // math.gcd(Dn, 2 ** smax)
acc = [0] * n                                                         # 2^(e IM) L0 A(s) x0
for c in range(3):
    lam = [int(v) * (L0 // Dn) for v in cert['lam_n'][c]]
    for ee, r in enumerate(erows):
        if lam[ee]:
            row = wsum([P['Ecoef'][i][r] for i in range(JE)])
            for v in range(N):
                if row[v]:
                    acc[c * N + v] += lam[ee] * int(row[v])
for j in act:
    m = blocks[j]['m']; Nm = cert['N'][j]
    Yi, s_ = cert['Yq'][j]
    Yint = Yi.astype(object) * (L0 // 2 ** s_) + cert['dYn'][j] * (L0 // Dn)
    Z = Nm.dot(Yint).dot(Nm.T)
    V = np.stack([Z[:m, :m].ravel(), Z[m:, m:].ravel(), (Z[:m, m:] + Z[:m, m:].T).ravel()], 1)
    Rm = Fs[j] * fz(V)
    for c in range(3):
        for r in range(N):
            acc[c * N + r] += int(Rm[r, c])
cs = {key: [sum(P['c'][key][i][v] * Fraction(1, 2 ** (e * i)) for i in range(len(P['c'][key]))) for v in range(N)]
      for key in ('ca', 'cb', 'cab')}
cvec = cs['ca'] + cs['cb'] + [2 * v for v in cs['cab']]
rfull = [cvec[r] * 2 ** (e * IM) - Fraction(acc[r], L0) for r in range(n)]  # = 2^(e IM) r(s)
log('residual of x0 at s: max |r| = %.3e (scaled by 2^(e IM))' % max(abs(float(x)) for x in rfull))
# ---- exact solve M delta = rfull_R
Mq = flint.fmpq_mat(M)
rq = flint.fmpq_mat(rho, 1, [flint.fmpq(rfull[r].numerator, rfull[r].denominator) for r in rows])
u = Mq.solve(rq, algorithm='dixon')
Dd = 1
for i in range(rho):
    qd = int(u[i, 0].q); Dd = Dd * qd // math.gcd(Dd, qd)
dn = [int(u[i, 0].p) * (Dd // int(u[i, 0].q)) for i in range(rho)]   # delta = dn / Dd
log('exact solve done: solution denominator 2^%.0f' % math.log2(Dd))
# ---- map x0 + delta to the data at d: common denominator D = Dn Dd 2^(e G), G = max degree over active blocks and rows
G = max([blocks[j]['deg'] for j in act] + [int(P['Edeg'][r]) for r in erows])
D = Dn * Dd * 2 ** (e * G)
dYn = {}
for j in act:
    sc = 2 ** (e * (G - blocks[j]['deg']))
    dYn[j] = (cert['dYn'][j].astype(object) * Dd) * sc
lam_n = [[(int(cert['lam_n'][c][ee]) * Dd) * 2 ** (e * (G - int(P['Edeg'][erows[ee]]))) for ee in range(len(erows))] for c in range(3)]
nmax_rel = {}
for idx, inf in enumerate(sel):
    if inf[0] == 'lam':
        _, c, ee = inf
        lam_n[c][ee] += dn[idx] * Dn * 2 ** (e * (G - int(P['Edeg'][erows[ee]])))
    else:
        _, j, a, bb = inf
        add = dn[idx] * Dn * 2 ** (e * (G - blocks[j]['deg']))
        dYn[j][a, bb] += add
        if a != bb:
            dYn[j][bb, a] += add
        nmax_rel[j] = max(nmax_rel.get(j, 0.0), abs(dn[idx] / Dd))
Yq = {j: (cert['Yq'][j][0], cert['Yq'][j][1] + e * blocks[j]['deg']) for j in act}
worst = 0.0
for j in act:
    Yi, s_ = cert['Yq'][j]
    lmin = np.linalg.eigvalsh(Yi.astype(float) / 2.0 ** s_).min()
    worst = max(worst, nmax_rel.get(j, 0.0) * Yi.shape[0] / lmin)
log('largest correction entry x r_b / lambda_min(Yhat_b) over blocks: %.3e' % worst)
pickle.dump(dict(N=cert['N'], Yq=Yq, dYn=dYn, lam_n=lam_n, D=D, erows=erows, k=P['k'], sup='s2', d=2 ** e,
                 note='xsample.py: x0 + A_RS(s)^-1 r_R(s) at s = 2^-%d' % e), open(out, 'wb'), protocol=4)
log('certificate at d = 2^%d written (verify with xverify.py on xpolyeval.py data at d = %d)' % (e, 2 ** e))
