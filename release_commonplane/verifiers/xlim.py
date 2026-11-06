"""Dual-facially-reduced re-solve: the all-theta SDP with every active doubled block compressed by its exact kernel-complement
basis N_b (kernel = lemma face (+) ranges of the zero families, from xrat3.kernels) and inactive blocks dropped.  Its dual is
c_tot = E_tot^T lam + nu tr_tot + sum_b Fdbl_b^*(N_b Y_b N_b^T), Y_b >= 0: the IPM returns Y_b directly in N coordinates, centred
in the relative interior, so no projection of a fuzzy dual kernel is needed before rounding.
Numerics: blocks in whitened coordinates (T = met^(-1/2), natural scale), compression basis orthonormalised (M = T2^-1 N = Q R),
then Y_N = s_b R^-1 Y_Q R^-T.  Usage: python xatd2.py XPICKLE XSOL XZERO OUT.pkl [thr DMAX]"""
import sys, os, math, pickle, time
import numpy as np
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xval import to_float, isqrt_psd
from dual_extract import solve_dual
from xrat3 import kernels, blkdiag2

t0 = time.time()
# xlim: the same reduced max-margin solve on given data (e.g. the s = 0 limit) with the exact face bases N_b and active set taken
# from a finite-d reduced solve (they are d-independent).  Usage: python xlim.py XPICKLE REDPICKLE OUT.pkl [maxit]
xpk, redpk, out = sys.argv[1], sys.argv[2], sys.argv[3]
maxit = int(sys.argv[4]) if len(sys.argv) > 4 else 40
Dex = pickle.load(open(xpk, 'rb'))
red0 = pickle.load(open(redpk, 'rb'))
sig = {(b['cut'], b['st'], b['ai'], b['tau']): j for j, b in enumerate(Dex['blocks'])}
Dref_sig = red0.get('sig')
Nb = {}
for j, Nm in red0['N'].items():
    key = Dref_sig[j] if Dref_sig else j
    jj = sig[key] if Dref_sig else j
    assert Dex['blocks'][jj]['m'] * 2 == Nm.shape[0]
    Nb[jj] = Nm
print('face bases from %s: %d active blocks' % (redpk, len(Nb)), flush=True)
D = to_float(Dex, white=True)                     # blocks: s_b T_b^T F_b(P y') T_b
N = D['N']
E = D['E']
Eb = np.zeros((3 * E.shape[0], 3 * N))
for i in range(3):
    Eb[i * E.shape[0]:(i + 1) * E.shape[0], i * N:(i + 1) * N] = E
blocks, owners, Rs = [], [], {}
for j in sorted(Nb):
    m = Dex['blocks'][j]['m']
    T = D['T'][j]
    M = np.linalg.solve(blkdiag2(T), Nb[j].astype(float))          # T2^-1 N
    Q, R = np.linalg.qr(M)
    Rs[j] = R
    Fw = D['blocks'][j]['F']                                        # (N, m, m), whitened, natural scale
    Fd = np.zeros((3 * N, 2 * m, 2 * m))
    Fd[:N, :m, :m] = Fw; Fd[N:2 * N, m:, m:] = Fw; Fd[2 * N:, :m, m:] = Fw; Fd[2 * N:, m:, :m] = np.transpose(Fw, (0, 2, 1))
    Fr = np.einsum('ar,iab,bs->irs', Q, Fd, Q, optimize=True)
    blocks.append(dict(m=Q.shape[1], F=Fr)); owners.append(j)
# Normalisation sum_b tr(compressed block) = 1 instead of tr.y = 1: the zero points (all compressed blocks 0) are then excluded,
# and the dual reads c = E^T lam + sum_b F_b^*(Z_b + nu I): nu = optimal value = largest uniform margin of Y_Q = Z + nu I.
arow = sum(np.trace(b['F'], axis1=1, axis2=2) for b in blocks)
cvec = np.concatenate([D['ca'], D['cb'], 2 * D['cab']])
Db = dict(N=3 * N, E=Eb, tr=arow, c=cvec, blocks=blocks)
print('reduced all-theta problem (max-margin normalisation): vars %d, blocks %d, max block %d, sum r^2 %d (%.0fs)' % (
    3 * N, len(blocks), max(b['m'] for b in blocks), sum(b['m'] ** 2 for b in blocks), time.time() - t0), flush=True)
res = solve_dual(Db, maxiters=maxit)
fit = sum(np.einsum('iab,ab->i', b['F'], Zq) for b, Zq in zip(blocks, res['Z']))
Mls = np.hstack([Eb.T, arow[:, None]])
coef, *_ = np.linalg.lstsq(Mls, cvec - fit, rcond=None)
nu = coef[-1]
print('RESULT reduced all-theta: %s primal %+.4e dual %+.4e; margin nu %.4e, residual %.2e (%.0fs)' % (
    res['status'], res['primal'], res['dual'], nu, np.abs(cvec - fit - Mls @ coef).max(), time.time() - t0), flush=True)
Yf, marg = {}, []
for j, Zq in zip(owners, res['Z']):
    YQ = Zq + nu * np.eye(Zq.shape[0])
    Ri = np.linalg.inv(Rs[j])
    Yf[j] = D['s'][j] * Ri @ YQ @ Ri.T
    w = np.linalg.eigvalsh(YQ)
    marg.append(w.min() / max(w.max(), 1e-300))
res['Z'] = [Zq + nu * np.eye(Zq.shape[0]) for Zq in res['Z']]
gq = max(np.linalg.eigvalsh(YQ).max() for YQ in res['Z'])
print('reduced duals: min eig / own max %.2e, min eig / global max %.2e (%.0fs)' % (
    min(marg), min(np.linalg.eigvalsh(YQ).min() for YQ in res['Z']) / gq, time.time() - t0), flush=True)
pickle.dump(dict(N=Nb, Yf=Yf, status=res['status'], primal=res['primal'], dual=res['dual']), open(out, 'wb'), protocol=4)
