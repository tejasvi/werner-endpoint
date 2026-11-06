"""Polynomial structure of the S2 data in d (k = 4) and the limit data at s = 1/d -> 0.
Cut-(3,) blocks and equality rows: modular interpolation over the nodes d in DLIST from the chunk residues (xbuild.py chunk files),
degree checks (block b of a type with F_t fully contracted site labels has degree <= 2 F_t, Lemma 5.1; equality rows degree <= 4),
and exact top coefficients by CRT.  Integer-valued polynomials: the top coefficient times (degree)! is an integer.
Cut-() blocks are d-independent (taken from one exact data file).  Objective and trace limits: top coefficients of the site factors
(zs = d^cyc(p) - d^cyc(SWAP03 p)/2 -> [p = id] - [p = SWAP03]/2), L = 16 d^16 -> 16.
Scaling (paper A s5.2): multiplier of block b times d^(2 F_t), equality coefficients times d^4; the limit blocks are the top
coefficients.  Output: limit data in the xbuild format (d = 'inf'); per block 'nat' = natural-scale factor, 'Ft'.
Usage: python xinterp.py K OUT.pkl DATA_D4.pkl d1:dir1:nch1 d2:dir2:nch2 ...       (cwd = slice)"""
import sys, os, math, pickle, time, itertools
from fractions import Fraction
import numpy as np
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xdata import XRelax, s2_support, apply_factors, P4, SWAP03, F as Fr
from xbuild import crt_join, PRIMES20, NPRIMES
from local import compose, ncycles
from relaxM import WORDS, SIDX, perm_op

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)

K, out, d4pk = int(sys.argv[1]), sys.argv[2], sys.argv[3]
nodes = []
for a in sys.argv[4:]:
    dd, ddir, nch = a.split(':')
    nodes.append((int(dd), ddir, int(nch)))
nodes.sort()
ds = [n[0] for n in nodes]
X = XRelax(K, d=4, keep=s2_support, verbose=False)
N = X.N
outs0 = [o for o in X.outs if o['cut'] == ()]
outs3 = [o for o in X.outs if o['cut'] == (3,)]
sx3 = X.site[(3,)]
Ft = [sum(1 for i in o['st'] if sx3.labels[i][0] == 1) for o in outs3]
primes = PRIMES20[:NPRIMES + 1]
log('structure: N %d, %d cut-() and %d cut-(3,) output blocks; nodes d = %s' % (N, len(outs0), len(outs3), ds))
# ---- per-node denominators: xbuild stores cut-(3,) blocks as den_phi(d)^K x true blocks and equality rows as 2 den_eq(d)^K x true
# rows, with den(d) = lcm of the denominators at that d (it can drop at special d, e.g. 576 -> 192 at d = 12).  Rescale every node to
# the common denominators DEN_PHI = lcm_d den_phi(d), DEN_EQ = lcm_d den_eq(d).
from xdata import SiteX
from xbuild import delete_matrix, lcm_den
s0_ = X.site[()]
den_phi, den_eq = {}, {}
for dd, _, _ in nodes:
    P = SiteX((3,), dd).FTG.astype(object).dot(s0_.IFG)
    den_phi[dd] = lcm_den(P.ravel())
    den_eq[dd] = lcm_den(delete_matrix(dd, 0).astype(object).dot(s0_.IFG).ravel())
DEN_PHI = 1; DEN_EQ = 1
for dd in den_phi:
    DEN_PHI = DEN_PHI * den_phi[dd] // math.gcd(DEN_PHI, den_phi[dd])
    DEN_EQ = DEN_EQ * den_eq[dd] // math.gcd(DEN_EQ, den_eq[dd])
log('per-node den_phi %s, den_eq %s -> common %d, %d' % (den_phi, den_eq, DEN_PHI, DEN_EQ))
# ---- residues per node
res3 = {}; resE = {}; bound = {}
for dd, ddir, nch in nodes:
    chunks = [pickle.load(open(os.path.join(ddir, 'chunk_%03d.pkl' % c), 'rb')) for c in range(nch)]
    assert all(c['primes'] == primes for c in chunks)
    nE = chunks[0]['E'][0].shape[0]
    R3 = [[np.zeros((N, o['m'], o['m']), dtype=np.int64) for o in outs3] for _ in primes]
    RE = [np.zeros((nE, N), dtype=np.int64) for _ in primes]
    seen = np.zeros(N, dtype=int)
    for c in chunks:
        J = c['J']; seen[J] += 1
        for pi in range(len(primes)):
            for oi in range(len(outs3)):
                R3[pi][oi][J] = c['F3'][pi][oi]
            RE[pi][:, J] = c['E'][pi]
    assert (seen == 1).all()
    f3 = (DEN_PHI // den_phi[dd]) ** K
    fE = (DEN_EQ // den_eq[dd]) ** K
    for pi, p in enumerate(primes):
        for oi in range(len(outs3)):
            R3[pi][oi] = (R3[pi][oi] * (f3 % p)) % p
        RE[pi] = (RE[pi] * (fE % p)) % p
    res3[dd], resE[dd] = R3, RE
    bound[dd] = max(c['bound'] for c in chunks) * max(f3, fE)
    del chunks
    log('node d=%d loaded (bound %.2e)' % (dd, bound[dd]))
# ---- interpolation: integer adjugate of the Vandermonde matrix on the nodes
n = len(ds)
Vq = [[Fraction(dd) ** kk for kk in range(n)] for dd in ds]
import flint
Vm = flint.fmpq_mat(n, n, [flint.fmpq(int(v.numerator), int(v.denominator)) for row in Vq for v in row])
detV = int(Fr(Vm.det()))
Vinv = Vm.inv()
Vadj = [[int(Fr(Vinv[kk, i]) * detV) for i in range(n)] for kk in range(n)]      # detV * V^-1, integer: coeff_k = sum_i Vadj[k][i] v_i / detV
log('Vandermonde on %d nodes: det %d' % (n, detV))
# exact coefficients from exact node values: CRT of each node value (|v_i| <= bound_i), then detV * coeff_k = sum_i Vadj[k][i] v_i
# in integers for every k < n (a CRT of detV * coeff_k itself would need sum_i |Vadj[k][i]| bound_i < M / 2, false at k = 4).
# The degree is the largest k with a nonzero exact coefficient; the coefficients above it vanish exactly (node checks).
M = 1
for p in primes[:NPRIMES]:
    M *= p
def node_vals(resl_nodes):
    """resl_nodes[i][pi]: residues at node ds[i] modulo primes[pi] -> exact node values (bound- and extra-prime checked)."""
    out_ = []
    pc = primes[NPRIMES]
    for i, dd in enumerate(ds):
        assert 2 * bound[dd] + 1 < M, 'CRT modulus too small'
        v = crt_join(resl_nodes[i][:NPRIMES], primes[:NPRIMES])
        assert (np.mod(v, pc).astype(np.int64) == resl_nodes[i][NPRIMES]).all(), 'extra-prime check failed'
        out_.append(v)
    return out_
def interp_num(vals, kk):
    """detV * (coefficient of d^kk), exact."""
    return sum(vals[i] * Vadj[kk][i] for i in range(n))
# ---- blocks: degree checks and exact top coefficients (detV * coefficient of d^deg)
top3, degs3 = [], []
degfail = 0
for oi, o in enumerate(outs3):
    vals = node_vals([[res3[dd][pi][oi] for pi in range(len(primes))] for dd in ds])
    nums = [interp_num(vals, kk) for kk in range(n)]
    nzk = [kk for kk in range(n) if nums[kk].any()]
    deg = max(nzk) if nzk else -1
    if deg > 2 * Ft[oi]:
        degfail += 1
    degs3.append(deg)
    top3.append(nums[deg] if deg >= 0 else None)
log('cut-(3,) blocks: degree check (<= 2 F_t) failures %d of %d; actual degree < 2 F_t in %d blocks; zero blocks %d' % (
    degfail, len(outs3), sum(1 for oi in range(len(outs3)) if 0 <= degs3[oi] < 2 * Ft[oi]), sum(1 for x in degs3 if x < 0)))
Evals = node_vals([[resE[dd][pi] for pi in range(len(primes))] for dd in ds])
nrowE = Evals[0].shape[0]
degE = np.full(nrowE, -1)
Etop = np.zeros(Evals[0].shape, dtype=object)
for kk in range(n):
    v = interp_num(Evals, kk)
    nzr = v.any(axis=1)
    degE[nzr] = kk
    Etop[nzr] = v[nzr]                                                 # rows end with their top coefficient
del Evals
degfailE = int((degE > K).sum())
log('equality rows: degree check (<= 4) failures %d; row degrees histogram %s' % (degfailE, dict(zip(*np.unique(degE, return_counts=True)))))
assert degfail == 0 and degfailE == 0
blocks = []
D4 = pickle.load(open(d4pk, 'rb'))
by_sig = {(b['cut'], b['st'], b['ai'], b['tau']): b for b in D4['blocks']}
for o in outs0:
    b = by_sig.get(((), o['st'], o['ai'], o['tau']))
    if b is not None:
        blocks.append(dict(b, Ft=0, nat=1.0))
# leading coefficients of the cut-(3,) site metrics: G(d) is linear in d for f = 1 labels (checked at d = 4, 5, 6), constant else
from xdata import SiteX
S4_, S5_, S6_ = sx3, SiteX((3,), 5), SiteX((3,), 6)
Gtop = []
for i, lab in enumerate(sx3.labels):
    G4, G5, G6 = (np.array(Sx.G[i], dtype=object) for Sx in (S4_, S5_, S6_))
    assert ((G6 - G5) == (G5 - G4)).all(), 'site metric not linear in d'
    Gtop.append(G5 - G4 if lab[0] == 1 else G4)
for oi, o in enumerate(outs3):
    deg = degs3[oi]
    if deg < 0:
        continue
    v = top3[oi]                                                       # detV * top coefficient
    fac = math.factorial(deg)
    num = v * fac
    if all(int(x) == 0 for x in num.ravel()):
        continue
    # top coefficient times deg! is an integer (integer-valued polynomial)
    Fq = [Fraction(int(x), detV) for x in num.ravel()]
    assert all(x.denominator == 1 for x in Fq), 'top coefficient times deg! not integral'
    Fint = np.array([int(x) for x in Fq], dtype=object).reshape(num.shape)
    GV = apply_factors([Gtop[i] for i in o['st']] + [np.eye(X.aux[(3,)].dims[o['ai']], dtype=np.int64)], o['V'])
    met = np.array([[float(x) for x in row] for row in o['V'].T.dot(GV)])     # natural metric of the limit (whitening only)
    blocks.append(dict(cut=(3,), st=o['st'], ai=o['ai'], tau=o['tau'], m=o['m'], F=Fint, Ft=Ft[oi], deg=deg, met=met,
                       nat=1.0 / (float(DEN_PHI) ** K * fac)))
log('limit blocks assembled: %d (cut () %d, cut (3,) %d)' % (len(blocks), sum(1 for b in blocks if b['cut'] == ()),
    sum(1 for b in blocks if b['cut'] == (3,))))
Ev = Etop * math.factorial(K)                                                            # rows of degree < 4 carry an extra integer factor
Eint = np.array([Fraction(int(x), detV) for x in Ev.ravel()], dtype=object).reshape(Ev.shape)
assert all(x.denominator == 1 for x in Eint.ravel())
Eint = np.array([int(x) for x in Eint.ravel()], dtype=object).reshape(Ev.shape)
nz = np.array([any(v != 0 for v in row) for row in Eint])
log('limit equality rows: %d nonzero of %d' % (int(nz.sum()), len(nz)))
# ---- objective and trace limits (exact): functionals with the top site coefficients
s0, a0 = X.site[()], X.aux[()]
zs_obj = np.array([Fraction(int(p == tuple(range(4)))) - Fraction(1, 2) * int(p == SWAP03) for p in P4], dtype=object)
zs_tr = np.array([Fraction(int(p == tuple(range(4)))) for p in P4], dtype=object)
S = perm_op(SWAP03)
def za_th(which):
    za = []
    for (x, y) in WORDS:
        v = int(round(S[SIDX[y], SIDX[x]]))
        if which == 'a':
            v *= 2 * (y[3] == 0) * (x[3] == 0)
        elif which == 'b':
            v *= 2 * (y[3] == 1) * (x[3] == 1)
        za.append(Fraction(v))
    return np.array(za, dtype=object)
za_tr = np.array([Fraction(int(x == y)) for (x, y) in WORDS], dtype=object)
funcs = {'ca': (zs_obj, za_th('a')), 'cb': (zs_obj, za_th('b')), 'cp': (zs_obj, za_th('p')), 'tr': (zs_tr, za_tr)}
vecs = {key: np.zeros(N, dtype=object) for key in funcs}
for key, (zs, za) in funcs.items():
    zrow = zs.dot(s0.IFG)
    zaG = a0.FT.astype(object).dot(za)
    for b in X.vars:
        mats = [zrow[s0.rows(l)].reshape(s0.dims[l], s0.dims[l]) for l in b['st']] + [zaG[a0.rows(b['ai'])].reshape(a0.dims[b['ai']], a0.dims[b['ai']])]
        WZW = b['W'].T.dot(apply_factors(mats, b['W']))
        nc = len(b['cosets'])
        for jj, Sj in enumerate(b['basis']):
            vecs[key][b['off'] + jj] = Fraction(nc) * np.sum(Sj * WZW) / 16
log('objective and trace limits computed')
Dinf = dict(k=K, d='inf', sup='s2', N=N, E=Eint[nz], blocks=blocks, ca=vecs['ca'], cb=vecs['cb'],
            cab=vecs['cp'] - (vecs['ca'] + vecs['cb']) / 2, tr=vecs['tr'], den_phi=DEN_PHI, varmet=D4['varmet'],
            nodes=ds, detV=detV)
pickle.dump(Dinf, open(out, 'wb'), protocol=4)
log('saved limit data: %d blocks, %d equality rows' % (len(blocks), int(nz.sum())))
