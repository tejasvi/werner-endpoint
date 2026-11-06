"""Exact polynomial data in s = 1/d (all orders) for the S2 relaxation at fixed k, from xbuild chunk residues at nodes d (same
interpolation and denominator normalisation as xinterp.py).  Scaled convention (paper A s5.2):
   block b:        Fhat_b(s) = d^-deg_b F_b(d) = sum_j s^j Fhat_{b,j},  Fhat_{b,j} = coefficient of d^(deg_b - j)
   equality row r: Ehat_r(s) = d^-deg_r E_r(d),  objective/trace c(s) = sum_j s^j c_j  (c(d) = P(d) / (16 d^(4k)))
stored as integers: Fhat_{b,j} * deg_b! * DEN_PHI^k (cut (3,)), Ehat_{r,j} * k! * 2 DEN_EQ^k; c_j exact Fractions.
cut-() blocks are d-independent (deg 0).  Usage: python xpoly.py K OUT.pkl DATA_D4.pkl d1:dir1:nch1 ...   (cwd = slice)"""
import sys, os, math, pickle, time
from fractions import Fraction
import numpy as np
import flint
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xdata import XRelax, s2_support, apply_factors, P4, SWAP03, SiteX, F as Fr
from xbuild import crt_join, PRIMES20, NPRIMES, delete_matrix, lcm_den
from local import compose, ncycles
from relaxM import WORDS, SIDX, perm_op

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)

K, out, d4pk = int(sys.argv[1]), sys.argv[2], sys.argv[3]
nodes = sorted((int(a.split(':')[0]), a.split(':')[1], int(a.split(':')[2])) for a in sys.argv[4:])
ds = [x[0] for x in nodes]
X = XRelax(K, d=4, keep=s2_support, verbose=False)
N = X.N
outs0 = [o for o in X.outs if o['cut'] == ()]
outs3 = [o for o in X.outs if o['cut'] == (3,)]
sx3 = X.site[(3,)]
Ft = [sum(1 for i in o['st'] if sx3.labels[i][0] == 1) for o in outs3]
primes = PRIMES20[:NPRIMES + 1]
s0_ = X.site[()]
den_phi, den_eq = {}, {}
for dd in ds:
    den_phi[dd] = lcm_den(SiteX((3,), dd).FTG.astype(object).dot(s0_.IFG).ravel())
    den_eq[dd] = lcm_den(delete_matrix(dd, 0).astype(object).dot(s0_.IFG).ravel())
DEN_PHI = 1; DEN_EQ = 1
for dd in ds:
    DEN_PHI = DEN_PHI * den_phi[dd] // math.gcd(DEN_PHI, den_phi[dd])
    DEN_EQ = DEN_EQ * den_eq[dd] // math.gcd(DEN_EQ, den_eq[dd])
res3, resE, bound = {}, {}, {}
for dd, ddir, nch in nodes:
    chunks = [pickle.load(open(os.path.join(ddir, 'chunk_%03d.pkl' % c), 'rb')) for c in range(nch)]
    nE = chunks[0]['E'][0].shape[0]
    R3 = [[np.zeros((N, o['m'], o['m']), dtype=np.int64) for o in outs3] for _ in primes]
    RE = [np.zeros((nE, N), dtype=np.int64) for _ in primes]
    for c in chunks:
        J = c['J']
        for pi in range(len(primes)):
            for oi in range(len(outs3)):
                R3[pi][oi][J] = c['F3'][pi][oi]
            RE[pi][:, J] = c['E'][pi]
    f3 = (DEN_PHI // den_phi[dd]) ** K; fE = (DEN_EQ // den_eq[dd]) ** K
    for pi, p in enumerate(primes):
        for oi in range(len(outs3)):
            R3[pi][oi] = (R3[pi][oi] * (f3 % p)) % p
        RE[pi] = (RE[pi] * (fE % p)) % p
    res3[dd], resE[dd] = R3, RE
    bound[dd] = max(c['bound'] for c in chunks) * max(f3, fE)
log('nodes %s loaded; DEN_PHI %d DEN_EQ %d' % (ds, DEN_PHI, DEN_EQ))
n = len(ds)
Vm = flint.fmpq_mat(n, n, [flint.fmpq(dd ** kk) for dd in ds for kk in range(n)])
detV = int(Fr(Vm.det())); Vinv = Vm.inv()
Vadj = [[int(Fr(Vinv[kk, i]) * detV) for i in range(n)] for kk in range(n)]
M = 1
for p in primes[:NPRIMES]:
    M *= p
# exact coefficients from exact node values: CRT of each node value (|v_i| <= bound_i), then detV * coeff_k = sum_i Vadj[k][i] v_i
# in integers for every k < n (a CRT of detV * coeff_k itself would need sum_i |Vadj[k][i]| bound_i < M / 2, false here).
# The degree is the largest k with a nonzero exact coefficient; the coefficients above it vanish exactly (node checks).
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
D4 = pickle.load(open(d4pk, 'rb'))
by_sig = {(b['cut'], b['st'], b['ai'], b['tau']): b for b in D4['blocks']}
blocks = []
for o in outs0:
    b = by_sig.get(((), o['st'], o['ai'], o['tau']))
    if b is not None:
        blocks.append(dict(cut=(), st=o['st'], ai=o['ai'], tau=o['tau'], m=o['m'], deg=0, coef=[b['F']], scale=1))
for oi, o in enumerate(outs3):
    vals = node_vals([[res3[dd][pi][oi] for pi in range(len(primes))] for dd in ds])
    nums = [interp_num(vals, kk) for kk in range(n)]
    nzk = [kk for kk in range(n) if nums[kk].any()]
    if not nzk:
        continue
    deg = max(nzk)
    assert deg <= 2 * Ft[oi]
    fac = math.factorial(deg)
    coef = []
    for j in range(deg + 1):                                           # s^j <-> d^(deg - j)
        v = nums[deg - j] * fac
        assert not np.mod(v, detV).any(), 'coefficient times deg! not integral'
        coef.append(v // detV)
    blocks.append(dict(cut=(3,), st=o['st'], ai=o['ai'], tau=o['tau'], m=o['m'], deg=deg, coef=coef, scale=fac * DEN_PHI ** K))
log('block coefficients: %d blocks' % len(blocks))
Evals = node_vals([[resE[dd][pi] for pi in range(len(primes))] for dd in ds])
nrowE = Evals[0].shape[0]
degE = np.full(nrowE, -1)
Enum = []
for kk in range(n):
    v = interp_num(Evals, kk)
    degE[v.any(axis=1)] = kk
    if kk <= K:
        Enum.append(v * math.factorial(K))                             # detV K! (coefficient of d^kk), all rows
assert (degE <= K).all()
del Evals
Ecoef = []
for j in range(K + 1):
    v = np.zeros((nrowE, N), dtype=object)
    for kk in range(K + 1):
        rr = np.nonzero(degE - j == kk)[0]
        v[rr] = Enum[kk][rr]
    assert not np.mod(v, detV).any(), 'equality coefficient times K! not integral'
    Ecoef.append(v // detV)
keep = degE >= 0
log('equality coefficients: %d rows (degrees %s)' % (int(keep.sum()), dict(zip(*np.unique(degE, return_counts=True)))))
# objective / trace: c(d) * 16 d^(4k) is a polynomial of degree <= 4k; exact values at 4k+1 points from the site polynomials
a0 = X.aux[()]
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
def functional_at(dd, zsfun, za):
    zs = np.array([zsfun(p, dd) for p in P4], dtype=object)
    zrow = zs.dot(s0_.IFG); zaG = a0.FT.astype(object).dot(za)
    out_ = np.zeros(N, dtype=object)
    for b in X.vars:
        mats = [zrow[s0_.rows(l)].reshape(s0_.dims[l], s0_.dims[l]) for l in b['st']] + [zaG[a0.rows(b['ai'])].reshape(a0.dims[b['ai']], a0.dims[b['ai']])]
        WZW = b['W'].T.dot(apply_factors(mats, b['W']))
        for jj, Sj in enumerate(b['basis']):
            out_[b['off'] + jj] = len(b['cosets']) * np.sum(Sj * WZW)     # = c(d) * 16 d^(4k)
    return out_
zobj = lambda p, dd: Fraction(dd ** ncycles(p)) - Fraction(1, 2) * dd ** ncycles(compose(SWAP03, p))
ztr = lambda p, dd: Fraction(dd ** ncycles(p))
pts = list(range(4, 4 + 4 * K + 1))
cvals = {key: [functional_at(dd, zf, za) for dd in pts] for key, (zf, za) in
         {'ca': (zobj, za_th('a')), 'cb': (zobj, za_th('b')), 'cp': (zobj, za_th('p')), 'tr': (ztr, za_tr)}.items()}
nn = len(pts)
Vc = flint.fmpq_mat(nn, nn, [flint.fmpq(dd ** kk) for dd in pts for kk in range(nn)]).inv()
ccoef = {}
for key, vals in cvals.items():
    co = []
    for kk in range(nn):                                               # coefficient of d^kk of P(d)
        co.append(np.array([sum(Fr(Vc[kk, i]) * vals[i][r] for i in range(nn)) for r in range(N)], dtype=object))
    ccoef[key] = [co[4 * K - j] / 16 for j in range(4 * K + 1)]       # c(s) = sum_j s^j P_{4k-j} / 16
ccoef['cab'] = [cp - (ca + cb) / 2 for ca, cb, cp in zip(ccoef['ca'], ccoef['cb'], ccoef['cp'])]
log('objective coefficients computed (degree %d in s)' % (4 * K))
pickle.dump(dict(k=K, N=N, blocks=blocks, Ecoef=[E[keep] for E in Ecoef], Edeg=degE[keep], Escale=math.factorial(K),
                 c=ccoef, DEN_PHI=DEN_PHI, DEN_EQ=DEN_EQ, nodes=ds, varmet=D4['varmet']), open(out, 'wb'), protocol=4)
log('saved polynomial data')
