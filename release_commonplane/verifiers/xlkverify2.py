"""Exact verification of a polynomial left-kernel certificate (xlkx2.py output, q kept solutions) against the exact polynomial
data (xpoly.py), as xlkverify.py but sized for k = 4 (all solutions at once, nonzero variables only, flint products):
for every kept solution w(s) = sum_j s^j w_j and every order k,
   (a) sum_{i+j=k} Ehat_i (w_j)_c = 0                                   (every equality row, every copy c)
   (b) sum_{i+j=k} N_b^T Fdbl(Fhat_{b,i}; w_j) N_b = 0                  (every active block)
   (c) sum_{i+j=k} w_j . c_i = 0,  c_i = (c_a, c_b, 2 c_ab)_i            (consistency)
and rank W(0) = q (the left-kernel dimension at s = 0).   Usage: python xlkverify2.py POLYPICKLE REDPICKLE LKPICKLE"""
import sys, os, pickle, time, math
from fractions import Fraction
import numpy as np
import flint

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)
P = pickle.load(open(sys.argv[1], 'rb')); red = pickle.load(open(sys.argv[2], 'rb')); L = pickle.load(open(sys.argv[3], 'rb'))
assert L['ok']
N = P['N']; n = 3 * N
W = L['coefs']
nsol = W[0].shape[1]; Dw = len(W) - 1
def den_lcm(A):
    d = 1
    for x in A.ravel():
        d = d * x.denominator // math.gcd(d, x.denominator)
    return d
Wden = [den_lcm(Wj) for Wj in W]
Wint = [np.array([[int(x * Wden[j]) for x in row] for row in Wj], dtype=object) for j, Wj in enumerate(W)]
fz = lambda A: flint.fmpz_mat(A.shape[0], A.shape[1], [int(v) for v in np.asarray(A, dtype=object).ravel()])
def fz_entries(M_):
    return np.array([int(x) for x in M_.entries()], dtype=object).reshape(M_.nrows(), M_.ncols())
Wc = [[fz(Wint[j][c * N:(c + 1) * N]) for c in range(3)] for j in range(Dw + 1)]     # N x nsol per order and copy
def lk(js):
    v = 1
    for j in js:
        v = v * Wden[j] // math.gcd(v, Wden[j])
    return v
# (a) equality rows
Ec = [fz(E) for E in P['Ecoef']]
bad_a = 0
for k in range(len(Ec) + Dw):
    js = [j for j in range(Dw + 1) if 0 <= k - j < len(Ec)]
    if not js:
        continue
    Lk = lk(js)
    for c in range(3):
        acc = None
        for j in js:
            term = Ec[k - j] * Wc[j][c] * (Lk // Wden[j])
            acc = term if acc is None else acc + term
        if not acc.is_zero():
            bad_a += 1
log('(a) equality rows: nonzero (order, copy) combinations %d' % bad_a)
# (b) compressed blocks, all solutions at once: vec(N1^T B N1) = vec(B) kron(N1, N1) etc.
bad_b = 0
Wt = [[fz(Wint[j][c * N:(c + 1) * N].T) for c in range(3)] for j in range(Dw + 1)]  # nsol x N per order and copy
for jb, Nm in red['N'].items():
    b = P['blocks'][jb]; m = b['m']; r_ = Nm.shape[1]
    N1, N2 = Nm[:m], Nm[m:]
    K11 = fz(np.kron(N1, N1)); K22 = fz(np.kron(N2, N2)); K12 = fz(np.kron(N1, N2))
    C2s = [C.reshape(N, m * m) for C in b['coef']]
    nzb = [v for v in range(N) if any(x != 0 for C2 in C2s for x in C2[v])]  # variables used by the block (any order)
    if not nzb:
        continue
    full = len(nzb) > N // 2
    if full:                                                           # dense block: full products, no W restriction
        Cz = [fz(C2) for C2 in C2s]; Wb = Wt
    else:
        Cz = [fz(C2[nzb]) for C2 in C2s]
        Wb = [[fz(Wint[j][c * N + np.array(nzb)].T) for c in range(3)] for j in range(Dw + 1)]
    for k in range(len(Cz) + Dw):
        js = [j for j in range(Dw + 1) if 0 <= k - j < len(Cz)]
        if not js:
            continue
        Lk = lk(js)
        Bc = [None, None, None]
        for j in js:
            for c in range(3):
                t = (Wb[j][c] * Cz[k - j]) * (Lk // Wden[j])                # nsol x m^2
                Bc[c] = t if Bc[c] is None else Bc[c] + t
        X11 = fz_entries(Bc[0] * K11).reshape(nsol, r_, r_)
        X22 = fz_entries(Bc[1] * K22).reshape(nsol, r_, r_)
        X12 = fz_entries(Bc[2] * K12).reshape(nsol, r_, r_)
        Rm = X11 + X22 + X12 + np.transpose(X12, (0, 2, 1))
        bad_b += sum(1 for s_ in range(nsol) if any(x != 0 for x in Rm[s_].ravel()))
log('(b) compressed blocks: nonzero (block, order, solution) combinations %d' % bad_b)
# (c) consistency with the objective
cc = P['c']
bad_c = 0
Wq = [flint.fmpq_mat(n, nsol, [flint.fmpq(x.numerator, x.denominator) for x in Wj.ravel()]) for Wj in W]
cq = []
for i in range(len(cc['ca'])):
    cv = list(cc['ca'][i]) + list(cc['cb'][i]) + [2 * v for v in cc['cab'][i]]
    cq.append(flint.fmpq_mat(1, n, [flint.fmpq(Fraction(x).numerator, Fraction(x).denominator) for x in cv]))
for k in range(len(cq) + Dw):
    tot = None
    for j in range(Dw + 1):
        i = k - j
        if 0 <= i < len(cq):
            t = cq[i] * Wq[j]
            tot = t if tot is None else tot + t
    if tot is not None:
        bad_c += sum(1 for s_ in range(nsol) if tot[0, s_] != 0)
log('(c) consistency w(s).c(s): nonzero (order, solution) combinations %d' % bad_c)
rk0 = Wq[0].rank()
log('rank W(0) = %d (left kernel dimension at s = 0: %d, kept solutions %d)' % (rk0, L['q'], nsol))
print('LEFT-KERNEL CERTIFICATE %s' % ('VERIFIED' if bad_a == 0 and bad_b == 0 and bad_c == 0 and rk0 == L['q'] else 'NOT VERIFIED'))
