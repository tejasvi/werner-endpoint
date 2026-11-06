"""Verdict 4, step B (own code): power-of-two scalings Dr, Dc of A_RS(0), a dyadic approximate inverse X of
At_0 = Dr A_RS(0) Dc, and exactly  theta0 = ||I - At_0 X||_inf,  ||X||_inf,  beta = ||X||_inf / (1 - theta0).
Scalings (my choice): Dc_k = 2^-g_k with g_k = ceil(log2 max_i |A_ik|); Dr_i = 2^-f_i with f_i = ceil(log2 max_k |A_ik| Dc_k).
X = round(inv(At_0 in float64) * 2^kx) / 2^kx.  Exact product with flint.  Usage: bounds_B.py bA_0.pkl OUT"""
import sys
import time
import math
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
A0 = pickle.load(open(sys.argv[1], 'rb'))
assert A0['orders'] == [0]
At = A0['At'][0]
n = 4780
colmax = [0] * n
for (i, k), v in At.items():
    colmax[k] = max(colmax[k], abs(v))
assert all(x > 0 for x in colmax), 'zero column in A_RS(0)'
g = [int(x).bit_length() for x in colmax]                 # 2^(g-1) <= max < 2^g
rowmax = [Fraction(0)] * n
for (i, k), v in At.items():
    rowmax[i] = max(rowmax[i], Fraction(abs(v), 2 ** g[k]))
assert all(x > 0 for x in rowmax), 'zero row in A_RS(0)'
f = [math.ceil(math.log2(float(x))) if float(x) > 0 else 0 for x in rowmax]
# exact float of the scaled matrix (each entry v * 2^(-g_k - f_i); float64 rounding is fine for the approximate inverse)
Af = np.zeros((n, n))
for (i, k), v in At.items():
    Af[i, k] = math.ldexp(float(v) if abs(v) < 2 ** 1000 else float(Fraction(v)), -g[k] - f[i])
log('scaled At_0 built: max |entry| %.3f, min row max %.3e' % (np.abs(Af).max(), np.abs(Af).max(axis=1).min()))
Xf = np.linalg.inv(Af)
kx = 52 - int(math.ceil(math.log2(np.abs(Xf).max())))
Xi = np.rint(np.ldexp(Xf, kx)).astype(np.int64)
log('float inverse done; kx = %d, max |X int| = %d' % (kx, int(np.abs(Xi).max())))
# exact:  At_0 X = Dr A Dc X.  With A'[i,k] = A[i,k] 2^(G - g_k) (integer, G = max g), (A' Xi)[i,j] = 2^(G + kx + f_i) (At_0 X)[i,j]
G = max(g)
rows = [[] for _ in range(n)]
Ap = flint.fmpz_mat(n, n)
for (i, k), v in At.items():
    Ap[i, k] = v << (G - g[k])
Xm = flint.fmpz_mat(n, n, [int(x) for x in Xi.ravel()])
log('flint matrices built (G = %d)' % G)
Pm = Ap * Xm
log('flint product done')
theta_num = []
th = Fraction(0)
for i in range(n):
    sc = G + kx + f[i]                      # (At_0 X)[i,j] = Pm[i,j] / 2^sc ; may be negative sc
    tot = 0
    for j in range(n):
        v = int(Pm[i, j])
        e = -v if j != i else (1 << sc) - v if sc >= 0 else None
        if sc < 0:
            raise AssertionError('negative scale exponent')
        tot += abs(e)
    th = max(th, Fraction(tot, 1 << sc))
xn = max(Fraction(int(np.abs(Xi[i]).sum()), 2 ** kx) for i in range(n))
beta = xn / (1 - th) if th < 1 else None
log('theta0 = ||I - At_0 X||_inf = %.6e (exact rational), ||X||_inf = %.6e, beta = %s' % (float(th), float(xn), '%.6e' % float(beta) if beta else 'NONE'))
pickle.dump({'f': f, 'g': g, 'theta0': th, 'Xnorm': xn, 'beta': beta, 'kx': kx}, open(sys.argv[2], 'wb'), protocol=4)
log('saved %s' % sys.argv[2])
