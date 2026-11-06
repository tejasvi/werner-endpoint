"""Mutation tests for the all-d checks (each must FAIL on altered input).
M1: one producer coefficient coef_b[0] + 1 -> the s = 0 comparison with my build reports exactly one mismatching (block, coord).
M2: one W_0 entry changed -> the left-kernel identities (a)/(b) get nonzero residues at a prime."""
import sys
import glob
import math
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload

W_ = '<ROOT>/independent_check/'
p = 1073741789
S = safeload.load(W_ + 'alld/bundle/struct_k4d4_s2.pkl')
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
tk = lambda t: None if t is None else tuple(t)
sig = {(o['cut'], tuple(o['st']), o['ai'], tk(o['tau'])): bi for bi, o in enumerate(S['outputs'])}
pblk = {sig[(b['cut'], tuple(b['st']), b['ai'], tk(b['tau']))]: b for b in P['blocks']}
F3 = {}
for fn in sorted(glob.glob(W_ + 'alld/work/e_p%d_inf_c*.pkl' % p)):
    for bi, dct in pickle.load(open(fn, 'rb'))['F3'].items():
        F3.setdefault(bi, {}).update(dct)
bi0 = [bi for bi in sorted(pblk) if S['outputs'][bi]['cut'] == (3,) and pblk[bi]['deg'] == 8][0]
b = pblk[bi0]
m = b['m']
C0 = np.asarray(b['coef'][0], dtype=object).copy()
i0 = [i for i in range(1633) if i in F3[bi0] and any(int(x) for x in C0[i].ravel())][0]
C0[i0, 0, 0] += 1
fac = math.factorial(b['deg'])
nb = 0
for i in range(1633):
    mine = np.mod(np.rint(F3[bi0][i]), p).astype(np.int64) if i in F3[bi0] else np.zeros((m, m), dtype=np.int64)
    nb += not np.array_equal(mine * fac % p, np.mod(C0[i], p).astype(np.int64))
print('M1 (coef[0] + 1 in block %d coord %d): mismatching coordinates %d (expect 1)' % (bi0, i0, nb))
# M2: W_0 entry changed; test (a) on all rows and copies at s = 1, prime 1048573
q_ = 1048573
LK = safeload.load(W_ + 'alld/bundle/xlk4.pkl')
Wc = [np.asarray(Wj, dtype=object) for Wj in LK['coefs']]
N = P['N']


def wmod(Wj):
    A = np.zeros(Wj.shape)
    for (r, c), x in np.ndenumerate(Wj):
        if x != 0:
            fx = Fraction(x)
            A[r, c] = (fx.numerator % q_) * pow(fx.denominator % q_, -1, q_) % q_
    return A


def resid(Wlist):
    Ws = np.zeros(Wlist[0].shape)
    for Wj in Wlist:                   # s = 1
        Ws = np.fmod(Ws + wmod(Wj), q_)
    Es = np.zeros((P['Ecoef'][0].shape[0], N))
    for E in P['Ecoef']:
        Es = np.fmod(Es + np.mod(np.asarray(E, dtype=object), q_).astype(np.float64), q_)
    return sum(int(np.count_nonzero(np.fmod(Es @ Ws[c * N:(c + 1) * N], q_))) for c in range(3))


print('M2: (a) residues at s = 1 with the original W: %d (expect 0)' % resid(Wc[:9]))
Wm = [Wj.copy() for Wj in Wc[:9]]
r0, c0 = [(r, c) for (r, c), x in np.ndenumerate(Wm[0]) if x != 0][5]
Wm[0][r0, c0] = Fraction(Wm[0][r0, c0]) + 1
print('M2: (a) residues at s = 1 with W_0[%d,%d] + 1: %d (expect > 0)' % (r0, c0, resid(Wm)))
