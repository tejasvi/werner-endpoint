"""Check the polynomial data (xpoly.py) against exact data built directly at a dimension d that is not an interpolation node:
   cut-() blocks:   Fhat_b,0 == F_b(d)                                   (d-independent)
   cut-(3,) blocks: sum_j d^(deg-j) Fhat_{b,j} * den_phi(d)^k == deg! DEN_PHI^k F_b(d)      (xbuild stores den_phi(d)^k x block)
   equality rows:   sum_j d^(deg_r-j) Ehat_{r,j} == c_E E_r(d) with one rational constant c_E for all rows
   objective/trace: sum_j d^-j c_j == c(d) exactly.
Blocks are matched by their labels (cut, st, ai, tau).   Usage: python xnodecheck.py POLYPICKLE BUILD_D.pkl"""
import sys, pickle, math
from fractions import Fraction
import numpy as np

P = pickle.load(open(sys.argv[1], 'rb')); B = pickle.load(open(sys.argv[2], 'rb'))
d = int(B['d']); K = P['k']
assert B['N'] == P['N'] and B['k'] == K
byb = {(b['cut'], b['st'], b['ai'], b['tau']): b for b in B['blocks']}
bad_b = 0
for b in P['blocks']:
    bb = byb.pop((b['cut'], b['st'], b['ai'], b['tau']))
    Fp = sum(b['coef'][j] * d ** (b['deg'] - j) for j in range(len(b['coef'])))
    if b['cut'] == ():
        ok = (Fp == bb['F']).all()
    else:
        ok = (Fp * int(B['den_phi']) ** K == bb['F'].astype(object) * (math.factorial(b['deg']) * P['DEN_PHI'] ** K)).all()
    bad_b += not ok
print('blocks: %d checked, %d mismatches, %d built blocks without a polynomial counterpart' % (len(P['blocks']), bad_b, len(byb)))
Ep = np.zeros(P['Ecoef'][0].shape, dtype=object)
for r, dr in enumerate(P['Edeg']):
    Ep[r] = sum(P['Ecoef'][j][r] * d ** (int(dr) - j) for j in range(int(dr) + 1))
Eb = B['E'].astype(object)
assert Ep.shape == Eb.shape, 'equality rows: %s vs %s' % (Ep.shape, Eb.shape)
nz = np.argwhere(Eb != 0)
r0, c0 = nz[0]
cE = Fraction(int(Ep[r0, c0]), int(Eb[r0, c0]))
okE = (Ep * cE.denominator == Eb * cE.numerator).all()
print('equality rows: E_poly == c_E E_built for every entry: %s (c_E = %s = %s x K!)' % (okE, cE, cE / math.factorial(K)))
okc = True
for key in ('ca', 'cb', 'cab', 'tr'):
    cp = [sum(P['c'][key][j][v] * Fraction(1, d ** j) for j in range(len(P['c'][key]))) for v in range(P['N'])]
    okc = okc and all(Fraction(x) == Fraction(y) for x, y in zip(cp, B[key]))
print('objective/trace vectors equal: %s' % okc)
print('NODE CHECK at d = %d: %s' % (d, 'PASS' if bad_b == 0 and not byb and okE and okc else 'FAIL'))
