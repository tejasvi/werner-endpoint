"""Is the limit data file (xk4dinf_s2.pkl, used by the s = 0 certificate) the s^0 part of the polynomial data (xpoly4.pkl,
used by the uniform argument)?  Per block a single positive rational factor, per equality row a factor, objective equal."""
import sys
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload

Linf = safeload.load('<ROOT>/certificates/alld/xk4dinf_s2.pkl')
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
tk = lambda t: None if t is None else tuple(t)
pk = {(b['cut'], tuple(b['st']), b['ai'], tk(b['tau'])): b for b in P['blocks']}
facs = {}
bad = 0
for bi, b in enumerate(Linf['blocks']):
    key = (b['cut'], tuple(b['st']), b['ai'], tk(b['tau']))
    q = pk[key]
    F = np.asarray(b['F'], dtype=object)
    C0 = np.asarray(q['coef'][0], dtype=object)
    nz = np.flatnonzero(C0.ravel())
    if len(nz) == 0:
        ok = not any(int(x) for x in F.ravel())
        fac = None
    else:
        fac = Fraction(int(F.ravel()[nz[0]]), int(C0.ravel()[nz[0]]))
        ok = all(int(a) * fac.denominator == int(c) * fac.numerator for a, c in zip(F.ravel(), C0.ravel())) and fac > 0
    facs.setdefault((b['cut'], q['deg']), set()).add(fac)
    bad += not ok
print('blocks: %d, mismatches %d; factor F_inf / coef[0] by (cut, deg): %s' % (len(Linf['blocks']), bad, {k: sorted(v, key=str)[:4] for k, v in facs.items()}))
E = np.asarray(Linf['E'], dtype=object)
E0 = np.asarray(P['Ecoef'][0], dtype=object)
assert E.shape == E0.shape, (E.shape, E0.shape)
rf = set()
ebad = 0
for r in range(E.shape[0]):
    nz = np.flatnonzero(E0[r])
    if len(nz) == 0:
        ebad += any(int(x) for x in E[r])
        continue
    fac = Fraction(int(E[r][nz[0]]), int(E0[r][nz[0]]))
    rf.add(fac)
    ebad += not all(int(a) * fac.denominator == int(c) * fac.numerator for a, c in zip(E[r], E0[r]))
print('equality rows: %d, non-proportional %d, distinct factors %s' % (E.shape[0], ebad, sorted(rf)[:5]))
for key in ('ca', 'cb', 'cab', 'tr'):
    v = [Fraction(x) for x in Linf[key]]
    w = [Fraction(x) for x in P['c'][key][0]]
    print('objective %s: equal to the s^0 coefficient: %s' % (key, v == w))
