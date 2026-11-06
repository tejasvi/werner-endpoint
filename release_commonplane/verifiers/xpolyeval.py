"""Exact relaxation data at an arbitrary dimension d from the polynomial data (xpoly.py), in the xbuild data format:
   blocks F_b = sum_j d^(deg_b - j) Fhat_{b,j}  (= deg_b! DEN^k times the true block at d, integers),
   equality rows E_r = sum_j d^(deg_r - j) Ehat_{r,j},   c(d) = sum_j d^-j c_j  (exact Fractions).
Also stores 'Fscale_deg' (deg_b) so that a scaled multiplier Yhat_b maps to Yhat_b * d^-deg_b.
Usage: python xpolyeval.py POLYPICKLE d OUT.pkl [LIMITDATA for met/nat fields]"""
import sys, pickle
from fractions import Fraction
import numpy as np

P = pickle.load(open(sys.argv[1], 'rb')); d = int(sys.argv[2]); out = sys.argv[3]
Dlim = pickle.load(open(sys.argv[4], 'rb')) if len(sys.argv) > 4 else None
blocks = []
for jb, b in enumerate(P['blocks']):
    deg = b['deg']
    F = sum(b['coef'][j] * (d ** (deg - j)) for j in range(len(b['coef'])))
    nb = dict(cut=b['cut'], st=b['st'], ai=b['ai'], tau=b['tau'], m=b['m'], F=F, deg=deg)
    if Dlim is not None:
        lb = Dlim['blocks'][jb]
        assert (lb['cut'], lb['st'], lb['ai'], lb['tau']) == (b['cut'], b['st'], b['ai'], b['tau'])
        nb['met'] = lb['met']
        nb['nat'] = lb.get('nat', 1.0) * float(d) ** (-deg) if b['cut'] == (3,) else 1.0
    blocks.append(nb)
Ec = P['Ecoef']
E = np.zeros(Ec[0].shape, dtype=object)
for r, dr in enumerate(P['Edeg']):
    E[r] = sum(Ec[j][r] * (d ** (int(dr) - j)) for j in range(int(dr) + 1))
c = {key: sum(P['c'][key][j] * Fraction(1, d ** j) for j in range(len(P['c'][key]))) for key in ('ca', 'cb', 'cab', 'tr')}
pickle.dump(dict(k=P['k'], d=d, sup='s2', N=P['N'], E=E, blocks=blocks, ca=c['ca'], cb=c['cb'], cab=c['cab'], tr=c['tr'],
                 den_phi=P['DEN_PHI'], varmet=P['varmet'], from_poly=True), open(out, 'wb'), protocol=4)
print('data at d = %d written (%d blocks, %d equality rows)' % (d, len(blocks), E.shape[0]))
