"""Relaxation data R(d) at one large d, for the spot check of the producer's certificate there (own evaluation code):
  cut-() blocks: d-independent (checked exactly against my coordinate system in theta_checks4);
  cut-(3,) blocks: P_b(d) = sum_j coef_b[j] d^(deg_b - j)  (= deg_b! 576^4 times the true block; the polynomials were checked
                   against my own builds at s = 0, d = 14, 20 and are polynomial in d by Lemma 5.1);
  equality rows:   sum_j Ecoef_j d^(4 - j);
  objective:       MY exact value C_ab(B_i)(d) from the local4 polynomial maps (also compared with the producer's c(1/d)).
Writes the standard data format (k, N, E, blocks[F], ca, cb, cab, tr).  usage: spot_data.py d OUT"""
import sys
import time
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
d = int(sys.argv[1])
out = sys.argv[2]
CERT = safeload.load(sys.argv[3])          # only the blocks / rows this certificate uses are evaluated (others zero)
need_b = set(CERT['N'])
need_r = set(int(e) for e in CERT['erows'])
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
Linf = safeload.load('<ROOT>/certificates/alld/xk4dinf_s2.pkl')
S = safeload.load(W_ + 'alld/bundle/struct_k4d4_s2.pkl')
LOC = pickle.load(open(W_ + 'alld/work/local4.pkl', 'rb'))
N = P['N']
blocks = []
for jb, b in enumerate(P['blocks']):
    lb = Linf['blocks'][jb]
    assert (lb['cut'], tuple(lb['st']), lb['ai']) == (b['cut'], tuple(b['st']), b['ai'])
    deg = b['deg']
    F = np.zeros(np.asarray(b['coef'][0]).shape, dtype=object)
    if jb in need_b:
        for j, cj in enumerate(b['coef']):
            F = F + np.asarray(cj, dtype=object) * d ** (deg - j)
    blocks.append(dict(cut=b['cut'], st=b['st'], ai=b['ai'], tau=b['tau'], m=b['m'], F=F, deg=deg))
log('blocks evaluated (%d used by the certificate)' % len(need_b))
E = np.zeros(np.asarray(P['Ecoef'][0]).shape, dtype=object)
for r in need_r:
    E[r] = sum(np.asarray(Ej[r], dtype=object) * d ** (4 - j) for j, Ej in enumerate(P['Ecoef']))
log('equality rows evaluated (%d used by the certificate)' % len(need_r))
# my objective at d (as theta_checks4)
f0, offs = LOC['f0'], LOC['offs']
ab0 = LOC['aux']['blocks'][()]
adim = [len(x) for x in ab0]
aux_coord = LOC['aux']['coord']
ob = sum(c * d ** e for e, c in enumerate(LOC['poly']['obj']))[0]
tr = sum(c * d ** e for e, c in enumerate(LOC['poly']['trace']))[0]
L = (2 * d ** 4) ** 4


def mode_apply(Tn, M, axis):
    Tm = np.moveaxis(Tn, axis, 0)
    shp = Tm.shape
    R = M.dot(Tm.reshape(shp[0], -1))
    return np.moveaxis(R.reshape((M.shape[0],) + shp[1:]), 0, axis)


def aux_mat(vec70, ai):
    M = np.zeros((adim[ai], adim[ai]), dtype=object)
    for k, (w, i, j) in enumerate(aux_coord):
        if w == ai:
            M[i, j] = vec70[k]
    return M


mine = {k: [None] * N for k in ('ca', 'cb', 'cab', 'tr')}
for v in S['variables']:
    st, ai, off = tuple(v['st']), v['ai'], v['off']
    W = np.array(v['W'], dtype=object)
    mp = W.shape[1]
    shape = [f0[x] for x in st] + [adim[ai]]
    nH = int(np.prod(shape))
    norder = len(set(itertools.permutations(st)))
    for key, sitev, auxv, scale in (('ca', ob, LOC['aux']['obj'][0, 0], 2), ('cb', ob, LOC['aux']['obj'][1, 1], 2),
                                    ('cab', ob, LOC['aux']['obj'][0, 1] + LOC['aux']['obj'][1, 0], 1), ('tr', tr, LOC['aux']['tr'], 1)):
        mats = [np.array(sitev[offs[x]:offs[x] + f0[x] ** 2], dtype=object).reshape(f0[x], f0[x]) for x in st] + [aux_mat(auxv, ai)]
        Wt = W.reshape(shape + [mp])
        for l in range(5):
            Wt = mode_apply(Wt, mats[l], l)
        M = W.T.dot(Wt.reshape(nH, mp))
        for j, B in enumerate(v['basis']):
            B = np.array(B, dtype=object)
            val = sum(Fraction(B[a, b]) * Fraction(M[a, b]) for a in range(mp) for b in range(mp))
            mine[key][off + j] = val * norder * scale / L
prod = {key: [sum(Fraction(P['c'][key][j][i]) * Fraction(1, d ** j) for j in range(len(P['c'][key]))) for i in range(N)]
        for key in ('ca', 'cb', 'cab', 'tr')}
for key in ('ca', 'cb', 'cab', 'tr'):
    log('objective %s at d: mine == producer c(1/d): %s' % (key, mine[key] == prod[key]))
pickle.dump(dict(k=4, d=d, N=N, E=E, blocks=blocks, ca=np.array(mine['ca'], dtype=object), cb=np.array(mine['cb'], dtype=object),
                 cab=np.array(mine['cab'], dtype=object), tr=np.array(mine['tr'], dtype=object)), open(out, 'wb'), protocol=4)
log('saved %s' % out)
