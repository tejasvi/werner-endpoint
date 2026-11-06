"""Exact checks of the S2 coordinate system (d >= 4) and the cheap data checks, as ../theta_checks.py for d = 3:
 (1) W full column rank, S_j symmetric and independent;  (2) left replica invariance Pi(s)^T H = H (generators of S4);
 (3) site-stabiliser invariance;  (4) cut-() outputs: producer coef[0] == V_b^T H_b(B_i)^T V_b for all 409 blocks, all i;
 (5) objective at d in DSPECS (and the s = 0 limit): my C_ab(B_i)(d) (local4 polynomial maps) == producer c(s = 1/d), exactly.
usage: theta_checks4.py DSPEC ...   (integers >= 4 or 'inf')"""
import sys
import time
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload
from aud_common import PERMS, PIDX, act_bits, inverse

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
S = safeload.load(W_ + 'alld/bundle/struct_k4d4_s2.pkl')
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
LOC = pickle.load(open(W_ + 'alld/work/local4.pkl', 'rb'))
f0, offs = LOC['f0'], LOC['offs']
ab0 = LOC['aux']['blocks'][()]
adim = [len(b) for b in ab0]
aux_coord = LOC['aux']['coord']
specs = sys.argv[1:]


def oarr(A):
    return np.array(A, dtype=object)


def mode_apply(Tn, M, axis):
    Tm = np.moveaxis(Tn, axis, 0)
    shp = Tm.shape
    R = M.dot(Tm.reshape(shp[0], -1))
    return np.moveaxis(R.reshape((M.shape[0],) + shp[1:]), 0, axis)


def aux_pi(ai, s):
    blk = [tuple(b) for b in ab0[ai]]
    idx = {b: k for k, b in enumerate(blk)}
    Pm = np.zeros((len(blk), len(blk)), dtype=object)
    for k, b in enumerate(blk):
        Pm[idx[act_bits(s, b)], k] = 1
    return Pm


def rank_q(A):
    A = oarr(A)
    return flint.fmpq_mat(A.shape[0], A.shape[1], [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for x in A.ravel()]).rank()


def aux_mat(vec70, ai):
    a = adim[ai]
    M = np.zeros((a, a), dtype=object)
    for k, (w, i, j) in enumerate(aux_coord):
        if w == ai:
            M[i, j] = vec70[k]
    return M


def obj_site(dspec):
    co = LOC['poly']['obj']
    if dspec == 'inf':
        return co[4][0]
    d = int(dspec)
    return sum(c * d ** e for e, c in enumerate(co))[0]


L_of = lambda dspec: None if dspec == 'inf' else (2 * int(dspec) ** 4) ** 4
GENS = [(1, 0, 2, 3), (1, 2, 3, 0)]
bad = []
Hall = {}
yobj = {sp_: {k: [None] * 1633 for k in ('ca', 'cb', 'cab')} for sp_ in specs}
for vi, v in enumerate(S['variables']):
    st, ai, off = tuple(v['st']), v['ai'], v['off']
    W = oarr(v['W'])
    Sj = [oarr(B) for B in v['basis']]
    mp = W.shape[1]
    shape = [f0[x] for x in st] + [adim[ai]]
    nH = int(np.prod(shape))
    assert W.shape[0] == nH and all(B.shape == (mp, mp) and np.array_equal(B, B.T) for B in Sj)
    assert rank_q(W) == mp and rank_q(np.array([B.ravel() for B in Sj], dtype=object)) == len(Sj), vi
    Hs = [W.dot(B).dot(W.T) for B in Sj]
    for s in GENS:
        mats = [oarr(LOC['pi0'][x][PIDX[s]]) for x in st] + [aux_pi(ai, s)]
        Wt = W.reshape(shape + [mp])
        for l in range(5):
            Wt = mode_apply(Wt, mats[l].T, l)
        if not np.array_equal(Wt.reshape(nH, mp), W):
            for H in Hs:
                Ht = H.reshape(shape + [nH])
                for l in range(5):
                    Ht = mode_apply(Ht, mats[l].T, l)
                if not np.array_equal(Ht.reshape(nH, nH), H):
                    bad.append(('replica', vi, s))
    for pm in PERMS:
        if tuple(st[pm[l]] for l in range(4)) != st:
            continue
        pinv = inverse(pm)
        ax = [pinv[l] for l in range(4)] + [4]
        for H in Hs:
            Hp = np.transpose(H.reshape(shape + shape), ax + [5 + a for a in ax]).reshape(nH, nH)
            if not np.array_equal(Hp, H):
                bad.append(('stabiliser', vi, pm))
    norder = len(set(itertools.permutations(st)))
    for sp_ in specs:
        ob = obj_site(sp_)
        Om = [oarr(ob[offs[x]:offs[x] + f0[x] ** 2]).reshape(f0[x], f0[x]) for x in st]
        L = L_of(sp_)
        for key, auxv, scale in (('ca', LOC['aux']['obj'][0, 0], 2), ('cb', LOC['aux']['obj'][1, 1], 2),
                                 ('cab', LOC['aux']['obj'][0, 1] + LOC['aux']['obj'][1, 0], 1)):
            mats = Om + [aux_mat(auxv, ai)]
            Wt = W.reshape(shape + [mp])
            for l in range(5):
                Wt = mode_apply(Wt, mats[l], l)
            M = W.T.dot(Wt.reshape(nH, mp))
            for j, B in enumerate(Sj):
                val = sum(Fraction(B[a, b]) * Fraction(M[a, b]) for a in range(mp) for b in range(mp)) * norder * scale
                # finite d: c = val / L;  limit: c(0) = (top coefficient) / 16
                yobj[sp_][key][off + j] = val / L if L else val / 16
    Hall[(st, ai)] = (Hs, off)
log('variables %d; structural failures %d %s' % (len(S['variables']), len(bad), bad[:4]))
# (4) cut-() outputs against xpoly (deg 0, coef[0])
tk = lambda t: None if t is None else tuple(t)
pk = {(b['cut'], tuple(b['st']), b['ai'], tk(b['tau'])): b for b in P['blocks']}
nb = nc = 0
for o in S['outputs']:
    if o['cut'] != ():
        continue
    b = pk[((), tuple(o['st']), o['ai'], tk(o['tau']))]
    assert b['deg'] == 0
    F = b['coef'][0]
    V = oarr(o['V'])
    Hs, off = Hall[(tuple(o['st']), o['ai'])]
    tgt = {off + j: V.T.dot(H.T).dot(V) for j, H in enumerate(Hs)}
    for i in range(1633):
        nc += 1
        Fi = oarr(F[i])
        ok = np.array_equal(Fi, tgt[i]) if i in tgt else not any(int(x) for x in Fi.ravel())
        nb += not ok
log('cut() outputs: %d (block, coord) pairs, %d mismatches' % (nc, nb))
# (5) objective
for sp_ in specs:
    for key in ('ca', 'cb', 'cab'):
        co = [[Fraction(x) for x in c] for c in P['c'][key]]
        if sp_ == 'inf':
            prod = co[0]
        else:
            s = Fraction(1, int(sp_))
            prod = [sum(co[j][i] * s ** j for j in range(len(co))) for i in range(1633)]
        nd = sum(1 for a, b in zip(yobj[sp_][key], prod) if a != b)
        log('objective %s at d=%s: %d of 1633 coordinates differ (exact)' % (key, sp_, nd))
