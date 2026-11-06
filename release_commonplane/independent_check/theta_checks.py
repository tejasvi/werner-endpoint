"""Exact structural checks of the producer's coordinate system y (Theta basis) and the cheap data checks.

B_i (i = off_v + j) is the element of the full commutant whose cut-() Gram form on the sorted label tuple st_v and
aux block ai_v is H = W_v S_{v,j} W_v^T, whose Gram forms on the other orderings of st_v are the site-permuted
copies, and whose Gram forms on all other label classes vanish.  Checks:
  (1) shapes; S_j symmetric; W full column rank; S_j linearly independent  =>  the 1331 B_i are independent;
  (2) left replica invariance Pi(s)^T H = H for s in generators of S4 (Pi = (x)_l pi_{st_l}(s) (x) pi_aux(s));
  (3) invariance under site permutations stabilising st (factor permutation of the Gram form);
  (4) D1: objective C_00, C_11, C_01 and trace at every B_i, exactly, against c_a, c_b, c_ab, tr of the data file;
  (5) D3 for cut (): V_b^T H_b(B_i) V_b against F_b[i] for all 267 cut-() outputs and all i.
With dim S = 1331 (Gram rank of orbit sums), (1)-(3) make {B_i} a basis of S = A_full^Gamma."""
import sys
import time
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload
from aud_common import *

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
S = safeload.load(W_ + 'pkt/struct_k4d3_min.pkl')
D = safeload.load(W_ + 'p1x/slice/xk4_min.pkl')
LOC = pickle.load(open(W_ + 'work/local.pkl', 'rb'))
L = (2 * 3 ** 4) ** 4

f0 = [LOC['site'][((), l)]['f'] for l in range(4)]
ab0 = LOC['aux']['blocks'][()]
adim = [len(b) for b in ab0]


def oarr(A):
    return np.array(A, dtype=object)


def mode_apply(Tn, M, axis):
    """Tn object tensor; M object matrix (r x Tn.shape[axis]); returns tensor with axis replaced by r."""
    Tm = np.moveaxis(Tn, axis, 0)
    shp = Tm.shape
    R = M.dot(Tm.reshape(shp[0], -1))
    return np.moveaxis(R.reshape((M.shape[0],) + shp[1:]), 0, axis)


def aux_pi(ai, s):
    blk = [tuple(b) for b in ab0[ai]]
    idx = {b: k for k, b in enumerate(blk)}
    P = np.zeros((len(blk), len(blk)), dtype=object)
    for k, b in enumerate(blk):
        P[idx[act_bits(s, b)], k] = 1
    return P


def rank_q(A):
    A = oarr(A)
    M = flint.fmpq_mat(A.shape[0], A.shape[1], [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for x in A.ravel()])
    return M.rank()


GENS = [(1, 0, 2, 3), (1, 2, 3, 0)]
# local objective maps restricted to label blocks, reshaped f x f
offs = LOC['offs']
obj_site = LOC['maps']['obj'][0]
tr_site = LOC['maps']['trace'][0]


def lab_mat(vec, l):
    f = f0[l]
    return oarr(vec[offs[l]:offs[l] + f * f]).reshape(f, f)


aux_coord = LOC['aux']['coord']


def aux_mat(vec70, ai):
    a = adim[ai]
    M = np.zeros((a, a), dtype=object)
    for k, (w, i, j) in enumerate(aux_coord):
        if w == ai:
            M[i, j] = vec70[k]
    return M


nvar = len(S['variables'])
y_obj = {key: [None] * 1331 for key in ('a', 'b', 'ab', 'tr')}
cover = [0] * 1331
H_all = {}
bad = []
off_expect = 0
for vi, v in enumerate(S['variables']):
    st, ai, off = tuple(v['st']), v['ai'], v['off']
    W = oarr(v['W'])
    Sj = [oarr(B) for B in v['basis']]
    mprime = W.shape[1]
    nH = int(np.prod([f0[x] for x in st])) * adim[ai]
    # (1) shapes, ranks
    assert list(v['dims']) == [f0[x] for x in st] + [adim[ai]], (vi, v['dims'])
    assert W.shape[0] == nH and all(B.shape == (mprime, mprime) for B in Sj)
    assert off == off_expect, (vi, off, off_expect)
    off_expect += len(Sj)
    assert all(np.array_equal(B, B.T) for B in Sj)
    assert rank_q(W) == mprime, ('W rank', vi)
    assert rank_q(np.array([B.ravel() for B in Sj], dtype=object)) == len(Sj), ('S_j dependent', vi)
    Hs = [W.dot(B).dot(W.T) for B in Sj]
    # (2) replica invariance: Pi(s)^T W = W  (else test H directly)
    shape = [f0[x] for x in st] + [adim[ai]]
    for s in GENS:
        si = PIDX[s]
        mats = [oarr(LOC['site'][((), x)]['pi'][si]) for x in st] + [aux_pi(ai, s)]
        Wt = W.reshape(shape + [mprime])
        for l in range(5):
            Wt = mode_apply(Wt, mats[l].T, l)
        if not np.array_equal(Wt.reshape(nH, mprime), W):
            for H in Hs:
                Ht = H.reshape(shape + [nH])
                for l in range(5):
                    Ht = mode_apply(Ht, mats[l].T, l)
                if not np.array_equal(Ht.reshape(nH, nH), H):
                    bad.append(('replica', vi, s))
    # (3) stabiliser of st under site permutations
    stab = [p for p in PERMS if tuple(st[p[l]] for l in range(4)) == st]
    for p in stab:
        # (P_pi J)_l uses site pi^-1(l); with st fixed, Q_pi H Q_pi^T permutes the 4 site axes
        pinv = inverse(p)
        ax = [pinv[l] for l in range(4)] + [4]
        for H in Hs:
            Ht = H.reshape(shape + shape)
            Hp = np.transpose(Ht, ax + [5 + a for a in ax]).reshape(nH, nH)
            if not np.array_equal(Hp, H):
                bad.append(('stabiliser', vi, p))
    norder = len(set(itertools.permutations(st)))
    # (4) objective and trace (site-symmetric product functionals: every ordering gives the same value)
    Om_sites = [lab_mat(obj_site, x) for x in st]
    Tr_sites = [lab_mat(tr_site, x) for x in st]
    for key, auxv, sites, scale in (('a', LOC['aux']['obj'][0, 0], Om_sites, Fraction(2, L)),
                                    ('b', LOC['aux']['obj'][1, 1], Om_sites, Fraction(2, L)),
                                    ('ab', LOC['aux']['obj'][0, 1] + LOC['aux']['obj'][1, 0], Om_sites, Fraction(1, L)),
                                    ('tr', LOC['aux']['tr'], Tr_sites, Fraction(1, L))):
        mats = sites + [aux_mat(auxv, ai)]
        Wt = W.reshape(shape + [mprime])
        for l in range(5):
            Wt = mode_apply(Wt, mats[l], l)          # Omega W (Omega = (x) mats acting on the row index)
        M = W.T.dot(Wt.reshape(nH, mprime))          # W^T Omega W
        for j, B in enumerate(Sj):
            val = sum(Fraction(B[a, b]) * Fraction(M[a, b]) for a in range(mprime) for b in range(mprime))
            y_obj[key][off + j] = scale * norder * val
    for j in range(len(Sj)):
        cover[off + j] += 1
    H_all[vi] = (st, ai, Hs, off)
log('variables: %d, coordinates %d; structural failures: %d %s' % (nvar, off_expect, len(bad), bad[:5]))
assert off_expect == 1331 and all(c == 1 for c in cover)

# (4) compare objective / trace
names = {'a': 'ca', 'b': 'cb', 'ab': 'cab', 'tr': 'tr'}
for key, dn in names.items():
    mine = y_obj[key]
    prod = [Fraction(x) for x in D[dn]]
    nd = sum(1 for a, b in zip(mine, prod) if a != b)
    log('D1 %s: %d of 1331 coordinates differ (exact)' % (dn, nd))
    if nd:
        ex = [(i, mine[i], prod[i]) for i in range(1331) if mine[i] != prod[i]][:5]
        log('   examples %s' % (ex,))

# (5) cut-() outputs
byclass = {}
for vi, (st, ai, Hs, off) in H_all.items():
    byclass[(st, ai)] = (Hs, off)
nbad = 0
nchk = 0
for bi, (o, b) in enumerate(zip(S['outputs'], D['blocks'])):
    if o['cut'] != ():
        continue
    assert tuple(o['st']) == tuple(b['st']) and o['ai'] == b['ai'] and o['cut'] == b['cut']
    V = oarr(o['V'])
    F = b['F']
    Hs, off = byclass[(tuple(o['st']), o['ai'])]
    target = {off + j: V.T.dot(H.T).dot(V) for j, H in enumerate(Hs)}
    for i in range(1331):
        Fi = F[i]
        if i in target:
            ok = np.array_equal(oarr(Fi), target[i])
        else:
            ok = not any(int(x) for x in Fi.ravel())
        nchk += 1
        if not ok:
            nbad += 1
            if nbad <= 5:
                log('   cut() mismatch block %d coord %d' % (bi, i))
log('D3 cut(): %d (block, coordinate) pairs checked, %d mismatches' % (nchk, nbad))
pickle.dump({'y_obj': y_obj}, open(W_ + 'work/theta_obj.pkl', 'wb'), protocol=4)
log('done')
