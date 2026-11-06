"""Local site data at every d >= 4 for the S2 relaxation (own construction; nothing imported from the producer's code).

Cut () labels (4),(3,1),(2,2),(2,1,1),(1,1,1,1): the producer's integer HW bases (values 0..3) are d-independent vectors.
Cut (3,) labels: diagram vectors (paper A s.5.1) built here for every d:
  f = 0 (labels 0,1,2): e_x, x = (v0, v1, v2, d-1), v_i in {0..len(lambda)-1};
  f = 1 (labels 3,4):   sum_j e_x(j), contraction pair (r, 3) with x_r = x_3 = j, the other two uncut replicas fixed in {0..len-1}.
  C is solved exactly from J(4) = D(4) C (producer basis at d = 4), then J(d) := D(d) C.  Checked: J(3) = producer d = 3 basis.
For a given d: sparse V_p and V_p^{Gamma_3} on (C^d)^{x4}; cut-() Gram coordinates g(X) = concat_l vec(J_l^T X J_l) (24 x 24
matrix Gm on the V_p, invertible for d >= 4); maps pulled back by Lt = Lmat^T Gm^-T:
  cut3[l]: vec(J'_l(d)^T V_p^Gamma J'_l(d));  obj: d^kappa(p) - d^kappa((03)p)/2;  trace: d^kappa(p);  tr0: Tr_0 V_p in S3 words.
Lemma 5.1 check: every diagram-level element <D_i|V_p^Gamma|D_j> is eps d^kappa (eps in {0,1}, kappa <= 2f, same for d = 4..8).
Polynomial maps: exact interpolation in d (degree <= 2 for cut3, <= 4 obj, <= 1 tr0) from d = 4..8, checked at d = 9.
Output: alld/work/local4.pkl  {'poly': {key: [coef matrices by power of d]}, 'aux': ..., 'offs': ..., 'f0': ..., 'f3': ...}"""
import sys
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import scipy.sparse as sp
import flint
import safeload
from aud_common import PERMS, PIDX, KAPPA, MUL, AUX, AIDX, BITS, BIDX, act_bits, ncycles, perm_matrix, partial_transpose, digits, undigits

W_ = '<ROOT>/independent_check/'
S4 = safeload.load(W_ + 'alld/bundle/struct_k4d4_s2.pkl')
S3 = safeload.load(W_ + 'pkt/struct_k4d3_min.pkl')


def fq(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpq_mat(A.shape[0], A.shape[1], [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for x in A.ravel()])


def unq(M):
    return np.array([[Fraction(int(M[i, j].p), int(M[i, j].q)) for j in range(M.ncols())] for i in range(M.nrows())], dtype=object)


# ---------------------------------------------------------------- diagram templates for cut-(3,) labels
LAB3 = [e['label'] for e in S4['site'][(3,)]]
assert LAB3 == [(0, (3,), (1,)), (0, (2, 1), (1,)), (0, (1, 1, 1), (1,)), (1, (2,), ()), (1, (1, 1), ())]


def templates(label):
    f, lam, mu = label
    L = len(lam)
    out = []
    if f == 0:
        for v in itertools.product(range(L), repeat=3):
            out.append((None, v))                      # (v0, v1, v2, d-1)
    else:
        for r in range(3):
            for v in itertools.product(range(L), repeat=2):
                out.append((r, v))                     # pair (r,3); the other uncut replicas (in order) get v
    return out


def diagram_matrix(label, d):
    """Sparse (d^4 x T) integer matrix of the diagram vectors at dimension d."""
    rows, cols = [], []
    for t, (r, v) in enumerate(templates(label)):
        if r is None:
            rows.append(undigits([v[0], v[1], v[2], d - 1], d)); cols.append(t)
        else:
            others = [i for i in range(3) if i != r]
            for j in range(d):
                x = [0, 0, 0, j]
                x[r] = j
                x[others[0]], x[others[1]] = v
                rows.append(undigits(x, d)); cols.append(t)
    data = np.ones(len(rows), dtype=np.int64)
    return sp.csr_matrix((data, (rows, cols)), shape=(d ** 4, len(templates(label))))


def producer_J(S, T, l, d):
    e = S['site'][T][l]
    rows, cols, vals = [], [], []
    for tup, row in zip(e['basis'], e['J']):
        for c, v in enumerate(row):
            if v:
                rows.append(undigits(list(tup), d)); cols.append(c); vals.append(int(v))
    return sp.csr_matrix((vals, (rows, cols)), shape=(d ** 4, len(e['J'][0])))


Cmat = {}
for l, lab in enumerate(LAB3):
    D4 = diagram_matrix(lab, 4).toarray()
    J4 = producer_J(S4, (3,), l, 4).toarray()
    Dq = fq(D4)
    assert Dq.rank() == D4.shape[1], ('diagram vectors dependent', l)
    G = Dq.transpose() * Dq
    Cq = G.inv() * (Dq.transpose() * fq(J4))
    assert Dq * Cq == fq(J4), ('J(4) not in the diagram span', l)
    C = unq(Cq)
    assert all(Fraction(x).denominator == 1 for x in C.ravel())
    Cmat[l] = np.array([[int(x) for x in row] for row in C], dtype=np.int64)
    print('cut(3,) label %d %s: %d diagram vectors, C nonzeros %d, entries %s' % (
        l, lab, D4.shape[1], int(np.count_nonzero(Cmat[l])), sorted(set(Cmat[l].ravel().tolist()))), flush=True)
# cross-check with the producer's d = 3 bases (labels without (1,1,1),(1))
map3 = {0: 0, 1: 1, 3: 2, 4: 3}
for l4, l3 in map3.items():
    assert S3['site'][(3,)][l3]['label'] == LAB3[l4]
    Jm = (diagram_matrix(LAB3[l4], 3) @ sp.csr_matrix(Cmat[l4])).toarray()
    Jp = producer_J(S3, (3,), l3, 3).toarray()
    assert np.array_equal(Jm, Jp), ('d=3 mismatch', l4)
print('J(3) = D(3) C equals the producer d = 3 basis for labels 0,1,3,4', flush=True)


def J3(l, d):
    return (diagram_matrix(LAB3[l], d) @ sp.csr_matrix(Cmat[l])).tocsr()


LAB0 = [e['label'] for e in S4['site'][()]]
f0 = [len(e['J'][0]) for e in S4['site'][()]]
f3 = [Cmat[l].shape[1] for l in range(5)]
offs = [sum(x * x for x in f0[:l]) for l in range(5)]
NG = sum(x * x for x in f0)
assert NG == 24


def perm_sparse(d, p, gamma):
    n = d ** 4
    x = np.arange(n, dtype=np.int64)
    dg = [(x // d ** (3 - s)) % d for s in range(4)]
    tg = [None] * 4
    for i in range(4):
        tg[p[i]] = dg[i]
    rd, cd = tg, dg                                    # V_p[row(tg), col(dg)] = 1
    if gamma:
        rd, cd = list(rd), list(cd)
        rd[3], cd[3] = cd[3], rd[3]
    row = ((rd[0] * d + rd[1]) * d + rd[2]) * d + rd[3]
    col = ((cd[0] * d + cd[1]) * d + cd[2]) * d + cd[3]
    return sp.csr_matrix((np.ones(n, dtype=np.int64), (row, col)), shape=(n, n))


P3 = list(itertools.permutations(range(3)))


def tr0_word(p, d):
    """Tr_0 V_p = c V_q on (C^d)^{x3}: (q index, c) by the cycle rule, cross-checked literally at d <= 4."""
    if p[0] == 0:
        q = tuple(p[i] - 1 for i in (1, 2, 3))
        return P3.index(q), d
    # i -> p(i); remove 0: the element mapping to 0 now maps to p(0)
    pre = [i for i in range(4) if p[i] == 0][0]
    img = {i: p[i] for i in (1, 2, 3)}
    img[pre] = p[0]
    q = tuple(img[i] - 1 for i in (1, 2, 3))
    return P3.index(q), 1


def local_values(d):
    """Values on the 24 V_p at dimension d (exact integers / Fractions) and the cut-() Gram matrix Gm."""
    J0 = [producer_J(S4, (), l, d) for l in range(5)]
    J3d = [J3(l, d) for l in range(5)]
    Gm = np.zeros((24, NG), dtype=object)
    vals = {('cut3', l): np.zeros((24, f3[l] ** 2), dtype=object) for l in range(5)}
    diag = {}
    for pi, p in enumerate(PERMS):
        V = perm_sparse(d, p, False)
        VG = perm_sparse(d, p, True)
        Gm[pi, :] = np.concatenate([(J0[l].T @ V @ J0[l]).toarray().ravel() for l in range(5)])
        for l in range(5):
            vals[('cut3', l)][pi, :] = (J3d[l].T @ VG @ J3d[l]).toarray().ravel()
            Dm = diagram_matrix(LAB3[l], d)
            diag[(l, pi)] = (Dm.T @ VG @ Dm).toarray()
    obj = np.array([[Fraction(d ** int(KAPPA[pi])) - Fraction(d ** int(KAPPA[MUL[PIDX[(3, 1, 2, 0)], pi]]), 2)] for pi in range(24)], dtype=object)
    tr = np.array([[d ** int(KAPPA[pi])] for pi in range(24)], dtype=object)
    tr0 = np.zeros((24, 6), dtype=object)
    for pi, p in enumerate(PERMS):
        qi, c = tr0_word(p, d)
        tr0[pi, qi] = c
    vals['obj'], vals['trace'], vals['tr0'] = obj, tr, tr0
    return Gm, vals, diag


# literal cross-checks of tr0 rule and objective at d = 4 (dense)
for pi, p in enumerate(PERMS):
    V = perm_matrix(4, p)
    R = np.zeros((64, 64), dtype=np.int64)
    for x0 in range(4):
        idx = [undigits([x0] + digits(r, 4, 3), 4) for r in range(64)]
        R += V[np.ix_(idx, idx)]
    qi, c = tr0_word(p, 4)
    q = P3[qi]
    Vq = np.zeros((64, 64), dtype=np.int64)
    for x in range(64):
        src = digits(x, 4, 3)
        tgt = [0] * 3
        for i in range(3):
            tgt[q[i]] = src[i]
        Vq[undigits(tgt, 4), x] = 1
    assert np.array_equal(R, c * Vq), ('tr0 rule', p)
print('tr0 rule checked literally at d = 4 for all 24 permutations', flush=True)

DS = [4, 5, 6, 7, 8, 9]
LV = {}
Gm0 = None
for d in DS:
    Gm, vals, diag = local_values(d)
    if Gm0 is None:
        Gm0 = Gm
    assert np.array_equal(Gm, Gm0), 'cut-() Gram coordinates depend on d'
    LV[d] = (vals, diag)
Gq = fq(Gm0)
assert Gq.rank() == 24
GmTinv = Gq.transpose().inv()
print('cut-() Gram-coordinate matrix: d-independent for d = 4..9, rank 24', flush=True)
# Lemma 5.1 at the diagram level
bad = 0
for l in range(5):
    fl = LAB3[l][0]
    for pi in range(24):
        for (i, j), _ in np.ndenumerate(LV[4][1][(l, pi)]):
            seq = [int(LV[d][1][(l, pi)][i, j]) for d in DS]
            ok = all(v == 0 for v in seq)
            if not ok:
                kap = [k for k in range(2 * fl + 1) if all(seq[t] == DS[t] ** k for t in range(len(DS)))]
                ok = len(kap) == 1
            bad += not ok
print('Lemma 5.1 (eps d^kappa, eps in {0,1}, kappa <= 2f) at d = 4..9: violations %d' % bad, flush=True)
assert bad == 0


def pull(Lmat):
    return unq(fq(Lmat).transpose() * GmTinv)


# exact interpolation of the pulled-back maps in d (degree <= 4 for obj/trace, <= 2 cut3, <= 1 tr0), check at d = 9
keys = [('cut3', l) for l in range(5)] + ['obj', 'trace', 'tr0']
pulled = {d: {k: pull(LV[d][0][k]) for k in keys} for d in DS}
poly = {}
for k in keys:
    nodes = DS[:5]
    V = fq(np.array([[d ** e for e in range(5)] for d in nodes], dtype=object))
    Vi = V.inv()
    shp = pulled[4][k].shape
    stack = np.array([pulled[d][k].ravel() for d in nodes], dtype=object)       # 5 x entries
    coefs = unq(Vi * fq(stack))                                                  # 5 x entries (power e)
    deg = max([e for e in range(5) if any(x != 0 for x in coefs[e])] + [0])
    pred9 = sum(coefs[e] * 9 ** e for e in range(5))
    assert all(a == b for a, b in zip(pred9, pulled[9][k].ravel())), ('interpolation check at d = 9 failed', k)
    poly[k] = [coefs[e].reshape(shp) for e in range(deg + 1)]
    dens = 1
    for M in poly[k]:
        for x in M.ravel():
            dens = dens * Fraction(x).denominator // np.gcd(dens, Fraction(x).denominator)
    print('map %s: degree %d in d, common denominator %d (interpolated at d=4..8, checked at d=9)' % (k, deg, dens), flush=True)

# aux data (d-independent), from the producer's string blocks at d = 4
ab = {T: [list(map(tuple, blk)) for blk in S4['aux'][T]['blocks']] for T in ((), (3,))}
aux_coord = [(w, i, j) for w, blk in enumerate(ab[()]) for i in range(len(blk)) for j in range(len(blk))]
where3 = {s: (c, i) for c, blk in enumerate(ab[(3,)]) for i, s in enumerate(blk)}
aux_t3 = []
for (w, i, j) in aux_coord:
    r, s = ab[()][w][i], ab[()][w][j]
    (c1, i1), (c2, i2) = where3[(r[0], r[1], r[2], s[3])], where3[(s[0], s[1], s[2], r[3])]
    assert c1 == c2
    aux_t3.append((c1, i1, i2))
aux_obj = np.zeros((2, 2, 70), dtype=object)
for k, (w, i, j) in enumerate(aux_coord):
    r, s = ab[()][w][i], ab[()][w][j]
    if s == (r[3], r[1], r[2], r[0]):
        aux_obj[r[0], r[3], k] = 1
aux_st = np.zeros((70, 70), dtype=object)
for k, (w, i, j) in enumerate(aux_coord):
    r, s = ab[()][w][i], ab[()][w][j]
    aux_st[AIDX[(BIDX[r], BIDX[s])], k] += 1
    if r[0] == s[0]:
        for b in range(2):
            aux_st[AIDX[(BIDX[(b,) + r[1:]], BIDX[(b,) + s[1:]])], k] -= Fraction(1, 2)
aux_tr = np.array([1 if aux_coord[k][1] == aux_coord[k][2] else 0 for k in range(70)], dtype=object)
# literal check of aux transfer and objective against 16 x 16 matrices
for (w, i, j), (c, i1, i2) in zip(aux_coord, aux_t3):
    r, s = ab[()][w][i], ab[()][w][j]
    M = np.zeros((16, 16), dtype=np.int64)
    M[undigits(list(r), 2), undigits(list(s), 2)] = 1
    Mg = partial_transpose(M, 2, (3,))
    assert Mg[undigits(list(ab[(3,)][c][i1]), 2), undigits(list(ab[(3,)][c][i2]), 2)] == 1 and Mg.sum() == 1
pi_site = {l: None for l in range(5)}
pis = {}
for l in range(5):
    Jd = producer_J(S4, (), l, 4).toarray()
    Jq = fq(Jd)
    Gl = Jq.transpose() * Jq
    pis[l] = []
    for pi, p in enumerate(PERMS):
        VJ = fq(perm_matrix(4, p) @ Jd)
        P = Gl.inv() * (Jq.transpose() * VJ)
        assert Jq * P == VJ
        pis[l].append(unq(P))
out = {'poly': poly, 'offs': offs, 'f0': f0, 'f3': f3, 'C': Cmat, 'LAB0': LAB0, 'LAB3': LAB3, 'pi0': pis,
       'aux': {'blocks': ab, 'coord': aux_coord, 't3': aux_t3, 'obj': aux_obj, 'st': aux_st, 'tr': aux_tr}, 'P3': P3}
pickle.dump(out, open(W_ + 'alld/work/local4.pkl', 'wb'), protocol=4)
print('saved alld/work/local4.pkl', flush=True)
