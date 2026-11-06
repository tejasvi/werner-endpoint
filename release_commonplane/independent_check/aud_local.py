"""Local (one tensor factor) exact data, computed from literal operators.

Site factor (C^3)^{x4}.  For cut T and label l the producer's struct gives an integer matrix J (rows = digit tuples).
We use J only as a compression.  Everything else is recomputed here:
  * pi(p) with V_p^{Gamma_T} J = J pi(p) (exact; checked), G = J^T J;
  * Gram coordinates of a site operator X in Comm = span{V_p}:  g(X) = concat_l vec(J_l^T X J_l)  (cut () labels);
    Gm[p] = g(V_p) (24 x 23), rank 23 => g is injective on Comm (kernel of p -> V_p is the sign vector);
  * any linear map Lmap on Comm, known on the V_p, is pulled back to Gram coordinates:  Lt = Lmat^T Gm (Gm^T Gm)^-1;
    consistency: sum_p sgn(p) Lmat[p] = 0;
  * maps: cut-(3,) Gram forms J'^T X^{Gamma_3} J' (labels 0..3 of cut (3,)), objective Tr((I - F_03/2) X),
    trace Tr X, Stiefel part Tr_0 X in the S3-word basis, and the Hilbert-Schmidt form.
Aux factor (C^2)^{x4}: Gram coordinates of cut () = the 70 weight-block entries (producer string order);
  transfer to cut (3,) charge blocks, objective parts, Stiefel part, all literal.
Output: work/local.pkl (Fractions as (num, den) pairs inside numpy object arrays)."""
import sys
import itertools
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload
from aud_common import *

STRUCT = '<ROOT>/independent_check/pkt/struct_k4d3_min.pkl'
OUT = '<ROOT>/independent_check/work/local.pkl'
S = safeload.load(STRUCT)
d = 3
n4 = d ** 4


def to_fmpq(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpq_mat(A.shape[0], A.shape[1], [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for x in A.ravel()])


def from_fmpq(M):
    return np.array([[Fraction(int(M[i, j].p), int(M[i, j].q)) for j in range(M.ncols())] for i in range(M.nrows())], dtype=object)


def site_J(T, l):
    e = S['site'][T][l]
    J = np.zeros((n4, len(e['J'][0])), dtype=np.int64)
    assert len(e['basis']) == len(e['J'])
    for tup, row in zip(e['basis'], e['J']):
        J[undigits(list(tup), d), :] = row
    return J, e['label']


VP = [perm_matrix(d, p) for p in PERMS]
VPG = [partial_transpose(V, d, (3,)) for V in VP]
sgn = np.array([(-1) ** (4 - ncycles(p)) for p in PERMS], dtype=object)      # sign of p
assert not np.any(sum(int(s) * VP[i] for i, s in enumerate(sgn)))            # antisymmetrizer vanishes at d = 3

res = {'site': {}, 'aux': {}}
for T, ops in (((), VP), ((3,), VPG)):
    for l in range(4):
        J, label = site_J(T, l)
        f = J.shape[1]
        Jq = to_fmpq(J)
        G = Jq.transpose() * Jq
        assert G.rank() == f
        Gi = G.inv()
        pis = []
        for p in range(24):
            VJ = to_fmpq(ops[p] @ J)
            pi = Gi * (Jq.transpose() * VJ)
            assert Jq * pi == VJ, ('span(J) not invariant', T, l, p)
            pis.append(from_fmpq(pi))
        res['site'][(T, l)] = {'J': J, 'label': label, 'G': from_fmpq(G), 'pi': pis, 'f': f}
        print('site T=%s label %d %s: f=%d, span invariant under all V_p%s' % (T, l, label, f, '^Gamma' if T else ''), flush=True)

# Gram coordinates for cut () labels 0..3
offs, o = [], 0
for l in range(4):
    offs.append(o)
    o += res['site'][((), l)]['f'] ** 2
NG = o
assert NG == 23
Gm = np.zeros((24, NG), dtype=object)
for p in range(24):
    row = []
    for l in range(4):
        J = res['site'][((), l)]['J']
        H = J.T @ VP[p] @ J
        row += [int(x) for x in H.ravel()]
    Gm[p, :] = row
Gmq = to_fmpq(Gm)
print('Gram-coordinate matrix Gm: rank %d of %d' % (Gmq.rank(), NG))
assert Gmq.rank() == 23
assert all(sum(int(sgn[p]) * Gm[p, j] for p in range(24)) == 0 for j in range(NG))
iota = Gmq * (Gmq.transpose() * Gmq).inv()          # 24 x 23, Gm^T iota = I
assert Gmq.transpose() * iota == flint.fmpq_mat(23, 23, [1 if i == j else 0 for i in range(23) for j in range(23)])


def pull(Lmat):
    """Lmat: 24 x m (values of a linear map on the V_p).  Returns Lt (m x 23) with Lt g(X) = L(X)."""
    Lmat = np.asarray(Lmat, dtype=object)
    for j in range(Lmat.shape[1]):
        assert sum(int(sgn[p]) * Fraction(Lmat[p, j]) for p in range(24)) == 0, 'map does not vanish on the kernel'
    Lt = to_fmpq(Lmat).transpose() * iota
    out = from_fmpq(Lt)
    # exactness check on every V_p
    chk = to_fmpq(out) * Gmq.transpose()
    assert chk == to_fmpq(Lmat).transpose()
    return out


maps = {}
# cut-(3,) Gram forms for each cut-(3,) label
for l in range(4):
    J3 = res['site'][((3,), l)]['J']
    Lmat = np.array([(J3.T @ VPG[p] @ J3).ravel() for p in range(24)], dtype=object)
    maps[('cut3', l)] = pull(Lmat)
# objective: Tr((I - F_03/2) V_p) = d^kappa(p) - d^kappa((03) p)/2
sw = PIDX[(3, 1, 2, 0)]
obj = np.array([[Fraction(d ** int(KAPPA[p])) - Fraction(d ** int(KAPPA[MUL[sw, p]]), 2)] for p in range(24)], dtype=object)
# literal check of the objective formula
F03 = VP[sw]
for p in range(24):
    lit = np.trace(VP[p]) - Fraction(int(np.trace(F03 @ VP[p])), 2)
    assert lit == obj[p, 0]
maps['obj'] = pull(obj)
maps['trace'] = pull(np.array([[int(np.trace(VP[p]))] for p in range(24)], dtype=object))
# Stiefel site part: Tr_0 V_p = c V_q, q in S3 on factors (1,2,3) -> (0,1,2)
P3 = list(itertools.permutations(range(3)))


def perm3_matrix(q):
    M = np.zeros((27, 27), dtype=np.int64)
    for x in range(27):
        src = digits(x, 3, 3)
        tgt = [0] * 3
        for i in range(3):
            tgt[q[i]] = src[i]
        M[undigits(tgt, 3), x] = 1
    return M


V3 = [perm3_matrix(q) for q in P3]
V3stack = np.array([M.ravel() for M in V3], dtype=np.int64)
assert np.linalg.matrix_rank(V3stack.astype(float)) == 6
tr0 = np.zeros((24, 6), dtype=object)
for p in range(24):
    R = np.zeros((27, 27), dtype=np.int64)
    V = VP[p]
    for x0 in range(3):
        idx = [undigits([x0] + digits(r, 3, 3), 3) for r in range(27)]
        R += V[np.ix_(idx, idx)]
    hits = [(qi, int(R[np.nonzero(V3[qi])][0])) for qi in range(6) if np.array_equal((R != 0), (V3[qi] != 0))]
    assert len(hits) == 1
    qi, c = hits[0]
    assert np.array_equal(R, c * V3[qi])
    tr0[p, qi] = c
maps['tr0'] = pull(tr0)
# Hilbert-Schmidt form on Comm: Tr(V_p^T V_q) = d^kappa(p^-1 q); in Gram coordinates HS = iota^T M iota
HSm = np.array([[d ** int(KAPPA[MUL[INV[p], q]]) for q in range(24)] for p in range(24)], dtype=object)
maps['HS'] = from_fmpq(iota.transpose() * to_fmpq(HSm) * iota)
res['maps'] = maps
res['offs'] = offs
res['iota'] = from_fmpq(iota)
res['Gm'] = Gm
res['P3'] = P3
print('site maps: cut3 labels', [maps[('cut3', l)].shape for l in range(4)], 'obj', maps['obj'].shape, 'tr0', maps['tr0'].shape)
for key, M in maps.items():
    den = 1
    for x in M.ravel():
        den = den * Fraction(x).denominator // np.gcd(den, Fraction(x).denominator)
    print('  map', key, 'common denominator', den)

# ---------------------------------------------------------------- aux
ab = {T: [list(map(tuple, blk)) for blk in S['aux'][T]['blocks']] for T in ((), (3,))}
# global index of aux Gram coordinates for cut (): (w, i, j) in producer string order
aux_coord = []
for w, blk in enumerate(ab[()]):
    for i in range(len(blk)):
        for j in range(len(blk)):
            aux_coord.append((w, i, j))
assert len(aux_coord) == 70
aux_pos = {c: k for k, c in enumerate(aux_coord)}
# cut-(3,) charge blocks: string -> (block, index)
where3 = {}
for c, blk in enumerate(ab[(3,)]):
    for i, s in enumerate(blk):
        where3[s] = (c, i)
assert len(where3) == 16
where0 = {}
for w, blk in enumerate(ab[()]):
    for i, s in enumerate(blk):
        assert sum(s) == w
        where0[s] = (w, i)
# transfer: |r><s| -> |r0 r1 r2 s3><s0 s1 s2 r3|
aux_t3 = []
for (w, i, j) in aux_coord:
    r, s = ab[()][w][i], ab[()][w][j]
    rr = (r[0], r[1], r[2], s[3])
    ss = (s[0], s[1], s[2], r[3])
    (c1, i1), (c2, i2) = where3[rr], where3[ss]
    assert c1 == c2
    aux_t3.append((c1, i1, i2))
# literal check of the transfer on all 16x16 units
for (w, i, j), (c, i1, i2) in zip(aux_coord, aux_t3):
    r, s = ab[()][w][i], ab[()][w][j]
    M = np.zeros((16, 16), dtype=np.int64)
    M[undigits(list(r), 2), undigits(list(s), 2)] = 1
    Mg = partial_transpose(M, 2, (3,))
    rr, ss = ab[(3,)][c][i1], ab[(3,)][c][i2]
    assert Mg[undigits(list(rr), 2), undigits(list(ss), 2)] == 1 and Mg.sum() == 1
# objective aux parts: Tr(P_i^(3) F_03 P_j^(3) |r><s|) = [r0 = i][r3 = j][s = swap03(r)]
aux_obj = np.zeros((2, 2, 70), dtype=object)
for k, (w, i, j) in enumerate(aux_coord):
    r, s = ab[()][w][i], ab[()][w][j]
    if s == (r[3], r[1], r[2], r[0]):
        aux_obj[r[0], r[3], k] = 1
# literal check of the aux objective
for ii in range(2):
    for jj in range(2):
        Pi = np.zeros((2, 2), dtype=np.int64); Pi[ii, ii] = 1
        Pj = np.zeros((2, 2), dtype=np.int64); Pj[jj, jj] = 1
        I2 = np.eye(2, dtype=np.int64)
        P3i = np.kron(np.kron(np.kron(I2, I2), I2), Pi)
        P3j = np.kron(np.kron(np.kron(I2, I2), I2), Pj)
        F = perm_matrix(2, (3, 1, 2, 0))
        Op = P3i @ F @ P3j
        for k, (w, i, j) in enumerate(aux_coord):
            r, s = ab[()][w][i], ab[()][w][j]
            M = np.zeros((16, 16), dtype=np.int64)
            M[undigits(list(r), 2), undigits(list(s), 2)] = 1
            assert int(np.trace(Op @ M)) == aux_obj[ii, jj, k]
# Stiefel aux part: s0(|r><s|) = |r><s| - [r0 = s0] 1/2 sum_b |b r123><b s123|, output in the 70 units (global AUX order)
aux_st = np.zeros((70, 70), dtype=object)          # [output unit (AUX index), input coord k]
for k, (w, i, j) in enumerate(aux_coord):
    r, s = ab[()][w][i], ab[()][w][j]
    aux_st[AIDX[(BIDX[r], BIDX[s])], k] += 1
    if r[0] == s[0]:
        for b in range(2):
            rb, sb = (b,) + r[1:], (b,) + s[1:]
            aux_st[AIDX[(BIDX[rb], BIDX[sb])], k] -= Fraction(1, 2)
aux_tr = np.array([1 if aux_coord[k][1] == aux_coord[k][2] else 0 for k in range(70)], dtype=object)
res['aux'] = {'blocks': ab, 'coord': aux_coord, 't3': aux_t3, 'obj': aux_obj, 'st': aux_st, 'tr': aux_tr}
print('aux: 70 coordinates, transfer/objective/Stiefel built and literal-checked')
pickle.dump(res, open(OUT, 'wb'), protocol=4)
print('saved', OUT)
