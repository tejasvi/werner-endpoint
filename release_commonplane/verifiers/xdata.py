"""Exact (rational) structure of the torus slice relaxation (relaxM), in Gram-form block coordinates.

Per site and cut T the module data come from local.module_data: integer embeddings J_l, metric G_l = J_l^T J_l and rational
pi_l(p) with V_p^{Gamma_T} J_l = J_l pi_l(p).  A PSD block is a Gram form H = J^T X J (J = tensor product of the site
embeddings and the aux selection), never an orthonormalised matrix, so every map is rational:
  site map cut () -> cut T on Gram coordinates  Phi_T = FTG_T @ IFG_(),  FTG_T[(k,a,b), p] = (G_k pi_k(p))[a,b],
      IFG_()[p, (l,i,j)] = (dim_l/24) (pi_l(p^-1) G_l^-1)[j,i]  (Fourier inversion; Phi_() is the identity);
  aux (torus) maps: 0/1 re-indexings of the 70 weight-preserving units;
  variables: H_b = W_b S W_b^T, W_b an integer basis of range(sum_g (x) G pi(g)) (bosonic part), S in an integer basis of
      the site-stabiliser-invariant symmetric matrices;
  output blocks: V^T H^T V with V = U_H Q_tau: U_H an integer basis of range(R_H) (R_H = cut-T symmetriser), Q_tau the
      range of a Young-symmetriser idempotent of the site stabiliser, one per irrep type tau.
PSD of H^T  <=>  PSD of every V^T H^T V (H^T = R_H^T H^T R_H; isotypic components are orthogonal for invariant forms and
an invariant form on M (x) tau is C_tau (x) g_tau with g_tau > 0)."""
import sys, os, itertools, math
from fractions import Fraction
import numpy as np
import flint

SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from local import module_data, perms, compose, inverse, ncycles, partitions
from relaxM import STR, SIDX, WORDS, WIDX, perm_op, ptrans16

P4 = perms(4)
I4 = {p: i for i, p in enumerate(P4)}
SWAP03 = (3, 1, 2, 0)


def F(x):
    """sympy Rational / int / fmpq / Fraction -> Fraction"""
    if isinstance(x, Fraction):
        return x
    if hasattr(x, 'p') and hasattr(x, 'q'):
        return Fraction(int(x.p), int(x.q))
    return Fraction(int(x))


def qmat(A):
    A = [[F(v) for v in row] for row in A]
    r, c = len(A), (len(A[0]) if A else 0)
    return flint.fmpq_mat(r, c, [flint.fmpq(v.numerator, v.denominator) for row in A for v in row])


def zmat(A):
    A = np.asarray(A)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()])


def q2obj(M):
    return np.array([[F(v) for v in row] for row in M.tolist()], dtype=object).reshape(M.nrows(), M.ncols())


def primitive_int_cols(A):
    """Fraction/int object array -> int object array with each column scaled to coprime integers."""
    A = np.array(A, dtype=object)
    out = np.zeros(A.shape, dtype=object)
    for j in range(A.shape[1]):
        col = [F(v) for v in A[:, j]]
        den = 1
        for v in col:
            den = den * v.denominator // math.gcd(den, v.denominator)
        ints = [int(v * den) for v in col]
        g = 0
        for v in ints:
            g = math.gcd(g, v)
        g = g or 1
        out[:, j] = [v // g for v in ints]
    return out


def pivots_of_rref(R, rank):
    piv = []
    for r in range(rank):
        for c in range(R.ncols()):
            if R[r, c] != 0:
                piv.append(c)
                break
    return piv


def colbasis(A):
    """Columns of A (int or Fraction object array) at the rref pivot positions: a basis of range(A)."""
    A = np.array(A, dtype=object)
    if A.size == 0:
        return A[:, :0]
    R, rank = qmat(A).rref()
    return A[:, pivots_of_rref(R, rank)]


def solve_right(W, Y):
    """B with W B = Y exactly (W full column rank)."""
    m = W.shape[1]
    R, rank = qmat(W.T).rref()
    assert rank == m
    rows = pivots_of_rref(R, rank)
    B = qmat(W[rows]).inv() * qmat(Y[rows])
    assert qmat(W) * B == qmat(Y)
    return B


def kron_all(mats):
    out = np.ones((1, 1), dtype=mats[0].dtype)
    for m_ in mats:
        out = np.kron(out, m_)
    return out


def factor_perm(dims, s, k):
    """Permutation matrix (int64) of the site-factor permutation s (site i -> site s[i]) on the tensor space with factor
    dimensions dims (k sites then aux), as in relax.Relaxation.factor_perm."""
    n = int(np.prod(dims))
    idx = np.arange(n).reshape(dims)
    axes = list(range(k + 1))
    for i in range(k):
        axes[s[i]] = i
    tgt = np.transpose(idx, axes).ravel()
    Pm = np.zeros((n, n), dtype=np.int64)
    Pm[np.arange(n), tgt] = 1
    return Pm


def coset_reps(st, siteperms):
    seen = {}
    for s in siteperms:
        new = [None] * len(st)
        for i in range(len(st)):
            new[s[i]] = st[i]
        new = tuple(new)
        if new not in seen:
            seen[new] = s
    return list(seen.items())


def sym_basis_int(Bs, m):
    """Integer basis of symmetric m x m matrices S with B S B^T = S for all B in Bs (fmpq_mat)."""
    pairs = [(i, j) for i in range(m) for j in range(i, m)]
    def E(i, j):
        M = flint.fmpq_mat(m, m)
        M[i, j] = 1
        M[j, i] = 1
        return M
    if len(Bs) <= 1:
        mats = [E(i, j) for i, j in pairs]
    else:
        rows = []
        for i, j in pairs:
            S = E(i, j)
            Rs = Bs[0] * S * Bs[0].transpose()
            for B in Bs[1:]:
                Rs = Rs + B * S * B.transpose()
            rows.append([Rs[a, b] for a, b in pairs])
        R, rank = flint.fmpq_mat(len(rows), len(pairs), [v for row in rows for v in row]).rref()
        mats = []
        for r in range(rank):
            M = flint.fmpq_mat(m, m)
            for c, (a, b) in enumerate(pairs):
                M[a, b] = R[r, c]
                M[b, a] = R[r, c]
            mats.append(M)
    out = []
    for M in mats:
        A = q2obj(M).reshape(-1, 1)
        out.append(primitive_int_cols(A).reshape(m, m))
    return out


def young_idempotents(st):
    """Primitive idempotents of the site stabiliser of the label tuple st (a Young subgroup), one per irrep type: products of
    normalised Young symmetrisers (row-filled tableaux) on the classes of equal labels.  Returns [(tau, {perm: Fraction})]."""
    k = len(st)
    classes = [tuple(i for i in range(k) if st[i] == v) for v in sorted(set(st))]
    def gmul(a, b):
        out = {}
        for p, x in a.items():
            for q, y in b.items():
                r = compose(p, q)
                out[r] = out.get(r, 0) + x * y
        return {p: v for p, v in out.items() if v}
    def sgn(p):
        return (-1) ** (len(p) - ncycles(p))
    def sym_group(pos, signed):
        out = {}
        for img in itertools.permutations(pos):
            p = list(range(k))
            for a, b in zip(pos, img):
                p[a] = b
            p = tuple(p)
            out[p] = Fraction(sgn(p) if signed else 1)
        return out
    per_class = []
    for pos in classes:
        c = len(pos)
        opts = []
        for lam in partitions(c):
            rows, at = [], 0
            for r in lam:
                rows.append(pos[at:at + r]); at += r
            cols = [tuple(rows[i][j] for i in range(len(rows)) if j < len(rows[i])) for j in range(lam[0])]
            a = {tuple(range(k)): Fraction(1)}
            for r in rows:
                a = gmul(a, sym_group(r, False))
            b = {tuple(range(k)): Fraction(1)}
            for cl in cols:
                b = gmul(b, sym_group(cl, True))
            cT = gmul(a, b)
            c2 = gmul(cT, cT)
            p0 = next(iter(cT))
            scale = c2[p0] / cT[p0]
            opts.append((lam, {p: v / scale for p, v in cT.items()}))
        per_class.append(opts)
    out = []
    for combo in itertools.product(*per_class):
        e = {tuple(range(k)): Fraction(1)}
        for lam, ec in combo:
            e = gmul(e, ec)
        out.append((tuple(lam for lam, _ in combo), e))
    return out


class SiteX:
    def __init__(self, cut, d):
        cut = tuple(sorted(cut))
        self.cut, self.d = cut, d
        data = module_data(4, cut, d)
        self.labels = list(data)
        self.dims = [data[l]['dim'] for l in self.labels]
        self.off = [0]
        for n in self.dims:
            self.off.append(self.off[-1] + n * n)
        self.D = self.off[-1]
        self.G, self.Gadj, self.Ginv, self.pi, self.M = [], [], [], [], []
        for l in self.labels:
            G = np.array([[int(v) for v in row] for row in data[l]['G'].tolist()], dtype=object)
            Gi = q2obj(qmat(G).inv())
            det = F(qmat(G).det())
            self.G.append(G); self.Ginv.append(Gi)
            self.Gadj.append(np.array([[int(v * det) for v in row] for row in Gi], dtype=object))
            pis = [np.array([[F(v) for v in row] for row in P.tolist()], dtype=object) for P in data[l]['pi']]
            self.pi.append(pis)
            Ms = []
            for P in pis:
                Mp = G.dot(P)
                assert all(F(v).denominator == 1 for v in Mp.ravel())
                Ms.append(np.array([[int(v) for v in row] for row in Mp], dtype=np.int64))
            self.M.append(np.array(Ms))                                    # (24, dim, dim) = J^T V_p^Gamma J
        self.FTG = np.zeros((self.D, 24), dtype=np.int64)
        for li, n in enumerate(self.dims):
            self.FTG[self.off[li]:self.off[li + 1], :] = self.M[li].reshape(24, n * n).T
        if not cut:
            IF = np.zeros((24, self.D), dtype=object)
            for a, p in enumerate(P4):
                pinv = I4[inverse(p)]
                for li, n in enumerate(self.dims):
                    A = self.pi[li][pinv].dot(self.Ginv[li])
                    IF[a, self.off[li]:self.off[li + 1]] = (Fraction(n, 24) * A.T).ravel()
            self.IFG = IF

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


class AuxX:
    def __init__(self, cut):
        cut = tuple(sorted(cut))
        self.cut = cut
        charge = lambda z: sum(z[i] for i in range(4) if i not in cut) - sum(z[i] for i in range(4) if i in cut)
        self.labels = sorted(set(charge(z) for z in STR))
        self.blocks = [[z for z in STR if charge(z) == c] for c in self.labels]
        self.pos = {z: (li, j) for li, bl in enumerate(self.blocks) for j, z in enumerate(bl)}
        self.dims = [len(b) for b in self.blocks]
        self.off = [0]
        for n in self.dims:
            self.off.append(self.off[-1] + n * n)
        self.D = self.off[-1]
        self.M = []
        for bl in self.blocks:
            idx = [SIDX[z] for z in bl]
            self.M.append(np.array([np.rint(ptrans16(perm_op(g), cut)[np.ix_(idx, idx)]) for g in P4]).astype(np.int64))
        self.FT = np.zeros((self.D, len(WORDS)), dtype=np.int64)
        for e, (x, y) in enumerate(WORDS):
            x2 = tuple(y[i] if i in cut else x[i] for i in range(4))
            y2 = tuple(x[i] if i in cut else y[i] for i in range(4))
            (li, i1), (lj, j1) = self.pos[x2], self.pos[y2]
            assert li == lj
            self.FT[self.off[li] + i1 * self.dims[li] + j1, e] = 1

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


def apply_factors(mats, A):
    """(x) mats applied to the columns of A (rows = tensor index), exact (object arrays)."""
    dims = [m_.shape[1] for m_ in mats]
    X = np.array(A, dtype=object).reshape(dims + [A.shape[1]])
    for i, m_ in enumerate(mats):
        X = np.moveaxis(np.tensordot(np.array(m_, dtype=object), X, axes=(1, i)), 0, i)
    return X.reshape(-1, A.shape[1])


class XRelax:
    """keep(cut, st, site) -> bool selects output label tuples (e.g. the minimal support)."""

    def __init__(self, k, d=3, cuts=((), (3,)), keep=None, verbose=True):
        self.k, self.d, self.cuts = k, d, tuple(cuts)
        self.verbose = verbose
        self.site = {c: SiteX(c, d) for c in self.cuts}
        self.aux = {c: AuxX(c) for c in self.cuts}
        self.siteperms = perms(k)
        s0, a0 = self.site[()], self.aux[()]
        self.Phi = {}
        for c in self.cuts:
            P = self.site[c].FTG.astype(object).dot(s0.IFG)
            den = 1
            for v in P.ravel():
                den = den * F(v).denominator // math.gcd(den, F(v).denominator)
            self.Phi[c] = (np.array([[int(F(v) * den) for v in row] for row in P], dtype=object), den)
        num, den = self.Phi[()]
        assert den == 1 and (num == np.eye(s0.D, dtype=np.int64)).all(), 'Phi_() is not the identity'
        self.PhiA = {c: self.aux[c].FT.dot(a0.FT.T) for c in self.cuts}
        self.build_variables()
        self.build_outputs(keep)

    def _log(self, s):
        if self.verbose:
            print(s, flush=True)

    def build_variables(self):
        k = self.k
        s0, a0 = self.site[()], self.aux[()]
        self.vars, off = [], 0
        for st in itertools.combinations_with_replacement(range(len(s0.labels)), k):
            for ai in range(len(a0.labels)):
                dims = [s0.dims[i] for i in st] + [a0.dims[ai]]
                Rt = sum(kron_all([s0.M[i][g] for i in st] + [a0.M[ai][g]]) for g in range(24))
                W = colbasis(Rt)
                m = W.shape[1]
                if m == 0:
                    continue
                stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(k))]
                Bs = [solve_right(W, factor_perm(dims, s, k).astype(object).dot(W)) for s in stab]
                basis = sym_basis_int(Bs, m)
                if not basis:
                    continue
                self.vars.append(dict(st=st, ai=ai, dims=dims, W=W, m=m, basis=basis,
                                      cosets=coset_reps(st, self.siteperms), off=off))
                off += len(basis)
        self.N = off
        self._log('variables: %d blocks, N %d' % (len(self.vars), self.N))

    def build_outputs(self, keep):
        k = self.k
        self.outs = []
        for cut in self.cuts:
            sx, ax = self.site[cut], self.aux[cut]
            H = [g for g in range(24) if set(P4[g][i] for i in cut) == set(cut)]
            nb = 0
            for st in itertools.combinations_with_replacement(range(len(sx.labels)), k):
                if keep is not None and not keep(cut, st, sx):
                    continue
                for ai in range(len(ax.labels)):
                    dims = [sx.dims[i] for i in st] + [ax.dims[ai]]
                    Rt = sum(kron_all([sx.M[i][g] for i in st] + [ax.M[ai][g]]) for g in H)
                    Wt = colbasis(Rt)
                    if Wt.shape[1] == 0:
                        continue
                    U = primitive_int_cols(apply_factors([sx.Gadj[i] for i in st] + [np.eye(ax.dims[ai], dtype=np.int64)], Wt))
                    stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(k))]
                    if len(stab) > 1:
                        Bs = {s: solve_right(U, factor_perm(dims, s, k).astype(object).dot(U)) for s in stab}
                        for tau, e in young_idempotents(st):
                            Rho = flint.fmpq_mat(U.shape[1], U.shape[1])
                            for s, v in e.items():
                                Rho = Rho + Bs[s] * flint.fmpq(v.numerator, v.denominator)
                            Q = colbasis(q2obj(Rho))
                            if Q.shape[1] == 0:
                                continue
                            V = primitive_int_cols(U.dot(Q))
                            self.outs.append(dict(cut=cut, st=st, ai=ai, tau=tau, dims=dims, V=V, m=V.shape[1])); nb += 1
                    else:
                        self.outs.append(dict(cut=cut, st=st, ai=ai, tau=None, dims=dims, V=U, m=U.shape[1])); nb += 1
            self._log('cut %s: %d output blocks (before zero pruning)' % (cut, nb))


def min_support(cut, st, sx):
    """cut () and the fully contracted cut-(3,) sector (every site label has one contraction, f = 1)."""
    return cut == () or (cut == (3,) and all(sx.labels[i][0] == 1 for i in st))


def s2_support(cut, st, sx):
    """min_support plus the cut-(3,) label (f = 0, lam = (1,1,1), mu = (1)) (present for d >= 4; equals min_support at d = 3)."""
    return cut == () or (cut == (3,) and all(sx.labels[i][0] == 1 or sx.labels[i] == (0, (1, 1, 1), (1,)) for i in st))


SUPPORTS = {'min': min_support, 's2': s2_support, 'all': None}


if __name__ == '__main__':
    import time
    k = int(sys.argv[1])
    sup, d = ((sys.argv[2] if len(sys.argv) > 2 else 'all') + ':3').split(':')[:2]      # e.g. 'min' or 'min:4'
    t0 = time.time()
    X = XRelax(k, d=int(d), keep=SUPPORTS[sup])
    print('k=%d d=%s %s: N %d, %d variable blocks' % (k, d, sup, X.N, len(X.vars)))
    from collections import Counter
    for cut in X.cuts:
        bs = [o for o in X.outs if o['cut'] == cut]
        print(cut, len(bs), sorted(Counter(o['m'] for o in bs).items()))
    print('Phi dens', {c: X.Phi[c][1] for c in X.cuts}, 'max |W|', max(max(abs(int(v)) for v in b['W'].ravel()) for b in X.vars),
          'max |V|', max(max(abs(int(v)) for v in o['V'].ravel()) for o in X.outs), '%.0fs' % (time.time() - t0))
