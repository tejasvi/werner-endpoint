"""Twirled four-replica moment relaxation (after Zenodo 23134454) for k copies of C^d.

Variables: three source families X_31, X_22, X_13 (operators on V^{x4}, V = (C^d)^{xk} x C^2),
twirled by U(d)^k x U(2), site permutations and complex conjugation, globally bosonic.
Each X_f is parametrised by symmetric matrices S_lam = J_lam^T X J_lam on the G_f-invariant
part of each irrep tuple lam = (lam_0..lam_{k-1}; mu) of the untransposed local algebras,
one representative per site-permutation orbit (orthonormal local modules: numerics only).

Constraint blocks (each a symmetric matrix linear in the variables, required PSD):
  * family cuts:  K^T X_f^{Gamma_T} K, K = one copy of each irrep tuple of the cut-T algebras,
    compressed to the range of the (G_f cap Stab T)-symmetriser;
  * coupled Gram: [[A(X31), B(X22)], [B(X22)^T, D(X13)]] on the cut-{3} irreps, compressed by
    the (01)-symmetriser;
Equalities: Stiefel contrasts (slot 0 of X31, X22; slot 3 of X13), AAB and ABB marginals.
Objective: Tr[Z_{0,3} X_31]/L, normalisation Tr X_31 / L = 1, L = (2 d^k)^4.
"""
from __future__ import annotations

import itertools
import math
import time

import numpy as np

from local import module_data, perms, compose, inverse, ncycles

P4 = perms(4)
I4 = {p: i for i, p in enumerate(P4)}
P3 = perms(3)
I3 = {p: i for i, p in enumerate(P3)}
TAU = (0, 1, 3, 2)
P0 = (2, 3, 1, 0)
SWAP03 = (3, 1, 2, 0)

FAMILY_GROUP = {
    '31': [p + (3,) for p in P3],
    '13': [p + (3,) for p in P3],
    '22': [(0, 1, 2, 3), (1, 0, 2, 3), (0, 1, 3, 2), (1, 0, 3, 2)],
}
FAMILY_CUTS = {
    '31': [(), (3,), (0,), (0, 1)],
    '13': [(), (3,), (0,), (0, 1)],
    '22': [(), (0,), (2,), (0, 1), (0, 2)],
}
FAMILIES = ('31', '22', '13')


class LocalNum:
    """Orthonormalised numeric module data for (n, m, cut)."""

    def __init__(self, n, m, cut):
        cut = tuple(sorted(cut))
        data = module_data(m, cut, n)
        self.n, self.m, self.cut = n, m, cut
        self.labels = list(data)
        self.dims = [data[l]['dim'] for l in self.labels]
        self.off = [0]
        for d in self.dims:
            self.off.append(self.off[-1] + d * d)
        self.D = self.off[-1]
        self.P = perms(m)
        self.pi = []
        for l in self.labels:
            G = np.array(data[l]['G'], dtype=float)
            w, Q = np.linalg.eigh(G)
            Gh = (Q * np.sqrt(w)) @ Q.T
            Gih = (Q / np.sqrt(w)) @ Q.T
            self.pi.append(np.array([Gh @ np.array(pi, dtype=float) @ Gih for pi in data[l]['pi']]))
        self.FT = np.zeros((self.D, len(self.P)))
        for li in range(len(self.labels)):
            self.FT[self.off[li]:self.off[li + 1], :] = self.pi[li].reshape(len(self.P), -1).T
        if not cut:
            self.IF = np.zeros((len(self.P), self.D))
            for a, p in enumerate(self.P):
                pinv = self.P.index(inverse(p))
                for li, dl in enumerate(self.dims):
                    A = self.pi[li][pinv]
                    self.IF[a, self.off[li]:self.off[li + 1]] = (dl / len(self.P)) * A.T.ravel()

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


def kron_all(mats):
    out = np.ones((1, 1))
    for m_ in mats:
        out = np.kron(out, m_)
    return out


def canonical_basis(P, tol=1e-8):
    """Deterministic orthonormal basis of range(P) (P an orthogonal projector): Gram-Schmidt on the
    columns of P in natural order, skipping columns already in the span."""
    cols = []
    for j in range(P.shape[1]):
        v = P[:, j].copy()
        for _ in range(2):
            for u in cols:
                v -= (u @ v) * u
        nv = np.linalg.norm(v)
        if nv > tol:
            cols.append(v / nv)
    if not cols:
        return np.zeros((P.shape[0], 0))
    return np.array(cols).T


def orth_range(R, tol=1e-9):
    w, Q = np.linalg.eigh((R + R.T) / 2)
    V = Q[:, w > 0.5]
    return canonical_basis(V @ V.T)


def sorted_tuples(nlab, k):
    return list(itertools.combinations_with_replacement(range(nlab), k))


class Relaxation:
    def __init__(self, k, d, gram=True, verbose=True, families_cuts=None):
        self.k, self.d = k, d
        self.L = float((2 * d ** k) ** 4)
        self.verbose = verbose
        self.gram = gram
        self.cuts = families_cuts or FAMILY_CUTS
        t0 = time.time()
        self.loc = {}
        allcuts = set(c for f in FAMILIES for c in self.cuts[f]) | {(3,)}
        for c in allcuts:
            self.loc['s', c] = LocalNum(d, 4, c)
            self.loc['a', c] = LocalNum(2, 4, c)
        self.loc3 = {'s': LocalNum(d, 3, ()), 'a': LocalNum(2, 3, ())}
        self._log('local data %.1fs' % (time.time() - t0))
        self.sites = list(range(k))
        self.siteperms = perms(k)
        self.build_variables()

    def _log(self, s):
        if self.verbose:
            print(s, flush=True)

    # ---------- source variables ----------
    def build_variables(self):
        k = self.k
        ls, la = self.loc['s', ()], self.loc['a', ()]
        self.vars = {}
        self.nvar = {}
        for f in FAMILIES:
            blocks = []
            G = FAMILY_GROUP[f]
            for st in sorted_tuples(len(ls.labels), k):
                for ai in range(len(la.labels)):
                    dims = [ls.dims[i] for i in st] + [la.dims[ai]]
                    R = sum(kron_all([ls.pi[i][I4[g]] for i in st] + [la.pi[ai][I4[g]]]) for g in G) / len(G)
                    U = orth_range(R)
                    m = U.shape[1]
                    if m == 0:
                        continue
                    stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(k))]
                    Bs = [U.T @ self.factor_perm(dims, s) @ U for s in stab]
                    basis = invariant_sym_basis(Bs, m)
                    if not basis:
                        continue
                    cosets = self.coset_reps(st)
                    blocks.append(dict(st=st, ai=ai, dims=dims, U=U, m=m, basis=basis, cosets=cosets,
                                       stab=len(stab)))
            off = 0
            for b in blocks:
                b['off'] = off
                off += len(b['basis'])
            self.vars[f] = blocks
            self.nvar[f] = off
            self._log('family %s: %d rep blocks, %d variables' % (f, len(blocks), off))
        self.N = sum(self.nvar.values())
        self.foff = {'31': 0, '22': self.nvar['31'], '13': self.nvar['31'] + self.nvar['22']}

    def factor_perm(self, dims, s):
        """Permutation matrix of site factor permutation s (site i -> site s[i]) on the tensor space
        with factor dimensions dims (k sites then aux); requires dims[s[i]] == dims[i]."""
        k = self.k
        n = int(np.prod(dims))
        idx = np.arange(n).reshape(dims)
        # (W v)[..a at position s(i)..] = v[..a at position i..]
        perm_axes = list(range(k + 1))
        for i in range(k):
            perm_axes[s[i]] = i
        tgt = np.transpose(idx, perm_axes).ravel()
        Pm = np.zeros((n, n))
        Pm[np.arange(n), tgt] = 1.0
        # Pm @ v : (Pm v)[J] = v[tgt[J]]
        return Pm

    def coset_reps(self, st):
        """Site permutations giving the distinct labelings of the orbit of st, with permuted tuple."""
        seen = {}
        for s in self.siteperms:
            new = [None] * self.k
            for i in range(self.k):
                new[s[i]] = st[i]
            new = tuple(new)
            if new not in seen:
                seen[new] = s
        return list(seen.items())

    def block_tensors(self, b):
        """Input tensors for all variables of rep block b: list over cosets of (labeltuple, T) with
        T of shape (K, d0^2, ..., d_{k-1}^2, da^2) in the local Fourier layout."""
        k = self.k
        U = b['U']
        dims = b['dims']
        S = np.array([U @ B @ U.T for B in b['basis']])  # (K, n, n)
        K = S.shape[0]
        T = S.reshape([K] + dims + dims)
        order = [0]
        for i in range(k + 1):
            order += [1 + i, 1 + k + 1 + i]
        T = T.transpose(order).reshape([K] + [x * x for x in dims])
        out = []
        for new, s in b['cosets']:
            axes = [0] + [None] * (k + 1)
            for i in range(k):
                axes[1 + s[i]] = 1 + i
            axes[k + 1] = k + 1
            out.append((new, np.ascontiguousarray(T.transpose(axes))))
        return out

    def apply_maps(self, f, smap, amap, out_rows_s=None, out_rows_a=None, callback=None):
        """For every variable of family f, apply site map smap (Ds_out x Ds_in) on each site factor
        and aux map amap (Da_out x Da_in); smap/amap act on the cut-() Fourier coordinates.
        callback(block, var_offset, tensor) receives tensors (K, Ds_out,..., Da_out)."""
        ls, la = self.loc['s', ()], self.loc['a', ()]
        for b in self.vars[f]:
            acc = None
            for new, T in self.block_tensors(b):
                X = T
                for i in range(self.k):
                    M = smap[:, ls.rows(new[i])]
                    X = np.moveaxis(np.tensordot(M, X, axes=(1, 1 + i)), 0, 1 + i)
                M = amap[:, la.rows(b['ai'])]
                X = np.moveaxis(np.tensordot(M, X, axes=(1, 1 + self.k)), 0, 1 + self.k)
                acc = X if acc is None else acc + X
            callback(b, b['off'], acc)

    # ---------- linear functionals ----------
    def functional(self, f, zs, za):
        """Row vector over family-f variables of sum_w x[w] prod zs[w_i] za[w_a]."""
        ls, la = self.loc['s', ()], self.loc['a', ()]
        out = np.zeros(self.nvar[f])
        smap = (zs @ ls.IF)[None, :]
        amap = (za @ la.IF)[None, :]

        def cb(b, off, X):
            out[off:off + X.shape[0]] = X.reshape(X.shape[0])
        self.apply_maps(f, smap, amap, callback=cb)
        return out

    def objective(self):
        d = self.d
        zs = np.array([d ** ncycles(p) - 0.5 * d ** ncycles(compose(SWAP03, p)) for p in P4])
        za = np.array([2.0 ** ncycles(compose(SWAP03, p)) for p in P4])
        c = np.zeros(self.N)
        c[self.foff['31']:self.foff['31'] + self.nvar['31']] = self.functional('31', zs, za) / self.L
        return c

    def trace_row(self, f):
        d = self.d
        zs = np.array([float(d ** ncycles(p)) for p in P4])
        za = np.array([2.0 ** ncycles(p) for p in P4])
        r = np.zeros(self.N)
        r[self.foff[f]:self.foff[f] + self.nvar[f]] = self.functional(f, zs, za) / self.L
        return r

    # ---------- equalities ----------
    def delete_matrix(self, n, slot, order=None):
        """C[S4] -> C[S3]: V_p -> n^{[p(slot)=slot]} V_{p'} (partial trace of replica slot),
        survivors relabelled by order (new position i <-> old slot order[i])."""
        if order is None:
            order = tuple(i for i in range(4) if i != slot)
        M = np.zeros((6, 24))
        for a, p in enumerate(P4):
            out = tuple(order.index(p[slot] if p[i] == slot else p[i]) for i in order)
            M[I3[out], a] += n if p[slot] == slot else 1
        return M

    def embed_matrix(self, slot):
        """C[S3] -> C[S4]: insert slot as a fixed point (survivors in natural order)."""
        order = tuple(i for i in range(4) if i != slot)
        M = np.zeros((24, 6))
        for a, q in enumerate(P3):
            p = [None] * 4
            p[slot] = slot
            for i_new, i_old in enumerate(order):
                p[i_old] = order[q[i_new]]
            M[I4[tuple(p)], a] = 1
        return M

    def equality_rows(self):
        """All equality functionals (rows) as a dense matrix over all variables."""
        ls, la = self.loc['s', ()], self.loc['a', ()]
        s3, a3 = self.loc3['s'], self.loc3['a']
        la4 = la
        rows = []
        # Stiefel contrasts
        for f, slot in (('31', 0), ('22', 0), ('13', 3)):
            smap = s3.FT @ self.delete_matrix(self.d, slot) @ ls.IF
            amap = la4.FT @ (np.eye(24) - 0.5 * self.embed_matrix(slot) @ self.delete_matrix(2, slot)) @ la.IF
            rows.append(self._eq_block(f, smap, amap))
        # marginals
        for (f1, s1, o1), (f2, s2, o2) in [((('31', 2, (0, 1, 3))), ('22', 2, (0, 1, 3))),
                                           ((('22', 1, (0, 2, 3))), ('13', 1, (3, 0, 2)))]:
            A = self._eq_block(f1, s3.FT @ self.delete_matrix(self.d, s1, o1) @ ls.IF,
                               a3.FT @ self.delete_matrix(2, s1, o1) @ la.IF)
            B = self._eq_block(f2, s3.FT @ self.delete_matrix(self.d, s2, o2) @ ls.IF,
                               a3.FT @ self.delete_matrix(2, s2, o2) @ la.IF)
            rows.append(A - B)
        return np.vstack(rows)

    def _eq_block(self, f, smap, amap):
        nout = smap.shape[0] ** self.k * amap.shape[0]
        out = np.zeros((nout, self.N))
        base = self.foff[f]

        def cb(b, off, X):
            K = X.shape[0]
            out[:, base + off:base + off + K] = X.reshape(K, -1).T
        self.apply_maps(f, smap, amap, callback=cb)
        return out

    # ---------- PSD blocks ----------
    def output_blocks(self, cut, H):
        """Output irrep-tuple reps for a cut with symmetriser group H; returns list of dicts."""
        ls, la = self.loc['s', cut], self.loc['a', cut]
        out = []
        for st in sorted_tuples(len(ls.labels), self.k):
            for ai in range(len(la.labels)):
                dims = [ls.dims[i] for i in st] + [la.dims[ai]]
                if H:
                    R = sum(kron_all([ls.pi[i][I4[g]] for i in st] + [la.pi[ai][I4[g]]]) for g in H) / len(H)
                    U = orth_range(R)
                else:
                    U = np.eye(int(np.prod(dims)))
                if U.shape[1] == 0:
                    continue
                stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(self.k))]
                if len(stab) > 1:
                    As = [U.T @ self.factor_perm(dims, s) @ U for s in stab]
                    Qs = split_by_group(As)
                else:
                    Qs = [np.eye(U.shape[1])]
                out.append(dict(st=st, ai=ai, dims=dims, U=U, m=U.shape[1], Qs=Qs))
        return out

    def extract(self, X, ob, cut):
        """From full output tensor X (K, Ds,...,Ds, Da) extract the block of output rep ob,
        compressed: returns (K, m, m)."""
        ls, la = self.loc['s', cut], self.loc['a', cut]
        k = self.k
        sl = [slice(None)] + [ls.rows(i) for i in ob['st']] + [la.rows(ob['ai'])]
        Y = X[tuple(sl)]
        K = Y.shape[0]
        dims = ob['dims']
        shp = [K]
        for x in dims:
            shp += [x, x]
        Y = Y.reshape(shp)
        order = [0] + [1 + 2 * i for i in range(k + 1)] + [2 + 2 * i for i in range(k + 1)]
        n = int(np.prod(dims))
        Y = Y.transpose(order).reshape(K, n, n)
        U = ob['U']
        return np.einsum('ia,kij,jb->kab', U, Y, U, optimize=True)

    def stab_group(self, f, cut):
        return [g for g in FAMILY_GROUP[f] if set(g[i] for i in cut) == set(cut)]

    def family_blocks(self, f, cut):
        """List of (m, F) with F of shape (nvar_f, m, m) for the PSD blocks of X_f^{Gamma_cut}."""
        H = self.stab_group(f, cut)
        # check H acts purely inside cut or outside cut
        for g in H:
            g_in = tuple(g[i] if i in cut else i for i in range(4))
            if g_in not in H:
                raise NotImplementedError('stabiliser not a product group: %s for cut %s' % (g, cut))
        obs = self.output_blocks(cut, H)
        smap = self.loc['s', cut].FT @ self.loc['s', ()].IF
        amap = self.loc['a', cut].FT @ self.loc['a', ()].IF
        Fs = [np.zeros((self.nvar[f], ob['m'], ob['m'])) for ob in obs]

        def cb(b, off, X):
            for j, ob in enumerate(obs):
                Fs[j][off:off + X.shape[0]] = self.extract(X, ob, cut)
        self.apply_maps(f, smap, amap, callback=cb)
        return obs, Fs

    def gram_blocks(self):
        cut = (3,)
        H = [(0, 1, 2, 3), (1, 0, 2, 3)]
        obs = self.output_blocks(cut, H)
        ls0, la0 = self.loc['s', ()], self.loc['a', ()]
        ls, la = self.loc['s', cut], self.loc['a', cut]
        PA = np.zeros((24, 24))
        PB = np.zeros((24, 24))
        for a, p in enumerate(P4):
            PA[I4[compose(compose(TAU, p), TAU)], a] = 1
            PB[I4[compose(p, P0)], a] = 1
        res = {}
        for f, Pm in (('31', PA), ('22', PB), ('13', PA)):
            smap = ls.FT @ Pm @ ls0.IF
            amap = la.FT @ Pm @ la0.IF
            Fs = [np.zeros((self.nvar[f], ob['m'], ob['m'])) for ob in obs]

            def cb(b, off, X, Fs=Fs):
                for j, ob in enumerate(obs):
                    Fs[j][off:off + X.shape[0]] = self.extract(X, ob, cut)
            self.apply_maps(f, smap, amap, callback=cb)
            res[f] = Fs
        return obs, res


def invariant_sym_basis(Bs, m, tol=1e-9):
    """Orthonormal (Frobenius) basis of symmetric m x m matrices S with B S B^T = S for all B."""
    E = []
    for i in range(m):
        for j in range(i, m):
            M = np.zeros((m, m))
            if i == j:
                M[i, i] = 1.0
            else:
                M[i, j] = M[j, i] = 1 / math.sqrt(2)
            E.append(M)
    if len(Bs) <= 1:
        return E
    A = np.zeros((len(E), len(E)))
    avg = [sum(B @ M @ B.T for B in Bs) / len(Bs) for M in E]
    for a in range(len(E)):
        for b in range(len(E)):
            A[a, b] = np.sum(E[a] * avg[b])
    w, Q = np.linalg.eigh((A + A.T) / 2)
    V = Q[:, w > 0.5]
    Qc = canonical_basis(V @ V.T)
    return [sum(Qc[a, c] * E[a] for a in range(len(E))) for c in range(Qc.shape[1])]


def split_by_group(As, seed=12345):
    """Symmetry-adapted sub-block bases for matrices commuting with the orthogonal representation
    As of a finite group: one basis (m x mult) per irreducible type (first-row components)."""
    m = As[0].shape[0]
    rng = np.random.default_rng(seed)
    c = rng.normal(size=len(As))
    Y = sum(ci * (A + A.T) for ci, A in zip(c, As))
    w, V = np.linalg.eigh(Y)
    scale = max(1.0, np.abs(w).max())
    clusters = []
    start = 0
    for i in range(1, m + 1):
        if i == m or w[i] - w[i - 1] > 1e-6 * scale:
            Vc = V[:, start:i]
            clusters.append(canonical_basis(Vc @ Vc.T))
            start = i
    reps = []
    for Q in clusters:
        if not any(max(np.abs(R.T @ A @ Q).max() for A in As) > 1e-7 for R in reps):
            reps.append(Q)
    return reps
