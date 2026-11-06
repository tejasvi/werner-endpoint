"""Exact local module data for m replicas of C^n with a partial-transpose cut.

Conventions (same as the Zenodo verifier):
  * a permutation p of range(m) is a tuple, p[i] = image of i;
  * V_p sends input tensor factor i to output factor p[i];
  * compose(p, q)[i] = p[q[i]], so V_p V_q = V_{compose(p, q)};
  * basis index of a digit tuple x is sum_i x[i] n^(m-1-i) (x[0] most significant);
  * Gamma_T swaps row and column digits at the slots in T.

The algebra A_T = span{V_p^{Gamma_T}} commutes with U on untransposed slots and conj(U) on
transposed slots.  Its irreducible modules are the highest-weight spaces of the mixed-tensor
GL(n) weights (lambda; mu): for each label we return a rational embedding J (columns = basis of
the highest-weight vectors of that weight), the metric G = J^T J and the matrices pi(p) with
V_p^{Gamma_T} J = J pi(p).  All arithmetic is exact (Fractions).
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from functools import lru_cache

import sympy as sp


def perms(m):
    return tuple(itertools.permutations(range(m)))


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def ncycles(p):
    seen, n = set(), 0
    for i in range(len(p)):
        if i not in seen:
            n += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return n


def partitions(k, maxpart=None):
    if maxpart is None:
        maxpart = k
    if k == 0:
        yield ()
        return
    for first in range(min(k, maxpart), 0, -1):
        for rest in partitions(k - first, first):
            yield (first,) + rest


def labels(m, cut, n):
    """Irreducible labels (f, lam, mu) present for m replicas, cut, local dimension n."""
    s = len(cut)
    r = m - s
    out = []
    for f in range(min(r, s) + 1):
        for lam in partitions(r - f):
            for mu in partitions(s - f):
                if len(lam) + len(mu) <= n:
                    out.append((f, lam, mu))
    return out


def label_name(lab):
    f, lam, mu = lab
    return 'f%d_%s_%s' % (f, ''.join(map(str, lam)) or 'e', ''.join(map(str, mu)) or 'e')


def highest_weight(lab, n):
    f, lam, mu = lab
    w = [0] * n
    for i, x in enumerate(lam):
        w[i] += x
    for i, x in enumerate(mu):
        w[n - 1 - i] -= x
    return tuple(w)


def digits_to_index(x, n):
    v = 0
    for t in x:
        v = v * n + t
    return v


def weight_of(x, cut, n):
    w = [0] * n
    for slot, t in enumerate(x):
        w[t] += -1 if slot in cut else 1
    return tuple(w)


def apply_perm_pt(p, cut, vec, n):
    """(V_p)^{Gamma_cut} applied to a sparse vector {digit tuple: coeff}.

    Matrix entries: for every source s, entry (row, col) = 1 where row = target(s), col = s with
    the digits at slots in cut swapped between row and col; target(s)[p[i]] = s[i].
    For a given col, the sources s that contribute are those whose col pattern equals col.
    We enumerate by the free digits: col fixes s at untransposed slots and target(s) at
    transposed slots; row takes target(s) at untransposed and s at transposed slots.
    """
    m = len(p)
    out = {}
    pinv = inverse(p)
    for col, c in vec.items():
        if not c:
            continue
        # unknown source digits s[i]; constraints: for i not in cut: s[i] = col[i];
        # for j in cut: target(s)[j] = s[pinv[j]] = col[j].
        s = [None] * m
        ok = True
        for i in range(m):
            if i not in cut:
                s[i] = col[i]
        for j in cut:
            i = pinv[j]
            if s[i] is None:
                s[i] = col[j]
            elif s[i] != col[j]:
                ok = False
                break
        if not ok:
            continue
        free = [i for i in range(m) if s[i] is None]
        nfree = len(free)
        # free digits range over all values (closed loops / contractions)
        for vals in itertools.product(range(n), repeat=nfree):
            ss = list(s)
            for i, v in zip(free, vals):
                ss[i] = v
            target = [0] * m
            for i in range(m):
                target[p[i]] = ss[i]
            # consistency at transposed slots: target[j] == col[j]
            if any(target[j] != col[j] for j in cut):
                continue
            row = tuple(ss[i] if i in cut else target[i] for i in range(m))
            out[row] = out.get(row, 0) + c
    return {k: v for k, v in out.items() if v}



def dense_perm_pt(p, cut, n):
    """Full matrix of (V_p)^{Gamma_cut} as a dict-of-entries {(row_tuple, col_tuple): 1}."""
    m = len(p)
    entries = {}
    for source in itertools.product(range(n), repeat=m):
        target = [0] * m
        for i in range(m):
            target[p[i]] = source[i]
        row, col = list(target), list(source)
        for s in cut:
            row[s], col[s] = col[s], row[s]
        key = (tuple(row), tuple(col))
        assert key not in entries
        entries[key] = 1
    return entries


@lru_cache(maxsize=None)
def module_data(m, cut, n):
    """Exact irreducible module data for (m replicas, cut, local dimension n).

    Returns dict label -> dict(J=sympy Matrix over the weight-space basis, basis=list of digit
    tuples, G=metric, pi=list of sympy matrices indexed like perms(m), dim=int).
    """
    cut = tuple(sorted(cut))
    allx = list(itertools.product(range(n), repeat=m))
    out = {}
    P = perms(m)
    for lab in labels(m, cut, n):
        hw = highest_weight(lab, n)
        W = [x for x in allx if weight_of(x, cut, n) == hw]
        Widx = {x: i for i, x in enumerate(W)}
        # raising operators E_j : W(hw) -> W(hw + e_j - e_{j+1})
        rows = []
        for j in range(n - 1):
            img = {}
            for col, x in enumerate(W):
                for slot in range(m):
                    if slot not in cut and x[slot] == j + 1:
                        y = list(x); y[slot] = j
                        img.setdefault(tuple(y), {}).setdefault(col, 0)
                        img[tuple(y)][col] += 1
                    if slot in cut and x[slot] == j:
                        y = list(x); y[slot] = j + 1
                        img.setdefault(tuple(y), {}).setdefault(col, 0)
                        img[tuple(y)][col] -= 1
            for y, d in img.items():
                row = [0] * len(W)
                for col, v in d.items():
                    row[col] += v
                if any(row):
                    rows.append(row)
        if rows:
            Rm = sp.Matrix(rows)
            ns = Rm.nullspace()
        else:
            ns = [sp.eye(len(W))[:, i] for i in range(len(W))]
        if not ns:
            raise AssertionError(('empty highest weight space', m, cut, n, lab))
        J = sp.Matrix.hstack(*ns)
        # clear denominators column-wise to integers
        cols = []
        for c in range(J.shape[1]):
            col = J[:, c]
            den = 1
            for v in col:
                den = sp.ilcm(den, sp.fraction(v)[1])
            col = col * den
            g = 0
            for v in col:
                g = sp.igcd(g, int(v))
            cols.append(col / g)
        J = sp.Matrix.hstack(*cols)
        dim = J.shape[1]
        G = J.T * J
        # pivot rows for solving J pi = M J
        rref, piv_cols = J.T.rref()
        piv = list(piv_cols)  # rows of J forming an invertible square submatrix
        Jp = J.extract(piv, list(range(dim)))
        Jp_inv = Jp.inv()
        pis = []
        for p in P:
            MJ = sp.zeros(len(W), dim)
            for c in range(dim):
                vec = {W[i]: J[i, c] for i in range(len(W)) if J[i, c] != 0}
                img = apply_perm_pt(p, cut, vec, n)
                for x, v in img.items():
                    if x not in Widx:
                        raise AssertionError('module not weight-preserving')
                    MJ[Widx[x], c] += v
            pi = Jp_inv * MJ.extract(piv, list(range(dim)))
            if J * pi != MJ:
                raise AssertionError(('not invariant', m, cut, n, lab, p))
            pis.append(pi)
        out[lab] = dict(J=J, basis=W, G=G, pi=pis, dim=dim, hw=hw)
    return out


def check_completeness(m, cut, n, data=None):
    """sum over labels of dim^2 should equal the dimension of the algebra span{V_p^Gamma}."""
    if data is None:
        data = module_data(m, tuple(sorted(cut)), n)
    tot = sum(v['dim'] ** 2 for v in data.values())
    return tot
