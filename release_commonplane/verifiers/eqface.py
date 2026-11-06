"""Equality-implied facial reduction: for each PSD block S_b(y) (linear in y), the vectors v with S_b(z) v = 0 for every z in
null(E) (E = Stiefel-contrast equalities, which hold at every physical point by an algebraic identity) are common kernel
vectors of all feasible points of the relaxation; compressing to their complement is exact (no loss, no sampling).
Note: the normalisation tr.y = 1 is affine; null(E) includes the trace direction, so the kernel is computed on null(E).
Usage: from eqface import eq_face; D2, info = eq_face(D)"""
import numpy as np


def eq_face(D, tol=1e-9, verbose=True):
    N = D['N']
    E = D['E']
    if E.shape[0]:
        U, s, Vt = np.linalg.svd(E, full_matrices=True)
        r = int((s > s.max() * 1e-10).sum())
        Z = Vt[r:].T
    else:
        Z = np.eye(N)
    newb, nz, gaps = [], 0, []
    for blk in D['blocks']:
        n = blk['m']
        F = blk['F']                                   # (N, n, n)
        SZ = np.einsum('ij,ikl->jkl', Z, F)            # (dimZ, n, n): S_b on a basis of null(E)
        Mst = SZ.reshape(-1, n)                        # stacked rows
        u, sv, vt = np.linalg.svd(Mst, full_matrices=False)   # thin SVD: only sv and the right vectors are used
        sc = sv.max() if sv.size else 1.0
        rk = int((sv > tol * sc).sum())
        Vk = vt[:rk].T                                 # row space = complement of the common kernel
        if rk < n:
            nz += n - rk
            gaps.append((sv[rk] / sc if rk < len(sv) else 0.0, sv[rk - 1] / sc if rk else 0.0))
        if rk:
            nb = dict(blk); nb['F'] = np.einsum('ja,ijk,kb->iab', Vk, F, Vk, optimize=True); nb['m'] = rk
            newb.append(nb)
    D2 = dict(D); D2['blocks'] = newb
    info = dict(zero_modes=nz, blocks_before=len(D['blocks']), blocks_after=len(newb),
                worst_zero=max([g[0] for g in gaps] or [0.0]), min_kept=min([g[1] for g in gaps] or [1.0]))
    if verbose:
        print('eq-implied face: zero modes %d, blocks %d -> %d, worst zero sv %.1e, min kept sv %.1e' % (
            nz, info['blocks_before'], info['blocks_after'], info['worst_zero'], info['min_kept']), flush=True)
    return D2, info
