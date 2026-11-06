"""Rationalisation of the all-theta dual in exact coordinates (paper-A style: round, solve the equalities exactly, exact LDL).
Certificate: c_tot = E_tot^T lam + sum_b Fdbl_b^*(Z_b), Z_b = N_b Y_b N_b^T, Y_b > 0, all exact rationals, where
c_tot = (c_a, c_b, 2 c_ab) and Fdbl_b^*(Z) = (F^*(Z11), F^*(Z22), F^*(Z12 + Z12^T)).  Then for every theta
c_theta = E^T lam_theta + sum_b F_b^*(m^T Z_b m) with m = (cos, sin) (x) I, so c_theta . y >= 0 on the relaxation.
Steps: (1) per block, kernel of the numerical dual (natural whitened scale) -> exact coordinates -> rational reconstruction ->
N_b = exact basis of the orthogonal complement; (2) Y_b by least squares, rounded to 2^-s; (3) exact residual; (4) exact
correction on a pivoted subset of columns (all equality multipliers plus selected Y entries); (5) exact PD test (LDL).
Usage: python xrat.py XPICKLE XSOL_PICKLE OUT.pkl [thr]"""
import sys, os, math, pickle, time
from fractions import Fraction
import numpy as np
import scipy.linalg as sla
import flint
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xval import isqrt_psd
from xdata import F as Fr

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)


def ratrec(x, dmax):
    q = Fraction(float(x)).limit_denominator(dmax)
    return q, abs(float(q) - float(x))


def int_nullspace(Q):
    """Q: list of rows of Fractions (r x n) -> integer basis (n x (n - rank)) of {v : Q v = 0} from the rref (one vector per
    free column, scaled to coprime integers)."""
    r, n = len(Q), len(Q[0])
    M = flint.fmpq_mat(r, n, [flint.fmpq(v.numerator, v.denominator) for row in Q for v in row])
    R, rank = M.rref()
    piv = []
    for i in range(rank):
        for c in range(n):
            if R[i, c] != 0:
                piv.append(c); break
    free = [c for c in range(n) if c not in piv]
    out = np.zeros((n, len(free)), dtype=object)
    for t, f in enumerate(free):
        v = [Fraction(0)] * n
        v[f] = Fraction(1)
        for i, p in enumerate(piv):
            v[p] = -Fr(R[i, f])
        den = 1
        for x in v:
            den = den * x.denominator // math.gcd(den, x.denominator)
        ints = [int(x * den) for x in v]
        g = 0
        for x in ints:
            g = math.gcd(g, x)
        out[:, t] = [x // g for x in ints]
    return out


def ldl_pd(Y):
    """Exact test of positive definiteness of a symmetric Fraction matrix (LDL without pivoting); returns min pivot or None."""
    n = Y.shape[0]
    A = [[Fraction(Y[i, j]) for j in range(n)] for i in range(n)]
    piv_min = None
    for i in range(n):
        p = A[i][i]
        if p <= 0:
            return None, i
        piv_min = p if piv_min is None or p < piv_min else piv_min
        for r in range(i + 1, n):
            f = A[r][i] / p
            if f:
                Ar, Ai = A[r], A[i]
                for c in range(i + 1, n):
                    Ar[c] -= f * Ai[c]
    return piv_min, n


def fstar_int(Fb, A_int):
    """F^*(A) = (<F_i, A>)_i for integer object tensor Fb (N, m, m) and integer object matrix A (m, m)."""
    return np.tensordot(Fb, A_int, axes=([1, 2], [0, 1]))


if __name__ == '__main__':
    xpk, solpk, out = sys.argv[1], sys.argv[2], sys.argv[3]
    thr = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-8
    DMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 200
    Dex = pickle.load(open(xpk, 'rb')); sol = pickle.load(open(solpk, 'rb'))
    k, N = Dex['k'], Dex['N']
    blocks = Dex['blocks']
    # ---------- (1) kernels -> exact N_b.  Coordinates: whitened block B_w = T^T B_ex T (T = met^(-1/2)).  The face kernel maps
    # as K_ex = T K_w; ranges of zero points (dual kernel inside the face) map as P_ex = T^(-T) P_w.  The numerical dual is first
    # replaced by its compression to K_ex^perp (Euclidean, exact coordinates): same pairing with every B_ex(y), y in null(E).
    stats = dict(maxerr=0.0, maxden=1)
    def rat_subspace(Kf, dmax, tol):
        """float basis (n x r) -> rational basis (list of r columns, RREF form at pivoted rows)."""
        if Kf.shape[1] == 0:
            return []
        _, _, piv = sla.qr(Kf.T, pivoting=True)
        piv = piv[:Kf.shape[1]]
        Kr = Kf @ np.linalg.inv(Kf[piv])
        Q = []
        for c in range(Kr.shape[1]):
            col = []
            for i in range(Kf.shape[0]):
                q, e = ratrec(Kr[i, c], dmax)
                col.append(q); stats['maxerr'] = max(stats['maxerr'], e); stats['maxden'] = max(stats['maxden'], q.denominator)
            Q.append(col)
        return Q
    def blkdiag2(A):
        n, r = A.shape
        out = np.zeros((2 * n, 2 * r)); out[:n, :r] = A; out[n:, r:] = A
        return out
    gz = 0.0
    Zn = {}
    for j, Z in sol['Zx'].items():
        b = blocks[j]
        T2 = blkdiag2(isqrt_psd(b['met']))
        sc = float(Dex['den_phi']) ** k if b['cut'] == (3,) else 1.0
        Ti = np.linalg.inv(T2)
        Zn[j] = sc * Ti @ Z @ Ti.T
        gz = max(gz, np.linalg.eigvalsh(Zn[j]).max())
    Nb, Yf, gaps, inactive, nface, nker = {}, {}, [], 0, 0, 0
    for j, Zw in Zn.items():
        b = blocks[j]
        m = b['m']
        T = isqrt_psd(b['met'])
        Vk = sol['Vks'][j]
        u_, s_, vt_ = np.linalg.svd(Vk.T, full_matrices=True)
        Kw = vt_[Vk.shape[1]:].T                                        # whitened face kernel (single copy)
        w, V = np.linalg.eigh(Zw)
        kmask = w < thr * gz
        if (~kmask).sum() == 0:
            inactive += 1
            continue
        gaps.append((w[kmask].max() / gz if kmask.any() else 0.0, w[~kmask].min() / gz))
        K2w = blkdiag2(Kw)
        Sw = V[:, kmask]
        Pw = Sw - K2w @ (K2w.T @ Sw)
        if Pw.shape[1]:
            uu, ss, _ = np.linalg.svd(Pw, full_matrices=False)
            Pw = uu[:, ss > 0.5]
        Kq = rat_subspace(T @ Kw, 10 ** 5, 1e-9)                         # face kernel, exact coordinates
        Kall = [col + [Fraction(0)] * m for col in Kq] + [[Fraction(0)] * m + col for col in Kq]
        Kall += rat_subspace(np.linalg.inv(blkdiag2(T)).T @ Pw, DMAX, 1e-6)
        nface += 2 * len(Kq); nker += len(Kall)
        n2 = 2 * m
        Nmat = int_nullspace(Kall) if Kall else np.eye(n2, dtype=np.int64).astype(object)
        # compress the numerical dual to K_ex^perp (Euclidean), then least squares in the basis N
        Zx = sol['Zx'][j]
        if Kq:
            Kf = np.array([[float(v) for v in col] for col in Kall[:2 * len(Kq)]]).T
            Qk, _ = np.linalg.qr(Kf)
            Pi = np.eye(n2) - Qk @ Qk.T
            Zx = Pi @ Zx @ Pi
        Nf = Nmat.astype(float)
        Np = np.linalg.pinv(Nf)
        Yf[j] = Np @ Zx @ Np.T
        Yf[j] = (Yf[j] + Yf[j].T) / 2
        Nb[j] = Nmat
    log('kernels: active blocks %d, inactive %d, face dims %d, total kernel dims %d, worst kernel eig/gz %.1e, min kept eig/gz '
        '%.1e, rational reconstruction max error %.1e, max denominator %d' % (len(Nb), inactive, nface, nker,
        max(g[0] for g in gaps), min(g[1] for g in gaps), stats['maxerr'], stats['maxden']))
    # ---------- (2) rounding
    Yq = {}
    for j, Y in Yf.items():
        s = int(math.ceil(-math.log2(1e-15 * np.abs(Y).max())))
        Yi = np.rint(Y * 2.0 ** s).astype(np.int64)
        Yi = (Yi + Yi.T) // 2
        Yq[j] = (Yi.astype(object), 2 ** s)
    # ---------- (3) exact residual
    c_tot = [np.array(Dex['ca'], dtype=object), np.array(Dex['cb'], dtype=object), 2 * np.array(Dex['cab'], dtype=object)]
    Fobj = {j: blocks[j]['F'] for j in Nb}
    def fdbl_star(j, Zint, den):
        m = blocks[j]['m']
        Z11, Z22, Z12 = Zint[:m, :m], Zint[m:, m:], Zint[:m, m:]
        Fb = Fobj[j]
        return [fstar_int(Fb, Z11), fstar_int(Fb, Z22), fstar_int(Fb, Z12 + Z12.T)], den
    res = [c.copy() for c in c_tot]
    for j, (Yi, den) in Yq.items():
        Nm = Nb[j]
        Zint = Nm.dot(Yi).dot(Nm.T)
        parts, den = fdbl_star(j, Zint, den)
        for i in range(3):
            res[i] = res[i] - np.array([Fraction(int(v), den) for v in parts[i]], dtype=object)
    rvec = np.concatenate(res)
    log('exact residual after rounding: max |r| %.2e' % max(abs(float(v)) for v in rvec))
    # ---------- (4) exact correction: columns = equality multipliers (independent rows of E, 3 copies) + Y entries
    E = Dex['E']
    Eq = flint.fmpz_mat(E.shape[0], N, [int(v) for v in E.ravel()])
    R, rk = flint.fmpq_mat(Eq).transpose().rref()
    from xdata import pivots_of_rref
    erows = pivots_of_rref(R, rk)
    Er = E[erows]                                                      # independent equality rows (rk x N)
    cols_f, col_info = [], []
    for i in range(3):
        for e in range(rk):
            v = np.zeros(3 * N); v[i * N:(i + 1) * N] = Er[e].astype(float)
            cols_f.append(v / np.abs(v).max()); col_info.append(('lam', i, e))
    nlam = len(cols_f)
    for j, Nm in Nb.items():
        r_ = Nm.shape[1]
        Nf = Nm.astype(float)
        Ff = Fobj[j].astype(float)
        m = blocks[j]['m']
        for a in range(r_):
            for bb in range(a, r_):
                A = np.outer(Nf[:, a], Nf[:, bb]); A = A + A.T if a != bb else A
                v = np.concatenate([np.tensordot(Ff, A[:m, :m], axes=([1, 2], [0, 1])), np.tensordot(Ff, A[m:, m:], axes=([1, 2], [0, 1])),
                                    np.tensordot(Ff, A[:m, m:] + A[:m, m:].T, axes=([1, 2], [0, 1]))])
                nv = np.abs(v).max()
                cols_f.append(v / nv if nv > 0 else v); col_info.append(('Y', j, a, bb))
    Af = np.array(cols_f).T
    Lam = Af[:, :nlam]
    Ql, _ = np.linalg.qr(Lam)
    AY = Af[:, nlam:] - Ql @ (Ql.T @ Af[:, nlam:])
    sv = np.linalg.svd(Af, compute_uv=False)
    rank_all = int((sv > 1e-10 * sv.max()).sum())
    nY = rank_all - nlam
    _, _, pivY = sla.qr(AY, pivoting=True, mode='economic')
    selY = list(pivY[:nY])
    log('columns: %d multipliers + %d Y entries, rank %d (of %d equations); selecting %d Y columns' % (
        nlam, AY.shape[1], rank_all, 3 * N, nY))
    # exact columns of the selected Y entries
    sel = list(range(nlam)) + [nlam + c for c in selY]
    Acols = []
    for ci in sel:
        info = col_info[ci]
        if info[0] == 'lam':
            _, i, e = info
            v = np.zeros(3 * N, dtype=object); v[:] = 0
            v[i * N:(i + 1) * N] = Er[e]
        else:
            _, j, a, bb = info
            Nm = Nb[j]
            A = np.outer(Nm[:, a], Nm[:, bb]).astype(object)
            A = A + A.T if a != bb else A
            m = blocks[j]['m']
            parts, _ = fdbl_star(j, A, 1)
            v = np.concatenate(parts)
        Acols.append([Fraction(int(x)) if not isinstance(x, Fraction) else x for x in v])
    nr, nc = 3 * N, len(sel)
    den_r = 1
    for x in rvec:
        den_r = den_r * Fraction(x).denominator // math.gcd(den_r, Fraction(x).denominator)
    Aq = flint.fmpq_mat(nr, nc, [flint.fmpq(Acols[c][i].numerator, Acols[c][i].denominator) for i in range(nr) for c in range(nc)])
    rq = flint.fmpq_mat(nr, 1, [flint.fmpq(Fraction(x).numerator, Fraction(x).denominator) for x in rvec])
    Rr, rkA = Aq.transpose().rref()
    rows = pivots_of_rref(Rr, rkA)
    log('exact system: %d x %d, rank %d' % (nr, nc, rkA))
    Asq = flint.fmpq_mat(rkA, nc, [Aq[i, c] for i in rows for c in range(nc)])
    rsq = flint.fmpq_mat(rkA, 1, [rq[i, 0] for i in rows])
    u = Asq.solve(rsq)
    resid_ok = (Aq * u == rq)
    log('exact solve done; all %d equations satisfied exactly: %s' % (nr, resid_ok))
    # ---------- (5) assemble and test PD exactly
    Yfin = {j: np.array([[Fraction(int(v), den) for v in row] for row in Yi], dtype=object) for j, (Yi, den) in Yq.items()}
    lam = [[Fraction(0)] * rk for _ in range(3)]
    maxdy = 0.0
    for idx, ci in enumerate(sel):
        val = Fr(u[idx, 0])
        info = col_info[ci]
        if info[0] == 'lam':
            lam[info[1]][info[2]] = val
        else:
            _, j, a, bb = info
            Yfin[j][a, bb] += val
            if a != bb:
                Yfin[j][bb, a] += val
            maxdy = max(maxdy, abs(float(val)) / np.abs(Yf[j]).max())
    npd, worst, minpiv_rel = 0, None, np.inf
    for j, Y in Yfin.items():
        pmin, at = ldl_pd(Y)
        if pmin is None:
            worst = (j, at)
        else:
            npd += 1
            minpiv_rel = min(minpiv_rel, float(pmin) / np.abs(Yf[j]).max())
    log('max |dY|/max|Y| %.2e; exact LDL: %d of %d blocks positive definite, min pivot (rel) %.2e%s' % (
        maxdy, npd, len(Yfin), minpiv_rel, '' if worst is None else ', first failure block %d at pivot %d' % worst))
    ok = resid_ok and npd == len(Yfin)
    pickle.dump(dict(ok=ok, N=Nb, Y=Yfin, lam=lam, erows=erows, k=k, sup=Dex['sup']), open(out, 'wb'), protocol=4)
    log('CERTIFICATE %s' % ('VALID (exact identity + exact PD)' if ok else 'NOT valid'))
