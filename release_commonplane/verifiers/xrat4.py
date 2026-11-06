"""Rationalisation for k = 4 sizes (same certificate as xrat.py; exact products with flint).
Certificate: c_tot = E_tot^T lam + sum_b Fdbl_b^*(N_b Y_b N_b^T), Y_b = Yhat_b + dY_b positive definite, exact rationals.
PD test without huge LDLs: exact LDL of Yhat_b - tau_b I (dyadic entries) and ||dY_b||_F^2 < tau_b^2 (exact), so
Y_b = (Yhat_b - tau_b I) + (tau_b I + dY_b) > 0 by Weyl.
Usage: python xrat2.py XPICKLE XSOL_PICKLE OUT.pkl [thr DMAX]"""
import sys, os, math, pickle, time
from fractions import Fraction
import numpy as np
import scipy.linalg as sla
import flint
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xval import isqrt_psd
from xdata import F as Fr, pivots_of_rref
from xrat import ratrec, int_nullspace, ldl_pd

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)


def blkdiag2(A):
    n, r = A.shape
    out = np.zeros((2 * n, 2 * r)); out[:n, :r] = A; out[n:, r:] = A
    return out


def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()])


def kernels(Dex, sol, thr, dmax, zp=None):
    """As xrat.py step (1): exact bases N_b and least-squares Y_b (float) per active doubled block."""
    k = Dex['k']; blocks = Dex['blocks']
    stats = dict(maxerr=0.0, maxden=1)
    def rat_subspace(Kf, dm):
        if Kf.shape[1] == 0:
            return []
        _, _, piv = sla.qr(Kf.T, pivoting=True)
        piv = piv[:Kf.shape[1]]
        Kr = Kf @ np.linalg.inv(Kf[piv])
        Q = []
        for c in range(Kr.shape[1]):
            col = []
            for i in range(Kf.shape[0]):
                q, e = ratrec(Kr[i, c], dm)
                col.append(q); stats['maxerr'] = max(stats['maxerr'], e); stats['maxden'] = max(stats['maxden'], q.denominator)
            Q.append(col)
        return Q
    Zn, gz = {}, 0.0
    for j, Z in sol['Zx'].items():
        b = blocks[j]
        Ti = np.linalg.inv(blkdiag2(isqrt_psd(b['met'])))
        sc = 1.0 / b['nat'] if 'nat' in b else (float(Dex['den_phi']) ** k if b['cut'] == (3,) else 1.0)
        Zn[j] = sc * Ti @ Z @ Ti.T
        gz = max(gz, np.linalg.eigvalsh(Zn[j]).max())
    Nb, Yf, gaps, inactive, nker = {}, {}, [], 0, 0
    for j, Zw in Zn.items():
        b = blocks[j]; m = b['m']
        T = isqrt_psd(b['met'])
        Vk = sol['Vks'][j]
        _, _, vt_ = np.linalg.svd(Vk.T, full_matrices=True)
        Kw = vt_[Vk.shape[1]:].T
        w, V = np.linalg.eigh(Zw)
        kmask = w < thr * gz
        if w.max() < 1e-6 * gz:                                       # (nearly) inactive block: Z_b = 0 (as in xzero.py)
            inactive += 1
            continue
        gaps.append((w[kmask].max() / gz if kmask.any() else 0.0, w[~kmask].min() / gz))
        K2w = blkdiag2(Kw)
        Sw = V[:, kmask]
        Pw = Sw - K2w @ (K2w.T @ Sw)
        if Pw.shape[1]:
            uu, ss, _ = np.linalg.svd(Pw, full_matrices=False)
            Pw = uu[:, ss > 0.5]
        Kq = rat_subspace(T @ Kw, 10 ** 5)
        Kall = [col + [Fraction(0)] * m for col in Kq] + [[Fraction(0)] * m + col for col in Kq]
        if zp is not None:                                            # physical zero-family prediction (accurate)
            assert zp['Pw'][j].shape[1] == Pw.shape[1], 'physical prediction and dual kernel differ in block %d' % j
            Pw = zp['Pw'][j]
        Kall += rat_subspace(np.linalg.inv(blkdiag2(T)).T @ Pw, dmax)
        nker += len(Kall)
        n2 = 2 * m
        Nmat = int_nullspace(Kall) if Kall else np.eye(n2, dtype=np.int64).astype(object)
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
    log('kernels: active %d, inactive %d, kernel dims %d, worst kernel eig/gz %.1e, min kept eig/gz %.1e, reconstruction max '
        'error %.1e, max denominator %d' % (len(Nb), inactive, nker, max(g[0] for g in gaps), min(g[1] for g in gaps),
        stats['maxerr'], stats['maxden']))
    return Nb, Yf


if __name__ == '__main__':
    # xrat4: N_b and Y_b come from the dual-facially-reduced re-solve (xatd2.py)
    xpk, redpk, out = sys.argv[1], sys.argv[2], sys.argv[3]
    Dex = pickle.load(open(xpk, 'rb')); red = pickle.load(open(redpk, 'rb'))
    N = Dex['N']; blocks = Dex['blocks']
    Nb, Yf = red['N'], {j: np.array(Y, dtype=float) for j, Y in red['Yf'].items()}
    log('reduced solve %s, primal %+.3e, dual %+.3e; %d active blocks' % (red['status'], red['primal'], red['dual'], len(Nb)))
    act = sorted(Nb)
    # exact block data as flint matrices (N x m^2)
    Fz = {j: fz(blocks[j]['F'].reshape(N, -1)) for j in act}
    log('flint block matrices ready')
    def fdbl_star_exact(j, Zint):
        """(F^*(Z11), F^*(Z22), F^*(Z12 + Z12^T)) for an integer matrix Zint (2m x 2m): flint (N x m^2) * (m^2 x 3)."""
        m = blocks[j]['m']
        Z11, Z22, Z12 = Zint[:m, :m], Zint[m:, m:], Zint[:m, m:]
        M = np.stack([Z11.ravel(), Z22.ravel(), (Z12 + Z12.T).ravel()], 1)
        R = Fz[j] * fz(M)
        return [[int(R[i, c]) for i in range(N)] for c in range(3)]
    c_tot = [list(Dex['ca']), list(Dex['cb']), [2 * v for v in Dex['cab']]]
    def round_Y(Yf):
        Yq = {}
        for j in act:
            Y = Yf[j]
            s = int(math.ceil(-math.log2(1e-15 * np.abs(Y).max())))
            Yi = np.rint(Y * 2.0 ** s).astype(np.int64)
            Yi = (Yi + Yi.T) // 2
            Yq[j] = (Yi.astype(object), s)
        return Yq
    def exact_residual(Yq):
        """r = c_tot - sum_b Fdbl^*(N Yhat N^T), exactly (common denominator 2^smax)."""
        smax = max(s for _, s in Yq.values())
        acc = [[0] * N for _ in range(3)]
        for j in act:
            Yi, s = Yq[j]
            Zint = Nb[j].dot(Yi * (2 ** (smax - s))).dot(Nb[j].T)
            parts = fdbl_star_exact(j, Zint)
            for c in range(3):
                acc[c] = [a + p for a, p in zip(acc[c], parts[c])]
        D2 = 2 ** smax
        return [Fraction(c_tot[c][i]) - Fraction(acc[c][i], D2) for c in range(3) for i in range(N)]
    # ---------- candidate columns (float, normalised; scl = factor to the true column of a symmetric Y-entry change)
    E = Dex['E']
    R, rk = flint.fmpq_mat(fz(E)).transpose().rref()
    erows = pivots_of_rref(R, rk)
    Er = E[erows]
    cols_f, info, scl = [], [], []
    for c in range(3):
        for e in range(rk):
            v = np.zeros(3 * N); v[c * N:(c + 1) * N] = Er[e].astype(float)
            nv = np.abs(v).max()
            cols_f.append(v / nv); info.append(('lam', c, e)); scl.append(nv)
    nlam = len(cols_f)
    for j in act:
        m = blocks[j]['m']
        Nf = Nb[j].astype(float)
        N1, N2 = Nf[:m], Nf[m:]
        Ff = blocks[j]['F'].astype(float)
        sF = np.abs(Ff).max()
        Ff = Ff / sF
        G1 = np.einsum('ar,iab,bs->irs', N1, Ff, N1, optimize=True)
        G2 = np.einsum('ar,iab,bs->irs', N2, Ff, N2, optimize=True)
        G3 = np.einsum('ar,iab,bs->irs', N1, Ff, N2, optimize=True)
        G3 = G3 + np.transpose(G3, (0, 2, 1))
        r_ = Nf.shape[1]
        for a in range(r_):
            for bb in range(a, r_):
                v = np.concatenate([G1[:, a, bb], G2[:, a, bb], G3[:, a, bb]])
                nv = np.abs(v).max()
                if nv > 0:
                    cols_f.append(v / nv); info.append(('Y', j, a, bb)); scl.append(nv * sF * (2 if a != bb else 1))
    Af = np.array(cols_f).T
    log('candidate columns: %d multipliers + %d Y entries, %d equations' % (nlam, Af.shape[1] - nlam, 3 * N))
    Ql, _ = np.linalg.qr(Af[:, :nlam])
    # ---------- round; float correction of Y from the exact residual, minimum norm with each block's change measured in
    # units of its margin (lambda_min of Y_b), multipliers free; round again
    marg = {j: max(np.linalg.eigvalsh(Yf[j]).min(), 1e-300) for j in act}
    wcol = np.array([1.0] * nlam + [scl[idx] * marg[info[idx][1]] for idx in range(nlam, len(info))])
    wcol[:nlam] = 1e3 * wcol[nlam:].max()
    for it in range(3):
        Yq = round_Y(Yf)
        rvec = exact_residual(Yq)
        rf = np.array([float(x) for x in rvec])
        rperp = np.linalg.norm(rf - Ql @ (Ql.T @ rf))
        log('pass %d: exact residual max |r| %.2e, part outside the multiplier span %.2e, min_b lambda_min(Y_b)/margin_b %.4f' % (
            it, np.abs(rf).max(), rperp, min(np.linalg.eigvalsh(Yf[j]).min() / marg[j] for j in act)))
        if it == 2:
            break
        z = np.linalg.lstsq(Af * wcol[None, :], rf, rcond=1e-14)[0]
        for idx in range(nlam, len(info)):
            _, j, a, bb = info[idx]
            dlt = z[idx] * wcol[idx] / scl[idx]
            Yf[j][a, bb] += dlt
            if a != bb:
                Yf[j][bb, a] += dlt
    AY = Af[:, nlam:] - Ql @ (Ql.T @ Af[:, nlam:])
    sv = np.linalg.svd(Af, compute_uv=False)
    rank_all = int((sv > 1e-10 * sv.max()).sum())
    _, _, pivY = sla.qr(AY, pivoting=True, mode='economic')
    selY = [nlam + c for c in pivY[:rank_all - nlam]]
    log('rank %d -> %d Y columns selected' % (rank_all, len(selY)))
    del Af, AY
    # ---------- exact selected columns
    sel = list(range(nlam)) + selY
    ncol = len(sel)
    colvals = {}
    byblock = {}
    for idx, ci in enumerate(sel):
        if info[ci][0] == 'Y':
            byblock.setdefault(info[ci][1], []).append((idx, info[ci][2], info[ci][3]))
    for j, lst in byblock.items():
        m = blocks[j]['m']
        Nm = Nb[j]
        Ms = []
        for idx, a, bb in lst:
            S = np.zeros((Nm.shape[1], Nm.shape[1]), dtype=object)
            S[a, bb] = 1; S[bb, a] = 1
            Zint = Nm.dot(S).dot(Nm.T)
            Z11, Z22, Z12 = Zint[:m, :m], Zint[m:, m:], Zint[:m, m:]
            Ms += [Z11.ravel(), Z22.ravel(), (Z12 + Z12.T).ravel()]
        R = Fz[j] * fz(np.stack(Ms, 1))
        for t, (idx, a, bb) in enumerate(lst):
            colvals[idx] = [int(R[i, 3 * t + c]) for c in range(3) for i in range(N)]
    for idx, ci in enumerate(sel):
        if info[ci][0] == 'lam':
            _, c, e = info[ci]
            v = [0] * (3 * N)
            v[c * N:(c + 1) * N] = [int(x) for x in Er[e]]
            colvals[idx] = v
    A = flint.fmpz_mat(3 * N, ncol, [colvals[c][i] for i in range(3 * N) for c in range(ncol)])
    del colvals
    den_r = 1
    for x in rvec:
        den_r = den_r * x.denominator // math.gcd(den_r, x.denominator)
    rint = [int(x * den_r) for x in rvec]
    log('exact matrix assembled (%d x %d), rhs denominator 2^%.0f' % (3 * N, ncol, math.log2(den_r)))
    # independent rows: rank mod a prime (rows of A = pivot columns of A^T)
    p = 2 ** 61 - 1
    Amod = flint.nmod_mat(ncol, 3 * N, [int(A[i, c]) % p for c in range(ncol) for i in range(3 * N)], p)
    Rm, rkm = Amod.rref()
    rows = pivots_of_rref(Rm, rkm)
    log('rank mod p %d (columns %d)' % (rkm, ncol))
    if rkm < ncol:                                                   # drop dependent columns (pivot columns of A mod p)
        Rc, rkc = Amod.transpose().rref()
        keep = pivots_of_rref(Rc, rkc)
        sel = [sel[c] for c in keep]
        A = flint.fmpz_mat(3 * N, len(keep), [int(A[i, c]) for i in range(3 * N) for c in keep])
        ncol = len(keep)
        log('kept %d independent columns' % ncol)
    Asq = flint.fmpq_mat(flint.fmpz_mat(rkm, ncol, [int(A[i, c]) for i in rows for c in range(ncol)]))
    rsq = flint.fmpq_mat(rkm, 1, [flint.fmpq(rint[i], den_r) for i in rows])
    u = Asq.solve(rsq)
    log('exact solve done')
    # common denominator D of the solution; integer numerators (no Fraction arithmetic on huge numbers)
    D = 1
    uq = [u[i, 0] for i in range(ncol)]
    for x in uq:
        qd = int(x.q)
        D = D * qd // math.gcd(D, qd)
    unum = [int(x.p) * (D // int(x.q)) for x in uq]
    Au = A * flint.fmpz_mat(ncol, 1, unum)
    ok_eq = all(int(Au[i, 0]) * den_r == rint[i] * D for i in range(3 * N))
    log('all %d equations satisfied exactly: %s; solution denominator 2^%.0f' % (3 * N, ok_eq, math.log2(D)))
    # ---------- assemble dY = dYn / D, lam = lam_n / D; PD test (Weyl)
    dYn = {j: np.zeros((Nb[j].shape[1], Nb[j].shape[1]), dtype=object) for j in act}
    for j in act:
        dYn[j][:] = 0
    lam_n = [[0] * rk for _ in range(3)]
    for idx, ci in enumerate(sel):
        if info[ci][0] == 'lam':
            lam_n[info[ci][1]][info[ci][2]] = unum[idx]
        else:
            _, j, a, bb = info[ci]
            dYn[j][a, bb] += unum[idx]
            if a != bb:
                dYn[j][bb, a] += unum[idx]
    npd, fails, worst_ratio = 0, [], 0.0
    for j in act:
        Yi, s = Yq[j]
        Yhat = Yi.astype(float) / 2.0 ** s
        lmin = np.linalg.eigvalsh(Yhat).min()
        if lmin <= 0:
            fails.append((j, 'Yhat not PD (float %.2e)' % lmin)); continue
        tsh = int(math.floor(math.log2(lmin / 2)))
        tau = Fraction(2) ** tsh
        M = np.array([[Fraction(int(Yi[a, c]), 2 ** s) - (tau if a == c else 0) for c in range(Yi.shape[1])] for a in range(Yi.shape[0])], dtype=object)
        pmin, at = ldl_pd(M)
        if pmin is None:
            fails.append((j, 'Yhat - tau I not PD at pivot %d' % at)); continue
        nrm2 = sum(int(x) * int(x) for x in dYn[j].ravel())            # ||dY||_F^2 = nrm2 / D^2
        ok_n = (nrm2 * 4 ** (-tsh) < D * D) if tsh < 0 else (nrm2 < D * D * 4 ** tsh)
        if not ok_n:
            fails.append((j, '||dY|| >= tau')); continue
        npd += 1
        worst_ratio = max(worst_ratio, math.exp(0.5 * (math.log(nrm2 + 1) - 2 * math.log(D)) - tsh * math.log(2)))
    log('PD: %d of %d blocks certified (exact LDL of Yhat - tau I, ||dY||_F < tau); worst ||dY||/tau %.2e; failures %s' % (
        npd, len(act), worst_ratio, fails[:5]))
    ok = ok_eq and npd == len(act)
    pickle.dump(dict(ok=ok, N=Nb, Yq=Yq, dYn=dYn, lam_n=lam_n, D=D, erows=erows, k=Dex['k'], sup=Dex.get('sup'),
                     sel_info=[info[ci] for ci in sel], rows=rows), open(out, 'wb'), protocol=4)
    log('CERTIFICATE %s' % ('VALID (exact identity + exact PD)' if ok else 'NOT valid'))
