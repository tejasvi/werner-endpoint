"""Checks for Section 4.6 and Appendix B.4 of the accompanying paper (Theorems 4.6 and 4.7), in the notation of the paper.

Part A (sympy): the identities marked (dagger) in Steps 3-4 of the proof of Theorem 4.7, typed exactly as displayed
(a_j, b_j, w_j, abar, bbar, kappa, kappa_ij, hat-lambda_0, hat-mu_0, tau_j, tilde-tau_j), plus the eigenvalues of the
quadratic part in Step 4 and w_i e_j - w_j e_i.
Part B (numpy, k = 2..5, random positive coefficients): Step 1 identity and (B.5); the formula for A_10; the block
structure of A_00 (block without digit 1 = M, block with only digit 1 at j = 2[M^(j) + a_j W]); Lemma B.11 in its
strengthened form (exact Schur complements, 1..6 copies, nu = 0 and nu > 0); tilde-A_00 >= underline-A_00; the Step 3
display equals the quadratic form of [[uA00, A01], [A10, uA11]]; the chain raw form >= scaled form >= G >= 0; G never
increases under merging; the final matrices are PSD.
Run: python3 code/check_sec10.py   (prints OK lines and minima; asserts on failure)."""
import itertools
import numpy as np
import sympy as sp


def part_a():
    a, b, l0, m0, T, L = sp.symbols('a b lambda0 mu0 tau Lhat', real=True)
    ab, bb, ka = sp.symbols('abar bbar kappa', real=True)
    # (I) per-copy minimum over hat-lambda_j + hat-mu_j = tau_j
    w, e = a + b, a * l0 + b * m0
    f = 2 * L**2 / a + 2 * (T - L)**2 / b - 4 * l0 * L - 4 * m0 * (T - L)
    Ls = sp.solve(sp.diff(f, L), L)[0]
    assert sp.simplify(sp.diff(f, L, 2) - (4 / a + 4 / b)) == 0
    assert sp.simplify(f.subs(L, Ls) - (2 * (T - e)**2 / w - 2 * (a * l0**2 + b * m0**2))) == 0
    print('OK (I) per-copy minimum (dagger 1)')

    # (II) merge identity, G with coefficients 2(abar^2 - kappa)/(1 - abar), 2(bbar^2 - kappa)/(1 - bbar)
    ai, bi, aj, bj, ti, tj = sp.symbols('a_i b_i a_j b_j tau_i tau_j', real=True)
    wi, wj = ai + bi, aj + bj
    ei, ej = ai * l0 + bi * m0, aj * l0 + bj * m0
    kij = ai * bj + aj * bi
    def G_part(taus, es, ws, kap):
        s = sum(2 * ((tt - ee)**2 / ww - tt**2) for tt, ee, ww in zip(taus, es, ws))
        return s + 2 * (ab**2 - kap) / (1 - ab) * l0**2 + 2 * (bb**2 - kap) / (1 - bb) * m0**2
    before = G_part([ti, tj], [ei, ej], [wi, wj], ka)
    after = G_part([ti + tj], [ei + ej], [wi + wj], ka + kij)
    tti, ttj = (ti - ei) / wi, (tj - ej) / wj
    D = 2 * wi * wj / (wi + wj) * (tti - ttj)**2 + 4 * ti * tj + 2 * kij * (l0**2 / (1 - ab) + m0**2 / (1 - bb))
    assert sp.simplify(before - after - D) == 0
    # the (u+v+sum tau)^2 term is unchanged by merging since tau_i + tau_j is kept
    print('OK (II) merge identity (dagger 2)')

    # (III) quadratic part, eigenvalues, minimum over (tilde-tau_i, tilde-tau_j), and w_i e_j - w_j e_i
    x1, x2 = sp.symbols('x1 x2', real=True)
    Dx = (2 * wi * wj / (wi + wj) * (x1 - x2)**2 + 4 * (wi * x1 + ei) * (wj * x2 + ej)
          + 2 * kij * (l0**2 / (1 - ab) + m0**2 / (1 - bb)))
    H = sp.hessian(Dx, (x1, x2)) / 2
    Hq = 2 * wi * wj * sp.Matrix([[1 / (wi + wj), 1 - 1 / (wi + wj)], [1 - 1 / (wi + wj), 1 / (wi + wj)]])
    assert sp.simplify(H - Hq) == sp.zeros(2, 2)
    ev = [sp.simplify(z) for z in Hq.eigenvals().keys()]
    want = [sp.simplify(2 * wi * wj), sp.simplify(2 * wi * wj * (2 / (wi + wj) - 1))]
    assert all(any(sp.simplify(z - y) == 0 for z in ev) for y in want)
    sol = sp.solve([sp.diff(Dx, x1), sp.diff(Dx, x2)], [x1, x2], dict=True)[0]
    target = (2 * kij * (l0**2 / (1 - ab) + m0**2 / (1 - bb))
              - 2 * (ai * bj - aj * bi)**2 * (l0 - m0)**2 / (wi * wj * (2 - wi - wj)))
    assert sp.simplify(Dx.subs(sol) - target) == 0
    assert sp.expand(wi * ej - wj * ei - (ai * bj - aj * bi) * (m0 - l0)) == 0
    print('OK (III) eigenvalues 2 w_i w_j, 2 w_i w_j (2/(w_i+w_j) - 1); minimum (dagger 3); w_i e_j - w_j e_i')

    # (IV) polynomial identity
    lhs = kij * wi * wj - (ai * bj - aj * bi)**2
    rhs = ai**2 * aj * bj + ai * aj**2 * bi + 4 * ai * aj * bi * bj + ai * bi * bj**2 + aj * bi**2 * bj
    assert sp.expand(lhs - rhs) == 0
    print('OK (IV) kappa_ij w_i w_j - (a_i b_j - a_j b_i)^2 identity (dagger 4)')

    # (V) one copy with data (abar, bbar), w = abar + bbar, kappa = abar bbar
    w1, e1 = ab + bb, ab * l0 + bb * m0
    G1 = (l0 + m0 + T)**2 + 2 * ((T - e1)**2 / w1 - T**2) + 2 * (ab**2 - ab * bb) / (1 - ab) * l0**2 \
        + 2 * (bb**2 - ab * bb) / (1 - bb) * m0**2
    SOS = (2 - w1) / w1 * (T + (bb - ab) * (l0 - m0) / (2 - w1))**2 \
        + 2 * (1 - ab * bb) * ((1 - bb) * l0 + (1 - ab) * m0)**2 / ((2 - w1) * (1 - ab) * (1 - bb))
    assert sp.simplify(G1 - SOS) == 0
    print('OK (V) one-copy sum of squares (dagger 5)')


# ---------------------------------------------------------------- Part B
def strings(k):
    return list(itertools.product(range(3), repeat=k))


def K1(x, xp):
    m = np.zeros((3, 3))
    if x == xp:
        m += 2 * np.eye(3)
    m[x, xp] -= 1.0
    return m


def kron_all(ms):
    out = np.ones((1, 1))
    for m in ms:
        out = np.kron(out, m)
    return out


def vec_f(k, c, coef0, coefs):
    """f_c = coef0 |c^k> + sum_j coefs[j] |2_j c^{k-1}> as a dict string -> coefficient."""
    d = {tuple([c] * k): coef0}
    for j in range(k):
        s = [c] * k
        s[j] = 2
        d[tuple(s)] = coefs[j]
    return d


def Kop(k, fa, fb):
    """K^{(x)k}(|f_a><f_b|) for real/complex dict vectors."""
    n = 3**k
    A = np.zeros((n, n), dtype=complex)
    for x, cx in fa.items():
        for xp, cxp in fb.items():
            A += cx * np.conj(cxp) * kron_all([K1(x[l], xp[l]) for l in range(k)])
    return A


def idx(k):
    return {s: i for i, s in enumerate(strings(k))}


def qk(C, k, t):
    T = C.reshape([3] * (2 * k))
    tot = 0.0
    for J in itertools.chain.from_iterable(itertools.combinations(range(k), r) for r in range(k + 1)):
        X = T
        rem = list(range(k))
        for j in sorted(J, reverse=True):
            pos = rem.index(j)
            nr = len(rem)
            X = np.trace(X, axis1=pos, axis2=pos + nr)
            rem.pop(pos)
        tot += (-t)**len(J) * np.sum(np.abs(X)**2)
    return tot


def M_op(alpha0, alphas):
    """M on {0,2}^m indexed by bitmask patterns; returns M, W, D, levels, partial."""
    m = len(alphas)
    N = 2**m
    W = np.diag([2.0**bin(P).count('1') for P in range(N)])
    D = np.diag([sum(alphas[j]**2 for j in range(m) if not (P >> j) & 1) for P in range(N)])
    dl = np.zeros((N, N))
    for P in range(N):
        for j in range(m):
            if (P >> j) & 1:
                dl[P & ~(1 << j), P] += alphas[j]
    L = alpha0 * np.eye(N) - dl
    return L.T @ W @ L + 2 * W @ D, W, D, [bin(P).count('1') for P in range(N)], dl


def schur_onto(A, keep):
    Ai = np.linalg.inv(A)
    return np.linalg.inv(Ai[np.ix_(keep, keep)])


def part_b(rng):
    worst = {}
    def rec(name, val):
        worst[name] = min(worst.get(name, np.inf), val)

    # Lemma B.11 (strengthened), 1..6 copies
    for m in range(1, 7):
        for trial in range(40):
            a0 = rng.uniform(0.05, 1.5)
            al = rng.uniform(0, 1.5, m) * (rng.uniform(size=m) > 0.2)
            nu = 0.0 if trial % 2 == 0 else rng.uniform(0, 2)
            M, W, D, lev, dl = M_op(a0, al)
            Mn = M + nu * W
            Delta = np.array([sum(al[j]**2 * (1 if (P >> j) & 1 else 3) for j in range(m)) for P in range(2**m)])
            for lvl in range(m + 1):
                keep = [P for P in range(2**m) if lev[P] <= lvl]
                S = schur_onto(Mn, keep)
                top = [i for i, P in enumerate(keep) if lev[P] == lvl]
                Sm = S[np.ix_(top, top)]
                bound = (a0**2 + nu) * 2**lvl * np.eye(len(top)) + 2.0**(lvl - 1) * np.diag(Delta[[keep[i] for i in top]])
                rec('Lemma B.11: min eig(S_m - bound)', np.linalg.eigvalsh(Sm - bound).min() / np.abs(Sm).max())
                if lvl == m:
                    rec('Lemma B.11 top level: -|S_m - bound|', -np.abs(Sm - bound).max())

    for k in range(2, 6):
        ix = idx(k)
        n = 3**k
        for trial in range(6):
            al = rng.uniform(0.05, 1.2, k + 1)
            be = rng.uniform(0.05, 1.2, k + 1)
            if trial == 0:  # the zero family shape: equal tail coefficients
                al[1:] = 0.3; be[1:] = 0.3
            al /= np.linalg.norm(al); be /= np.linalg.norm(be)
            a, bq = al[1:]**2, be[1:]**2
            abar, bbar = a.sum(), bq.sum()
            f0 = vec_f(k, 0, al[0], al[1:])
            f1 = vec_f(k, 1, be[0], be[1:])
            A = {(p, q): Kop(k, [f0, f1][p], [f0, f1][q]) for p in (0, 1) for q in (0, 1)}
            # Step 1: identity with q_k(1/2, C) for random complex g
            g = [rng.normal(size=n) + 1j * rng.normal(size=n) for _ in range(2)]
            F = [np.zeros(n, dtype=complex) for _ in range(2)]
            for c, fd in enumerate((f0, f1)):
                for s, v in fd.items():
                    F[c][ix[s]] = v
            C = np.outer(F[0], g[0].conj()) + np.outer(F[1], g[1].conj())
            lhs = 2**k * qk(C, k, 0.5)
            rhs = sum(g[p].conj() @ A[(p, q)] @ g[q] for p in (0, 1) for q in (0, 1))
            rec('Step 1 identity: -|2^k q - form|/|form|', -abs(lhs - rhs) / max(1, abs(rhs)))
            for c in (0, 1):
                rec('(B.5): min eig(A_cc - |f_c|^2 I)', np.linalg.eigvalsh(A[(c, c)] - np.linalg.norm(F[c])**2 * np.eye(n)).min())
            big = np.block([[A[(0, 0)], A[(0, 1)]], [A[(1, 0)], A[(1, 1)]]])
            rec('Theorem 4.7: min eig of [[A00,A01],[A10,A11]] / scale', np.linalg.eigvalsh(big).min() / np.abs(big).max())
            # Step 2: formula for A_10
            eps = (-1)**k
            form = np.outer(F[1], F[0].conj()).astype(complex)
            for j in range(k):
                for cdig in range(3):
                    s0 = [0] * k; s0[j] = cdig
                    s1 = [1] * k; s1[j] = cdig
                    form[ix[tuple(s1)], ix[tuple(s0)]] -= 2 * al[j + 1] * be[j + 1]
            rec('Step 2: -|A10 - formula|', -np.abs(A[(1, 0)] - eps * form).max())
            # Step 2: block structure of A_00
            A00 = A[(0, 0)].real
            ones = lambda s: frozenset(l for l in range(k) if s[l] == 1)
            S = strings(k)
            offblock = max(abs(A00[ix[s], ix[sp_]]) for s in S for sp_ in S if ones(s) != ones(sp_))
            rec('Step 2: -max |A00| across digit-1 blocks', -offblock)
            M, W, D, lev, dl = M_op(al[0], al[1:])
            def pat_str(P, m, positions, fill):
                s = list(fill)
                for t_, l in enumerate(positions):
                    s[l] = 2 if (P >> t_) & 1 else 0
                return tuple(s)
            no1 = [ix[pat_str(P, k, list(range(k)), [0] * k)] for P in range(2**k)]
            rec('Step 2: -|block without 1 - M|', -np.abs(A00[np.ix_(no1, no1)] - M).max())
            for j in range(k):
                others = [l for l in range(k) if l != j]
                Mj, Wj, _, _, _ = M_op(al[0], al[1:][others])
                fill = [0] * k; fill[j] = 1
                blk = [ix[pat_str(P, k - 1, others, fill)] for P in range(2**(k - 1))]
                rec('Step 2: -|block only-1-at-j - 2[M^(j) + a_j W]|', -np.abs(A00[np.ix_(blk, blk)] - 2 * (Mj + a[j] * Wj)).max())
            # Step 2: tilde-A_00 >= underline-A_00 (and mirror)
            def T_coords(c):
                cb = 1 - c
                out = [ix[tuple([c] * k)]]
                for j in range(k):
                    s = [c] * k; s[j] = 2; out.append(ix[tuple(s)])
                for j in range(k):
                    s = [c] * k; s[j] = cb; out.append(ix[tuple(s)])
                return out
            T0, T1 = T_coords(0), T_coords(1)
            def underline(coef, tails):
                tb = tails.sum()
                U = np.zeros((2 * k + 1, 2 * k + 1))
                U[0, 0] = coef[0]**2 + 2 * tb
                U[0, 1:k + 1] = U[1:k + 1, 0] = -coef[0] * coef[1:]
                for j in range(k):
                    U[1 + j, 1 + j] = 2 * coef[0]**2 + 3 * tb - 2 * tails[j]
                    U[1 + k + j, 1 + k + j] = 2 * coef[0]**2 + 3 * tb - tails[j]
                return U
            uA00, uA11 = underline(al, a), underline(be, bq)
            tA00 = schur_onto(A00, T0)
            tA11 = schur_onto(A[(1, 1)].real, T1)
            rec('Step 2: min eig(tilde A00 - underline A00)', np.linalg.eigvalsh(tA00 - uA00).min())
            rec('Step 2: min eig(tilde A11 - underline A11)', np.linalg.eigvalsh(tA11 - uA11).min())
            A10T = (eps * A[(1, 0)].real)[np.ix_(T1, T0)]
            assert np.abs(A[(1, 0)]).max() > 0
            # A_10 vanishes off T0 and maps into T1
            mask = np.ones((n, n), bool); mask[np.ix_(T1, T0)] = False
            rec('Step 2: -max |A10| outside T1 x T0', -np.abs(A[(1, 0)][mask]).max())
            Mfin = np.block([[uA00, A10T.T], [A10T, uA11]])
            rec('Step 2 conclusion: min eig [[uA00, A01],[A10, uA11]] / scale', np.linalg.eigvalsh(Mfin).min() / np.abs(Mfin).max())
            # Step 3: display = quadratic form; chain raw >= scaled >= G >= 0
            for _ in range(20):
                vlam = rng.normal(size=2 * k + 1); vmu = rng.normal(size=2 * k + 1)
                l0, lj, lpj = vlam[0], vlam[1:k + 1], vlam[k + 1:]
                m0, mj, mpj = vmu[0], vmu[1:k + 1], vmu[k + 1:]
                al0, alj, be0, bej = al[0], al[1:], be[0], be[1:]
                qf = np.concatenate([vlam, vmu]) @ Mfin @ np.concatenate([vlam, vmu])
                adl = al0 * l0 + alj @ lj
                bdm = be0 * m0 + bej @ mj
                disp = ((adl + bdm)**2
                        + np.sum(2 * (al0 * lj - alj * l0)**2 + (3 * abar - 2 * a) * lj**2) - (alj @ lj)**2
                        + np.sum(2 * (be0 * mj - bej * m0)**2 + (3 * bbar - 2 * bq) * mj**2) - (bej @ mj)**2
                        - 4 * np.sum(alj * bej * lj * mj) + np.sum((2 + abar - a) * lpj**2) + np.sum((2 + bbar - bq) * mpj**2)
                        - 4 * m0 * np.sum(alj * bej * lpj) - 4 * l0 * np.sum(alj * bej * mpj))
                rec('Step 3: -|display - quadratic form|/scale', -abs(disp - qf) / max(1, abs(qf)))
                rec('Step 3: 2 al0^2 + 3 abar - a_j = 2 + abar - a_j', -np.abs(2 * al0**2 + 3 * abar - a - (2 + abar - a)).max())
                hl0, hm0, hlj, hmj = al0 * l0, be0 * m0, alj * lj, bej * mj
                tau = hlj + hmj
                kap = np.sum(a * bq)
                scaled = ((hl0 + hm0 + tau.sum())**2
                          + np.sum(2 * hlj**2 / a + 2 * hmj**2 / bq - 4 * hl0 * hlj - 4 * hm0 * hmj - 2 * tau**2)
                          + 2 * (abar - kap) / (1 - abar) * hl0**2 + 2 * (bbar - kap) / (1 - bbar) * hm0**2)
                rec('Step 3: raw form - scaled form (>= 0)', (qf - scaled) / max(1, abs(qf)))
                w = a + bq
                e = a * hl0 + bq * hm0
                G = ((hl0 + hm0 + tau.sum())**2 + 2 * np.sum((tau - e)**2 / w - tau**2)
                     + 2 * (abar**2 - kap) / (1 - abar) * hl0**2 + 2 * (bbar**2 - kap) / (1 - bbar) * hm0**2)
                rec('Step 3: scaled form - G (>= 0)', (scaled - G) / max(1, abs(scaled)))
                rec('Step 4: G >= 0 (G/scale)', G / max(1, abs(scaled)))
                # merging: G never increases
                if k >= 2:
                    i, j = 0, 1
                    a2 = np.concatenate([[a[i] + a[j]], a[2:]]); b2 = np.concatenate([[bq[i] + bq[j]], bq[2:]])
                    t2 = np.concatenate([[tau[i] + tau[j]], tau[2:]])
                    w2 = a2 + b2; e2 = a2 * hl0 + b2 * hm0; kap2 = np.sum(a2 * b2)
                    G2 = ((hl0 + hm0 + t2.sum())**2 + 2 * np.sum((t2 - e2)**2 / w2 - t2**2)
                          + 2 * (abar**2 - kap2) / (1 - abar) * hl0**2 + 2 * (bbar**2 - kap2) / (1 - bbar) * hm0**2)
                    rec('Step 4: G_before - G_after (>= 0)', (G - G2) / max(1, abs(G)))
    for kname, v in worst.items():
        print(f'{kname}: {v:.3e}')
    tol = -1e-9
    bad = {kname: v for kname, v in worst.items() if v < tol}
    assert not bad, bad
    print('OK Part B (all minima >= -1e-9)')


if __name__ == '__main__':
    part_a()
    part_b(np.random.default_rng(20261025))
