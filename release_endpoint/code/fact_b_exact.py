# fact_b_exact.py: the computer-verified step in the proof of Theorem 5.1 (paper, Lemma B.7, condition (G2); Table 2, C2).
#
# For the Gaussian-integer vector psi_0 below, on two copies with local supports U = span{e_0, e_1} (d = 3), in the
# order (first copy, second copy, Q), take one copy m as transverse and l as the other copy. With kappa = Theta psi_0 =
# (Y (x) Y (x) Y) conj(psi_0) (not normalised), psi_b = <b|_m psi_0 and kappa_b = <b|_m kappa, the second-order form on
# eta = e_2 (x) zeta, zeta in U (x) Q, is the 4 x 4 Hermitian matrix
#     S = 2 E'(tau_0) - (1/2) W^* E'(sigma_0)^{-1} W,
#     E'(X) = sum_a (sigma_a (x) I) X (sigma_a (x) I),  sigma_0 = sum_b psi_b psi_b^*,  tau_0 = sum_b kappa_b kappa_b^*,
#     W zeta = sum_b E'(zeta psi_b^*) kappa_b.
# Checked in exact arithmetic over Q(i), for m = first copy and for m = second copy:
#   (1) S psi_b = 0 for b = 0, 1 (the tilts);  (2) rank S = 2;  (3) S restricted to the orthogonal complement of the
#   tilts has positive leading principal minors.  Hence (G2) holds for psi_0 with either copy transverse.
# The script also recomputes S from the full operator E = D (x) D (x) id_Q on (C^3)^{(x)2} (x) Q, D(X) = 2 Tr(X) I - X,
# in floating point, as an independent cross-check of the formula.
import sys
import numpy as np
import sympy as sp

PSI0 = [3 - 5*sp.I, -5 - 4*sp.I, -4 - 2*sp.I, -3 - sp.I, -4 + sp.I, 3, 4 - 3*sp.I, 1 - 4*sp.I]
I2 = sp.eye(2)
SX = sp.Matrix([[0, 1], [1, 0]]); SY = sp.Matrix([[0, -sp.I], [sp.I, 0]]); SZ = sp.Matrix([[1, 0], [0, -1]])


def kron(*ms):
    out = ms[0]
    for m_ in ms[1:]:
        out = sp.kronecker_product(out, m_)
    return out


def swap_copies(v):
    """reorder (first copy a, second copy b, Q q) -> (b, a, q); index 4a + 2b + q"""
    w = [0] * 8
    for a in range(2):
        for b in range(2):
            for q in range(2):
                w[4 * b + 2 * a + q] = v[4 * a + 2 * b + q]
    return w


def exact_form(psi_list):
    psi = sp.Matrix(psi_list)
    kap = kron(SY, SY, SY) * psi.conjugate()
    comp = lambda v, b: sp.Matrix(v[4 * b: 4 * b + 4])           # <b|_m v, a vector on (copy l) (x) Q
    psib = [comp(psi, 0), comp(psi, 1)]; kapb = [comp(kap, 0), comp(kap, 1)]
    sig0 = psib[0] * psib[0].H + psib[1] * psib[1].H
    tau0 = kapb[0] * kapb[0].H + kapb[1] * kapb[1].H
    P = [kron(SX, I2), kron(SY, I2), kron(SZ, I2)]
    Ep = lambda A: sum((Pa * A * Pa for Pa in P), sp.zeros(4, 4))
    cols = []
    for i in range(4):
        z = sp.zeros(4, 1); z[i] = 1
        cols.append(sum((Ep(z * psib[b].H) * kapb[b] for b in range(2)), sp.zeros(4, 1)))
    W = sp.Matrix.hstack(*cols)
    S = sp.simplify(2 * Ep(tau0) - sp.Rational(1, 2) * W.H * Ep(sig0).inv() * W)
    return S, psib, kap


def full_form(psi_list, kap):
    """S from the full operator E on (C^3)^{(x)2} (x) Q, floating point."""
    d = 3
    def D_on(A, axis):            # A: tensor (3,3,2,3,3,2); apply D(X) = 2 Tr(X) I - X on copy 'axis' (0 or 1)
        tr = np.trace(A, axis1=axis, axis2=axis + 3)               # partial trace over that copy
        Id = np.eye(d)
        if axis == 0:
            T = np.einsum('ij,bqcr->ibqjcr', Id, tr)
        else:
            T = np.einsum('ij,aqcr->aiqcjr', Id, tr)
        return 2 * T - A
    def E(A):
        A = A.reshape(3, 3, 2, 3, 3, 2)
        return D_on(D_on(A, 0), 1).reshape(18, 18)
    def lift(v):
        t = np.zeros((3, 3, 2), complex); t[:2, :2, :] = np.array([complex(x) for x in v]).reshape(2, 2, 2)
        return t.reshape(-1)
    p0 = lift(psi_list); k0 = lift(list(kap))
    A = E(np.outer(p0, p0.conj())); ev, V = np.linalg.eigh(A)
    ker = np.abs(ev) < 1e-9 * ev[-1]
    Ap = V[:, ~ker] @ np.diag(1 / ev[~ker]) @ V[:, ~ker].conj().T
    etas = []
    for i in range(4):
        t = np.zeros((3, 3, 2), complex); z = np.zeros(4, complex); z[i] = 1; t[2, :2, :] = z.reshape(2, 2)
        etas.append(t.reshape(-1))
    Xk = [E(np.outer(e, p0.conj())) @ k0 for e in etas]
    Sn = np.zeros((4, 4), complex)
    for i in range(4):
        for j in range(4):
            Sn[i, j] = np.vdot(k0, E(np.outer(etas[j], etas[i].conj())) @ k0) - np.vdot(Xk[i], Ap @ Xk[j])
    return Sn, int(ker.sum())


ok_all = True
for label, vec in (("first copy transverse", PSI0), ("second copy transverse", swap_copies(PSI0))):
    S, psib, kap = exact_form(vec)
    tilts_ok = all(sp.simplify(S * psib[b]) == sp.zeros(4, 1) for b in range(2))
    r = S.rank(simplify=True)
    Bt = sp.Matrix.hstack(psib[0], psib[1]); Bc = sp.Matrix.hstack(*(Bt.H).nullspace())
    Sc = sp.simplify(Bc.H * S * Bc)
    m1 = sp.simplify(Sc[0, 0]); m2 = sp.simplify(Sc.det())
    pos = bool(sp.re(sp.N(m1, 30)) > 0 and sp.re(sp.N(m2, 30)) > 0 and abs(sp.im(sp.N(m1, 30))) < 1e-25 and abs(sp.im(sp.N(m2, 30))) < 1e-25)
    Sn, dimker = full_form(vec, kap)
    Sx = np.array(S.evalf(), dtype=complex)
    rel = np.abs(Sx - Sn).max() / np.abs(Sx).max()
    print(f"[{label}] psi_0 = {[str(x) for x in vec]}")
    print(f"  (1) S psi_b = 0 for b = 0, 1: {tilts_ok}")
    print(f"  (2) rank S = {r}")
    print(f"  (3) leading minors on the complement: {sp.N(m1, 10)}, {sp.N(m2, 10)}; positive: {pos}")
    print(f"  float cross-check with the full operator E: max relative deviation {rel:.2e}; dim ker E(psi_0 psi_0^*) = {dimker}")
    ok = tilts_ok and r == 2 and pos and rel < 1e-10 and dimker == 1
    print(f"  (G2) for this transverse copy: {ok}")
    ok_all = ok_all and ok
print("FACT C2 (G2 nonempty, both copies transverse): " + ("PASS" if ok_all else "FAIL"))
sys.exit(0 if ok_all else 1)
