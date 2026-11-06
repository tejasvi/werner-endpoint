# sd_check.py: checks for Theorem 7.2 and its proof (paper Section 7 and Appendix B.3; Table 2, C3).
# Symbolic: c = 4 - 2 sqrt2 is a root of c^2 - 8c + 8; at delta = cm and nu_1 = 1/2 the two inequalities L >= R_i, L >= R_ii
#   reduce to the stated forms, whose slacks at m = 1/4 are (c^2 - 8c + 8)/(c(4 - c)) and half of it; for 1/4 < m < 2/(8 - c),
#   L(1/4) = R_i(1/4) = 1 + 1/sqrt2 and L' > R_i' (exactly: the threshold where L' = R_i' lies below 1/4).
# Floating point: formula (B.3) against the full operator E = D (x) D (x) id_Q; the bound m_2(V) >= (1 - 1/sqrt2) nu_3(V)
#   on random planes of the class, d = 3..6; equality at V = span{|00>, Omega}; the values of C_*.
import sys
import numpy as np
import sympy as sp

ok_all = True
def report(name, ok):
    global ok_all
    ok_all = ok_all and bool(ok)
    print(f"  {name}: {bool(ok)}")

print("symbolic")
m, dl = sp.symbols('m delta', positive=True)
c = 4 - 2*sp.sqrt(2)
report("c^2 - 8c + 8 = 0 at c = 4 - 2 sqrt2", sp.simplify(c**2 - 8*c + 8) == 0)
cs = sp.symbols('c', positive=True)
nu1 = sp.Rational(1, 2)
L = sp.Rational(1, 4) + (2 - cs*m)/(4*dl)
Ri = 1 + (1 - nu1)/(2 - (4 + cs)*m)
Rii = 1 + (1 - nu1 - m)/(dl + (4 - 2*cs)*m) + m/(2 - (4 + cs)*m)
L1, Ri1, Rii1 = [sp.simplify(e.subs(dl, cs*m)) for e in (L, Ri, Rii)]
f1 = sp.simplify((L1 - Ri1) - (1/(2*cs*m) - 1 - 1/(4 - 2*(4 + cs)*m)))              # L - R_i
f2 = sp.simplify((L1 - Rii1)*2*m - (1/cs - 2*m - (1 - 2*m)/(4 - cs) - 2*m**2/(2 - (4 + cs)*m)))
report("at delta = cm, nu_1 = 1/2: L = 1/(2cm), and L - R_i and 2m(L - R_ii) are the two stated slacks", f1 == 0 and f2 == 0 and sp.simplify(L1 - 1/(2*cs*m)) == 0)
s1 = sp.simplify((1/(2*cs*m) - 1 - 1/(4 - 2*(4 + cs)*m)).subs(m, sp.Rational(1, 4)))
s2 = sp.simplify((1/cs - 2*m - (1 - 2*m)/(4 - cs) - 2*m**2/(2 - (4 + cs)*m)).subs(m, sp.Rational(1, 4)))
report("slacks at m = 1/4 are (c^2 - 8c + 8)/(c(4 - c)) and half of it",
       sp.simplify(s1 - (cs**2 - 8*cs + 8)/(cs*(4 - cs))) == 0 and sp.simplify(s2 - s1/2) == 0)
# monotonicity in m on (0, 1/4] for the actual c (grid; exact derivative signs are elementary)
g1 = sp.lambdify(m, (1/(2*cs*m)).subs(cs, c)); h1 = sp.lambdify(m, (1 + 1/(4 - 2*(4 + cs)*m)).subs(cs, c))
h2 = sp.lambdify(m, (2*m + (1 - 2*m)/(4 - cs) + 2*m**2/(2 - (4 + cs)*m)).subs(cs, c))
grid = np.linspace(1e-3, 0.25, 2000)
report("on (0, 1/4]: 1/(2cm) decreases, 1 + 1/(4 - 2(4+c)m) and the right side of the second form increase",
       np.all(np.diff(g1(grid)) < 0) and np.all(np.diff(h1(grid)) > 0) and np.all(np.diff(h2(grid)) > 0))
Lb = (1 - 2*m)/(2 - (8 - c)*m); Rb = 1 + 2*m/(2 - (4 + c)*m)
report("L(1/4) = R_i(1/4) = 1 + 1/sqrt2",
       sp.simplify(Lb.subs(m, sp.Rational(1, 4)) - (1 + 1/sp.sqrt(2))) == 0 and sp.simplify(Rb.subs(m, sp.Rational(1, 4)) - (1 + 1/sp.sqrt(2))) == 0)
dL = sp.simplify(sp.diff(Lb, m)); dR = sp.simplify(sp.diff(Rb, m))
report("L' = (4 - c)/(2 - (8 - c)m)^2 and R_i' = 4/(2 - (4 + c)m)^2",
       sp.simplify(dL - (4 - c)/(2 - (8 - c)*m)**2) == 0 and sp.simplify(dR - 4/(2 - (4 + c)*m)**2) == 0)
# L' > R_i'  <=>  sqrt(4 - c)(2 - (4 + c)m) > 2(2 - (8 - c)m) on the interval (both bases positive there)  <=>  m > m0
m0 = sp.nsimplify((4 - 2*sp.sqrt(4 - c))/(2*(8 - c) - sp.sqrt(4 - c)*(4 + c)))
top = 2/(8 - c)
report(f"threshold m0 = {float(m0):.6f} < 1/4, and both bases are positive below 2/(8-c) = {float(top):.6f}",
       bool(sp.N(m0) < sp.Rational(1, 4)) and bool(sp.N(top) < sp.N(2/(4 + c))) and bool(sp.N(2*(8 - c) - sp.sqrt(4 - c)*(4 + c)) > 0))

print("floating point")
rng = np.random.default_rng(7)
def crandn(*s): return rng.standard_normal(s) + 1j*rng.standard_normal(s)
def E_full(Y, d):               # (D (x) D (x) id_Q)(Y), Y on C^d (x) C^d (x) C^2, D(X) = 2 Tr(X) I - X
    T = Y.reshape(d, d, 2, d, d, 2)
    def D_on(A, ax):
        tr = np.trace(A, axis1=ax, axis2=ax + 3); Id = np.eye(d)
        T2 = np.einsum('ij,bqcr->ibqjcr', Id, tr) if ax == 0 else np.einsum('ij,aqcr->aiqcjr', Id, tr)
        return 2*T2 - A
    return D_on(D_on(T, 0), 1).reshape(2*d*d, 2*d*d)
def class_plane(d):
    Ua, _ = np.linalg.qr(crandn(d, d)); Ub, _ = np.linalg.qr(crandn(d, d))
    AB, _ = np.linalg.qr(crandn(d, 2)); al, be = AB[:, 0], AB[:, 1]
    x1 = sum(al[i]*np.kron(Ua[:, i], Ub[:, i]) for i in range(d)); x2 = sum(be[i]*np.kron(Ua[:, i], Ub[:, i]) for i in range(d))
    return x1, x2, al, be
def m2_and_nu3(x1, x2, d):
    psi = (np.kron(x1, [1, 0]) + np.kron(x2, [0, 1]))/np.sqrt(2)
    lamE = np.linalg.eigvalsh(E_full(np.outer(psi, psi.conj()), d))[0]
    PV = np.outer(x1, x1.conj()) + np.outer(x2, x2.conj())
    nu = np.sort(np.linalg.eigvalsh(np.einsum('iaja->ij', PV.reshape(d, d, d, d))))[::-1]
    return lamE/2, nu[2], psi
# (B.3)
dev = 0
for d in (3, 4):
    x1, x2, _a, _b = class_plane(d)
    psi = (np.kron(x1, [1, 0]) + np.kron(x2, [0, 1]))/np.sqrt(2)
    R = np.outer(psi, psi.conj()).reshape(d, d, 2, d, d, 2)
    r1Q = np.einsum('aiqbir->aqbr', R)          # Tr_2: copy-1 and Q
    r2Q = np.einsum('iaqibr->aqbr', R)          # Tr_1: copy-2 and Q
    Id = np.eye(d)
    term1 = np.einsum('aqbr,ij->aiqbjr', r1Q, Id).reshape(2*d*d, 2*d*d)
    term2 = np.einsum('aqbr,ij->iaqjbr', r2Q, Id).reshape(2*d*d, 2*d*d)
    rhs = 2*np.eye(2*d*d) - 2*term1 - 2*term2 + np.outer(psi, psi.conj())
    dev = max(dev, np.abs(E_full(np.outer(psi, psi.conj()), d) - rhs).max())
report(f"(B.3) against the full operator, d = 3, 4: max deviation {dev:.1e}", dev < 1e-12)
cst = 1 - 1/np.sqrt(2); worst = np.inf
for d in (3, 4, 5, 6):
    for _ in range(400):
        x1, x2, _a, _b = class_plane(d)
        m2, nu3, _p = m2_and_nu3(x1, x2, d)
        if nu3 > 1e-9:
            worst = min(worst, m2/(cst*nu3))
report(f"class planes, d = 3..6 (1600): min of m_2(V) / ((1 - 1/sqrt2) nu_3(V)) = {worst:.4f} >= 1", worst >= 1 - 1e-9)
d = 3
e = np.eye(3)
x1 = np.kron(e[0], e[0]); x2 = (np.kron(e[1], e[1]) + np.kron(e[2], e[2]))/np.sqrt(2)
m2, nu3, _p = m2_and_nu3(x1, x2, d)
report(f"V = span{{|00>, Omega}}: m_2 = {m2:.12f}, (1 - 1/sqrt2) nu_3 = {cst*nu3:.12f} (equality)", abs(m2 - cst*nu3) < 1e-12 and abs(nu3 - 0.5) < 1e-12)
Cst = np.outer(x1, x1) - (np.sqrt(2) - 1)*np.outer(x2, x2)
def q2(C):
    trA = np.einsum('aiaj->ij', C.reshape(d, d, d, d)); trB = np.einsum('iaja->ij', C.reshape(d, d, d, d))
    return np.linalg.norm(C)**2 - 0.5*(np.linalg.norm(trA)**2 + np.linalg.norm(trB)**2) + 0.25*abs(np.trace(C))**2
report(f"C_*: q_2 = {q2(Cst):.12f} = 3 - 2 sqrt2, ||C_*||^2 = {np.linalg.norm(Cst)**2:.12f} = 4 - 2 sqrt2, ratio = m_2(V)",
       abs(q2(Cst) - (3 - 2*np.sqrt(2))) < 1e-12 and abs(np.linalg.norm(Cst)**2 - (4 - 2*np.sqrt(2))) < 1e-12
       and abs(q2(Cst)/np.linalg.norm(Cst)**2 - m2) < 1e-12)
print("CHECK C3 (Theorem 7.2): " + ("PASS" if ok_all else "FAIL"))
sys.exit(0 if ok_all else 1)
