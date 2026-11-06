# z2_check.py: checks for Theorem 3.2 (two copies: every zero is qubit-supported) and Corollary 3.3 (paper Section 3;
# check C4 of this package).
# Part A (symbolic, sympy): the computation in the sub-case dim E_s = 2 of the proof: the vectors T_11, T_22, T_12, the
#   determinant 4 Tr(C_S) det(C_S), the vector y, the Schur-form case, and, when Tr C_S = 0, the functional l with
#   l . T(s) = 0, l . y = 2 det C_S and span{T(s)} = ker l.
# Part B (floating point): the identity (P) q_2 = t_1 + beta of Song and Chen on random operators; at random
#   qubit-supported zeros, t_1 = beta = 0, z != 0 and N z = xi_0 (Step 2); random planes whose local supports both have
#   dimension three are not zeros. Part B is a numerical illustration; the proof does not use it.
import sys
import numpy as np
import sympy as sp

ok_all = True
def report(name, ok):
    global ok_all
    ok_all = ok_all and bool(ok)
    print(f"  {name}: {bool(ok)}")

print("Part A (symbolic)")
c11, c12, c21, c22, tau, c = sp.symbols('c11 c12 c21 c22 tau c')
def sym_coords(v):                # v in S (x) S as 4-vector (e1e1, e1e2, e2e1, e2e2) -> coordinates in (e1e1, e2e2, e1e2+e2e1)
    assert sp.simplify(v[1] - v[2]) == 0
    return sp.Matrix([v[0], v[3], v[1]])
def kron2(u, v): return sp.Matrix([u[0]*v[0], u[0]*v[1], u[1]*v[0], u[1]*v[1]])
def T_of(Cm, s): return kron2(s, Cm*s) + kron2(Cm*s, s)
e1 = sp.Matrix([1, 0]); e2 = sp.Matrix([0, 1])
CS = sp.Matrix([[c11, c12], [c21, c22]])
T11 = sym_coords(T_of(CS, e1)); T22 = sym_coords(T_of(CS, e2))
T12 = sym_coords(sp.expand(T_of(CS, e1 + e2) - T_of(CS, e1) - T_of(CS, e2)))
report("T_11 = (2c11, 0, c21)", T11 == sp.Matrix([2*c11, 0, c21]))
report("T_22 = (0, 2c22, c12)", T22 == sp.Matrix([0, 2*c22, c12]))
report("T_12 = (2c12, 2c21, c11 + c22)", sp.expand(T12 - sp.Matrix([2*c12, 2*c21, c11 + c22])) == sp.zeros(3, 1))
M = sp.Matrix.hstack(T11, T22, T12)
report("det[T_11, T_22, T_12] = 4 Tr(C_S) det(C_S)", sp.expand(M.det() - 4*(c11 + c22)*(c11*c22 - c12*c21)) == 0)
eps = kron2(e1, e2) - kron2(e2, e1)
I2 = sp.eye(2)
y4 = sp.Rational(1, 2)*(sp.kronecker_product(I2, CS) - sp.kronecker_product(CS, I2))*eps
y = sym_coords(sp.expand(y4))
report("y = (c12, -c21, (c22 - c11)/2)", sp.expand(y - sp.Matrix([c12, -c21, (c22 - c11)/2])) == sp.zeros(3, 1))
# Schur form C_S = [[tau, c], [0, 0]], (tau, c) != 0: span{T(s)} contains every vector with zero second coordinate, and so does y.
Cs = sp.Matrix([[tau, c], [0, 0]])
Ms = sp.Matrix.hstack(sym_coords(T_of(Cs, e1)), sym_coords(T_of(Cs, e2)),
                      sym_coords(sp.expand(T_of(Cs, e1 + e2) - T_of(Cs, e1) - T_of(Cs, e2))))
ys = sym_coords(sp.expand(sp.Rational(1, 2)*(sp.kronecker_product(I2, Cs) - sp.kronecker_product(Cs, I2))*eps))
second_zero = all(sp.simplify(Ms[1, j]) == 0 for j in range(3)) and sp.simplify(ys[1]) == 0
rank_tau = sp.Matrix([[Ms[0, j], Ms[2, j]] for j in range(3)]).subs({tau: 1}).rank() == 2      # tau != 0 (scale tau = 1)
rank_c = sp.Matrix([[Ms[0, j], Ms[2, j]] for j in range(3)]).subs({tau: 0, c: 1}).rank() == 2  # tau = 0, c != 0
# for tau != 0 the rank-2 claim must hold for every c: the (0,2)-minor of columns T_11, T_12 is 2 tau^2
minor = sp.Matrix([[Ms[0, 0], Ms[0, 2]], [Ms[2, 0], Ms[2, 2]]]).det()
report("Schur case: T(s) and y have zero second coordinate, and the T(s) span that plane", second_zero and rank_tau and rank_c and sp.expand(minor - 2*tau**2) == 0)
# Tr C_S = 0: l = (-c21, c12, 2 c11) kills T(s), l . y = 2 det C_S, and the T(s) have rank 2 when det C_S != 0
sub = {c22: -c11}
l = sp.Matrix([-c21, c12, 2*c11])
report("Tr C_S = 0: l . T_11 = l . T_22 = l . T_12 = 0",
       all(sp.expand((l.T*v)[0].subs(sub)) == 0 for v in (T11, T22, T12)))
report("Tr C_S = 0: l . y = 2 det C_S", sp.expand((l.T*y)[0].subs(sub) - 2*(c11*c22 - c12*c21).subs(sub)) == 0)
Mz = M.subs(sub)
m1 = Mz.extract([0, 1], [0, 1]).det(); m2 = Mz.extract([0, 2], [1, 2]).det()
# if both minors vanish then c11 = 0 and c12 = 0, hence det C_S = -c11^2 - c12 c21 = 0
report("Tr C_S = 0 != det C_S: rank[T_11, T_22, T_12] = 2 (minors -4 c11^2 and -2 c12^2)",
       sp.expand(m1 + 4*c11**2) == 0 and sp.expand(m2 + 2*c12**2) == 0 and Mz.det() == 0)

print("Part B (floating point)")
rng = np.random.default_rng(37)
m, n = 3, 4
dim = m * n
def crandn(*s): return rng.standard_normal(s) + 1j*rng.standard_normal(s)
def ptr_A(X):   # Tr_A of X on C^m (x) C^n
    return np.einsum('aiaj->ij', X.reshape(m, n, m, n))
def ptr_B(X):
    return np.einsum('iaja->ij', X.reshape(m, n, m, n))
def q2(C):
    return (np.linalg.norm(C)**2 - 0.5*(np.linalg.norm(ptr_A(C))**2 + np.linalg.norm(ptr_B(C))**2)
            + 0.25*abs(np.trace(C))**2)
# operators on H (x) H, H = A (x) B, index order (a1, b1, a2, b2)
I_HH = np.eye(dim*dim)
def perm_op(perm):
    P = np.zeros((dim*dim, dim*dim))
    for a1 in range(m):
        for b1 in range(n):
            for a2 in range(m):
                for b2 in range(n):
                    src = (a1, b1, a2, b2); tgt = tuple(src[k] for k in perm)
                    P[np.ravel_multi_index(tgt, (m, n, m, n)), np.ravel_multi_index(src, (m, n, m, n))] = 1
    return P
FA = perm_op((2, 1, 0, 3)); FB = perm_op((0, 3, 2, 1)); FAB = FA @ FB
Pmm = (I_HH - FA) @ (I_HH - FB) / 4; Ppp = (I_HH + FA) @ (I_HH + FB) / 4; PsymH = (I_HH + FAB) / 2
def parts(C, e1v, e2v):
    x1, x2 = C @ e1v, C @ e2v
    t1 = (2*np.linalg.norm(Pmm @ np.kron(e1v, x1))**2 + np.linalg.norm(Pmm @ (np.kron(e1v, x2) + np.kron(e2v, x1)))**2
          + 2*np.linalg.norm(Pmm @ np.kron(e2v, x2))**2)
    w = np.kron(e1v, x2) - np.kron(e2v, x1)
    S2 = np.stack([np.kron(e1v, e1v), (np.kron(e1v, e2v) + np.kron(e2v, e1v))/np.sqrt(2), np.kron(e2v, e2v)], axis=1)
    beta = np.linalg.norm(Ppp @ w)**2 - 0.5*np.linalg.norm(S2.conj().T @ w)**2
    return t1, beta, w
# (P) on random C with co-range in a random plane S
devs = []
for _ in range(20):
    Q_, _r = np.linalg.qr(crandn(dim, 2)); e1v, e2v = Q_[:, 0], Q_[:, 1]
    C = crandn(dim, 2) @ Q_.conj().T
    t1, beta, _w = parts(C, e1v, e2v)
    devs.append(abs(q2(C) - t1 - beta) / max(1.0, abs(q2(C))))
report(f"(P): q_2 = t_1 + beta on 20 random C, max deviation {max(devs):.1e} < 1e-12", max(devs) < 1e-12)
# the q_2 form on {C : ran C* in V} for an orthonormal basis (a, b) of V: C = f1 a* + f2 b*, phi = (f1, f2)
def form_matrix(a, b):
    G = np.zeros((2*dim, 2*dim), complex)
    # polarisation on basis vectors: h(e_i + e_j) = G_ii + G_jj + 2 Re G_ij, h(e_i + i e_j) = G_ii + G_jj - 2 Im G_ij
    basis = np.eye(2*dim)
    def Cof(phi): return np.outer(phi[:dim], a.conj()) + np.outer(phi[dim:], b.conj())
    def qq(phi): return q2(Cof(phi))
    for i in range(2*dim):
        G[i, i] = qq(basis[i])
    for i in range(2*dim):
        for j in range(i+1, 2*dim):
            s = qq(basis[i] + basis[j]); t = qq(basis[i] + 1j*basis[j])
            re = (s - G[i, i] - G[j, j]) / 2; im = -(t - G[i, i] - G[j, j]) / 2
            G[i, j] = re + 1j*im; G[j, i] = np.conj(G[i, j])
    return G, Cof
ok_zero = True
for _ in range(3):
    A0, _r = np.linalg.qr(crandn(m, 2)); B0, _r = np.linalg.qr(crandn(n, 2))
    V = np.stack([np.kron(A0 @ crandn(2), B0 @ crandn(2)) + np.kron(A0 @ crandn(2), B0 @ crandn(2)) for _k in range(2)], axis=1)
    Qv, _r = np.linalg.qr(V); a, b = Qv[:, 0], Qv[:, 1]
    G, Cof = form_matrix(a, b)
    ev, U = np.linalg.eigh(G)
    C = Cof(U[:, 0])
    t1, beta, w = parts(C, a, b)
    xi0 = PsymH @ w; z = Pmm @ xi0
    PS = np.outer(a, a.conj()) + np.outer(b, b.conj())
    N = np.kron(PS, np.eye(dim)) + np.kron(np.eye(dim), PS)
    ok_zero = ok_zero and ev[0] > -1e-10 and abs(ev[0]) < 1e-10 and abs(t1) < 1e-10 and abs(beta) < 1e-10 \
        and np.linalg.norm(z) > 1e-6 and np.linalg.norm(N @ z - xi0) < 1e-10
report("qubit-supported zeros: m_2(V) = 0, t_1 = beta = 0, z != 0 and N z = xi_0 (3 random planes)", ok_zero)
mins = []
for _ in range(50):
    Qv, _r = np.linalg.qr(crandn(dim, 2)); a, b = Qv[:, 0], Qv[:, 1]
    G, _c = form_matrix(a, b)
    mins.append(np.linalg.eigvalsh(G)[0])
report(f"50 random planes (local supports of dimension 3): min m_2(V) = {min(mins):.3f} > 0", min(mins) > 1e-3)
print("CHECK C4 (Theorem 3.2): " + ("PASS" if ok_all else "FAIL"))
sys.exit(0 if ok_all else 1)
