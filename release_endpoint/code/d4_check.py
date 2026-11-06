# d4_check.py: numerical illustration of Corollary 3.4 (paper Section 3; check C6 of this package). The proof does not use it.
# For traceless A, B in M_4 and X = A (x) I + I (x) B, the bound sigma_1(X)^2 + sigma_2(X)^2 <= 2(||A||^2 + ||B||^2) holds,
# with equality exactly for (A, B) = kappa((Tr_B C)_0, (Tr_A C)_0), C a two-copy zero. Checks:
#  - pairs built from zeros C on random qubit-supported planes in C^4 (x) C^4 give ratio 1, and rank(A + cI) <= 2 and
#    rank(B + cI) <= 2 with c = Tr(C)/4;
#  - the pair A = diag(1, -1, 0, 0), B = 0 satisfies the rank condition but gives ratio 1/2;
#  - the two explicit diagonal saturating pairs of Liu and Chen [LC26, Theorem 7, case 3] give ratio 1 and satisfy the
#    rank condition;
#  - random traceless pairs give ratio < 1.
import sys
import numpy as np

rng = np.random.default_rng(151)
d = 4
def crandn(*s): return rng.standard_normal(s) + 1j*rng.standard_normal(s)
def ptr_A(C): return np.einsum('aiaj->ij', C.reshape(d, d, d, d))      # trace over the first factor
def ptr_B(C): return np.einsum('iaja->ij', C.reshape(d, d, d, d))      # trace over the second factor
def q2(C):
    return (np.linalg.norm(C)**2 - 0.5*(np.linalg.norm(ptr_A(C))**2 + np.linalg.norm(ptr_B(C))**2)
            + 0.25*abs(np.trace(C))**2)
def ratio(A, B):
    X = np.kron(A, np.eye(d)) + np.kron(np.eye(d), B)
    s = np.linalg.svd(X, compute_uv=False)
    return (s[0]**2 + s[1]**2) / (2*(np.linalg.norm(A)**2 + np.linalg.norm(B)**2))
def rank(M, tol=1e-9): return int(np.sum(np.linalg.svd(M, compute_uv=False) > tol*max(1.0, np.linalg.norm(M))))
def zero_on_plane(a, b):
    """unit C with co-range in span{a, b} (orthonormal) minimising q_2, via the Hermitian form on phi = (f1, f2)"""
    n = d*d
    def Cof(phi): return np.outer(phi[:n], a.conj()) + np.outer(phi[n:], b.conj())
    G = np.zeros((2*n, 2*n), complex); E = np.eye(2*n)
    diag = [q2(Cof(E[i])) for i in range(2*n)]
    for i in range(2*n):
        G[i, i] = diag[i]
        for j in range(i+1, 2*n):
            re = (q2(Cof(E[i] + E[j])) - diag[i] - diag[j]) / 2
            im = -(q2(Cof(E[i] + 1j*E[j])) - diag[i] - diag[j]) / 2
            G[i, j] = re + 1j*im; G[j, i] = np.conj(G[i, j])
    ev, U = np.linalg.eigh(G)
    return ev[0], Cof(U[:, 0])

ok_all = True
print("pairs from zeros on random qubit-supported planes:")
for t in range(3):
    A0, _r = np.linalg.qr(crandn(d, 2)); B0, _r = np.linalg.qr(crandn(d, 2))
    V = np.stack([sum(np.kron(A0 @ crandn(2), B0 @ crandn(2)) for _k in range(2)) for _j in range(2)], axis=1)
    Qv, _r = np.linalg.qr(V)
    m2, C = zero_on_plane(Qv[:, 0], Qv[:, 1])
    trC = np.trace(C)
    A = ptr_B(C) - trC/d*np.eye(d); B = ptr_A(C) - trC/d*np.eye(d)
    r = ratio(A, B); c = trC/d
    ra, rb = rank(A + c*np.eye(d)), rank(B + c*np.eye(d))
    ok = abs(m2) < 1e-10 and abs(r - 1) < 1e-10 and ra <= 2 and rb <= 2
    ok_all = ok_all and ok
    print(f"  plane {t}: m_2 = {m2:.1e}, ratio = {r:.12f}, rank(A + cI) = {ra}, rank(B + cI) = {rb}: {ok}")
A = np.diag([1., -1., 0., 0.]); B = np.zeros((d, d))
r = ratio(A, B); ok = abs(r - 0.5) < 1e-12 and rank(A) <= 2
ok_all = ok_all and ok
print(f"rank condition without saturation: A = diag(1,-1,0,0), B = 0: ratio = {r:.6f}: {ok}")
for name, A, B, c in (("[LC26] Thm 7, 3(a)", np.diag([.25, -.25, 0, 0]), np.diag([.25, -.25, 0, 0]), 0.0),
                      ("[LC26] Thm 7, 3(b)", np.diag([-3/8, 1/8, 1/8, 1/8]), np.diag([-1/8, -1/8, 1/8, 1/8]), -1/8)):
    r = ratio(A, B); ra, rb = rank(A + c*np.eye(d)), rank(B + c*np.eye(d))
    ok = abs(r - 1) < 1e-12 and ra <= 2 and rb <= 2
    ok_all = ok_all and ok
    print(f"{name}: ratio = {r:.12f}, rank(A + cI) = {ra}, rank(B + cI) = {rb} with c = {c}: {ok}")
best = 0.0
for _ in range(2000):
    A = crandn(d, d); B = crandn(d, d)
    A -= np.trace(A)/d*np.eye(d); B -= np.trace(B)/d*np.eye(d)
    best = max(best, ratio(A, B))
ok = best < 1
ok_all = ok_all and ok
print(f"2000 random traceless pairs: largest ratio = {best:.4f} < 1: {ok}")
print("CHECK C6 (Corollary 3.4): " + ("PASS" if ok_all else "FAIL"))
sys.exit(0 if ok_all else 1)
