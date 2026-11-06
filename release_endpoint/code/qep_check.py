# qep_check.py: a small reproducible instance of the numerical evidence for Conjecture 7.1 (paper Section 7; check C7 of this package).
# For a plane V in (C^d)^{(x)k} with orthonormal basis (a, b), m_k(V) is the smallest eigenvalue of E_{1/2}(psi psi^*),
# psi = a (x) q_1 + b (x) q_2, E_{1/2} = D^{(x)k} (x) id_Q with D(X) = Tr(X) I - X/2 (paper, (2.1)); nu_3^(l)(V) is the third
# largest eigenvalue of the reduced operator of P_V on copy l. Conjecture 7.1: 2^k m_k(V) >= min_l nu_3^(l)(V).
# Here k = 3, d = 3: (1) the ratio 2^k m_k / min_l nu_3^(l) on random planes; (2) local minimisation (SLSQP) of m_k(V) subject
# to nu_3^(l)(V) >= 2 delta at every copy, from a few random starts, compared with the conjectured bound 2^{1-k} delta.
# This is numerical evidence only.
import sys
import numpy as np
from scipy.optimize import minimize

k, d = 3, 3
dim = d**k
rng = np.random.default_rng(2026)


def E_half(R):
    """D^{(x)k} (x) id_Q applied to R on (C^d)^{(x)k} (x) C^2, D(X) = Tr(X) I - X/2."""
    T = R.reshape([d]*k + [2] + [d]*k + [2])
    for j in range(k):
        tr = np.trace(T, axis1=j, axis2=j + k + 1)                  # remove copy j on both sides
        # reinsert identity on copy j
        tr = np.expand_dims(np.expand_dims(tr, j), j + k + 1)
        Idshape = [1]*(2*k + 2); Idshape[j] = d; Idshape[j + k + 1] = d
        Id = np.eye(d).reshape(Idshape)
        T = tr*Id - 0.5*T
    return T.reshape(2*dim, 2*dim)


def frame(x):
    v = x[:2*dim] + 1j*x[2*dim:]
    M = v.reshape(dim, 2)
    Qm, _ = np.linalg.qr(M)
    return Qm[:, 0], Qm[:, 1]


def m_k(x):
    a, b = frame(x)
    psi = np.stack([a, b], axis=1).reshape(-1)                      # index order (copies, Q)
    return np.linalg.eigvalsh(E_half(np.outer(psi, psi.conj())))[0]


def nu3(x):
    a, b = frame(x)
    PV = (np.outer(a, a.conj()) + np.outer(b, b.conj())).reshape([d]*k*2)
    out = []
    for l in range(k):
        keep = [l]
        axes_trace = [j for j in range(k) if j != l]
        T = PV
        for j in sorted(axes_trace, reverse=True):
            T = np.trace(T, axis1=j, axis2=j + T.ndim//2)
        ev = np.sort(np.linalg.eigvalsh(T))[::-1]
        out.append(ev[2])
    return np.array(out)


ok_all = True
ratios = []
for _ in range(200):
    x = rng.standard_normal(4*dim)
    ratios.append(2**k*m_k(x)/nu3(x).min())
print(f"random planes (200): ratio 2^k m_k / min nu_3 in [{min(ratios):.3f}, {max(ratios):.3f}]")
ok_all = ok_all and min(ratios) >= 1
delta = 0.05
best = np.inf
for start in range(4):
    x0 = rng.standard_normal(4*dim)
    cons = [{'type': 'ineq', 'fun': (lambda x, l=l: nu3(x)[l] - 2*delta)} for l in range(k)]
    res = minimize(m_k, x0, method='SLSQP', constraints=cons, options={'maxiter': 400, 'ftol': 1e-12})
    val, nus = m_k(res.x), nu3(res.x)
    feas = nus.min() >= 2*delta*(1 - 1e-3)        # constraint met up to the solver tolerance
    r = 2**k*val/nus.min()                         # the ratio of Conjecture 7.1 at the point found (valid in any case)
    print(f"start {start}: m_k = {val:.6f}, nu_3 = {np.round(nus, 4)}, ratio to 2^(1-k) delta = {val/(2**(1-k)*delta):.4f}, "
          f"ratio 2^k m_k/min nu_3 = {r:.4f}, feasible {feas}")
    ok_all = ok_all and feas
    best = min(best, r)
print(f"constrained minimisation at delta = {delta}: smallest ratio 2^k m_k / min nu_3 = {best:.4f} (>= 1 expected)")
ok_all = ok_all and best >= 1 - 1e-6 and np.isfinite(best)
print("CHECK C7 (Conjecture 7.1, numerical instance k = 3, d = 3): " + ("PASS" if ok_all else "FAIL"))
sys.exit(0 if ok_all else 1)
