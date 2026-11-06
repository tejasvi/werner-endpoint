"""Random NON-Hermitian common-plane C = V c V^* (V: C^2 -> (C^3)^{x4} isometry, c random complex 2x2):
q4(C) directly, q4(H) + q4(K) with H = (C + C^*)/2, K = (C - C^*)/2i, and the chain through the relaxation:
for P in {H, K}: P = A diag(mu1, mu2) A^* (A = V U), scale s = 2 (mu1^2 + mu2^2), th = atan2(mu2, mu1),
q4(P) = s q4(C_th(A)) and q4(C_th(A)) = c_th . y(A) (producer coordinates, own pipeline in phys_points).
usage: phys_cp.py SEED NC"""
import sys
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import phys_points as PP

seed, nc = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(seed)
for t in range(nc):
    V, _ = np.linalg.qr(rng.normal(size=(81, 2)) + 1j * rng.normal(size=(81, 2)))
    c = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    C = V @ c @ V.conj().T
    qC = PP.q4(C)
    H = (C + C.conj().T) / 2
    K = (C - C.conj().T) / 2j
    qH, qK = PP.q4(H), PP.q4(K)
    total = 0.0
    for name, P in (('H', H), ('K', K)):
        Pc = V.conj().T @ P @ V                      # 2x2 Hermitian
        mu, U = np.linalg.eigh(Pc)
        A = V @ U
        s = 2 * float(mu @ mu)
        th = float(np.arctan2(mu[1], mu[0]))
        qd, cmine, cprod, certval = PP.check_point(A, th)
        total += s * cprod
        PP.log('  part %s: s = %.6e, theta = %+.4f, s*q4(C_th) = %+.6e, q4(%s) direct = %+.6e, s * c.y = %+.6e'
               % (name, s, th, s * qd, name, qH if name == 'H' else qK, s * cprod))
    PP.log('C #%d: q4(C) = %+.8e, q4(H) + q4(K) = %+.8e, sum of s * c_th.y = %+.8e' % (t, qC, qH + qK, total))
