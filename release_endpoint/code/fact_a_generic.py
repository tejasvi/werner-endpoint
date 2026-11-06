# fact_a_generic.py: exact check of Lemma B.8 for j <= jmax copies (paper, Appendix B.1; check C5 of this package). Not used in the proofs.
#
# For a qubit vector psi in (C^2)^{(x)j} (x) Q with Gaussian-integer entries, Lemma B.8 calls psi good if
#   (a) the T = empty block sum_{alpha in {1,2,3}^j} sigma_alpha psi psi^* sigma_alpha has kernel exactly span{Theta psi},
#       i.e. the vectors sigma_alpha psi span a space of dimension 2^{j+1} - 1 (it is at most 2^{j+1} - 1 by Lemma B.2);
#   (b) for every T != empty the first factor of A_T is nonsingular, i.e. the vectors sigma_beta psi_a (beta in {1,2,3}^{j-|T|},
#       a in {0,1}^{|T|}, psi_a = <a|_T psi) span C^{2^{j-|T|+1}};
#   (c) psi has Q-rank 2.
# Ranks are bounded below exactly by Gaussian elimination over F_p, p = 10^9 + 9 = 1 (mod 4), with i -> a square root of -1
# mod p. Reduction Z[i] -> F_p is a ring homomorphism, so a rank mod p is a lower bound for the rank over C.
# Usage: fact_a_generic.py jmax seed [jmin]
import sys, itertools
import numpy as np

jmax, seed = int(sys.argv[1]), int(sys.argv[2])
jmin = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = np.random.default_rng(seed)
p = 1000000009
assert p % 4 == 1


def sqrt_m1(p):
    for g in range(2, 100):
        x = pow(g, (p - 1) // 4, p)
        if x * x % p == p - 1:
            return x


I_P = sqrt_m1(p)


def red(re, im):
    return (np.asarray(re, dtype=object) + I_P * np.asarray(im, dtype=object)) % p


PAU = {1: (np.array([[0, 1], [1, 0]]), np.zeros((2, 2), int)),
       2: (np.zeros((2, 2), int), np.array([[0, -1], [1, 0]])),
       3: (np.array([[1, 0], [0, -1]]), np.zeros((2, 2), int))}


def pauli_mod(a):
    re, im = PAU[a]
    return np.array(red(re, im), dtype=np.int64)


def rank_mod(M):
    """rank over F_p by Gaussian elimination in int64 (entries < p < 2^30, products < 2^62)."""
    A = np.array(M, dtype=np.int64) % p
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r == rows:
            break
        nzr = np.flatnonzero(A[r:, c]) + r
        if nzr.size == 0:
            continue
        piv = nzr[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        others = np.flatnonzero(A[:, c])
        others = others[others != r]
        if others.size:
            A[others] = (A[others] - (A[others, c][:, None] * A[r][None, :]) % p) % p
        r += 1
    return r


def apply_paulis(labels, v, n):
    out = v.reshape([2] * n + [2])
    for site, a in enumerate(labels):
        out = np.moveaxis(np.tensordot(pauli_mod(a), out, axes=([1], [site])) % p, 0, site)
    return out.reshape(-1) % p


all_ok = True
for j in range(jmin, jmax + 1):
    re = rng.integers(-9, 10, size=2 ** j * 2)
    im = rng.integers(-9, 10, size=2 ** j * 2)
    psi = np.array(red(re, im), dtype=np.int64)
    alls = list(itertools.product((1, 2, 3), repeat=j))
    idx = rng.permutation(len(alls))[:min(len(alls), 3 * 2 ** (j + 1))]
    ra = rank_mod(np.array([apply_paulis(alls[i], psi, j) for i in idx], dtype=np.int64).T)
    if ra < 2 ** (j + 1) - 1:
        ra = rank_mod(np.array([apply_paulis(al, psi, j) for al in alls], dtype=np.int64).T)
    ok_a = (ra == 2 ** (j + 1) - 1)
    ok_b = True
    worst = None
    T0 = psi.reshape([2] * j + [2])
    for size in range(1, j + 1):
        for T in itertools.combinations(range(j), size):
            n = j - size
            rest = [m for m in range(j) if m not in T]
            Tt = np.transpose(T0, list(T) + rest + [j]).reshape(2 ** size, 2 ** n * 2)
            pairs = [(a, be) for a in range(2 ** size) for be in itertools.product((1, 2, 3), repeat=n)]
            sel = rng.permutation(len(pairs))[:min(len(pairs), 3 * 2 ** (n + 1))]
            rb = rank_mod(np.array([apply_paulis(pairs[q][1], Tt[pairs[q][0]], n) for q in sel], dtype=np.int64).T)
            if rb < 2 ** (n + 1):
                rb = rank_mod(np.array([apply_paulis(be, Tt[a], n) for a, be in pairs], dtype=np.int64).T)
            if rb != 2 ** (n + 1):
                ok_b = False
                worst = (T, rb, 2 ** (n + 1))
    ok_c = rank_mod(psi.reshape(2 ** j, 2)) == 2
    ok = ok_a and ok_b and ok_c
    all_ok = all_ok and ok
    print(f"j = {j}: (a) rank {ra} (need {2 ** (j + 1) - 1}): {ok_a};  (b) all T-blocks nonsingular: {ok_b}"
          f"{' ' + str(worst) if worst else ''};  (c) Q-rank 2: {ok_c}", flush=True)
print(f"FACT C5 (good vectors exist for j = {jmin}..{jmax}): " + ("PASS" if all_ok else "FAIL"))
sys.exit(0 if all_ok else 1)
