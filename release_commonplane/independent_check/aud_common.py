"""Independent audit (auditor) of the k=4, d=3 common-plane certificate: common definitions.

Everything here is written from paper A (werner_copies_v4.md, s.3) and ROUND2_NOTE s.1-2; nothing is
imported from the producer's code.

Conventions.
  Four replicas, local factors l = 0..3 (sites, C^3) and l = 4 (auxiliary Q = C^2).
  V_p on (C^n)^{x4} sends tensor factor i to factor p[i]:  V_p |x_0 x_1 x_2 x_3> = |y>, y_{p[i]} = x_i.
  Then V_p V_q = V_{p o q} with (p o q)[i] = p[q[i]], and V_p^T = V_{p^-1}.
  Aux operators: the 70 matrix units |r><s| on (C^2)^{x4} with |r| = |s| (torus commutant).
  A word is (w_0, w_1, w_2, w_3, u): V_w = V_{w_0} x ... x V_{w_3} x E_u.
  Word code = (((w0*24 + w1)*24 + w2)*24 + w3)*70 + u.
"""
import itertools
import numpy as np

D_SITE = 3
K_SITES = 4
PERMS = tuple(itertools.permutations(range(4)))
PIDX = {p: i for i, p in enumerate(PERMS)}
NP = 24


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def ncycles(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return c


MUL = np.array([[PIDX[compose(p, q)] for q in PERMS] for p in PERMS], dtype=np.int64)
INV = np.array([PIDX[inverse(p)] for p in PERMS], dtype=np.int64)
KAPPA = np.array([ncycles(p) for p in PERMS], dtype=np.int64)

# ---------------------------------------------------------------- aux matrix units
BITS = [tuple((x >> (3 - i)) & 1 for i in range(4)) for x in range(16)]   # bit string of basis index x
BIDX = {b: x for x, b in enumerate(BITS)}
AUX = [(r, s) for r in range(16) for s in range(16) if sum(BITS[r]) == sum(BITS[s])]
AIDX = {u: i for i, u in enumerate(AUX)}
NA = len(AUX)
assert NA == 70


def act_bits(p, b):
    """V_p |b> = |b'> with b'_{p[i]} = b_i."""
    out = [0] * 4
    for i in range(4):
        out[p[i]] = b[i]
    return tuple(out)


def aux_left(p, u):
    """V_p |r><s|  =  |p.r><s|."""
    r, s = AUX[u]
    return AIDX[(BIDX[act_bits(p, BITS[r])], s)]


def aux_right(p, u):
    """|r><s| V_p  =  |r> (V_p^T |s>)^T  =  |r><p^-1 . s|."""
    r, s = AUX[u]
    return AIDX[(r, BIDX[act_bits(inverse(p), BITS[s])])]


def aux_transpose(u):
    r, s = AUX[u]
    return AIDX[(s, r)]


AUX_LEFT = np.array([[aux_left(p, u) for u in range(NA)] for p in PERMS], dtype=np.int64)
AUX_RIGHT = np.array([[aux_right(p, u) for u in range(NA)] for p in PERMS], dtype=np.int64)
AUX_T = np.array([aux_transpose(u) for u in range(NA)], dtype=np.int64)
NWORDS = NP ** 4 * NA


def encode(w0, w1, w2, w3, u):
    return (((w0 * NP + w1) * NP + w2) * NP + w3) * NA + u


def decode_all():
    codes = np.arange(NWORDS, dtype=np.int64)
    u = codes % NA
    rest = codes // NA
    w3 = rest % NP
    rest //= NP
    w2 = rest % NP
    rest //= NP
    w1 = rest % NP
    w0 = rest // NP
    return w0, w1, w2, w3, u


# ---------------------------------------------------------------- literal local operators
def digits(x, n, m=4):
    return [(x // n ** (m - 1 - s)) % n for s in range(m)]


def undigits(ds, n):
    r = 0
    for x in ds:
        r = r * n + x
    return r


def perm_matrix(n, p):
    """Literal V_p on (C^n)^{x4} as a dense integer matrix (row = image index)."""
    N = n ** 4
    M = np.zeros((N, N), dtype=np.int64)
    for x in range(N):
        src = digits(x, n)
        tgt = [0] * 4
        for i in range(4):
            tgt[p[i]] = src[i]
        M[undigits(tgt, n), x] = 1
    return M


def aux_matrix(u):
    r, s = AUX[u]
    M = np.zeros((16, 16), dtype=np.int64)
    M[r, s] = 1
    return M


def partial_transpose(M, n, T):
    """Literal partial transpose of an operator on (C^n)^{x4} on the tensor factors in T."""
    N = n ** 4
    out = np.zeros_like(M)
    rows, cols = np.nonzero(M)
    for r, c in zip(rows, cols):
        rd, cd = digits(r, n), digits(c, n)
        for t in T:
            rd[t], cd[t] = cd[t], rd[t]
        out[undigits(rd, n), undigits(cd, n)] += M[r, c]
    return out
