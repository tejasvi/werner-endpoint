"""xlkx.py sized for k = 4: the exact polynomial left kernel by the reduced power-series parametrisation modulo primes, CRT and
rational reconstruction, with
  - the rows of M(s) (the columns of A(s)) compressed on the fly by one fixed random integer matrix (deterministic per row group,
    the same for every prime and every order): equality rows first to NE combinations per copy, then everything to NR rows;
  - only q solutions kept: the first q columns (rref pivots) of the solution matrix whose s^0 coefficients are independent.
The compression can only add spurious solutions; xlkverify2.py checks the kept solutions exactly against the uncompressed data.
Usage: python xlkx2.py POLYPICKLE REDPICKLE D OUT.pkl NR NP NE            (primes PRIMES20[-NP:] reversed, then CRT)
       python xlkx2.py POLYPICKLE REDPICKLE D PART.pkl NR NP NE i0 i1     (only primes [i0:i1] of that list, residues saved)
       python xlkx2.py join OUT.pkl PART.pkl ...                          (CRT of saved residues)"""
import sys, os, pickle, time, math
from fractions import Fraction
import numpy as np
import flint
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xbuild import PRIMES20

t0 = time.time()
def log(s):
    print('%s (%.0fs)' % (s, time.time() - t0), flush=True)


def rgroup(key, rows_, NR):
    return np.random.default_rng([5, key]).integers(-9, 10, size=(NR, rows_))


def mulmod(A, B, p):
    """(A @ B) mod p for int64 residues, exact via float64 chunks of the inner dimension (p < 2^20)."""
    A = A.astype(np.float64); B = B.astype(np.float64)
    out_ = np.zeros((A.shape[0], B.shape[1]))
    step = 4096
    for s0 in range(0, A.shape[1], step):
        out_ = np.mod(out_ + np.mod(A[:, s0:s0 + step] @ B[s0:s0 + step], p), p)
    return out_.astype(np.int64)


def to_nmod(A, p):
    return flint.nmod_mat(A.shape[0], A.shape[1], [int(v) for v in A.ravel()], p)


def from_nmod(M_):
    return np.array([int(x) for x in M_.entries()], dtype=np.int64).reshape(M_.nrows(), M_.ncols())


def pivots(R, rank):
    pv = []
    for r in range(rank):
        for c in range(R.ncols()):
            if int(R[r, c]) != 0:
                pv.append(c); break
    return pv


class System:
    """Exact polynomial data of M(s), stored once (object arrays restricted to the variables each block uses)."""
    def __init__(self, P, red, NR, NE):
        self.N = N = P['N']; self.n = 3 * N; self.NR = NR
        self.Eobj = [np.asarray(E, dtype=object) for E in P['Ecoef']]
        nE = self.Eobj[0].shape[0]
        self.RE = np.random.default_rng(11).integers(-9, 10, size=(min(NE, nE), nE))
        self.blocks = []
        for jb, Nm in red['N'].items():
            b = P['blocks'][jb]; m = b['m']
            orders = []
            for C in b['coef']:
                C2 = np.asarray(C, dtype=object).reshape(N, m * m)
                nzv = np.nonzero((C2 != 0).any(axis=1))[0]
                orders.append((nzv, C2[nzv].reshape(len(nzv), m, m)))
            self.blocks.append((jb, m, np.asarray(Nm, dtype=object), orders))
        self.J = max(max(len(o) for _, _, _, o in self.blocks), len(self.Eobj))

    def compressed_mod(self, p):
        """M_j (j < J): NR x n residues of R M_j, accumulated group by group."""
        N, NR = self.N, self.NR
        M = [np.zeros((NR, self.n), dtype=np.int64) for _ in range(self.J)]
        REp = np.mod(self.RE, p)
        Rgs = [np.mod(rgroup(1000000 + c, self.RE.shape[0], NR), p) for c in range(3)]
        for j, E in enumerate(self.Eobj):
            G = mulmod(REp, np.mod(E, p).astype(np.int64), p)              # NE x N
            for c in range(3):
                M[j][:, c * N:(c + 1) * N] = np.mod(M[j][:, c * N:(c + 1) * N] + mulmod(Rgs[c], G, p), p)
        for jb, m, Nm, orders in self.blocks:
            Nf = np.mod(Nm, p).astype(np.float64)
            N1, N2 = Nf[:m], Nf[m:]
            iu = np.triu_indices(Nm.shape[1])
            Rg = np.mod(rgroup(jb, len(iu[0]), NR), p)
            for j, (nzv, Cs) in enumerate(orders):
                if len(nzv) == 0:
                    continue
                Cf = np.mod(Cs, p).astype(np.float64)
                def cong(A, Bm):
                    X = np.mod(np.einsum('iab,bs->ias', Cf, Bm), p)
                    return np.mod(np.einsum('ar,ias->irs', A, X), p)
                G1 = cong(N1, N1); G2 = cong(N2, N2); G3 = cong(N1, N2); G3 = np.mod(G3 + np.transpose(G3, (0, 2, 1)), p)
                for c, Gc in enumerate((G1, G2, G3)):
                    g = Gc[:, iu[0], iu[1]].T.astype(np.int64)           # rows_b x |nzv|
                    cols = c * N + nzv
                    M[j][:, cols] = np.mod(M[j][:, cols] + mulmod(Rg, g, p), p)
        return M


def run_prime(S, p, D):
    n, NR, J = S.n, S.NR, S.J
    M = S.compressed_mod(p)
    log('prime %d: compressed rows ready (%d x %d, %d orders)' % (p, NR, n, J))
    M0 = to_nmod(M[0], p)
    R0, rk = M0.rref()
    C0 = pivots(R0, rk)                                                  # pivot columns
    RT, rkT = M0.transpose().rref()
    Rows0 = pivots(RT, rkT)                                              # independent rows
    assert rk == rkT
    K0, q = M0.nullspace()
    B0 = from_nmod(K0)[:, :q]
    Hn = from_nmod(to_nmod(M[0][np.ix_(Rows0, C0)], p).inv())
    def G(bm):                                                           # w with w_C0 = H b_Rows0, else 0
        w = np.zeros((n, bm.shape[1]), dtype=np.int64)
        w[C0] = mulmod(Hn, bm[Rows0], p)
        return w
    nt = q * (D + 1)
    W = []
    cons = []
    for k in range(D + J):
        b = np.zeros((NR, nt), dtype=np.int64)
        for i in range(1, min(k, J - 1) + 1):
            if k - i <= D:
                b = np.mod(b - mulmod(M[i], W[k - i], p), p)
        if k == 0:
            Wk = np.zeros((n, nt), dtype=np.int64); Wk[:, 0:q] = B0
        elif k <= D:
            Wk = G(b)
            cons.append(np.mod(mulmod(M[0], Wk, p) - b, p))                 # solvability residual
            Wk[:, q * k:q * (k + 1)] = np.mod(Wk[:, q * k:q * (k + 1)] + B0, p)
        else:
            cons.append(b)                                               # termination: b_k = 0
            Wk = None
        W.append(Wk)
    Cm = np.vstack(cons)
    Tn, nul = to_nmod(Cm, p).nullspace()
    T = from_nmod(Tn)[:, :nul]
    W0 = mulmod(W[0], T, p)
    Rw, rkw = to_nmod(W0, p).rref()
    keep = pivots(Rw, rkw)                                               # first independent solutions at s = 0
    Tk = T[:, keep]
    wcoef = [mulmod(W[j], Tk, p) for j in range(D + 1)]                  # w_j of the kept solutions (n x len(keep))
    log('prime %d: rank %d, q %d, solutions (deg <= %d) %d, rank at s = 0 %d' % (p, rk, q, D, nul, rkw))
    return dict(rank=rk, q=q, nul=nul, rkw=rkw, C0=C0, Rows0=Rows0, keep=keep, wcoef=wcoef)


def ratrec(a, m):
    """rational reconstruction of a mod m: a = num/den with |num|, den <= sqrt(m/2); None if none."""
    a %= m
    r0, r1, s0_, s1 = m, a, 0, 1
    bound = math.isqrt(m // 2)
    while r1 > bound:
        qq = r0 // r1
        r0, r1 = r1, r0 - qq * r1
        s0_, s1 = s1, s0_ - qq * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1) if s1 > 0 else Fraction(-r1, -s1)


sig = lambda r: (r['rank'], r['q'], r['nul'], r['rkw'], r['C0'], r['Rows0'], r['keep'])


def join(res, out):
    """CRT + rational reconstruction over the primes of res (the last one held out as a check)."""
    good = [res[0]]
    for p, r in res[1:]:
        if sig(r) != sig(res[0][1]):
            log('prime %d: different pivot structure, skipped' % p); continue
        good.append((p, r))
    res = good
    r0 = res[0][1]
    D = len(r0['wcoef']) - 1
    if r0['rkw'] < r0['q']:
        log('rank of the solutions at s = 0 is %d < q = %d: increase D' % (r0['rkw'], r0['q']))
    primes = [p for p, _ in res]
    Mmod = 1
    for p in primes[:-1]:
        Mmod *= p
    coefs = []
    fail = 0
    for j in range(D + 1):
        stack = [r['wcoef'][j] for _, r in res]
        Cj = np.zeros(stack[0].shape, dtype=object)
        for idx in np.ndindex(stack[0].shape):
            a, mm = 0, 1
            for (p, r), A in zip(res[:-1], stack[:-1]):
                inv = pow(mm, -1, p)
                a = a + mm * (((int(A[idx]) - a) * inv) % p)
                mm *= p
            q_ = ratrec(a, mm)
            if q_ is None or (q_.numerator - q_.denominator * int(stack[-1][idx])) % primes[-1] != 0:
                fail += 1
                q_ = None
            Cj[idx] = q_
        coefs.append(Cj)
    log('rational reconstruction: %d failures over %d coefficient entries (%d primes, modulus 2^%.0f)' % (
        fail, sum(C.size for C in coefs), len(primes) - 1, math.log2(Mmod)))
    pickle.dump(dict(D=D, q=r0['q'], rank=r0['rank'], nul=r0['nul'], nkeep=len(r0['keep']), coefs=coefs, primes=primes,
                     ok=(fail == 0 and r0['rkw'] == r0['q'])), open(out, 'wb'), protocol=4)


if __name__ == '__main__':
    if sys.argv[1] == 'join':
        res = []
        for f in sys.argv[3:]:
            res += pickle.load(open(f, 'rb'))
        join(res, sys.argv[2])
        sys.exit(0)
    P = pickle.load(open(sys.argv[1], 'rb')); red = pickle.load(open(sys.argv[2], 'rb'))
    D = int(sys.argv[3]); out = sys.argv[4]; NR = int(sys.argv[5]); NP = int(sys.argv[6]); NE = int(sys.argv[7])
    S = System(P, red, NR, NE)
    del P
    log('data stored: %d blocks, %d orders' % (len(S.blocks), S.J))
    plist = PRIMES20[-NP:][::-1]
    if len(sys.argv) > 9:
        plist = plist[int(sys.argv[8]):int(sys.argv[9])]
    res = [(p, run_prime(S, p, D)) for p in plist]
    if len(sys.argv) > 9:
        pickle.dump(res, open(out, 'wb'), protocol=4)
        log('residues of %d primes saved' % len(res))
    else:
        join(res, out)
