"""Exact SDP data for XRelax (xdata.py).
  cut-() blocks C = (V^T W) S_j (W^T V) and the functionals (objectives, trace) exactly (Python integers / Fractions);
  cut-(3,) blocks and the Stiefel equality rows by the tensor pipeline in int64 modulo primes p < 2^24, joined by CRT.
  A rigorous magnitude bound for the CRT comes from the same pipeline on absolute values (mode 'abs', float64).
Blocks of cut (3,) are den_Phi^k times the true Gram forms (positive scalar), equality rows are positive multiples.
Usage: python xbuild.py k (min|all) OUT.pkl"""
import sys, os, math, time, pickle, itertools
from fractions import Fraction
import numpy as np
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from xdata import XRelax, min_support, SUPPORTS, F, apply_factors, P4, I4, SWAP03
from local import perms, ncycles, compose
from relaxM import STR, SIDX, WORDS, WIDX, perm_op

PRIMES = [16777213, 16777199, 16777183, 16777153, 16777141, 16777139, 16777127, 16777121, 16777111, 16777099,
          16777049, 16777027, 16776989, 16776973, 16776971, 16776967, 16776961, 16776941, 16776931, 16776919]


def lcm_den(vals):
    den = 1
    for v in vals:
        q = F(v).denominator
        den = den * q // math.gcd(den, q)
    return den


def delete_matrix(n, slot=0):
    P3 = perms(3); I3 = {p: i for i, p in enumerate(P3)}
    order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((6, 24), dtype=np.int64)
    for a, p in enumerate(P4):
        out = tuple(order.index(p[slot] if p[i] == slot else p[i]) for i in order)
        M[I3[out], a] += n if p[slot] == slot else 1
    return M


def primes_below(top, count):
    import sympy
    out, p = [], top
    for _ in range(count):
        p = sympy.prevprime(p)
        out.append(int(p))
    return out


PRIMES20 = primes_below(2 ** 20, 24)     # float64 residue arithmetic is exact: every contraction sum stays below 2^53


class BE:
    """mode: 'abs' (float64 of absolute values: entrywise upper bounds), 'float', an int p (int64 mod p) or ('f', p) (float64
    residues mod p < 2^20; exact because every partial sum is an integer below 2^53)."""
    def __init__(self, mode):
        self.mode = mode
        self.p = mode if isinstance(mode, int) else (mode[1] if isinstance(mode, tuple) else None)
        self.fl = isinstance(mode, tuple)
        self.dtype = np.float64 if (self.fl or not self.p) else np.int64

    def conv(self, A):
        A = np.asarray(A, dtype=object)
        if self.p:
            return np.array([int(v) % self.p for v in A.ravel()], dtype=self.dtype).reshape(A.shape)
        out = np.array([float(v) for v in A.ravel()], dtype=np.float64).reshape(A.shape)
        return np.abs(out) if self.mode == 'abs' else out

    def red(self, X):
        return np.mod(X, self.p) if self.p else X

    def mm(self, A, B):
        return self.red(A @ B)

    def td(self, M, X, ax):
        return self.red(np.moveaxis(np.tensordot(M, X, axes=(1, ax)), 0, ax))


def layout(T, dims):
    """(n, n) Gram form -> per-factor layout (d0^2, d1^2, ..., da^2)."""
    nf = len(dims)
    T = T.reshape(list(dims) + list(dims))
    order = []
    for i in range(nf):
        order += [i, nf + i]
    return T.transpose(order).reshape([x * x for x in dims])


def unlayout(Y, dims):
    nf = len(dims)
    Y = Y.reshape([x for d_ in dims for x in (d_, d_)])
    order = [2 * i for i in range(nf)] + [2 * i + 1 for i in range(nf)]
    n = int(np.prod(dims))
    return Y.transpose(order).reshape(n, n)


def modular_part(X, mode, outs3, sorted_q, vsel=None):
    """cut-(3,) blocks (list over outs3 of arrays (N, m, m)) and equality rows (len(sorted_q)*70, N) in backend mode, for the
    variable blocks with index in vsel (all if None; other rows stay zero)."""
    be = BE(mode)
    k = X.k
    s0, a0 = X.site[()], X.aux[()]
    cut = (3,)
    sx, ax = X.site[cut], X.aux[cut]
    labs = sorted(set(l for o in outs3 for l in o['st']))
    rows = np.concatenate([np.arange(sx.off[l], sx.off[l + 1]) for l in labs]) if labs else np.zeros(0, dtype=int)
    lpos, at = {}, 0
    for l in labs:
        n2 = sx.dims[l] ** 2
        lpos[l] = slice(at, at + n2); at += n2
    Phi = be.conv(X.Phi[cut][0][rows])                                   # (Dsel, 23)
    PA = np.asarray(X.PhiA[cut], dtype=np.int64)                         # 0/1 bijection of the 70 unit coordinates
    assert (PA.sum(axis=0) == 1).all() and (PA.sum(axis=1) == 1).all()
    dest = PA.argmax(axis=0)                                             # cut-() aux coordinate -> cut-(3,) coordinate
    Eq_site = delete_matrix(X.d, 0).astype(object).dot(s0.IFG)         # (6, 23) rational
    den_eq = lcm_den(Eq_site.ravel())
    Eq = be.conv(np.array([[int(F(v) * den_eq) for v in row] for row in Eq_site], dtype=object))
    Mst = np.zeros((70, 70), dtype=np.int64)
    for e, (x, y) in enumerate(WORDS):
        Mst[e, e] += 2
        if x[0] == y[0]:
            for z in (0, 1):
                Mst[WIDX[((z,) + x[1:], (z,) + y[1:])], e] -= 1
    AE = be.conv(Mst.dot(a0.FT.T))                                       # 2 (E - I/2 (x) Tr_0 E) on Gram coords
    Vs = [be.conv(o['V']) for o in outs3]
    Fo = [np.zeros((X.N, o['m'], o['m']), dtype=be.dtype) for o in outs3]
    qidx = {q: i for i, q in enumerate(sorted_q)}
    Erows = np.zeros((len(sorted_q) * 70, X.N), dtype=be.dtype)
    for bi, b in enumerate(X.vars):
        if vsel is not None and bi not in vsel:
            continue
        st, ai, dims = b['st'], b['ai'], b['dims']
        W = be.conv(b['W'])
        for jj, S in enumerate(b['basis']):
            j = b['off'] + jj
            T = be.mm(be.mm(W, be.conv(S)), W.T)
            T0 = layout(T, dims)
            # ---- cut (3,) outputs
            if outs3:
                Y = T0
                for i in range(k):
                    Y = be.td(Phi[:, s0.rows(st[i])], Y, i)
                Ya = np.zeros(Y.shape[:k] + (70,), dtype=Y.dtype)
                Ya[..., dest[a0.rows(ai)]] = Y                            # aux: re-indexing only
                Y = Ya                                                    # (Dsel,)*k + (70,)
                Hacc = [None] * len(outs3)
                for new, s in b['cosets']:
                    perm = [0] * k
                    for i in range(k):
                        perm[s[i]] = i
                    Yp = Y.transpose(perm + [k])
                    for oi, o in enumerate(outs3):
                        sl = tuple(lpos[l] for l in o['st']) + (ax.rows(o['ai']),)
                        sub = unlayout(Yp[sl], o['dims'])
                        Hacc[oi] = sub if Hacc[oi] is None else be.red(Hacc[oi] + sub)
                for oi in range(len(outs3)):
                    Fo[oi][j] = be.mm(be.mm(Vs[oi].T, Hacc[oi]), Vs[oi])
            # ---- equalities (sorted S3-word tuples only; the variables are site symmetric)
            Z = T0
            for i in range(k):
                Z = be.td(Eq[:, s0.rows(st[i])], Z, i)
            Z = be.td(AE[:, a0.rows(ai)], Z, k)                         # (6,)*k + (70,)
            acc = None
            for new, s in b['cosets']:
                perm = [0] * k
                for i in range(k):
                    perm[s[i]] = i
                Zp = Z.transpose(perm + [k])
                acc = Zp if acc is None else be.red(acc + Zp)
            for q, qi in qidx.items():
                Erows[qi * 70:(qi + 1) * 70, j] = acc[q]
    return Fo, Erows, den_eq


def exact_part(X, outs0, vsel=None):
    """cut-() blocks exactly (object int arrays (N, m, m)) and the functionals as Fraction vectors (variable blocks in vsel)."""
    k, d = X.k, X.d
    s0, a0 = X.site[()], X.aux[()]
    Fo = [np.zeros((X.N, o['m'], o['m']), dtype=object) for o in outs0]
    L = Fraction((2 * d ** k) ** 4)
    zs_obj = np.array([Fraction(d ** ncycles(p)) - Fraction(1, 2) * d ** ncycles(compose(SWAP03, p)) for p in P4], dtype=object)
    zs_tr = np.array([Fraction(d ** ncycles(p)) for p in P4], dtype=object)
    S = perm_op(SWAP03)
    def za_th(which):
        za = []
        for (x, y) in WORDS:
            r, c = SIDX[y], SIDX[x]
            v = int(round(S[r, c]))
            if which == 'a':
                v *= 2 * (y[3] == 0) * (x[3] == 0)
            elif which == 'b':
                v *= 2 * (y[3] == 1) * (x[3] == 1)
            za.append(Fraction(v))
        return np.array(za, dtype=object)
    za_tr = np.array([Fraction(int(x == y)) for (x, y) in WORDS], dtype=object)
    funcs = {'ca': (zs_obj, za_th('a')), 'cb': (zs_obj, za_th('b')), 'cp': (zs_obj, za_th('p')), 'tr': (zs_tr, za_tr)}
    vecs = {key: np.zeros(X.N, dtype=object) for key in funcs}
    rowsG = {}
    for key, (zs, za) in funcs.items():
        zrow = zs.dot(s0.IFG)                                             # (23,) Fractions on Gram coords
        zaG = a0.FT.astype(object).dot(za)                                # (70,) on Gram coords
        rowsG[key] = (zrow, zaG)
    o_by = {(o['st'], o['ai']): [i for i, oo in enumerate(outs0) if (oo['st'], oo['ai']) == (o['st'], o['ai'])] for o in outs0}
    for bi, b in enumerate(X.vars):
        if vsel is not None and bi not in vsel:
            continue
        st, ai, dims = b['st'], b['ai'], b['dims']
        W = b['W']
        for key, (zrow, zaG) in rowsG.items():
            mats = [zrow[s0.rows(l)].reshape(s0.dims[l], s0.dims[l]) for l in st] + [zaG[a0.rows(ai)].reshape(a0.dims[ai], a0.dims[ai])]
            ZW = apply_factors(mats, W)                                   # (Z (x)) W, Z_l[i, j] = zrow[(l, i, j)]
            WZW = W.T.dot(ZW)
            nc = len(b['cosets'])
            for jj, Sj in enumerate(b['basis']):
                vecs[key][b['off'] + jj] = Fraction(nc) * np.sum(Sj * WZW) / L
        for oi in o_by.get((st, ai), []):
            VW = outs0[oi]['V'].T.dot(W)
            for jj, Sj in enumerate(b['basis']):
                Fo[oi][b['off'] + jj] = VW.dot(Sj).dot(VW.T)
    return Fo, vecs


def crt_join(res, primes):
    """Residue arrays (int64) -> object int array in the symmetric range."""
    M = 1
    X = np.zeros(res[0].shape, dtype=object)
    for r, p in zip(res, primes):
        # X = X + M * ((r - X) * M^-1 mod p)
        inv = pow(M, -1, p)
        t = (np.array(r, dtype=object) - X) % p
        t = (t * inv) % p
        X = X + M * t
        M *= p
    half = M // 2
    return np.where(X > half, X - M, X)


def chunk_compute(X, vsel, primes, verbose=False):
    """Everything that depends on the variable blocks in vsel: exact cut-() rows and functionals, 'abs' bounds, and residues of
    the cut-(3,) blocks / equality columns for each prime (float64-residue backend)."""
    t0 = time.time()
    outs0 = [o for o in X.outs if o['cut'] == ()]
    outs3 = [o for o in X.outs if o['cut'] == (3,)]
    sorted_q = list(itertools.combinations_with_replacement(range(6), X.k))
    J = [b['off'] + jj for bi, b in enumerate(X.vars) if bi in vsel for jj in range(len(b['basis']))]
    F0, vecs = exact_part(X, outs0, vsel)
    out = dict(J=J, F0=[A[J] for A in F0], vecs={key: v[J] for key, v in vecs.items()}, primes=list(primes))
    Fab, Eab, _ = modular_part(X, 'abs', outs3, sorted_q, vsel)
    out['bound'] = max([float(A[J].max()) for A in Fab if A.size] + [float(Eab[:, J].max())] + [0.0])
    out['F3'], out['E'] = [], []
    for p in primes:
        Fp, Ep, _ = modular_part(X, ('f', p), outs3, sorted_q, vsel)
        out['F3'].append([A[J].astype(np.int32) for A in Fp])
        out['E'].append(Ep[:, J].astype(np.int32))
        if verbose:
            print('  prime %d (%.0fs)' % (p, time.time() - t0), flush=True)
    return out


def assemble(X, chunks, nprimes, verbose=True):
    """Join chunk results: CRT over the first nprimes primes, check with the next one, rigorous bound check."""
    t0 = time.time()
    outs0 = [o for o in X.outs if o['cut'] == ()]
    outs3 = [o for o in X.outs if o['cut'] == (3,)]
    primes = chunks[0]['primes']
    assert all(c['primes'] == primes for c in chunks) and len(primes) > nprimes
    N = X.N
    nE = chunks[0]['E'][0].shape[0]
    F0 = [np.zeros((N, o['m'], o['m']), dtype=object) for o in outs0]
    vecs = {key: np.zeros(N, dtype=object) for key in chunks[0]['vecs']}
    res3 = [[np.zeros((N, o['m'], o['m']), dtype=np.int64) for o in outs3] for _ in primes]
    resE = [np.zeros((nE, N), dtype=np.int64) for _ in primes]
    seen = np.zeros(N, dtype=int)
    bound = 0.0
    for c in chunks:
        J = c['J']
        seen[J] += 1
        bound = max(bound, c['bound'])
        for i, A in enumerate(c['F0']):
            F0[i][J] = A
        for key in vecs:
            vecs[key][J] = c['vecs'][key]
        for pi in range(len(primes)):
            for i, A in enumerate(c['F3'][pi]):
                res3[pi][i][J] = A
            resE[pi][:, J] = c['E'][pi]
    assert (seen == 1).all(), 'chunks do not partition the variables'
    M = 1
    for p in primes[:nprimes]:
        M *= p
    assert 2 * bound * (1 + 1e-6) + 1 < M, 'CRT modulus too small for the bound'
    F3 = [crt_join([r[i] for r in res3[:nprimes]], primes[:nprimes]) for i in range(len(outs3))]
    E = crt_join(resE[:nprimes], primes[:nprimes])
    pchk = primes[nprimes]
    ok = all((np.array([int(v) % pchk for v in A.ravel()]).reshape(A.shape) == B).all() for A, B in zip(F3, res3[nprimes])) and \
        (np.array([int(v) % pchk for v in E.ravel()]).reshape(E.shape) == resE[nprimes]).all()
    if verbose:
        print('CRT: bound %.3e, modulus 2^%.1f, extra-prime check %s (%.0fs)' % (bound, math.log2(M), ok, time.time() - t0), flush=True)
    assert ok
    blocks = []
    for o, Fb in list(zip(outs0, F0)) + list(zip(outs3, F3)):
        if all(v == 0 for v in Fb.ravel()):
            continue
        sx, ax = X.site[o['cut']], X.aux[o['cut']]
        GV = apply_factors([sx.G[i] for i in o['st']] + [np.eye(ax.dims[o['ai']], dtype=np.int64)], o['V'])
        met = np.array([[float(v) for v in row] for row in o['V'].T.dot(GV)])      # natural metric V^T G V (whitening only)
        blocks.append(dict(cut=o['cut'], st=o['st'], ai=o['ai'], tau=o['tau'], m=o['m'], F=Fb, met=met))
    s0 = X.site[()]
    varmet = []
    for b in X.vars:
        dets = 1
        for i in b['st']:
            dets *= int(round(float(np.linalg.det(np.array(s0.G[i], dtype=float)))))
        GW = apply_factors([s0.Gadj[i] for i in b['st']] + [np.eye(b['dims'][-1], dtype=np.int64)], b['W'])
        Mv = np.array([[float(Fraction(int(v), dets)) for v in row] for row in b['W'].T.dot(GW)])   # W^T G^-1 W
        Sf = [np.array(S, dtype=float) for S in b['basis']]
        Gam = np.array([[np.trace(Mv @ A @ Mv @ B) for B in Sf] for A in Sf])
        varmet.append((b['off'], Gam))
    nz = np.array([any(v != 0 for v in row) for row in E])
    D = dict(k=X.k, N=N, E=E[nz], blocks=blocks, ca=vecs['ca'], cb=vecs['cb'], cab=vecs['cp'] - (vecs['ca'] + vecs['cb']) / 2,
             tr=vecs['tr'], den_phi=X.Phi[(3,)][1], bound=bound, nprimes=nprimes, varmet=varmet)
    if verbose:
        from collections import Counter
        print('exact data k=%d: N %d, E rows %d, blocks %d (%s) (%.0fs)' % (X.k, N, D['E'].shape[0], len(blocks),
              dict(Counter(b['cut'] for b in blocks)), time.time() - t0), flush=True)
    return D


NPRIMES = 8          # 8 primes below 2^20: CRT modulus ~2^160; the bound check in assemble() enforces sufficiency

if __name__ == '__main__':
    # single process:  python xbuild.py k (min|all) OUT.pkl
    # chunked:         python xbuild.py k (min|all) chunk CID NCH OUTDIR      then      python xbuild.py k (min|all) join NCH OUTDIR OUT.pkl
    k = int(sys.argv[1])
    sup, d = (sys.argv[2] + ':3').split(':')[:2]                                       # 'min' (d = 3) or e.g. 'min:4'
    d = int(d)
    t0 = time.time()
    X = XRelax(k, d=d, keep=SUPPORTS[sup], verbose=False)
    print('structure k=%d d=%d %s: N %d, %d variable blocks, %d output blocks (%.0fs)' % (k, d, sup, X.N, len(X.vars), len(X.outs),
          time.time() - t0), flush=True)
    primes = PRIMES20[:NPRIMES + 1]
    if sys.argv[3] == 'chunk':
        cid, nch, outdir = int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        vsel = set(bi for bi in range(len(X.vars)) if bi % nch == cid)
        res = chunk_compute(X, vsel, primes, verbose=True)
        pickle.dump(res, open(os.path.join(outdir, 'chunk_%03d.pkl' % cid), 'wb'), protocol=4)
        print('chunk %d/%d done: %d variables (%.0fs)' % (cid, nch, len(res['J']), time.time() - t0), flush=True)
    elif sys.argv[3] == 'join':
        nch, outdir, out = int(sys.argv[4]), sys.argv[5], sys.argv[6]
        chunks = [pickle.load(open(os.path.join(outdir, 'chunk_%03d.pkl' % c), 'rb')) for c in range(nch)]
        D = assemble(X, chunks, NPRIMES)
        D['sup'], D['d'] = sup, d
        pickle.dump(D, open(out, 'wb'), protocol=4)
    else:
        res = chunk_compute(X, set(range(len(X.vars))), primes)
        D = assemble(X, [res], NPRIMES)
        D['sup'], D['d'] = sup, d
        pickle.dump(D, open(sys.argv[3], 'wb'), protocol=4)
        print('done (%.0fs)' % (time.time() - t0), flush=True)
