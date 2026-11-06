"""Verdict 3, own check of the polynomial left-kernel certificate W(s) (xlk4.pkl) against the polynomial data (xpoly4.pkl).
Equations: 3 copies (a, b, ab) x N coordinates, targets (c_a, c_b, 2 c_ab); unknowns: lambda_c[r] for every equality row r
and Yhat_b (symmetric r_b x r_b) for the 514 active blocks, Z_b = N_b Yhat_b N_b^T (N_b from the limit certificate).
W^T A == 0 means, for every column w = (w_a, w_b, w_ab):
  (a) Ehat(s) w_c(s) == 0 for c = a, b, ab (all 8820 rows);
  (b) N_b^T [[F_b(w_a), F_b(w_ab)], [F_b(w_ab), F_b(w_b)]] N_b == 0, F_b(v) = sum_i v_i Fhat_b[i](s), every active block;
  (c) w(s) . (c_a, c_b, 2 c_ab)(s) == 0.
MODE 'exact': (c) as exact polynomial identities (Fractions), the copy order of the rows, deg W, rank W(0) = 119.
MODE 'modp P1 P2 ...': (a), (b) at the 17 points s = 1..17 in F_p (degree <= 16 identities, so 17 points give all
coefficients); with L = lcm of W denominators, the identities have integer coefficients bounded by B (printed), and
vanishing modulo primes with product > 2B proves them over Q."""
import sys
import math
import time
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
mode = sys.argv[1]
P = safeload.load('<ROOT>/certificates/alld/xpoly4.pkl')
Linf = safeload.load('<ROOT>/certificates/alld/xk4dinf_s2.pkl')
C = safeload.load(W_ + 'alld/bundle/xcert4inf.pkl')
LK = safeload.load(W_ + 'alld/bundle/xlk4.pkl')
N = P['N']
Wc = [np.asarray(Wj, dtype=object) for Wj in LK['coefs']]
q = Wc[0].shape[1]
assert all(Wj.shape == (3 * N, q) for Wj in Wc)
degW = max(j for j, Wj in enumerate(Wc) if any(x != 0 for x in Wj.ravel()))
tk = lambda t: None if t is None else tuple(t)
pk = {(b['cut'], tuple(b['st']), b['ai'], tk(b['tau'])): b for b in P['blocks']}
act = {}
for b, Nb in C['N'].items():
    lb = Linf['blocks'][b]
    act[b] = (pk[(lb['cut'], tuple(lb['st']), lb['ai'], tk(lb['tau']))], np.asarray(Nb, dtype=object))
log('loaded: N %d, q %d, deg W %d, active blocks %d' % (N, q, degW, len(act)))

if mode == 'exact':
    # (c) exact: integer-scaled polynomials
    def lcm_den(vals):
        d = 1
        for x in vals:
            d = d * Fraction(x).denominator // math.gcd(d, Fraction(x).denominator)
        return d
    tg = [[Fraction(x) for x in c] for c in P['c']['ca']], [[Fraction(x) for x in c] for c in P['c']['cb']], \
         [[2 * Fraction(x) for x in c] for c in P['c']['cab']]
    nl = len(tg[0])
    Dc = lcm_den([x for c in range(3) for l in range(nl) for x in tg[c][l]])
    Lw = lcm_den([x for Wj in Wc for x in Wj.ravel() if x != 0])
    Wi = [np.array([[int(Fraction(x) * Lw) for x in row] for row in Wj], dtype=object) for Wj in Wc[:degW + 1]]
    for order_name, perm in (('copy-major', np.arange(3 * N)), ('coordinate-major', np.array([3 * i + c for c in range(3) for i in range(N)]))):
        # target vector in the W row order: entry at row perm[c*N + i] is target_c[i]
        Tl = []
        for l in range(nl):
            v = np.zeros(3 * N, dtype=object)
            for c in range(3):
                for i in range(N):
                    v[perm[c * N + i]] = int(tg[c][l][i] * Dc)
            Tl.append(v)
        coef = {}
        for j in range(degW + 1):
            for l in range(nl):
                coef[j + l] = coef.get(j + l, 0) + Wi[j].T.dot(Tl[l])           # exact integers (object dot)
        bad = sum(1 for col in range(q) if any(int(coef[k][col]) != 0 for k in coef))
        log('(c) with %s rows: columns w with w(s).c(s) not identically 0: %d of %d (exact, degree <= %d)' % (order_name, bad, q, max(coef)))
    M0 = flint.fmpq_mat(3 * N, q, [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for x in Wc[0].ravel()])
    log('rank W(0) = %d (q = %d); W_9, W_10 zero: %s' % (M0.rank(), q, all(not any(x != 0 for x in Wc[j].ravel()) for j in range(degW + 1, len(Wc)))))
    sys.exit(0)

primes = [int(x) for x in sys.argv[2:]]
# integer bound B for the coefficients of (a), (b) after scaling W by L
L = 1
for Wj in Wc:
    for x in Wj.ravel():
        if x != 0:
            L = L * Fraction(x).denominator // math.gcd(L, Fraction(x).denominator)
mW = max(abs(int(Fraction(x) * L)) for Wj in Wc for x in Wj.ravel())
mE = max(max(abs(int(x)) for x in np.asarray(E, dtype=object).ravel()) for E in P['Ecoef'])
Ba = (degW + 1) * len(P['Ecoef']) * N * mE * mW
Bb = 0
for b, (pb, Nb) in act.items():
    colsum = max(sum(abs(int(Nb[r, c])) for r in range(Nb.shape[0])) for c in range(Nb.shape[1]))
    mF = max(max(abs(int(x)) for x in np.asarray(cj, dtype=object).ravel()) for cj in pb['coef'])
    Bb = max(Bb, (degW + 1) * len(pb['coef']) * 3 * N * mW * colsum * colsum * mF)
log('bounds: |coef (a)| <= 2^%d, |coef (b)| <= 2^%d; need prod p > 2^%d' % (Ba.bit_length(), Bb.bit_length(), (2 * max(Ba, Bb)).bit_length()))
pts = list(range(1, 18))
for p in primes:
    assert L % p != 0 and p < 2 ** 21
    Wm = []
    for Wj in Wc[:degW + 1]:
        A = np.zeros(Wj.shape, dtype=np.float64)
        for (r, c), x in np.ndenumerate(Wj):
            if x != 0:
                fx = Fraction(x)
                A[r, c] = (fx.numerator % p) * pow(fx.denominator % p, -1, p) % p
        Wm.append(A)
    Ws = {}
    for s in pts:
        acc = np.zeros_like(Wm[0])
        for j, A in enumerate(Wm):
            acc = np.fmod(acc + A * pow(s, j, p), p)
        Ws[s] = acc
    nza = 0
    Em = [np.mod(np.asarray(E, dtype=object), p).astype(np.float64) for E in P['Ecoef']]
    for s in pts:
        Es = np.zeros_like(Em[0])
        for l, E in enumerate(Em):
            Es = np.fmod(Es + E * pow(s, l, p), p)
        for c in range(3):
            R = np.fmod(Es @ Ws[s][c * N:(c + 1) * N], p)
            nza += int(np.count_nonzero(R))
    del Em
    nzb = 0
    for b, (pb, Nb) in act.items():
        m = pb['m']
        Cm = [np.mod(np.asarray(cj, dtype=object), p).astype(np.float64).reshape(N, m * m) for cj in pb['coef']]
        N1 = np.array(Nb[:m], dtype=np.float64)
        N2 = np.array(Nb[m:], dtype=np.float64)
        for s in pts:
            Fs = np.zeros_like(Cm[0])
            for j, cj in enumerate(Cm):
                Fs = np.fmod(Fs + cj * pow(s, j, p), p)
            G = [np.fmod(Ws[s][c * N:(c + 1) * N].T @ Fs, p).reshape(q, m, m) for c in range(3)]
            K = (np.einsum('ui,wuv,vj->wij', N1, G[0], N1) + np.einsum('ui,wuv,vj->wij', N2, G[1], N2)
                 + np.einsum('ui,wuv,vj->wij', N1, G[2], N2) + np.einsum('ui,wuv,vj->wij', N2, G[2], N1))
            nzb += int(np.count_nonzero(np.mod(np.rint(K), p)))
    log('prime %d: (a) nonzero residues %d, (b) nonzero residues %d  [17 points s = 1..17]' % (p, nza, nzb))
