"""D2: every row of the producer's E (8820 x 1331) against my Stiefel coefficient functionals at the B_i.

Mine: St[(t,u), i] = 192^4 * 2 * coefficient of (x)_l V_{q_l} (x) E_u in S_0(B_i), t = sorted S3-word tuple (my S3 order),
u = aux unit (global AUX order).  Matching mod p: each producer row e must be proportional to exactly one of my rows
(zero rows matched to zero rows).  Exactness: cross products E[e,i] St[r,i0] - E[e,i0] St[r,i] vanish mod
P = prod p, and |.| <= 2 |E|max Bst < P  =>  exact proportionality; St[r,i0] != 0 mod p => nonzero.
usage: compare_d2.py p1 [p2 ...]"""
import sys
import glob
import math
import pickle
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload

W_ = '<ROOT>/independent_check/'
D = safeload.load(W_ + 'p1x/slice/xk4_min.pkl')
C = safeload.load(W_ + 'p1x/slice/xrat4min_q.pkl')
primes = [int(x) for x in sys.argv[1:]]
E = D['E']
NE = E.shape[0]


def load_st(tag):
    ST = {}
    files = sorted(glob.glob(W_ + 'work/eng_%s_c*.pkl' % tag))
    assert len(files) == 3
    for fn in files:
        ST.update(pickle.load(open(fn, 'rb'))['ST'])
    assert sorted(ST) == list(range(1331))
    M = np.stack([ST[i].reshape(-1) for i in range(1331)], axis=1)      # (8820, 1331)
    return M


Mabs = load_st('abs')
Bst = math.ceil(float(Mabs.max()) * (1 + 1e-9)) + 1
Emax = max(abs(int(x)) for x in E.ravel())
print('bounds: |St| <= 2^%d, |E| <= 2^%d; cross products < 2^%d' % (Bst.bit_length(), Emax.bit_length(), (2 * Emax * Bst).bit_length()))
zero_mine_exact = np.all(Mabs == 0, axis=1)          # abs bound 0  =>  exactly zero row
print('my rows identically zero (abs bound 0): %d of %d' % (int(zero_mine_exact.sum()), NE))

matches = {}
for p in primes:
    M = np.rint(load_st('p%d' % p)).astype(np.int64) % p
    Ep = np.array([[int(x) % p for x in row] for row in E], dtype=np.int64)

    def canon(R):
        keys = []
        for row in R:
            nz = np.flatnonzero(row)
            if len(nz) == 0:
                keys.append(None)
                continue
            inv = pow(int(row[nz[0]]), -1, p)
            keys.append((int(nz[0]), (row * inv % p).tobytes()))
        return keys
    km, ke = canon(M), canon(Ep)
    index = {}
    for r, k in enumerate(km):
        if k is not None:
            index.setdefault(k, []).append(r)
    unmatched = 0
    multi = 0
    m_p = {}
    for e, k in enumerate(ke):
        if k is None:
            m_p[e] = None
            continue
        rs = index.get(k, [])
        if len(rs) == 0:
            unmatched += 1
        elif len(rs) > 1:
            multi += 1
        if rs:
            m_p[e] = rs[0]
    nzE = sum(1 for k in ke if k is not None)
    nzM = sum(1 for k in km if k is not None)
    print('prime %d: nonzero rows E %d, mine %d; E rows without a proportional row of mine: %d; ambiguous %d'
          % (p, nzE, nzM, unmatched, multi))
    matches[p] = m_p
    # which of my rows are hit
    hit = set(r for r in m_p.values() if r is not None)
    print('   distinct rows of mine hit: %d' % len(hit))
# consistency of the matching across primes and the exact argument
same = all(matches[p] == matches[primes[0]] for p in primes)
P = math.prod(primes)
need = 2 * Emax * Bst
print('matching identical across primes: %s; P = 2^%d vs need 2^%d -> %s' % (
    same, P.bit_length(), need.bit_length(), 'EXACT' if P > need else 'need more primes'))
er = [int(x) for x in C['erows']]
print('certificate rows erows: %d; all matched to a Stiefel row: %s' % (
    len(er), all(matches[primes[0]].get(e) is not None for e in er)))
pickle.dump({'matches': matches[primes[0]], 'primes': primes}, open(W_ + 'work/d2_match.pkl', 'wb'), protocol=4)
