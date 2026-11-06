"""D3 for cut (3,): compare 192^4 * V_b^T H'_b(B_i) V_b (mine, mod p) with the producer's stored F_b[i] (mod p),
for all 86 cut-(3,) outputs and all i, for each prime given; then the exactness argument with the abs bounds:
equal mod P = prod p, and |mine| <= Bm, |prod| <= Bp with P > Bm + Bp  =>  equal as integers.
usage: compare_d3.py p1 [p2 ...]"""
import sys
import glob
import math
import pickle
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload

W_ = '<ROOT>/independent_check/'
D = safeload.load(W_ + 'p1x/slice/xk4_min.pkl')
primes = [int(x) for x in sys.argv[1:]]


def load_mode(tag):
    F3, ST = {}, {}
    files = sorted(glob.glob(W_ + 'work/eng_%s_c*.pkl' % tag))
    assert len(files) == 3, files
    vars_seen = []
    for fn in files:
        R = pickle.load(open(fn, 'rb'))
        vars_seen += R['vars']
        for bi, dct in R['F3'].items():
            F3.setdefault(bi, {}).update(dct)
        ST.update(R['ST'])
    assert sorted(vars_seen) == list(range(150))
    return F3, ST


F3abs, _ = load_mode('abs')
blocks3 = [bi for bi, b in enumerate(D['blocks']) if b['cut'] == (3,)]
Bm = 0.0
Bp = 0
for bi in blocks3:
    F = D['blocks'][bi]['F']
    Bp = max(Bp, max(abs(int(x)) for x in F.ravel()))
    for i, A in F3abs[bi].items():
        Bm = max(Bm, float(A.max()))
Bm_int = math.ceil(Bm * (1 + 1e-9)) + 1
print('bounds: |mine| <= %.3e (%d bits), |prod| <= %.3e (%d bits)' % (Bm_int, Bm_int.bit_length(), Bp, Bp.bit_length()))
P = 1
for p in primes:
    F3, _ = load_mode('p%d' % p)
    nbad = ncmp = nmiss = 0
    for bi in blocks3:
        F = D['blocks'][bi]['F']
        m = F.shape[1]
        for i in range(1331):
            prod = np.array([int(x) % p for x in F[i].ravel()], dtype=np.int64).reshape(m, m)
            if i in F3[bi]:
                mine = np.rint(F3[bi][i]).astype(np.int64) % p
            else:
                mine = np.zeros((m, m), dtype=np.int64)
                nmiss += 1
            ncmp += 1
            if not np.array_equal(mine, prod):
                nbad += 1
                if nbad <= 5:
                    print('  mismatch p=%d block %d coord %d' % (p, bi, i))
    print('prime %d: %d (block, coordinate) pairs compared (%d with no contribution from B_i), %d mismatches' % (p, ncmp, nmiss, nbad))
    if nbad == 0:
        P *= p
print('product of matching primes: %d bits; needed > %d bits  ->  %s' % (
    P.bit_length(), (Bm_int + Bp).bit_length(), 'EXACT EQUALITY PROVED' if P > Bm_int + Bp else 'need more primes'))
