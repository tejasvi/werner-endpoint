"""Mutation tests: each check must FAIL when the producer's data or certificate is altered in one place.
M1 D3: one cut-(3,) entry +1 (mod-p comparison, prime 1048573).   M2 D1: one c_a entry changed.
M3 D2: one E entry +1.   M4 identity: lam_n[0][3] + 1.   M5 PSD: dYn of one block x 10^4."""
import sys
import glob
import math
import pickle
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import flint
import safeload

W_ = '<ROOT>/independent_check/'
Dat = safeload.load(W_ + 'p1x/slice/xk4_min.pkl')
C = safeload.load(W_ + 'p1x/slice/xrat4min_q.pkl')
p = 1048573


def load_eng(tag):
    F3, ST = {}, {}
    for fn in sorted(glob.glob(W_ + 'work/eng_%s_c*.pkl' % tag)):
        R = pickle.load(open(fn, 'rb'))
        for bi, dct in R['F3'].items():
            F3.setdefault(bi, {}).update(dct)
        ST.update(R['ST'])
    return F3, ST


F3, ST = load_eng('p%d' % p)
# ---- M1
blocks3 = [bi for bi, b in enumerate(Dat['blocks']) if b['cut'] == (3,)]
bi0 = blocks3[40]
i0 = sorted(F3[bi0])[3]
nbad = 0
for bi in blocks3:
    F = Dat['blocks'][bi]['F']
    m = F.shape[1]
    for i in range(1331):
        prod = np.array([int(x) for x in F[i].ravel()], dtype=object).reshape(m, m)
        if (bi, i) == (bi0, i0):
            prod = prod.copy()
            prod[0, 0] += 1
        prod = (prod % p).astype(np.int64)
        mine = np.rint(F3[bi][i]).astype(np.int64) % p if i in F3[bi] else np.zeros((m, m), dtype=np.int64)
        nbad += not np.array_equal(mine, prod)
print('M1 (one cut-(3,) entry +1): mismatches %d (expect 1)' % nbad)
# ---- M2
yo = pickle.load(open(W_ + 'work/theta_obj.pkl', 'rb'))['y_obj']
ca = [Fraction(x) for x in Dat['ca']]
ca[5] += Fraction(1, 10 ** 9)
print('M2 (one c_a entry changed): mismatches %d (expect 1)' % sum(1 for a, b in zip(yo['a'], ca) if a != b))
# ---- M3
M = np.stack([np.rint(ST[i].reshape(-1)).astype(np.int64) % p for i in range(1331)], axis=1)
E = Dat['E']


def canon(row):
    nz = np.flatnonzero(row)
    inv = pow(int(row[nz[0]]), -1, p)
    return (int(nz[0]), (row * inv % p).tobytes())


keys = set(canon(r) for r in M)
row = np.array([int(x) for x in E[100]], dtype=object)
ok_orig = canon((row % p).astype(np.int64)) in keys
row2 = row.copy()
row2[7] += 1
ok_mut = canon((row2 % p).astype(np.int64)) in keys
print('M3 (one E entry +1): original row matched %s, mutated row matched %s (expect True, False)' % (ok_orig, ok_mut))
# ---- M4: the identity mutation is run by cert_check.py itself (argument mutlam; also mutY, mutdY)
D = int(C['D'])
print('M4: see cert_check.py mutlam / mutY / mutdY runs (logs/cert_check_mut*.log)')
# ---- M5 PSD with dYn x 10^8 on one block (x 10^4 keeps ||dY||/tau < 1, i.e. still a valid PD certificate)
b = sorted(C['N'])[10]
Yi, s = C['Yq'][b]
dY = np.asarray(C['dYn'][b], dtype=object) * 10 ** 8
Yf = np.array(Yi, dtype=float) / 2.0 ** int(s)
lmin = float(np.linalg.eigvalsh(Yf).min())
k = math.ceil(-math.log2(lmin / 2))
fro2 = sum(int(x) ** 2 for x in dY.ravel())
ok2 = fro2 < (D >> k) ** 2 if D % (1 << k) == 0 else fro2 * 4 ** k < D * D
print('M5 (dYn x 10^8 on block %d): Weyl bound ||dY||_F < tau holds: %s (expect False)' % (b, ok2))
