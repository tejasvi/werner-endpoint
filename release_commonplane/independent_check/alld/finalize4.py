"""Exactness argument for the verdict-1 builds (CRT bounds), from the compare4 logs and the abs-bound passes.
cut (3,): residues of deg_b! M_b(d) and P_b(d) agree modulo every prime used; |deg_b! M_b(d)| <= 8! Bm(d) (abs pass:
'abs20' bounds every d <= 20, 'absinf' the limit) and |P_b(d)| <= sum_j max|coef_b[j]| d^(deg_b - j); equality follows when
prod p > both bounds summed.  Equality rows: the same row of mine is matched modulo every prime, and the cross products
E[e,i] St[r,i0] - E[e,i0] St[r,i] are below prod p / 2 in absolute value, so the rows are exactly proportional."""
import sys
import re
import glob
import math
import pickle
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np

W_ = '<ROOT>/independent_check/alld/'
mag = pickle.load(open(W_ + 'work/xpoly_mag.pkl', 'rb'))


def absmax(tag):
    m3 = ms = 0.0
    for fn in sorted(glob.glob(W_ + 'work/e_%s_c*.pkl' % tag)):
        R = pickle.load(open(fn, 'rb'))
        for dct in R['F3'].values():
            for A in dct.values():
                m3 = max(m3, float(A.max()))
        for A in R['ST'].values():
            ms = max(ms, float(A.max()))
    return math.ceil(m3 * (1 + 1e-9)) + 1, math.ceil(ms * (1 + 1e-9)) + 1


B20 = absmax('abs20')
Binf = absmax('absinf')
for dspec in ('inf', '14', '20'):
    logs = sorted(glob.glob(W_ + 'logs/compare4_*_%s.log' % dspec))
    primes, ok3, okE = [], True, True
    for fn in logs:
        txt = open(fn).read()
        p = int(re.search(r'p=(\d+) cut', txt).group(1))
        primes.append(p)
        mm = re.search(r'cut\(3,\): (\d+) \(block,coord\) pairs compared, (\d+) mismatches; absent-from-xpoly blocks with nonzero mine: (\d+); deg != 2F_t: (\d+)', txt)
        ok3 &= mm is not None and mm.group(2) == '0' and mm.group(3) == '0' and mm.group(4) == '0'
        me = re.search(r'E rows: (\d+) rows, zero (\d+), without a proportional row of mine (\d+)', txt)
        if me:
            okE &= me.group(3) == '0'
    Pm = math.prod(primes)
    Bm = (Binf if dspec == 'inf' else B20)[0] * math.factorial(8)
    if dspec == 'inf':
        Bp = max(v[0] for v in mag['mag'].values())
    else:
        d = int(dspec)
        Bp = max(sum(v[j] * d ** (len(v) - 1 - j) for j in range(len(v))) for v in mag['mag'].values())
    exact3 = ok3 and Pm > Bm + Bp
    line = 'd=%s: primes %d (prod 2^%d); cut(3,) all-zero mismatches %s; bound 8! Bm + Bp = 2^%d -> cut(3,) %s' % (
        dspec, len(primes), Pm.bit_length() - 1, ok3, (Bm + Bp).bit_length(), 'EXACT' if exact3 else 'NOT EXACT')
    st_files = sorted(glob.glob(W_ + 'work/ematch_*_%s.pkl' % dspec))
    if st_files:
        matches = [pickle.load(open(fn, 'rb')) for fn in st_files]
        same = all(m_ == matches[0] for m_ in matches)
        Bst = (Binf if dspec == 'inf' else B20)[1]
        BE = mag['Emag'][0] if dspec == 'inf' else sum(mag['Emag'][j] * int(dspec) ** (4 - j) for j in range(len(mag['Emag'])))
        Pst = math.prod(int(re.search(r'ematch_(\d+)_', fn).group(1)) for fn in st_files)
        exactE = okE and same and Pst > 2 * 2 * BE * Bst
        line += '; E rows proportional %s, same match across %d primes %s, cross-product bound 2^%d -> E rows %s' % (
            okE, len(st_files), same, (4 * BE * Bst).bit_length(), 'EXACT' if exactE else 'NOT EXACT')
    print(line)
