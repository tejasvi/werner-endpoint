"""Closing the verdict-1 caveat: the producer's polynomial data equal the interpolation of MY builds.
Per point (d finite, or 'inf' = leading coefficients) the compare4 logs give: cut-(3,) residues deg_b! M_b(d) == P_b(d) for
every prime used, and (if the Stiefel part was kept) every producer equality row proportional to my row ematch[r] for every
prime.  Exactness per point: prod p > 8! Bm(d) + Bp(d) (blocks; Bm from the abs pass covering d), and prod p > 4 BE(d) Bst(d)
(rows; cross products), with the same matched row for all primes.
Polynomial identity: T_b(d) (mine) and P_b(d)/(deg_b! 576^4) (producer) have degree <= deg_b <= 8; equal leading coefficients
('inf') and equality at 8 distinct finite d force identity.  Rows: E_r(d) and my St_r'(d) have degree <= 4; every 2x2 minor
E_r[i] St_r'[j] - E_r[j] St_r'[i] has degree <= 8, vanishing leading coefficient ('inf') and 8 finite roots, so it vanishes
identically: E_r(d) is proportional to my Stiefel row r' at every d (same r' at every point).
usage: finalize5.py LOGDIR1 [LOGDIR2 ...]   (compare4 logs named compare4_<p>_<d>.log or cmp_<p>_<d>.log)"""
import sys
import re
import glob
import math
import pickle
import os

W_ = '<ROOT>/independent_check/alld/'
mag = pickle.load(open(W_ + 'work/xpoly_mag.pkl', 'rb'))


def absmax(tag):
    m3 = ms = 0.0
    files = sorted(glob.glob(W_ + 'work/e_%s_c*.pkl' % tag))
    assert len(files) == 4, (tag, files)
    for fn in files:
        R = pickle.load(open(fn, 'rb'))
        for dct in R['F3'].values():
            for A in dct.values():
                m3 = max(m3, float(A.max()))
        for A in R['ST'].values():
            ms = max(ms, float(A.max()))
    return math.ceil(m3 * (1 + 1e-9)) + 1, math.ceil(ms * (1 + 1e-9)) + 1


bounds = {'abs20': absmax('abs20'), 'absinf': absmax('absinf'), 'abs32': absmax('abs32')}
res = {}
for ld in sys.argv[1:]:
    for fn in glob.glob(os.path.join(ld, '*.log')):
        m = re.match(r'(?:compare4|cmp)_(\d+)_(\w+)\.log$', os.path.basename(fn))
        if not m:
            continue
        p, dspec = int(m.group(1)), m.group(2)
        txt = open(fn).read()
        mm = re.search(r'cut\(3,\): (\d+) \(block,coord\) pairs compared, (\d+) mismatches; absent-from-xpoly blocks with nonzero mine: (\d+); deg != 2F_t: (\d+)', txt)
        me = re.search(r'E rows: (\d+) rows, zero (\d+), without a proportional row of mine (\d+)', txt)
        ok3 = mm is not None and mm.group(1) == '269445' and mm.groups()[1:] == ('0', '0', '0')
        okE = None if me is None else (me.group(3) == '0' and me.group(2) == '0')
        r = res.setdefault(dspec, {})
        r[p] = (ok3, okE)
allmatch = {}
summary = []
exact_pts3, exact_ptsE = [], []
for dspec in sorted(res, key=lambda x: (x != 'inf', int(x) if x != 'inf' else 0)):
    r = res[dspec]
    P3 = math.prod(p for p, (o3, oE) in r.items() if o3)
    all3 = all(o3 for o3, oE in r.values())
    if dspec == 'inf':
        Bm, Bst = bounds['absinf']
        Bp = max(v[0] for v in mag['mag'].values())
        BE = mag['Emag'][0]
    else:
        d = int(dspec)
        Bm, Bst = bounds['abs20'] if d <= 20 else bounds['abs32']
        assert d <= 32
        Bp = max(sum(v[j] * d ** (len(v) - 1 - j) for j in range(len(v))) for v in mag['mag'].values())
        BE = sum(mag['Emag'][j] * d ** (4 - j) for j in range(len(mag['Emag'])))
    ex3 = all3 and P3 > math.factorial(8) * Bm + Bp
    line = 'd=%s: %d primes (2^%d), cut(3,) %s (need 2^%d)' % (dspec, len(r), P3.bit_length() - 1, 'EXACT' if ex3 else 'no', (math.factorial(8) * Bm + Bp).bit_length())
    if ex3:
        exact_pts3.append(dspec)
    pE = [p for p, (o3, oE) in r.items() if oE]
    if pE:
        files = [W_ + 'work/ematch_%d_%s.pkl' % (p, dspec) for p in pE]
        files = [f for f in files if os.path.exists(f)]
        matches = [pickle.load(open(f, 'rb')) for f in files]
        same = len(matches) == len(pE) and all(m_ == matches[0] for m_ in matches)
        PE = math.prod(pE)
        exE = same and all(oE for o3, oE in r.values() if oE is not None) and PE > 4 * BE * Bst
        line += '; E rows: %d primes (2^%d), same match %s, %s (need 2^%d)' % (len(pE), PE.bit_length() - 1, same, 'EXACT' if exE else 'no', (4 * BE * Bst).bit_length())
        if exE:
            exact_ptsE.append(dspec)
            allmatch[dspec] = matches[0]
    summary.append(line)
print('\n'.join(summary))
fin3 = [x for x in exact_pts3 if x != 'inf']
finE = [x for x in exact_ptsE if x != 'inf']
same_rows = len(set(tuple(m_) for m_ in allmatch.values())) == 1 if allmatch else False
print('blocks: exact at leading coefficient %s and %d finite d %s -> polynomial identity: %s' % (
    'inf' in exact_pts3, len(fin3), fin3, 'inf' in exact_pts3 and len(fin3) >= 8))
print('rows: exact proportionality at leading coefficient %s and %d finite d %s, same matched row at all these points %s -> identity: %s' % (
    'inf' in exact_ptsE, len(finE), finE, same_rows, 'inf' in exact_ptsE and len(finE) >= 8 and same_rows))
