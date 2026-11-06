"""Verdict 1 data check: my S2 builds (engine4.py) against the producer's polynomial data xpoly4.pkl, modulo a prime.
cut (3,) block b (signature cut, st, ai, tau), coordinate i:
   producer at d:   P_b(d) = sum_j coef_b[j] d^(deg_b - j)   (= deg_b! 576^4 T_b(d) if correct);   at 'inf': coef_b[0]
   mine:            M_b(d) = 576^4 V_b^T H'_b(B_i) V_b   (engine4; at 'inf' the top-degree product, degree 2F_t)
   test:            P_b(d) == deg_b! M_b(d)  (mod p);  blocks absent from xpoly must be 0 in mine;  at 'inf' also deg_b == 2 F_t.
Equality rows (only for DSPECs whose engine run kept the Stiefel part): producer row r at d, sum_j Ecoef[j][r] d^(4-j)
(at 'inf': Ecoef[0][r]) must be proportional (mod p) to one of my Stiefel coefficient rows.
Also writes the exact per-block magnitude data needed for the CRT argument (alld/work/xpoly_mag.pkl, computed once).
usage: compare4.py PRIME DSPEC[:st] ...   (':st' = also compare equality rows)"""
import sys
import os
import glob
import math
import pickle
import time
W_ = os.environ.get('AUDIT_W', '<ROOT>/independent_check/')
sys.path.insert(0, W_)
import numpy as np
import safeload

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
p = int(sys.argv[1])
specs = [(a.split(':')[0], a.endswith(':st')) for a in sys.argv[2:]]
S = safeload.load(W_ + 'alld/bundle/struct_k4d4_s2.pkl')
P = safeload.load(os.environ.get('XPOLY', '<ROOT>/certificates/alld/xpoly4.pkl'))
log('xpoly4 loaded: %d blocks, N %d, DEN_PHI %s, nodes %s' % (len(P['blocks']), P['N'], P['DEN_PHI'], P['nodes']))
assert P['DEN_PHI'] == 576 and P['N'] == 1633
sig = {}
tk = lambda t: None if t is None else tuple(t)
for bi, o in enumerate(S['outputs']):
    key = (o['cut'], tuple(o['st']), o['ai'], tk(o['tau']))
    assert key not in sig, ('duplicate output signature', key)
    sig[key] = bi
print('outputs with tau None:', sum(1 for o in S['outputs'] if o['tau'] is None))
pblk = {}
for b in P['blocks']:
    key = (b['cut'], tuple(b['st']), b['ai'], tk(b['tau']))
    assert key in sig, key
    pblk[sig[key]] = b
outs3 = [bi for bi, o in enumerate(S['outputs']) if o['cut'] == (3,)]
Ft = {bi: sum(1 for x in S['outputs'][bi]['st'] if x in (3, 4)) for bi in outs3}
print('cut-(3,) outputs %d; present in xpoly %d; degrees %s' % (
    len(outs3), sum(1 for bi in outs3 if bi in pblk), sorted(set((pblk[bi]['deg'], 2 * Ft[bi]) for bi in outs3 if bi in pblk))))
magf = W_ + 'alld/work/xpoly_mag.pkl'
if not os.path.exists(magf):
    mag = {}
    for bi in outs3:
        if bi in pblk:
            mag[bi] = [max(abs(int(x)) for x in np.asarray(c, dtype=object).ravel()) for c in pblk[bi]['coef']]
    Emag = [max(abs(int(x)) for x in np.asarray(E, dtype=object).ravel()) for E in P['Ecoef']]
    pickle.dump({'mag': mag, 'Emag': Emag, 'deg': {bi: pblk[bi]['deg'] for bi in pblk}}, open(magf, 'wb'), protocol=4)
    log('magnitudes written to %s' % magf)
modc = {}
for bi in outs3:
    if bi in pblk:
        modc[bi] = [np.mod(np.asarray(c, dtype=object), p).astype(np.int64) for c in pblk[bi]['coef']]
log('producer cut-(3,) coefficients reduced mod p')


def load_mine(dspec):
    files = sorted(glob.glob(W_ + 'alld/work/e_p%d_%s_c*.pkl' % (p, dspec)))
    assert len(files) == 4, (dspec, files)
    F3, ST, seen = {}, {}, []
    for fn in files:
        R = pickle.load(open(fn, 'rb'))
        assert R['mode'] == str(p) and R['d'] == dspec
        seen += R['vars']
        for bi, dct in R['F3'].items():
            F3.setdefault(bi, {}).update(dct)
        ST.update(R['ST'])
    assert sorted(seen) == list(range(len(S['variables'])))
    return F3, ST


for dspec, do_st in specs:
    F3, ST = load_mine(dspec)
    nb = nz_absent = ndegbad = ncmp = 0
    for bi in outs3:
        m = len(S['outputs'][bi]['V'][0])
        if bi not in pblk:
            for i in range(1633):
                mine = np.mod(np.rint(F3[bi][i]), p).astype(np.int64) if i in F3[bi] else np.zeros((m, m), dtype=np.int64)
                nz_absent += int(mine.any())
            continue
        b = pblk[bi]
        deg = b['deg']
        if dspec == 'inf':
            if deg != 2 * Ft[bi]:
                ndegbad += 1
            prod = modc[bi][0]
        else:
            d = int(dspec)
            prod = np.zeros_like(modc[bi][0])
            for j, c in enumerate(modc[bi]):
                prod = (prod + c * pow(d, deg - j, p)) % p
        fac = math.factorial(deg) % p
        for i in range(1633):
            mine = np.mod(np.rint(F3[bi][i]), p).astype(np.int64) if i in F3[bi] else np.zeros((m, m), dtype=np.int64)
            ncmp += 1
            if not np.array_equal(mine * fac % p, prod[i] % p):
                nb += 1
                if nb <= 5:
                    log('  mismatch d=%s block %d coord %d' % (dspec, bi, i))
    log('RESULT d=%s p=%d cut(3,): %d (block,coord) pairs compared, %d mismatches; absent-from-xpoly blocks with nonzero mine: %d; '
        'deg != 2F_t: %d' % (dspec, p, ncmp, nb, nz_absent, ndegbad))
    if do_st:
        M = np.stack([np.mod(np.rint(ST[i].reshape(-1)), p).astype(np.int64) for i in range(1633)], axis=1)
        if dspec == 'inf':
            Ep = np.mod(np.asarray(P['Ecoef'][0], dtype=object), p).astype(np.int64)
        else:
            d = int(dspec)
            Ep = np.zeros((P['Ecoef'][0].shape[0], 1633), dtype=np.int64)
            for j, E in enumerate(P['Ecoef']):
                Ep = (Ep + np.mod(np.asarray(E, dtype=object), p).astype(np.int64) * pow(d, 4 - j, p)) % p
        assert all(int(x) == 4 for x in P['Edeg'])

        def canon(row):
            nzr = np.flatnonzero(row)
            if len(nzr) == 0:
                return None
            inv = pow(int(row[nzr[0]]), -1, p)
            return (int(nzr[0]), (row * inv % p).tobytes())
        keys = {}
        for r in range(M.shape[0]):
            k = canon(M[r])
            if k is not None:
                keys.setdefault(k, r)
        unmatched = sum(1 for r in range(Ep.shape[0]) if canon(Ep[r]) is not None and canon(Ep[r]) not in keys)
        zeroE = sum(1 for r in range(Ep.shape[0]) if canon(Ep[r]) is None)
        match = [keys.get(canon(Ep[r])) for r in range(Ep.shape[0])]
        pickle.dump(match, open(W_ + 'alld/work/ematch_%d_%s.pkl' % (p, dspec), 'wb'))
        log('RESULT d=%s p=%d E rows: %d rows, zero %d, without a proportional row of mine %d' % (dspec, p, Ep.shape[0], zeroE, unmatched))
