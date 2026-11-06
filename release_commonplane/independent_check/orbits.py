"""Orbits of words (w_0..w_3, u) under: left and right replica permutations (all factors at once),
permutations of the 4 site components, and transposition (w -> w^-1, |r><s| -> |s><r|).
Output work/orbits.npz: oid (int32 per word code), rep (min code per orbit), size."""
import sys
import time
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
from aud_common import *

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)

w0, w1, w2, w3, u = decode_all()
W = [w0, w1, w2, w3]
log('decoded %d words' % NWORDS)

GENS = [(1, 0, 2, 3), (1, 2, 3, 0), (3, 0, 1, 2)]          # S4 generators (+ inverse of the 4-cycle)
maps = []
for g in GENS:
    gi = PIDX[g]
    maps.append(encode(*[MUL[gi][x] for x in W], AUX_LEFT[gi][u]).astype(np.int32))
    maps.append(encode(*[MUL[x, gi] for x in W], AUX_RIGHT[gi][u]).astype(np.int32))
maps.append(encode(*[INV[x] for x in W], AUX_T[u]).astype(np.int32))
maps.append(encode(w1, w0, w2, w3, u).astype(np.int32))          # site transposition (01)
maps.append(encode(w1, w2, w3, w0, u).astype(np.int32))          # site 4-cycle
maps.append(encode(w3, w0, w1, w2, u).astype(np.int32))          # its inverse
del w0, w1, w2, w3, u, W
log('built %d maps' % len(maps))

# each map must be a permutation of the word set
for m in maps:
    assert np.bincount(m, minlength=NWORDS).max() == 1
log('maps are bijections')

lab = np.arange(NWORDS, dtype=np.int32)
it = 0
while True:
    it += 1
    old = lab.copy()
    for m in maps:                      # the map set is closed under inverses, so forward pulls suffice
        np.minimum(lab, lab[m], out=lab)
    lab = lab[lab]
    ch = int(np.count_nonzero(lab != old))
    log('iteration %d: changed %d' % (it, ch))
    if ch == 0:
        break

# verify closure: label constant along every map
for m in maps:
    assert np.array_equal(lab, lab[m])
reps, oid, size = np.unique(lab, return_inverse=True, return_counts=True)
log('orbits: %d; size min %d max %d; sum %d' % (len(reps), size.min(), size.max(), size.sum()))
np.savez('<ROOT>/independent_check/work/orbits.npz', oid=oid.astype(np.int32),
         rep=reps.astype(np.int64), size=size.astype(np.int64))
log('saved')
