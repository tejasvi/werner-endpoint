"""Orbits of words under left and right replica permutations only (for physical-point moments).
Output work/lr_orbits.npz: lid (int32 per word), rep (min code), size, parent (full orbit id of the rep)."""
import sys
import time
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
from aud_common import *

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
w0, w1, w2, w3, u = decode_all()
W = [w0, w1, w2, w3]
maps = []
for g in [(1, 0, 2, 3), (1, 2, 3, 0), (3, 0, 1, 2)]:
    gi = PIDX[g]
    maps.append(encode(*[MUL[gi][x] for x in W], AUX_LEFT[gi][u]).astype(np.int32))
    maps.append(encode(*[MUL[x, gi] for x in W], AUX_RIGHT[gi][u]).astype(np.int32))
del w0, w1, w2, w3, u, W
lab = np.arange(NWORDS, dtype=np.int32)
while True:
    old = lab.copy()
    for m in maps:
        np.minimum(lab, lab[m], out=lab)
    lab = lab[lab]
    if np.array_equal(lab, old):
        break
for m in maps:
    assert np.array_equal(lab, lab[m])
reps, lid, size = np.unique(lab, return_inverse=True, return_counts=True)
oid = np.load('<ROOT>/independent_check/work/orbits.npz')['oid']
parent = oid[reps]
# every LR orbit lies inside one full orbit
assert np.array_equal(oid, parent[lid.ravel()])
log('LR orbits: %d (sizes %d..%d)' % (len(reps), size.min(), size.max()))
np.savez('<ROOT>/independent_check/work/lr_orbits.npz', lid=lid.astype(np.int32), rep=reps.astype(np.int64),
         size=size.astype(np.int64), parent=parent.astype(np.int64))
log('saved')
