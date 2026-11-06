"""All-theta (doubled) SDP in exact coordinates: numerical solve on the equality-implied face (CVXOPT), dual blocks mapped
back to the unscaled exact block coordinates: Zx_b = s_b Vk_b Z_b Vk_b^T (s_b = float scaling of block b, Vk_b = face basis,
doubled: Vk_b (+) Vk_b).  Usage: python xatd.py XPICKLE OUTPREFIX"""
import sys, os, math, pickle, time
import numpy as np
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from eqface import eq_face
from dual_extract import solve_dual
from xval import to_float

if __name__ == '__main__':
    t0 = time.time()
    Dex = pickle.load(open(sys.argv[1], 'rb'))
    out = sys.argv[2]
    D = to_float(Dex, white=True)
    N = D['N']
    D2, info = eq_face(dict(D, c=D['ca']), verbose=True)
    # face bases per block (recomputed: eq_face keeps only the compressed F); same SVD as eq_face
    U, s, Vt = np.linalg.svd(D['E'], full_matrices=True)
    r = int((s > s.max() * 1e-10).sum())
    Znull = Vt[r:].T
    Vks = []
    for b in D['blocks']:
        n = b['m']
        SZ = np.einsum('ij,ikl->jkl', Znull, b['F']).reshape(-1, n)
        u_, sv, vt = np.linalg.svd(SZ, full_matrices=False)
        rk = int((sv > 1e-9 * sv.max()).sum())
        Vks.append(vt[:rk].T)
    assert [V.shape[1] for V in Vks if V.shape[1]] == [b['m'] for b in D2['blocks']]
    E = D2['E']
    Eb = np.zeros((3 * E.shape[0], 3 * N))
    for i in range(3):
        Eb[i * E.shape[0]:(i + 1) * E.shape[0], i * N:(i + 1) * N] = E
    blocks, owners = [], []
    for j, (b, Vk) in enumerate(zip(D['blocks'], Vks)):
        n = Vk.shape[1]
        if n == 0:
            continue
        Fr = np.einsum('ja,ijk,kb->iab', Vk, b['F'], Vk, optimize=True)
        Fb = np.zeros((3 * N, 2 * n, 2 * n))
        Fb[:N, :n, :n] = Fr; Fb[N:2 * N, n:, n:] = Fr; Fb[2 * N:, :n, n:] = Fr; Fb[2 * N:, n:, :n] = np.transpose(Fr, (0, 2, 1))
        blocks.append(dict(m=2 * n, F=Fb)); owners.append(j)
    Db = dict(N=3 * N, E=Eb, tr=np.concatenate([D['tr'], D['tr'], np.zeros(N)]),
              c=np.concatenate([D['ca'], D['cb'], 2 * D['cab']]), blocks=blocks)
    print('all-theta exact coords: vars %d, blocks %d, max block %d (%.0fs)' % (3 * N, len(blocks), max(b['m'] for b in blocks),
          time.time() - t0), flush=True)
    res = solve_dual(Db)
    print('RESULT all-theta (exact coords) %s primal %+.4e dual %+.4e (%.0fs)' % (res['status'], res['primal'], res['dual'],
          time.time() - t0), flush=True)
    Zx = {}
    for j, Zr in zip(owners, res['Z']):
        Vk = Vks[j]
        V2 = np.zeros((2 * Vk.shape[0], 2 * Vk.shape[1]))
        V2[:Vk.shape[0], :Vk.shape[1]] = Vk; V2[Vk.shape[0]:, Vk.shape[1]:] = Vk
        T = D['T'][j]
        T2 = np.zeros((2 * T.shape[0], 2 * T.shape[1]))
        T2[:T.shape[0], :T.shape[1]] = T; T2[T.shape[0]:, T.shape[1]:] = T
        Zx[j] = D['s'][j] * T2 @ V2 @ Zr @ V2.T @ T2.T
    pickle.dump(dict(status=res['status'], primal=res['primal'], dual=res['dual'], Zx=Zx, Vks=Vks),
                open(out + '_xsol.pkl', 'wb'), protocol=4)
