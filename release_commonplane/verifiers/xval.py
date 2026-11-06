"""Validate exact-coordinate data (xbuild.py) against the numeric build: same SDP optimum at several theta (same support).
Usage: python xval.py XPICKLE NUMERIC_DM_PICKLE (min|all)"""
import sys, os, math, pickle, time
import numpy as np
SLICE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SLICE)
from eqface import eq_face
from dual_extract import solve_dual


def isqrt_psd(M):
    w, Q = np.linalg.eigh((M + M.T) / 2)
    return (Q / np.sqrt(w)) @ Q.T


def to_float(D, white=False):
    """Float SDP data from exact data.  Each block: F_float_b(y') = s_b T_b^T F_b(P y') T_b with T_b = (V^T G V)^(-1/2) (natural
    metric) and P = blockdiag(Gamma_b^(-1/2)) on the variables if white, else T_b = I, P = I; s_b > 0 normalises the block.
    A dual Z (float coordinates) maps to the exact block coordinates as s_b T_b Z T_b^T; equality rows are rescaled."""
    N = D['N']
    P = np.eye(N)
    if white:
        for off, Gam in D['varmet']:
            n = Gam.shape[0]
            P[off:off + n, off:off + n] = isqrt_psd(Gam)
    E = np.array([[float(v) for v in row] for row in D['E']]) @ P
    E = E / np.abs(E).max(axis=1, keepdims=True)
    blocks, Ts, ss = [], [], []
    for b in D['blocks']:
        Fb = np.array([float(v) for v in b['F'].ravel()]).reshape(b['F'].shape)
        T = isqrt_psd(b['met']) if white else np.eye(b['m'])
        Fb = np.einsum('ka,iab,bl->ikl', T, Fb, T, optimize=True)
        if white:
            for off, Gam in D['varmet']:
                n = Gam.shape[0]
                Fb[off:off + n] = np.einsum('ji,jab->iab', P[off:off + n, off:off + n], Fb[off:off + n])
        # natural scale when whitened (cut-(3,) blocks carry the factor den_phi^k); otherwise normalise the block
        if white:
            s = b['nat'] if 'nat' in b else (1.0 / float(D['den_phi']) ** D['k'] if b['cut'] == (3,) else 1.0)
        else:
            s = 1.0 / np.abs(Fb).max()
        blocks.append(dict(cut=b['cut'], st=b['st'], ai=b['ai'], q=b['tau'], m=b['m'], F=s * Fb))
        Ts.append(T); ss.append(s)
    fl = lambda v: P.T @ np.array([float(x) for x in v])
    return dict(N=N, E=E, blocks=blocks, tr=fl(D['tr']), ca=fl(D['ca']), cb=fl(D['cb']), cab=fl(D['cab']), T=Ts, s=ss, P=P)


if __name__ == '__main__':
    t0 = time.time()
    Dx = to_float(pickle.load(open(sys.argv[1], 'rb')), white=True)
    Dn = pickle.load(open(sys.argv[2], 'rb'))
    if sys.argv[3] == 'min':
        Dn = dict(Dn); Dn['blocks'] = [b for b in Dn['blocks'] if b['cut'] == () or (b['cut'] == (3,) and all(s >= 2 for s in b['st']))]
    key = lambda th: min(Dn['cM'].keys(), key=lambda x: abs(x - th))
    for th in (0.0, math.pi / 4, -math.pi / 4, math.pi / 2, math.pi / 6):
        c = math.cos(th) ** 2 * Dx['ca'] + math.sin(th) ** 2 * Dx['cb'] + 2 * math.sin(th) * math.cos(th) * Dx['cab']
        D2, _ = eq_face(dict(Dx, c=c), verbose=False)
        rx = solve_dual(D2)
        kk = key(th)
        D2n, _ = eq_face(dict(Dn, c=Dn['cM'][kk]), verbose=False)
        rn = solve_dual(D2n)
        print('theta %+.4f (numeric key %+.4f): exact-coord %s %+.6e / %+.6e | numeric %s %+.6e / %+.6e (%.0fs)' % (
            th, kk, rx['status'], rx['primal'], rx['dual'], rn['status'], rn['primal'], rn['dual'], time.time() - t0), flush=True)
