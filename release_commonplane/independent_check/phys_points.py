"""Physical-point checks (floating point, own pipeline).
For a random isometry A: C^2 -> (C^3)^{x4} and angle th: C_th = A M_th A^*/2, q4 = sum_J (-1/2)^|J| ||Tr_J C_th||_F^2.
Moments of the twirled X = L E_g (ga)^{x4}(ga)^{x4*}:  g_o = Tr(V_o^T X) = L Re sum_{w in o} <psi|V_w|psi>, psi = a^{x4},
evaluated on left/right-orbit representatives.  x = G^+ g (orbit-sum coordinates).  Checks:
  (i)  my objective C(x) = q4; trace = 1;
  (ii) producer coordinates y from the cut-() Gram forms H_{st,ai}(X) = J^T X J (W-fit residual), then
       c_th . y = q4, E y = 0, every F_b(y) PSD, and the certificate value lambda(th).E_r y + sum_b <m^T Z_b m, F_b(y)>.
usage: phys_points.py SEED NPOINTS [theta ...]"""
import sys
import time
import pickle
import itertools
from fractions import Fraction
sys.path.insert(0, '<ROOT>/independent_check')
import numpy as np
import safeload
from aud_common import *

t0 = time.time()
log = lambda s: print('[%.1fs] %s' % (time.time() - t0, s), flush=True)
W_ = '<ROOT>/independent_check/'
d = 3
L = float((2 * d ** 4) ** 4)
O = np.load(W_ + 'work/orbits.npz')
oid = O['oid']
LR = np.load(W_ + 'work/lr_orbits.npz')
GO = pickle.load(open(W_ + 'work/gram_obj.pkl', 'rb'))
G = np.array(GO['G'], dtype=np.float64)
C00 = np.array([float(x) for x in GO['C00']]); C11 = np.array([float(x) for x in GO['C11']])
C01 = np.array([float(x) for x in GO['C01']]); TRv = np.array([float(x) for x in GO['TR']])
S = safeload.load(W_ + 'pkt/struct_k4d3_min.pkl')
Dat = safeload.load(W_ + 'p1x/slice/xk4_min.pkl')
Cert = safeload.load(W_ + 'p1x/slice/xrat4min_q.pkl')
LOC = pickle.load(open(W_ + 'work/local.pkl', 'rb'))
N = 1331
ca = np.array([float(x) for x in Dat['ca']]); cb = np.array([float(x) for x in Dat['cb']]); cab = np.array([float(x) for x in Dat['cab']])
E = np.array(Dat['E'], dtype=np.float64)
Fb = [np.array(b['F'], dtype=np.float64) for b in Dat['blocks']]
# certificate Z_b in floats (Yhat + dYn/D), lambda in floats
Dc = int(Cert['D'])
Zf = {}
for b in Cert['N']:
    Nb = np.array(Cert['N'][b], dtype=np.float64)
    Yi, s = Cert['Yq'][b]
    # full relative precision (dY is tiny but meets large cut-(3,) entries)
    Mf = np.array(Yi, dtype=np.float64) / 2.0 ** int(s) + np.array([[float(Fraction(int(x), Dc)) for x in row] for row in np.asarray(Cert['dYn'][b], dtype=object)], dtype=np.float64)
    Zf[b] = Nb @ Mf @ Nb.T
lamf = [np.array([float(Fraction(int(x), Dc)) for x in Cert['lam_n'][c]], dtype=np.float64) for c in range(3)]
Er = E[[int(e) for e in Cert['erows']]]

# local Gram-form matrices A_lam[p] = J^T V_p J (cut ())
VP = [perm_matrix(d, p) for p in PERMS]
Aloc = {lam: np.array([(LOC['site'][((), lam)]['J'].T @ VP[p] @ LOC['site'][((), lam)]['J']).ravel() for p in range(24)], dtype=np.float64)
        for lam in range(4)}                                   # (24, f^2)
ab0 = LOC['aux']['blocks'][()]
aux_units = {ai: [AIDX[(BIDX[tuple(r)], BIDX[tuple(s)])] for r in ab0[ai] for s in ab0[ai]] for ai in range(5)}
f0 = [LOC['site'][((), l)]['f'] for l in range(4)]
a0 = [len(b) for b in ab0]
# words of the LR representatives
reps = LR['rep']
u_r = reps % NA
rest = reps // NA
w_r = []
for _ in range(4):
    w_r.append(rest % NP)
    rest = rest // NP
w_r = w_r[::-1]
letters = 'abcdefghijklmnop'
Yidx = [[letters[4 * k + l] for l in range(4)] for k in range(4)]


def moments(a5):
    """a5[x0,x1,x2,x3,q] = A/sqrt2.  Returns g (1633) = L Re sum_{w in o} <psi|V_w (x) E_u|psi>."""
    a_q = [a5[..., 0], a5[..., 1]]
    ac_q = [np.conj(a5[..., 0]), np.conj(a5[..., 1])]
    vals = np.zeros(len(reps))
    path_cache = {}
    for t in range(len(reps)):
        ws = [PERMS[int(w_r[l][t])] for l in range(4)]
        r, s = AUX[int(u_r[t])]
        rb, sb = BITS[r], BITS[s]
        ops, subs = [], []
        for k in range(4):
            ops.append(ac_q[rb[k]])
            subs.append(''.join(Yidx[k]))
        for k in range(4):
            ops.append(a_q[sb[k]])
            subs.append(''.join(Yidx[ws[l][k]][l] for l in range(4)))
        expr = ','.join(subs) + '->'
        if expr not in path_cache:
            path_cache[expr] = np.einsum_path(expr, *ops, optimize='greedy')[0]
        vals[t] = np.einsum(expr, *ops, optimize=path_cache[expr]).real
    g = np.bincount(LR['parent'], weights=vals * LR['size'], minlength=len(O['rep'])) * L
    return g


def q4(Cm):
    T = Cm.reshape([3] * 8)
    tot = 0.0
    letters_r, letters_c = 'abcd', 'efgh'
    for J in itertools.product((0, 1), repeat=4):
        cols = ''.join(letters_r[l] if J[l] else letters_c[l] for l in range(4))
        outs = ''.join(letters_r[l] + letters_c[l] for l in range(4) if not J[l])
        TJ = np.einsum(letters_r + cols + '->' + outs, T)
        tot += (-0.5) ** sum(J) * float(np.sum(np.abs(TJ) ** 2))
    return tot


def producer_y(x):
    xt = x[oid].reshape(NP, NP, NP, NP, NA)
    y = np.zeros(N)
    worst = 0.0
    for v in S['variables']:
        st, ai, off = tuple(v['st']), v['ai'], v['off']
        T = xt[..., aux_units[ai]]                        # (24,24,24,24, a^2)
        for l in range(4):
            T = np.moveaxis(np.tensordot(T, Aloc[st[l]], axes=([l], [0])), -1, l)
        shape = [f0[s_] for s_ in st] + [a0[ai]]
        Tt = T.reshape([z for s_ in shape for z in (s_, s_)])
        H = Tt.transpose([2 * l for l in range(5)] + [2 * l + 1 for l in range(5)]).reshape(int(np.prod(shape)), -1)
        Wm = np.array(v['W'], dtype=np.float64)
        Amat = np.array([(Wm @ np.array(B, dtype=np.float64) @ Wm.T).ravel() for B in v['basis']]).T
        sol, *_ = np.linalg.lstsq(Amat, H.ravel(), rcond=None)
        res = np.linalg.norm(Amat @ sol - H.ravel()) / max(1e-300, np.linalg.norm(H.ravel()))
        worst = max(worst, res)
        y[off:off + len(sol)] = sol
    return y, worst


def check_point(A, th):
    """A: 81 x 2 isometry, th: angle.  Returns (q4 direct, my C(x), producer c.y, certificate value, diagnostics)."""
    Mth = np.sqrt(2) * np.diag([np.cos(th), np.sin(th)])
    Cm = A @ Mth @ A.conj().T / 2
    qd = q4(Cm)
    a5 = (A / np.sqrt(2)).reshape(3, 3, 3, 3, 2)
    g = moments(a5)
    x, *_ = np.linalg.lstsq(G, g, rcond=None)
    gres = np.linalg.norm(G @ x - g) / np.linalg.norm(g)
    c, s_ = np.cos(th), np.sin(th)
    cmine = c * c * (C00 @ x) + s_ * s_ * (C11 @ x) + 2 * s_ * c * (C01 @ x)
    y, wres = producer_y(x)
    cprod = c * c * (ca @ y) + s_ * s_ * (cb @ y) + 2 * s_ * c * (cab @ y)
    Ey = np.linalg.norm(E @ y) / (np.linalg.norm(E) * np.linalg.norm(y))
    mineig = 1.0
    for bi, F in enumerate(Fb):
        Fy = np.tensordot(y, F, axes=(0, 0))
        ev = np.linalg.eigvalsh((Fy + Fy.T) / 2)
        sc = max(1e-300, np.abs(ev).max())
        mineig = min(mineig, ev.min() / sc)
    mvec = np.array([c, s_])
    certval = (c * c * lamf[0] + s_ * s_ * lamf[1] + s_ * c * lamf[2]) @ (Er @ y)
    for b, Zb in Zf.items():
        m = Fb[b].shape[1]
        Zt = c * c * Zb[:m, :m] + s_ * s_ * Zb[m:, m:] + s_ * c * (Zb[:m, m:] + Zb[m:, :m])
        certval += float(np.sum(Zt * np.tensordot(y, Fb[b], axes=(0, 0))))
    log('theta %+.4f: q4 %+.6e | mine C(x) %+.6e, trace %.12f, G-res %.1e | producer c.y %+.6e, W-fit res %.1e, |Ey|rel %.1e, '
        'min rel eig F_b(y) %+.1e, cert value %+.6e' % (th, qd, cmine, TRv @ x, gres, cprod, wres, Ey, mineig, certval))
    return qd, cmine, cprod, certval


if __name__ == '__main__':
    seed, npts = int(sys.argv[1]), int(sys.argv[2])
    thetas_fixed = [float(x) for x in sys.argv[3:]]
    rng = np.random.default_rng(seed)
    thetas = thetas_fixed + list(rng.uniform(0, 2 * np.pi, size=max(0, npts - len(thetas_fixed))))
    for th in thetas:
        Z = rng.normal(size=(81, 2)) + 1j * rng.normal(size=(81, 2))
        A, _ = np.linalg.qr(Z)
        check_point(A, th)
