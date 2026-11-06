"""Common-plane slice b = (I (x) M) a with M = sqrt2 diag(cos th, sin th) (real diagonal, ||b|| = 1):
C = A M A^* / 2 = (cos th P_u + sin th P_v)/sqrt2.  th = pi/4: C = P_R/2 (b = a); th = -pi/4: C = (P_u - P_v)/2 (b = sigma_z a).

M breaks the U(2) twirl on the qubit Q to the torus (diagonal unitaries), so the auxiliary factor uses the torus commutant:
the 70 weight-preserving matrix units E_xy = |x><y| on (C^2)^{x4} (n1(x) = n1(y)); after a partial transpose on the replicas in
T they become charge-preserving units with charge c(z) = n1(z_{T^c}) - n1(z_T); blocks of sizes 1,4,6,4,1.  Site factors keep
the U(d) data of the original code.  Single family X_40 = twirl |aaaa><aaaa| (all objectives are M-insertions in it):
  objective  Tr[(Z_{t,03} (x) I_12) M_3 X_40 M_3] / L,  aux part  za[e] = Tr[(M_3 F_03 M_3) E_e];
  trace      Tr X_40 / L = 1;   Stiefel contrast at slot 0: aux map E -> E - (I_0/2) (x) Tr_0 E, sites: delete replica 0.
"""
import sys
import itertools
import math
import time
import pickle

import numpy as np

sys.path.insert(0, '<ROOT>/verifiers')
import relax as RX
from relax import Relaxation, LocalNum, P4, I4, SWAP03, invariant_sym_basis, orth_range, sorted_tuples, kron_all
from local import ncycles, compose, perms

RX.FAMILY_GROUP['40'] = list(P4)
RX.FAMILY_CUTS['40'] = [(), (3,), (2, 3)]
RX.FAMILIES = ('40',)

STR = list(itertools.product((0, 1), repeat=4))          # index of z = sum z_i 2^(3-i)  (z[0] most significant)
SIDX = {z: i for i, z in enumerate(STR)}
WORDS = [(x, y) for w in range(5) for x in STR if sum(x) == w for y in STR if sum(y) == w]   # 70 units
WIDX = {e: i for i, e in enumerate(WORDS)}


def perm_op(p):
    """16x16 matrix of V_p on (C^2)^{x4}: V_p sends tensor factor i to factor p[i]."""
    V = np.zeros((16, 16))
    for z in STR:
        zz = [None] * 4
        for i in range(4):
            zz[p[i]] = z[i]
        V[SIDX[tuple(zz)], SIDX[z]] = 1.0
    return V


def ptrans16(Mt, cut):
    out = np.zeros_like(Mt)
    for r in STR:
        for c in STR:
            r2 = tuple(c[i] if i in cut else r[i] for i in range(4))
            c2 = tuple(r[i] if i in cut else c[i] for i in range(4))
            out[SIDX[r], SIDX[c]] = Mt[SIDX[r2], SIDX[c2]]
    return out


class LocalTorus:
    """Same interface as relax.LocalNum, for the torus commutant on (C^2)^{x4} with a partial-transpose cut."""

    def __init__(self, cut):
        cut = tuple(sorted(cut))
        self.n, self.m, self.cut = 2, 4, cut
        charge = lambda z: sum(z[i] for i in range(4) if i not in cut) - sum(z[i] for i in range(4) if i in cut)
        self.labels = sorted(set(charge(z) for z in STR))
        self.blocks = [[z for z in STR if charge(z) == c] for c in self.labels]
        self.pos = {}
        for li, bl in enumerate(self.blocks):
            for j, z in enumerate(bl):
                self.pos[z] = (li, j)
        self.dims = [len(b) for b in self.blocks]
        self.off = [0]
        for d in self.dims:
            self.off.append(self.off[-1] + d * d)
        self.D = self.off[-1]
        self.P = perms(4)
        self.pi = []
        for li, bl in enumerate(self.blocks):
            idx = [SIDX[z] for z in bl]
            arr = []
            for p in self.P:
                Vt = ptrans16(perm_op(p), cut)
                full = Vt[np.ix_(idx, idx)]
                # block-diagonality check
                other = [SIDX[z] for z in STR if z not in bl]
                assert np.abs(Vt[np.ix_(idx, other)]).max() < 1e-12
                arr.append(full)
            self.pi.append(np.array(arr))
        # FT: word coefficients (70 units E_xy, untransposed) -> block coordinates of sum_e x_e E_e^{Gamma_cut}
        self.FT = np.zeros((self.D, len(WORDS)))
        for e, (x, y) in enumerate(WORDS):
            x2 = tuple(y[i] if i in cut else x[i] for i in range(4))
            y2 = tuple(x[i] if i in cut else y[i] for i in range(4))
            (li, i1), (lj, j1) = self.pos[x2], self.pos[y2]
            assert li == lj
            self.FT[self.off[li] + i1 * self.dims[li] + j1, e] = 1.0
        if not cut:
            self.IF = self.FT.T.copy()

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


def unit16(e):
    x, y = WORDS[e]
    Mt = np.zeros((16, 16)); Mt[SIDX[x], SIDX[y]] = 1.0
    return Mt


class RelaxM(Relaxation):
    def __init__(self, k, d, verbose=True):
        self.k, self.d = k, d
        self.L = float((2 * d ** k) ** 4)
        self.verbose = verbose
        self.gram = False
        self.cuts = RX.FAMILY_CUTS
        self.loc = {}
        for c in RX.FAMILY_CUTS['40']:
            self.loc['s', c] = LocalNum(d, 4, c)
            self.loc['a', c] = LocalTorus(c)
        self.loc3 = {'s': LocalNum(d, 3, ())}
        self.sites = list(range(k))
        self.siteperms = perms(k)
        self.build_variables()

    def build_variables(self):
        k = self.k
        ls, la = self.loc['s', ()], self.loc['a', ()]
        self.vars, self.nvar = {}, {}
        G = RX.FAMILY_GROUP['40']
        blocks = []
        for st in sorted_tuples(len(ls.labels), k):
            for ai in range(len(la.labels)):
                dims = [ls.dims[i] for i in st] + [la.dims[ai]]
                R = sum(kron_all([ls.pi[i][I4[g]] for i in st] + [la.pi[ai][I4[g]]]) for g in G) / len(G)
                U = orth_range(R)
                m = U.shape[1]
                if m == 0:
                    continue
                stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(k))]
                Bs = [U.T @ self.factor_perm(dims, s) @ U for s in stab]
                basis = invariant_sym_basis(Bs, m)
                if not basis:
                    continue
                blocks.append(dict(st=st, ai=ai, dims=dims, U=U, m=m, basis=basis, cosets=self.coset_reps(st),
                                   stab=len(stab)))
        off = 0
        for b in blocks:
            b['off'] = off
            off += len(b['basis'])
        self.vars['40'], self.nvar['40'] = blocks, off
        self._log('family 40 (torus aux): %d rep blocks, %d variables' % (len(blocks), off))
        self.N = off
        self.foff = {'40': 0}

    def objective_M(self, th, t=0.5):
        d = self.d
        zs = np.array([d ** ncycles(p) - t * d ** ncycles(compose(SWAP03, p)) for p in P4])
        Mq = math.sqrt(2) * np.diag([math.cos(th), math.sin(th)])
        M3 = np.kron(np.eye(8), Mq)                        # M on replica 3 (last, least significant digit)
        O = M3 @ perm_op(SWAP03) @ M3
        za = np.array([np.trace(O @ unit16(e)) for e in range(len(WORDS))])
        return self.functional('40', zs, za) / self.L

    def trace_row(self, f='40'):
        d = self.d
        zs = np.array([float(d ** ncycles(p)) for p in P4])
        za = np.array([1.0 if x == y else 0.0 for (x, y) in WORDS])
        return self.functional('40', zs, za) / self.L

    def equality_rows(self):
        ls, la = self.loc['s', ()], self.loc['a', ()]
        s3 = self.loc3['s']
        smap = s3.FT @ self.delete_matrix(self.d, 0) @ ls.IF
        Mst = np.zeros((len(WORDS), len(WORDS)))
        for e, (x, y) in enumerate(WORDS):
            Mst[e, e] += 1.0
            if x[0] == y[0]:
                for z in (0, 1):
                    Mst[WIDX[((z,) + x[1:], (z,) + y[1:])], e] -= 0.5
        amap = la.FT @ Mst @ la.IF
        return self._eq_block('40', smap, amap)


def build(k, d, verbose=True):
    t0 = time.time()
    R = RelaxM(k, d, verbose=verbose)
    data = dict(k=k, d=d, N=R.N)
    data['tr'] = R.trace_row()
    E = R.equality_rows()
    U, s, Vt = np.linalg.svd(E, full_matrices=False)
    r = int((s > s.max() * 1e-10).sum())
    data['E'] = Vt[:r]
    if verbose:
        print('equalities raw', E.shape, 'rank', r, '%.1fs' % (time.time() - t0), flush=True)
    blocks = []
    for cut in RX.FAMILY_CUTS['40']:
        obs, Fs = R.family_blocks('40', cut)
        for ob, Fm in zip(obs, Fs):
            for qi, Q in enumerate(ob['Qs']):
                Fq = np.einsum('ia,kij,jb->kab', Q, Fm, Q, optimize=True)
                if np.abs(Fq).max() < 1e-12:
                    continue
                blocks.append(dict(cut=cut, st=ob['st'], ai=ob['ai'], q=qi, m=Q.shape[1], F=Fq))
        if verbose:
            print('cut', cut, 'output reps', len(obs), 'blocks so far', len(blocks), 'max m',
                  max([b['m'] for b in blocks] or [0]), '%.1fs' % (time.time() - t0), flush=True)
    data['blocks'] = blocks
    return R, data


if __name__ == '__main__':
    k, d = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    R, D = build(k, d)
    D['cM'] = {th: R.objective_M(th) for th in np.round(np.linspace(-math.pi / 2, math.pi / 2, 13), 12)}
    D['cM'][math.pi / 4] = R.objective_M(math.pi / 4)
    D['cM'][-math.pi / 4] = R.objective_M(-math.pi / 4)
    sizes = [b['m'] for b in D['blocks']]
    print('BUILD-M k=%d d=%d: N %d, eq rows %d, blocks %d, max block %d, svec total %d, time %.1fs' % (
        k, d, D['N'], D['E'].shape[0], len(sizes), max(sizes), sum(n * (n + 1) // 2 for n in sizes), time.time() - t0), flush=True)
    with open('<ROOT>/verifiers/DM_k%d_d%d.pkl' % (k, d), 'wb') as fh:
        pickle.dump(D, fh, protocol=4)
