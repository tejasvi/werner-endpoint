"""Solve (eq-implied face + CVXOPT) and extract the dual PSD multipliers Z_b per block; summarise active blocks and ranks.
Usage: python dual_extract.py PICKLE theta_key_or_none OUT.pkl"""
import sys, pickle, math, time
from collections import Counter, defaultdict
import numpy as np
sys.path.insert(0, '<ROOT>/verifiers')
from eqface import eq_face


def solve_dual(D, tol=1e-10, maxiters=200, show=False):
    from cvxopt import matrix, solvers
    N = D['N']; E = D['E']
    U, s, Vt = np.linalg.svd(E, full_matrices=True)
    r = int((s > s.max() * 1e-10).sum())
    Z = Vt[r:].T
    a = Z.T @ D['tr']; u0 = a / (a @ a)
    Ua, sa, Vta = np.linalg.svd(a[None, :], full_matrices=True)
    B = Z @ Vta[1:].T; y0 = Z @ u0
    nv = B.shape[1]
    sizes = [b['m'] for b in D['blocks']]
    G = np.zeros((sum(n * n for n in sizes), nv)); h = np.zeros(G.shape[0]); row = 0
    for b in D['blocks']:
        n = b['m']; Fv = b['F'].reshape(N, n * n)
        G[row:row + n * n] = -(Fv.T @ B); h[row:row + n * n] = Fv.T @ y0; row += n * n
    c = B.T @ D['c']; const = D['c'] @ y0
    solvers.options.update(show_progress=show, maxiters=maxiters, abstol=tol, reltol=tol, feastol=tol)
    sol = solvers.conelp(matrix(c), matrix(G), matrix(h), dims={'l': 0, 'q': [], 's': sizes})
    zz = np.array(sol['z']).ravel(); Ds = []; row = 0
    for n in sizes:
        M = zz[row:row + n * n].reshape(n, n); M = np.tril(M) + np.tril(M, -1).T; Ds.append(M); row += n * n
    y = y0 + B @ np.array(sol['x']).ravel()
    return dict(status=sol['status'], primal=sol['primal objective'] + const, dual=sol['dual objective'] + const, Z=Ds, y=y)


if __name__ == '__main__':
    path, thk, out = sys.argv[1], sys.argv[2], sys.argv[3]
    D = pickle.load(open(path, 'rb'))
    if thk != 'none':
        th = {'m4': -math.pi / 4, 'p4': math.pi / 4}[thk]
        key = min(D['cM'].keys(), key=lambda x: abs(x - th)); D = dict(D); D['c'] = D['cM'][key]
    D2, info = eq_face(D, verbose=False)
    t0 = time.time()
    res = solve_dual(D2)
    tr = [np.trace(Zb) for Zb in res['Z']]
    tot = sum(tr)
    act = []
    for b, Zb, t in zip(D2['blocks'], res['Z'], tr):
        w = np.linalg.eigvalsh(Zb)
        rk = int((w > 1e-7 * max(w.max(), 1e-300)).sum()) if w.max() > 1e-9 * tot else 0
        Sy = np.einsum('i,ijk->jk', res['y'], b['F'])
        act.append(dict(cut=b['cut'], st=b['st'], ai=b['ai'], q=b['q'], m=b['m'], trZ=t / tot, rankZ=rk, compl=np.abs(Zb @ Sy).max()))
    nact = sum(1 for a in act if a['rankZ'] > 0)
    print('%s %s: status %s primal %+.3e dual %+.3e | blocks %d, active %d, total rank %d, max |Z S| %.1e (%.0fs)' % (
        path, thk, res['status'], res['primal'], res['dual'], len(act), nact, sum(a['rankZ'] for a in act),
        max(a['compl'] for a in act), time.time() - t0), flush=True)
    bycut = defaultdict(lambda: [0, 0, 0.0])
    for a in act:
        if a['rankZ']:
            bc = bycut[a['cut']]; bc[0] += 1; bc[1] += a['rankZ']; bc[2] += a['trZ']
    for cut, (n, rk, w) in sorted(bycut.items()):
        print('   cut %-7s active blocks %3d  total rank %3d  trace share %.3f' % (cut, n, rk, w))
    pickle.dump(dict(act=act, res=dict(status=res['status'], primal=res['primal'], dual=res['dual']), Z=res['Z'],
                     meta=[dict(cut=b['cut'], st=b['st'], ai=b['ai'], q=b['q'], m=b['m']) for b in D2['blocks']]), open(out, 'wb'))
