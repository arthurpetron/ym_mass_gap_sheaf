#!/usr/bin/env python3
"""Items 1-2 analysis: continuum shift s(u) at 5 u (1.0, 1.54, 1.9, 2.41, 2.9), per scheme c, then slope fit s = s0 + k1 u + k2 u^2 (s0 = 2 b0 ln2 fixed).
Pairs: 6->12, 8->16, 12->24, pointwise at matched beta (u = g2(L,beta); chains at the same (L,beta) are pooled by concatenation, Gamma-method errors, tau ~ 0.5);
the two OLD u values use the joint-bootstrap interpolation (Joint, M=2) for 6->12 and 8->16 and the pointwise 12->24 at beta = 3.6, 4.5.
Each pair's shift is moved to the common u of its scheme (u of the 12->24 pair) with the exact two-loop slope dS/du (<= 1e-4 for |du| <= 0.05).
usage: stage3_analysis.py OUTPREFIX [NBOOT]"""
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from joint_fit import *
DIRS = ['/Users/darthur/ym_numerics_runs/prod', '/Users/darthur/ym_numerics_runs/prod2', '/Users/darthur/ym_numerics_runs/prod3']
EXC = ('_cold', '_tau', '.alt', 'bad_')
b0 = 11 / (24 * np.pi ** 2); b1 = 136 / 3 / (16 * np.pi ** 2) ** 2; K1_2L = 0.0026
def two(u, n=3000):
    x = 1 / u; h = np.log(2) / n
    for _ in range(n): x -= h * (2 * b0 + 2 * b1 / x)
    return 1 / u - x
def dtwo(u): return (two(u * 1.001) - two(u / 1.001)) / (u * 0.002)

RUNS = {}
for dr in DIRS:
    for f in sorted(glob.glob(os.path.join(dr, 'su2_L*_b*.csv'))):
        n = os.path.basename(f)
        if any(x in n for x in EXC): continue
        try: r = load_run(f, 3)
        except Exception: continue
        if len(r['sweep']) < 20: continue
        RUNS.setdefault((r['L'], round(r['beta'], 6)), []).append((n, r))

def series(L, b, cs):
    """pooled aligned series of g2 for all schemes cs (chains that contain all of them)"""
    out = []
    for n, r in RUNS.get((L, b), []):
        try: idx = [time_index(r, c) for c in cs]
        except AssertionError: continue
        out.append(np.column_stack([r['times'][i] ** 2 * r['E'][:, i, 0] / N_lat(c, L) for c, i in zip(cs, idx)]))
    return np.vstack(out) if out else None

def g2(L, b, c):
    X = series(L, b, [c])
    if X is None: return None
    m, e, tau, W = gamma_method(X[:, 0]); return m, e, len(X)

def pair(L, b, cs=(0.3, 0.4)):
    """pointwise shifts for schemes cs at beta b of the pair L->2L with covariance between the schemes"""
    X1 = series(L, b, list(cs)); X2 = series(2 * L, b, list(cs))
    if X1 is None or X2 is None: return None
    res = {}
    var = []; Cv = []
    S = []; U = []
    for X in (X1, X2):
        m = X.mean(0); e = np.array([gamma_method(X[:, i])[1] for i in range(X.shape[1])])
        r = np.corrcoef(X.T)[0, 1] if X.shape[1] > 1 else 0
        S.append(m); var.append(e); Cv.append(r)
    u = S[0]; sg = S[1]
    s = 1 / u - 1 / sg
    err = np.hypot(var[0] / u ** 2, var[1] / sg ** 2)
    cov01 = var[0][0] * var[0][1] / (u[0] ** 2 * u[1] ** 2) * Cv[0] + var[1][0] * var[1][1] / (sg[0] ** 2 * sg[1] ** 2) * Cv[1]
    return dict(u=u, sig=sg, s=s, e=err, cov=cov01, rho=cov01 / (err[0] * err[1]), N=(len(X1), len(X2)))

def lin(x, y, e, kind):
    x = np.asarray(x, float); y = np.asarray(y, float); e = np.asarray(e, float)
    if kind == 'const': A = np.ones((len(x), 1))
    elif kind == '1/L': A = np.column_stack([np.ones_like(x), np.sqrt(x)])
    else: A = np.column_stack([np.ones_like(x), x])
    W = np.diag(1 / e ** 2); cov = np.linalg.inv(A.T @ W @ A); p = cov @ A.T @ W @ y
    chi = float((y - A @ p) @ W @ (y - A @ p)); w = (cov @ A.T @ W)[0]
    return p[0], np.sqrt(cov[0, 0]), chi, len(y) - A.shape[1], w

def slope(us, y, e, k2free):
    us = np.asarray(us); w = 1 / np.asarray(e) ** 2; t = np.asarray(y) - S0
    A = np.column_stack([us, us ** 2]) if k2free else us[:, None]
    cov = np.linalg.inv(A.T @ (w[:, None] * A)); p = cov @ A.T @ (w * t); chi = float(np.sum(w * (t - A @ p) ** 2))
    return p, np.sqrt(np.diag(cov)), chi, len(us) - A.shape[1]

if __name__ == '__main__':
    pref = sys.argv[1]; NB = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    NEW = {1.0: (5.63, 5.74, 5.89), 1.9: (3.77, 3.88, 4.02), 2.9: (3.08, 3.19, 3.34)}
    OLD = {1.54: 4.5, 2.41: 3.6}
    pts = {0.3: [], 0.4: []}    # per c: list of dict(u, pairs: {L: (s, e)}, rho)
    lines = ['## Pair shifts (corrected to the common u of the 12->24 pair)\n', '| u nominal | c | u(12->24) | pair | beta | u of pair | N (L, 2L) | s raw | s at common u | err | rho(c=.3,.4) |', '|---|---|---|---|---|---|---|---|---|---|---|']
    D = Data(DIRS, obs='clover', norm='lat', excl=EXC)
    for un in sorted(set(NEW) | set(OLD)):
        if un in NEW: bset = {6: NEW[un][0], 8: NEW[un][1], 12: NEW[un][2]}
        else: bset = {12: OLD[un]}
        pp = {L: pair(L, round(b, 6)) for L, b in bset.items()}
        if pp.get(12) is None: continue
        rhos = {}
        for ic, c in enumerate((0.3, 0.4)):
            u12 = pp[12]['u'][ic]; entry = {}
            for L in (6, 8, 12):
                if un in OLD and L in (6, 8):
                    J = Joint(D, c, 2, [(L, 2 * L)], [u12], nboot=NB)
                    v = J.S[1:, 0, 0]; v = v[~np.isnan(v)]
                    if np.isnan(J.S[0, 0, 0]): continue
                    entry[L] = (J.S[0, 0, 0], np.std(v)); lines.append(f'| {un} | {c} | {u12:.4f} | {L}->{2*L} | Joint | {u12:.4f} | interp | {J.S[0,0,0]:.4f} | {J.S[0,0,0]:.4f} | {np.std(v):.4f} | - |')
                    continue
                p = pp.get(L)
                if p is None: continue
                sc = p['s'][ic] + dtwo(p['u'][ic]) * (u12 - p['u'][ic])
                entry[L] = (sc, p['e'][ic]); rhos[L] = p['rho']
                lines.append(f"| {un} | {c} | {u12:.4f} | {L}->{2*L} | {bset[L]:g} | {p['u'][ic]:.4f} | {p['N'][0]}, {p['N'][1]} | {p['s'][ic]:.4f} | {sc:.4f} | {p['e'][ic]:.4f} | {p['rho']:.2f} |")
            pts[c].append(dict(un=un, u=u12, pairs=entry, rho=rhos))
    open(pref + '_pairs.md', 'w').write('\n'.join(lines) + '\n')
    # continuum at each u, forms
    out = ['## Continuum shift per u and extrapolation form (x = 1/L^2, L = smaller lattice of the pair; independent pair errors)\n',
           '| c | u | pairs used | s_cont lin 3-pair (chi2/1) | lin 2-pair (8,12) | const (6,8,12) chi2/2 | lin in 1/L 3-pair | spread (max-min) | one-loop | two-loop |', '|---|---|---|---|---|---|---|---|---|---|']
    cont = {0.3: {}, 0.4: {}}
    for c in (0.3, 0.4):
        for pt in pts[c]:
            Ls = sorted(pt['pairs']);
            if len(Ls) < 3: continue
            x = [1 / L ** 2 for L in Ls]; y = [pt['pairs'][L][0] for L in Ls]; e = [pt['pairs'][L][1] for L in Ls]
            a3 = lin(x, y, e, 'lin'); a2 = lin(x[1:], y[1:], e[1:], 'lin'); ac = lin(x, y, e, 'const'); al = lin(x, y, e, '1/L')
            vals = [a3[0], a2[0], ac[0], al[0]]
            cont[c][pt['u']] = dict(forms={'lin3': a3, 'lin2': a2, 'const': ac, 'invL': al}, pt=pt)
            out.append(f"| {c} | {pt['u']:.3f} | {Ls} | {a3[0]:.4f}({a3[1]*1e4:.0f}) {a3[2]:.1f} | {a2[0]:.4f}({a2[1]*1e4:.0f}) | {ac[0]:.4f}({ac[1]*1e4:.0f}) {ac[2]:.1f} | {al[0]:.4f}({al[1]*1e4:.0f}) | {max(vals)-min(vals):.4f} | {S0:.4f} | {two(pt['u']):.4f} |")
    open(pref + '_cont.md', 'w').write('\n'.join(out) + '\n')
    # slope fits
    sl = ['## Slope fits s = s0 + k1 u + k2 u^2, s0 = %.4f fixed (c-scheme own u; independent u-points; stat. only)\n' % S0,
          '| c | form | n_u | k2 | k1 | sigma(k1) | k1 vs 0 (sigma) | k1 vs 0.0026 (sigma) | chi2/dof |', '|---|---|---|---|---|---|---|---|---|']
    summ = {}
    for c in (0.3, 0.4):
        us = sorted(cont[c])
        for form in ('lin3', 'lin2', 'const', 'invL'):
            y = [cont[c][u]['forms'][form][0] for u in us]; e = [cont[c][u]['forms'][form][1] for u in us]
            for k2free in (False, True):
                if k2free and len(us) < 3: continue
                p, sg, chi, dof = slope(us, y, e, k2free)
                sl.append(f"| {c} | {form} | {len(us)} | {'free: %.5f(%.5f)' % (p[1], sg[1]) if k2free else '0'} | {p[0]:.5f} | {sg[0]:.5f} | {p[0]/sg[0]:.1f} | {(p[0]-K1_2L)/sg[0]:+.1f} | {chi:.1f}/{dof} |")
                summ[(c, form, k2free)] = (p[0], sg[0], chi, dof)
    open(pref + '_slope.md', 'w').write('\n'.join(sl) + '\n')
    # c agreement: difference of continuum lin3 values (own u per scheme) -> compare at each nominal u
    ca = ['## c = 0.3 vs 0.4 agreement of the continuum shift (lin 3-pair; correlated pair errors with the measured rho; for the two OLD u pairs 6->12, 8->16 rho is set to the mean of the new-u values)\n',
          '| u nominal | s_cont(c=0.3) | s_cont(c=0.4) | diff | err(diff) | diff/err |', '|---|---|---|---|---|---|']
    rho_mean = {L: np.mean([pt['rho'][L] for pt in pts[0.3] if L in pt['rho'] and pt['un'] in NEW] or [0.9]) for L in (6, 8, 12)}
    for pt3 in pts[0.3]:
        pt4 = next((q for q in pts[0.4] if q['un'] == pt3['un']), None)
        if pt4 is None or len(pt3['pairs']) < 3 or len(pt4['pairs']) < 3: continue
        Ls = sorted(pt3['pairs']); x = [1 / L ** 2 for L in Ls]
        r3 = lin(x, [pt3['pairs'][L][0] for L in Ls], [pt3['pairs'][L][1] for L in Ls], 'lin'); r4 = lin(x, [pt4['pairs'][L][0] for L in Ls], [pt4['pairs'][L][1] for L in Ls], 'lin')
        w3, w4 = r3[4], r4[4]
        var = sum(w4[i] ** 2 * pt4['pairs'][L][1] ** 2 + w3[i] ** 2 * pt3['pairs'][L][1] ** 2 - 2 * w4[i] * w3[i] * pt3['rho'].get(L, rho_mean[L]) * pt3['pairs'][L][1] * pt4['pairs'][L][1] for i, L in enumerate(Ls))
        ca.append(f"| {pt3['un']} | {r3[0]:.4f}({r3[1]*1e4:.0f}) | {r4[0]:.4f}({r4[1]*1e4:.0f}) | {r4[0]-r3[0]:+.4f} | {np.sqrt(max(var,1e-12)):.4f} | {(r4[0]-r3[0])/np.sqrt(max(var,1e-12)):+.1f} |")
    open(pref + '_cagree.md', 'w').write('\n'.join(ca) + '\n')
    for f in ('_pairs', '_cont', '_slope', '_cagree'): print(open(pref + f + '.md').read())
