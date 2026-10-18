#!/usr/bin/env python3
"""Item 1: L=12 pooled statistics. For each beta: all L=12 chains (old prod/prod2 + new prod3 *_i1*), per-chain g2 (c=0.3,0.4) with Gamma errors,
first/second-half z for new chains, chi2 of chain means, split R-hat, pooled (inverse-variance) mean, error before/after, max|Q|.
usage: stage3_item1.py OUT.md beta[,beta..]   (dirs fixed)"""
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
from stageD_chains import rhat
R = '/Users/darthur/ym_numerics_runs'; DIRS = [R + '/prod', R + '/prod2', R + '/prod3']
out = sys.argv[1]; betas = [float(x) for x in sys.argv[2].split(',')]
L = 12
T = ['| beta | c | old chains: pooled g2 | new chains: pooled g2 | all pooled g2 (err) | err old -> all | chi2/dof chain means | R-hat | max z halves (new) | max&#124;Q&#124; new |', '|---|---|---|---|---|---|---|---|---|---|']
D = ['| chain | beta | n | c | g2 (Gamma err) | tau_int | z(2nd-1st) | max&#124;Q&#124; |', '|---|---|---|---|---|---|---|---|']
for b in betas:
    runs = []
    for d in DIRS:
        for f in sorted(glob.glob(f'{d}/su2_L{L}_b{b:.2f}*.csv')):
            n = os.path.basename(f)
            if any(k in n for k in ('.alt', '_cold', '_tau')): continue
            r = load_run(f, 3)
            if len(r['sweep']) > 50: runs.append((n, d.endswith('prod3'), r))
    for c in (0.3, 0.4):
        ser = {}; res = {}
        for n, new, r in runs:
            try: i = time_index(r, c)
            except AssertionError: continue
            t = r['times'][i]; x = t * t * r['E'][:, i, 0] / N_lat(c, L)
            m, e, tau, W = gamma_method(x); h = len(x) // 2
            a, ea = gamma_method(x[:h])[:2]; bb, eb = gamma_method(x[h:])[:2]; z = (bb - a) / np.hypot(ea, eb)
            Q = np.abs(r['E'][:, time_index(r, 0.4), 2]).max()
            ser[n] = x; res[n] = (new, m, e, tau, z, Q, len(x))
            D.append(f'| {n} | {b:g} | {len(x)} | {c} | {m:.5f}({e*1e5:.0f}e-5) | {tau:.2f} | {z:+.2f} | {Q:.3f} |')
        def pool(sel):
            v = [(res[k][1], res[k][2]) for k in res if sel(res[k])]
            if not v: return None
            m = np.array([a for a, _ in v]); e = np.array([x for _, x in v]); w = 1 / e ** 2
            return (w * m).sum() / w.sum(), 1 / np.sqrt(w.sum()), m, e
        po, pn, pa = pool(lambda x: not x[0]), pool(lambda x: x[0]), pool(lambda x: True)
        if pa is None or len(pa[2]) < 2: continue
        chi = np.sum(((pa[2] - pa[0]) / pa[3]) ** 2) / (len(pa[2]) - 1)
        zn = [abs(res[k][4]) for k in res if res[k][0]]; Qn = [res[k][5] for k in res if res[k][0]]
        f = lambda p: '-' if p is None else f'{p[0]:.5f}({p[1]*1e5:.0f}e-5)'
        T.append(f'| {b:g} | {c} | {f(po)} | {f(pn)} | {f(pa)} | {(po[1]*1e5 if po else float("nan")):.0f} -> {pa[1]*1e5:.0f} (e-5) | {chi:.2f} | {rhat(list(ser.values())):.3f} | {max(zn) if zn else float("nan"):.2f} | {max(Qn) if Qn else float("nan"):.3f} |')
open(out, 'w').write('\n'.join(T) + '\n\nPer-chain:\n\n' + '\n'.join(D) + '\n'); print('\n'.join(T)); print(); print('\n'.join(D))
