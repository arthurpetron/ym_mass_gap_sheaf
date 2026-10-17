#!/usr/bin/env python3
"""Control variate for g^2_GF using the plaquette, which is available at EVERY sweep while the flow is measured only every
`sep` sweeps: x_cv = x_i - b (p_i - Pbar_all), b = Cov(x,p)/Var(p) (fitted on the measured subset), Pbar_all = plaquette mean over all
post-thermalisation sweeps. Errors by blocked jackknife (nb blocks along the chain; each block's Pbar_all uses all its sweeps).
usage: control_variate.py RUNDIR OUT.md name1,name2,..."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
from ensemble_table import read_plq

def analyse(rundir, name, c, nb=20):
    r = load_run(os.path.join(rundir, name + '.csv'), 3)
    plq = np.array(read_plq(os.path.join(rundir, name + '.plaq'))); _, ix = np.unique(plq[:, 0], return_index=True); plq = plq[ix]
    sw = r['sweep']; i = time_index(r, c); t = r['times'][i]
    x = t * t * r['E'][:, i, 0] / N_lat(c, r['L'])
    d = dict(zip(plq[:, 0], plq[:, 1])); pm = np.array([d.get(s, np.nan) for s in sw]); ok = ~np.isnan(pm)
    x, pm, sw = x[ok], pm[ok], sw[ok]
    allp = plq[plq[:, 0] >= sw[0], :]
    n = len(x); edges = np.linspace(0, n, nb + 1).astype(int)
    swe = [sw[e] if e < n else sw[-1] + 1 for e in edges]
    def est(idx_blocks):
        xi = np.concatenate([x[edges[b]:edges[b + 1]] for b in idx_blocks]); pi = np.concatenate([pm[edges[b]:edges[b + 1]] for b in idx_blocks])
        pa = np.concatenate([allp[(allp[:, 0] >= swe[b]) & (allp[:, 0] < swe[b + 1]), 1] for b in idx_blocks])
        b = np.cov(xi, pi)[0, 1] / np.var(pi, ddof=1)
        return xi.mean(), xi.mean() - b * (pi.mean() - pa.mean()), b
    full = est(range(nb))
    jk = np.array([est([k for k in range(nb) if k != j]) for j in range(nb)])
    e_plain = np.sqrt((nb - 1) / nb * np.sum((jk[:, 0] - jk[:, 0].mean()) ** 2))
    e_cv = np.sqrt((nb - 1) / nb * np.sum((jk[:, 1] - jk[:, 1].mean()) ** 2))
    rho = np.corrcoef(x, pm)[0, 1]
    return r['L'], r['beta'], c, n, r['sep'], rho, full[0], e_plain, full[1], e_cv, full[2]

if __name__ == '__main__':
    rd, out, names = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
    L = ['| L | beta | c | n | sep | corr(g2,plaq) | g2 plain (jk err) | g2 CV (jk err) | error ratio CV/plain | variance gain |', '|---|---|---|---|---|---|---|---|---|---|']
    for nm in names:
        for c in (0.3, 0.4):
            Ls, b, c, n, sep, rho, m0, e0, m1, e1, bb = analyse(rd, nm, c)
            L.append(f'| {Ls} | {b:g} | {c} | {n} | {sep} | {rho:+.3f} | {m0:.4f}({e0*1e4:.0f}) | {m1:.4f}({e1*1e4:.0f}) | {e1/e0:.3f} | {1-(e1/e0)**2:+.1%} |')
    open(out, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
