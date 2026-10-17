#!/usr/bin/env python3
"""U(1): r(L,beta,c) = t^2 <E> beta / N_lat_u1(c,L)  (= 1 + O(1/beta) in the Coulomb phase if the pipeline is right;
free-field limit r -> 1 exactly). Prints per-ensemble r with Gamma-method errors, tau_int (samples), and step ratios
Sigma/u = r(2L)/r(L) for the pairs requested.  usage: u1_r.py OUT.md DIR[,DIR...] [PAIRS=4:8,6:12,8:16]"""
import sys, os, glob, re, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *

def collect(dirs, prefix='u1_'):
    d = {}
    for dr in dirs:
        for f in sorted(glob.glob(os.path.join(dr, prefix + 'L*_b*.csv'))):
            n = os.path.basename(f)
            if n.endswith('.alt.csv') or '_tau' in n or '_cold' in n or '_ch' in n or '_c5' in n or '_lowb' in n: continue
            r = load_run(f, 2)
            if len(r['sweep']) < 20: continue
            d[(r['L'], round(r['beta'], 3))] = (r, n)
    return d

def rval(r, c):
    i = time_index(r, c); t = r['times'][i]
    x = t * t * r['E'][:, i, 0] * r['beta'] / N_lat_u1(c, r['L'])
    m, e, tau, W = gamma_method(x)
    return m, e, tau

if __name__ == '__main__':
    out, dirs = sys.argv[1], sys.argv[2].split(',')
    pairs = [tuple(map(int, p.split(':'))) for p in (sys.argv[3] if len(sys.argv) > 3 else '4:8,6:12,8:16').split(',')]
    d = collect(dirs)
    betas = sorted({b for (_, b) in d})
    Ls = sorted({L for (L, _) in d})
    lines = ['## r(L,beta,c) = t^2<E>beta/N_lat_u1 (free field: 1)', '', '| beta | c | ' + ' | '.join(f'L={L}' for L in Ls) + ' |', '|---|---|' + '---|' * len(Ls)]
    R = {}
    for b in betas:
        for c in (0.3, 0.4):
            row = []
            for L in Ls:
                if (L, b) in d:
                    try:
                        m, e, tau = rval(d[(L, b)][0], c); R[(L, b, c)] = (m, e); row.append(f'{m:.4f}({e*1e4:.0f})')
                    except Exception:
                        row.append('-')
                else: row.append('-')
            lines.append(f'| {b:g} | {c} | ' + ' | '.join(row) + ' |')
    lines += ['', '## Sigma/u = r(2L)/r(L) (tree-improved N)', '', '| beta | c | ' + ' | '.join(f'{a}->{b2}' for a, b2 in pairs) + ' |', '|---|---|' + '---|' * len(pairs)]
    for b in betas:
        for c in (0.3, 0.4):
            row = []
            for a, b2 in pairs:
                if (a, b, c) in R and (b2, b, c) in R:
                    m1, e1 = R[(a, b, c)]; m2, e2 = R[(b2, b, c)]
                    q = m2 / m1; qe = q * np.hypot(e1 / m1, e2 / m2); row.append(f'{q:.4f}({qe*1e4:.0f})')
                else: row.append('-')
            lines.append(f'| {b:g} | {c} | ' + ' | '.join(row) + ' |')
    open(out, 'w').write('\n'.join(lines) + '\n'); print('\n'.join(lines))
