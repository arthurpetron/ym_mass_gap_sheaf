#!/usr/bin/env python3
"""Stage D(a): topology at stronger coupling. Per ensemble (name pattern *_lowb and the production runs at the same L,beta):
histogram of rounded flowed clover charge Q (c=0.5 and 0.4), fraction of |Q|>=1, number of Q changes (tunnelling), g^2_GF per |Q| sector,
Q^2 mean (susceptibility), tau_int of Q^2; and the fixed-beta step-scaling quantity d(beta) = 1/g^2(L) - 1/g^2(2L) (continuum-N-free: tree-improved N) with the
full ensemble vs Q-restricted to Q=0 (rounded at c=0.5) for the pairs (4,8) and (6,12).
usage: stageD_topology.py OUT.md DIR[,DIR] """
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *

def load_all(dirs, L, beta):
    runs = []
    for dr in dirs:
        for f in sorted(glob.glob(os.path.join(dr, f'su2_L{L}*_b{beta:.2f}*.csv'))):
            n = os.path.basename(f)
            if '.alt' in n or '_cold' in n or '_tau' in n: continue
            r = load_run(f, 3)
            if len(r['sweep']) > 50 and abs(r['beta'] - beta) < 1e-9 and r['L'] == L: runs.append((n, r))
    return runs

def qround(Q): return np.rint(Q).astype(int)

def sector_stats(runs, c, cq):
    g2, Qs, sw = [], [], []
    for n, r in runs:
        try: i = time_index(r, c); iq = time_index(r, cq)
        except AssertionError: continue
        t = r['times'][i]
        g2.append(t * t * r['E'][:, i, 0] / N_lat(c, r['L'])); Qs.append(r['E'][:, iq, 2]); sw.append(r['sep'])
    if not g2: return None
    return np.concatenate(g2), np.concatenate(Qs), g2, Qs

def main(dirs, out):
    lines = []
    Lb = [(4, (1.8, 2.0, 2.2, 2.4, 2.6)), (6, (2.0, 2.2, 2.4, 2.6)), (8, (2.2, 2.4, 2.6)), (12, (2.4,))]
    lines += ['## Topological charge at stronger coupling (flowed clover Q; rounded)', '',
              '| L | beta | n | cq | max&#124;Q&#124; | frac &#124;round Q&#124;>=1 | #Q changes | <Q^2> | hist | g2(c=0.3) all | g2 Q=0 | g2 &#124;Q&#124;>=1 |', '|---|---|---|---|---|---|---|---|---|---|---|---|']
    store = {}
    for L, bs in Lb:
        for b in bs:
            runs = load_all(dirs, L, b)
            if not runs: continue
            for cq in (0.4, 0.5):
                res = sector_stats(runs, 0.3, cq)
                if res is None: continue
                g, Q, gl, Ql = res
                R = qround(Q)
                chg = sum(int(np.sum(qround(q)[1:] != qround(q)[:-1])) for q in Ql)
                vals, cnt = np.unique(R, return_counts=True)
                m0 = R == 0
                a = gamma_method(g)[:2]
                z = gamma_method(g[m0])[:2] if m0.sum() > 20 else (np.nan, np.nan)
                nz = gamma_method(g[~m0])[:2] if (~m0).sum() > 20 else (np.nan, np.nan)
                lines.append(f'| {L} | {b:g} | {len(g)} | {cq} | {np.abs(Q).max():.2f} | {np.mean(~m0):.4f} | {chg} | {np.mean(Q**2):.4f} | {dict(zip(vals.tolist(), cnt.tolist()))} | {a[0]:.4f}({a[1]*1e4:.0f}) | {z[0]:.4f}({z[1]*1e4:.0f}) | ' + (f'{nz[0]:.4f}({nz[1]*1e4:.0f})' if not np.isnan(nz[0]) else '-') + ' |')
                if cq == 0.5: store[(L, b)] = (runs,)
    lines += ['', '## Fixed-beta step-scaling quantity d = 1/g2(L) - 1/g2(2L), all configurations vs Q=0 only (Q rounded at c=0.5)', '',
              '| pair | beta | c | d (all) | d (Q=0 only) | difference | n_L (frac Q=0), n_2L (frac Q=0) |', '|---|---|---|---|---|---|---|']
    for (L, L2) in ((4, 8), (6, 12)):
        for b in sorted({b for (l, b) in store if l == L and (L2, b) in store}):
            for c in (0.3, 0.4):
                vals = {}
                for LL in (L, L2):
                    g, Q, gl, Ql = sector_stats(store[(LL, b)][0], c, 0.5)
                    m0 = qround(Q) == 0
                    vals[LL] = (g, m0)
                def inv(g): 
                    m, e = gamma_method(g)[:2]; return 1 / m, e / m ** 2
                (i1, e1), (i2, e2) = inv(vals[L][0]), inv(vals[L2][0])
                (j1, f1), (j2, f2) = inv(vals[L][0][vals[L][1]]), inv(vals[L2][0][vals[L2][1]])
                d_all = i1 - i2; de = np.hypot(e1, e2); d0 = j1 - j2; d0e = np.hypot(f1, f2)
                lines.append(f'| {L}->{L2} | {b:g} | {c} | {d_all:.4f}({de*1e4:.0f}) | {d0:.4f}({d0e*1e4:.0f}) | {d0-d_all:+.4f} | {len(vals[L][0])} ({vals[L][1].mean():.3f}), {len(vals[L2][0])} ({vals[L2][1].mean():.3f}) |')
    open(out, 'w').write('\n'.join(lines) + '\n'); print('\n'.join(lines))

if __name__ == '__main__':
    main(sys.argv[2].split(','), sys.argv[1])
