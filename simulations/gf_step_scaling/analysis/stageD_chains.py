#!/usr/bin/env python3
"""Stage D(b)/C: multi-chain comparison. Chains = runs with the same (L,beta,observable) and different seeds. Gelman-Rubin R-hat (split chains,
first-half/second-half) for g^2 at c=0.3,0.4 and the chain means with Gamma errors, chi2 of chain means about the weighted mean.
usage: stageD_chains.py OUT.md DIR[,DIR] L:beta[,L:beta...] """
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *

def rhat(chains):
    ch = [np.asarray(c) for c in chains]
    split = []
    for c in ch:
        h = len(c) // 2; split += [c[:h], c[h:2 * h]]
    n = min(len(c) for c in split); split = [c[:n] for c in split]; m = len(split)
    means = np.array([c.mean() for c in split]); W = np.mean([c.var(ddof=1) for c in split]); B = n * means.var(ddof=1)
    var = (n - 1) / n * W + B / n
    return np.sqrt(var / W)

def main(dirs, out, specs):
    lines = ['| L | beta | #chains | n each | c | chain means g2 (Gamma err) | chi2/dof of chain means | R-hat (split) | weighted mean |', '|---|---|---|---|---|---|---|---|---|']
    for sp in specs:
        L, b = sp.split(':'); L = int(L); b = float(b)
        runs = []
        for dr in dirs:
            for f in sorted(glob.glob(os.path.join(dr, f'su2_L{L}_b{b:.2f}*.csv'))):
                n = os.path.basename(f)
                if '.alt' in n or '_cold' in n or '_tau' in n: continue
                r = load_run(f, 3)
                if len(r['sweep']) > 50: runs.append((n, r))
        for c in (0.3, 0.4):
            ser, ms, es = [], [], []
            for n, r in runs:
                try: i = time_index(r, c)
                except AssertionError: continue
                t = r['times'][i]; x = t * t * r['E'][:, i, 0] / N_lat(c, L)
                m, e, tau, W = gamma_method(x); ser.append(x); ms.append(m); es.append(e)
            if len(ser) < 2: continue
            ms, es = np.array(ms), np.array(es); w = 1 / es ** 2; mw = (w * ms).sum() / w.sum()
            chi = np.sum(((ms - mw) / es) ** 2) / (len(ms) - 1)
            lines.append(f'| {L} | {b:g} | {len(ser)} | {min(len(s) for s in ser)} | {c} | ' + ', '.join(f'{m:.4f}({e*1e4:.0f})' for m, e in zip(ms, es)) + f' | {chi:.2f} | {rhat(ser):.3f} | {mw:.4f}({1/np.sqrt(w.sum())*1e4:.0f}) |')
    open(out, 'w').write('\n'.join(lines) + '\n'); print('\n'.join(lines))

if __name__ == '__main__':
    main(sys.argv[2].split(','), sys.argv[1], sys.argv[3].split(','))
