#!/usr/bin/env python3
"""Stage B(iii): step-scaling shift s = 1/u - 1/Sigma per scheme c for the 4->8 pair (c=0.5 only exists at L=4,6,8) and, once
the c=0.5 L=16 runs exist, a pointwise 8->16 check at matched beta.  usage: stageB_c05.py OUT.md NBOOT DIR[,DIR]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from joint_fit import *
out, nb, dirs = sys.argv[1], int(sys.argv[2]), sys.argv[3].split(',')
d = Data(dirs, obs='clover', norm='lat')
L = ['one-loop shift 2 b0 ln2 = %.4f' % S0]
targets = [1.3, 1.6, 2.0, 2.4]
L.append('\n### 4->8 shift s(u) = 1/u - 1/Sigma by scheme c, same beta set (common beta of L=4 and L=8 for each c); (xx) = bootstrap err\n')
for M in (2, 3):
    L.append(f'\nM={M}\n\n| u | c=0.3 | c=0.4 | c=0.5 |\n|---|---|---|---|')
    res = {}
    for c in (0.3, 0.4, 0.5):
        J = Joint(d, c, M, [(4, 8)], targets, nboot=nb)
        res[c] = J.S
    for iu, u in enumerate(targets):
        row = [f'{u:g}']
        for c in (0.3, 0.4, 0.5):
            S = res[c][:, 0, iu]; v = S[1:]; v = v[~np.isnan(v)]
            row.append(f'{S[0]:.4f}({np.std(v)*1e4:.0f})' if not np.isnan(S[0]) else '-')
        L.append('| ' + ' | '.join(row) + ' |')
# pointwise L=8 vs L=16 at matched beta
L.append('\n### 8->16 pointwise at matched beta: s_pt = 1/g2(L=8,beta) - 1/g2(L=16,beta) (u = g2(L=8,beta)); needs c=0.5 at L=16\n')
L.append('| beta | c | g2(8) | g2(16) | s_pt | s_pt-S0 (sigma) |\n|---|---|---|---|---|---|')
for b in sorted({b for (l, b) in d.runs if l == 16}):
    for c in (0.3, 0.4, 0.5):
        a, z = d.g2(8, b, c), d.g2(16, b, c)
        if a is None or z is None: continue
        s = 1 / a[0] - 1 / z[0]; e = np.hypot(a[1] / a[0] ** 2, z[1] / z[0] ** 2)
        L.append(f'| {b:g} | {c} | {a[0]:.4f}({a[1]*1e4:.0f}) | {z[0]:.4f}({z[1]*1e4:.0f}) | {s:.4f}({e*1e4:.0f}) | {(s-S0)/e:+.1f} |')
open(out, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
