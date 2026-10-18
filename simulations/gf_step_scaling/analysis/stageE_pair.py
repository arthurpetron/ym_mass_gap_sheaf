#!/usr/bin/env python3
"""Stage E: 12->24 pointwise step-scaling shift s = 1/g2(12,b) - 1/g2(24,b) at the L=24 betas, u = g2(12,b); the 8->16 shift at the same u
(from the joint bootstrap interpolation of the 8 and 16 ensembles, common-beta fit M=2/3), and the exact 2-pair linear (a/L)^2 extrapolation
s_cont = s(12->24) + (s(12->24) - s(8->16)) * (1/144)/(1/64 - 1/144).  usage: stageE_pair.py OUT.md NBOOT DIR[,DIR]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from joint_fit import *
out, nb, dirs = sys.argv[1], int(sys.argv[2]), sys.argv[3].split(',')
d = Data(dirs, obs='clover', norm='lat')
two = lambda u: 2 * np.log(2) * (11 / (24 * np.pi ** 2) + 34 / 3 / (16 * np.pi ** 2) ** 2 * u)
L = [f'one-loop 2 b0 ln2 = {S0:.4f}\n', '| beta | c | n(L=24) | u = g2(12) | g2(24) | s(12->24) | s(8->16) at same u (M=2, M=3) | 2-pair extrap (M=2) | one-loop | first-order two-loop |', '|---|---|---|---|---|---|---|---|---|---|']
rng = np.random.default_rng(3)
for b in sorted({b for (l, b) in d.runs if l == 24}):
    for c in (0.3, 0.4):
        a, z = d.g2(12, b, c), d.g2(24, b, c)
        if a is None or z is None: continue
        s = 1 / a[0] - 1 / z[0]; e = np.hypot(a[1] / a[0] ** 2, z[1] / z[0] ** 2)
        u = a[0]
        row = []; s8 = {}
        for M in (2, 3):
            J = Joint(d, c, M, [(8, 16)], [u], nboot=nb)
            v = J.S[1:, 0, 0]; v = v[~np.isnan(v)]
            s8[M] = (J.S[0, 0, 0], np.std(v)); row.append(f'{s8[M][0]:.4f}({np.std(v)*1e4:.0f})')
        f = (1 / 144) / (1 / 64 - 1 / 144)
        sc = s + (s - s8[2][0]) * f; ec = np.hypot(e * (1 + f), s8[2][1] * f)
        L.append(f'| {b:g} | {c} | {len(d.runs[(24, b)][0][1]["sweep"])} | {u:.3f}({a[1]*1e4:.0f}) | {z[0]:.4f}({z[1]*1e4:.0f}) | {s:.4f}({e*1e4:.0f}) | {" , ".join(row)} | {sc:.4f}({ec*1e4:.0f}) | {S0:.4f} | {two(u):.4f} |')
open(out, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
