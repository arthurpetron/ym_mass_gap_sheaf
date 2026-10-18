#!/usr/bin/env python3
"""Stage E: thermalisation / sector check of the L=24 chains: first-half vs second-half z-score (Gamma-method errors) for g2(c=0.3,0.4),
plaquette; max|Q|, tau_int.  usage: stageE_therm.py OUT.md DIR NAME[,NAME]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
out, dr, names = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
L = ['| run | n | start | obs | mean | Gamma err | tau_int (samples) | 1st half | 2nd half | z (2nd-1st) | max&#124;Q&#124; (c=0.4) |', '|---|---|---|---|---|---|---|---|---|---|---|']
for nm in names:
    r = load_run(os.path.join(dr, nm + '.csv'), 3); n = len(r['sweep']); h = n // 2
    iq = time_index(r, 0.4); Qmax = np.abs(r['E'][:, iq, 2]).max()
    obs = [(f'g2 c={c}', (lambda i, t: t * t * r['E'][:, i, 0] / N_lat(c, 24))(time_index(r, c), r['times'][time_index(r, c)])) for c in (0.3, 0.4)] + [('plaquette', r['plaq'])]
    for lab, x in obs:
        m, e, tau, W = gamma_method(x); a, ea = gamma_method(x[:h])[:2]; b, eb = gamma_method(x[h:])[:2]
        L.append(f"| {nm} | {n} | {'cold' if nm.endswith('_cs') else 'hot'} | {lab} | {m:.5f} | {e:.5f} | {tau:.2f} | {a:.5f}({ea:.5f}) | {b:.5f}({eb:.5f}) | {(b-a)/np.hypot(ea,eb):+.2f} | {Qmax:.4f} |")
open(out, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
