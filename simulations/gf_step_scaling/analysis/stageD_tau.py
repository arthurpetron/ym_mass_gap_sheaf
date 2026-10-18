#!/usr/bin/env python3
"""Stage D(b): tau_int from sep=1 runs (each sample = 1 heatbath+4 overrelax sweep... see run header 'sep'). tau_int in units of measurement spacing and in sweeps,
Gamma-method (Wolff windowing, S=1.5/2 default of gfana), normalised autocorrelation rho(1,2,4,8), and the sep=1 sample error vs naive error.
usage: stageD_tau.py OUT.md DIR NAME[,NAME...]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
out, dr, names = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
L_ = ['| run | L | beta | n | sep | obs | mean | Gamma err | naive err | tau_int (samples) | tau_int (sweeps) | rho(1) | rho(2) | rho(4) | rho(8) |', '|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|']
def rho(x, k): x = x - x.mean(); return float(np.mean(x[:-k] * x[k:]) / np.var(x))
for nm in names:
    r = load_run(os.path.join(dr, nm + '.csv'), 2 if nm.startswith('u1') else 3)
    obs = []
    for c in (0.3, 0.4):
        i = time_index(r, c); t = r['times'][i]
        obs.append((f'g2 c={c}', t * t * r['E'][:, i, 0] / N_lat(c, r['L'])))
    obs.append(('plaquette', r['plaq']) if 'plaq' in r else ('E(c=0.3)', r['E'][:, time_index(r, 0.3), 0]))
    for lab, x in obs:
        m, e, tau, W = gamma_method(x)
        L_.append(f"| {nm} | {r['L']} | {r['beta']:g} | {len(x)} | {r['sep']} | {lab} | {m:.5f} | {e:.5f} | {x.std(ddof=1)/np.sqrt(len(x)):.5f} | {tau:.2f} | {tau*r['sep']:.2f} | {rho(x,1):.3f} | {rho(x,2):.3f} | {rho(x,4):.3f} | {rho(x,8):.3f} |")
open(out, 'w').write('\n'.join(L_) + '\n'); print('\n'.join(L_))
