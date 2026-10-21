#!/usr/bin/env python3
"""prod7 phase 2: read tuning runs (tune_L*_b*_tw.csv), interpolate 1/g2(c=0.3) linearly in beta per L to target u, write jobs7_prod.txt
(R1 subset first, then 16->32). Only uses c=0.3 to define u. Q per config is in the csv (col Q per flow time). Usage: python3 mk_prod.py [--write]"""
import sys, glob, re, numpy as np
sys.path.insert(0, '/Users/darthur/Dore Dropbox/Arthur Petron/codex/ym_mass_gap_sheaf/simulations/gf_step_scaling/analysis')
import twist_norm as T
def g2(fn, L, c=0.3):
    d = np.loadtxt(fn, comments='#'); t = c*c*L*L/8
    return t*t*d[:, 3].mean()/T.N_twist_lat(c, L), np.abs(d[:, 5]).max()
tune = {}
for fn in sorted(glob.glob('tune_L*_b*_tw.csv')):
    L, b = re.match(r'tune_L(\d+)_b([\d.]+)_tw', fn).groups(); L = int(L); b = float(b)
    g, qm = g2(fn, L); tune.setdefault(L, []).append((b, g, qm)); print(f'L{L} beta{b:.2f} g2={g:.4f} max|Q|={qm:.3f}')
# targets: u defined as g2(L=12, beta12) at c=0.3 (prod5/6 convention)
U_EXIST = {1.49: (4.44, 4.60, 1.48933), 2.01: (3.785, 3.929, 2.01384), 2.40: (3.47, 3.62, 2.39768), 2.94: (3.21, 3.33, 2.94334)}
def beta_for(L, u):
    pts = sorted(tune[L], key=lambda x: abs(1/x[1]-1/u))[:2]
    (b1, g1, _), (b2, g2_, _) = pts
    return b1 + (1/u - 1/g1)*(b2 - b1)/(1/g2_ - 1/g1)
F = '--twist 1 --therm 300 --sep 10 --nor 4 --eps 0.1 --alt-eps 0 --start cold --ckpt-every 50 --c 0.3,0.4'
jobs = []; s = 97100
def J(name, L, b, n):
    global s; s += 1; jobs.append(f'{name}|su2gf --L {L} --beta {b:.3f} {F} --nmeas {n} --seed {s}')
new = {}
for u in (3.6, 4.5):
    new[u] = (beta_for(8, u), beta_for(12, u), beta_for(16, u)); print('u', u, 'beta8,12,16 = %.3f %.3f %.3f' % new[u])
b16 = {u: beta_for(16, v[2]) for u, v in U_EXIST.items()}; b16.update({u: new[u][2] for u in new}); print('beta16', b16)
# R1 first (longest first): L24 chains, L16(beta8), L12, L8
for u in (3.6, 4.5):
    for ch in 'ab': J(f'su2_L24_b{new[u][1]:.3f}_u{u}{ch}', 24, new[u][1], 600)
for u in (3.6, 4.5):
    J(f'su2_L16_b{new[u][0]:.3f}_u{u}', 16, new[u][0], 1200); J(f'su2_L12_b{new[u][1]:.3f}_u{u}', 12, new[u][1], 1200); J(f'su2_L8_b{new[u][0]:.3f}_u{u}', 8, new[u][0], 2000)
# then 16->32 for all 6 u: L32 4x300, L16(beta16) 1200
for u in (3.6, 4.5, 2.94, 2.40, 2.01, 1.49):
    for ch in 'abcd': J(f'su2_L32_b{b16[u]:.3f}_u{u}{ch}', 32, b16[u], 280)
    J(f'su2_L16_b{b16[u]:.3f}_u{u}s', 16, b16[u], 1200)
print('\n'.join(jobs))
if '--write' in sys.argv: open('jobs7_prod.txt', 'w').write('\n'.join(jobs) + '\n'); print('wrote jobs7_prod.txt', len(jobs))
