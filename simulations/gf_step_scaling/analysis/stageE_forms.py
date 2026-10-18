#!/usr/bin/env python3
"""Stage E: continuum forms including 12->24. At u = g2(12,beta) for the two L=24 betas, shifts of 4->8, 6->12, 8->16 from the joint bootstrap (M=2),
the pointwise 12->24 shift; weighted linear fits in x=(1/L)^2 (L = smaller lattice) over pair subsets; errors independent (12->24 shares L=12 data with 6->12: neglected)."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from joint_fit import *
D = ['/Users/darthur/ym_numerics_runs/prod', '/Users/darthur/ym_numerics_runs/prod2']
d = Data(D, obs='clover', norm='lat')
def two(u, n=4000):
    """exact (numerically integrated) two-loop shift 1/u - 1/Sigma for L->2L: d(1/g2)/dlnL = -(2 b0 + 2 b1 g2), b0 = 11/(24 pi^2), b1 = (136/3)/(16 pi^2)^2 (SU(2), Nf=0)"""
    b0 = 11 / (24 * np.pi ** 2); b1 = 136 / 3 / (16 * np.pi ** 2) ** 2; x = 1 / u; h = np.log(2) / n
    for _ in range(n): x -= h * (2 * b0 + 2 * b1 / x)
    return 1 / u - x
out = [f'one-loop {S0:.4f}\n', '| beta | c | u | pair shifts 4->8, 6->12, 8->16, 12->24 | 2 pairs (8,12) | 3 pairs (6,8,12) a, chi2 | 4 pairs a, chi2 | 3 pairs const (6,8,12) chi2 | exact two-loop |', '|---|---|---|---|---|---|---|---|---|']
def wfit(x, y, e, basis):
    A = np.array([[1, xi] if basis == 'lin' else [1] for xi in x]); W = np.diag(1 / np.array(e) ** 2)
    cov = np.linalg.inv(A.T @ W @ A); p = cov @ A.T @ W @ y; chi = float((y - A @ p) @ W @ (y - A @ p)); return p[0], np.sqrt(cov[0, 0]), chi, len(y) - A.shape[1]
for b in (3.6, 4.5):
    for c in (0.3, 0.4):
        a, z = d.g2(12, b, c), d.g2(24, b, c); u = a[0]
        s12 = 1 / a[0] - 1 / z[0]; e12 = np.hypot(a[1] / a[0] ** 2, z[1] / z[0] ** 2)
        J = Joint(d, c, 2, [(4, 8), (6, 12), (8, 16)], [u], nboot=800)
        s = [J.S[0, i, 0] for i in range(3)] + [s12]; e = [np.nanstd(J.S[1:, i, 0]) for i in range(3)] + [e12]
        x = [1 / 16, 1 / 36, 1 / 64, 1 / 144]
        r2 = wfit(x[2:], s[2:], e[2:], 'lin'); r3 = wfit(x[1:], s[1:], e[1:], 'lin'); r4 = wfit(x, s, e, 'lin'); rc = wfit(x[1:], s[1:], e[1:], 'const')
        f = lambda r: f'{r[0]:.4f}({r[1]*1e4:.0f}), chi2 {r[2]:.1f}/{r[3]}'
        out.append(f'| {b:g} | {c} | {u:.3f} | ' + ', '.join(f'{v:.4f}({ee*1e4:.0f})' for v, ee in zip(s, e)) + f' | {r2[0]:.4f}({r2[1]*1e4:.0f}) | {f(r3)} | {f(r4)} | {rc[0]:.4f}({rc[1]*1e4:.0f}), chi2 {rc[2]:.1f}/{rc[3]} | {two(u):.4f} |')
open('../results/followup/E_forms.md', 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))
