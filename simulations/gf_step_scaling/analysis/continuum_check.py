#!/usr/bin/env python3
"""Weighted linear-in-(a/L)^2 fits of 1/u-1/Sigma over the step-scaling pairs, with chi2/dof (3 pairs -> 1 dof) and
the two-finest-pairs fit (exact, no dof). Input: stepscaling_<norm>.csv from stepscale.py. Errors: the bootstrap errors of
each pair (stat.+beta interpolation); L=8 enters two pairs (as 2L of 4->8 and L of 8->16): the shift errors are slightly
correlated and this is ignored. usage: continuum_check.py RESDIR NORM"""
import sys, csv, os, numpy as np
res, norm = sys.argv[1], sys.argv[2]
rows = list(csv.DictReader(open(os.path.join(res, f'stepscaling_{norm}.csv'))))
S0 = float(rows[0]['one_loop_shift'])
out = ['| c | M | u | shift 4->8 | 6->12 | 8->16 | 3-pair fit a/L->0 | chi2 (1 dof) | slope | 2 finest pairs (exact) | one-loop |', '|---|---|---|---|---|---|---|---|---|---|---|']
for c in ('0.3', '0.4'):
  for M in ('2', '3'):
    for u in ('1.3', '1.6', '2.0', '2.4'):
        pts = {}
        for r in rows:
            if r['c'] == c and r['M'] == M and abs(float(r['u']) - float(u)) < 1e-9:
                pts[int(r['pair'].split('->')[0])] = (float(r['inv_shift']), float(r['inv_shift_err']))
        if set(pts) != {4, 6, 8}: continue
        Ls = [4, 6, 8]; x = np.array([1.0 / L ** 2 for L in Ls]); y = np.array([pts[L][0] for L in Ls]); e = np.array([pts[L][1] for L in Ls])
        A = np.vstack([np.ones(3), x]).T; W = np.diag(1 / e ** 2)
        cov = np.linalg.inv(A.T @ W @ A); p = cov @ A.T @ W @ y
        chi2 = float(np.sum(((A @ p - y) / e) ** 2))
        x2 = x[1:]; y2 = y[1:]; sl = (y2[1] - y2[0]) / (x2[1] - x2[0]); c2 = y2[1] - sl * x2[1]
        e2 = np.sqrt((e[2] * x2[0] / (x2[0] - x2[1])) ** 2 + (e[1] * x2[1] / (x2[0] - x2[1])) ** 2)
        out.append(f"| {c} | {M} | {u} | {y[0]:.4f}({e[0]*1e4:.0f}) | {y[1]:.4f}({e[1]*1e4:.0f}) | {y[2]:.4f}({e[2]*1e4:.0f}) | {p[0]:.4f}({np.sqrt(cov[0,0])*1e4:.0f}) | {chi2:.1f} | {p[1]:.2f} | {c2:.4f}({e2*1e4:.0f}) | {S0:.4f} |")
print('\n'.join(out))
