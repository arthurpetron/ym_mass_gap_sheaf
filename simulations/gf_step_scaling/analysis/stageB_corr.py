#!/usr/bin/env python3
"""Cross-correlation between L and 2L estimators. (1) series-level: corr of g^2(L,beta) and g^2(2L,beta) measurement series (independent chains: expect 0 within 1/sqrt(n));
(2) pair-shift covariance from the joint bootstrap (shared L=8, shared fit) and the effect on the continuum error (full vs diagonal covariance)."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from joint_fit import *
dirs = sys.argv[1].split(',')
d = Data(dirs)
lines = ['## (1) corr of the g^2 series of L and 2L at the same beta, measurement index by index (c=0.3)', '', '| pair | beta | n | corr | 1/sqrt(n) |', '|---|---|---|---|---|']
for (L, L2) in ((4, 8), (6, 12), (8, 16)):
    for b in sorted({b for (l, b) in d.runs if l == L and (L2, b) in d.runs}):
        r1 = d.runs[(L, b)][0][1]; r2 = d.runs[(L2, b)][0][1]
        try:
            i1 = time_index(r1, 0.3); i2 = time_index(r2, 0.3)
        except AssertionError: continue
        n = min(len(r1['sweep']), len(r2['sweep']))
        x1 = r1['E'][:n, i1, 0] * r1['times'][i1] ** 2; x2 = r2['E'][:n, i2, 0] * r2['times'][i2] ** 2
        lines.append(f'| {L}->{L2} | {b:g} | {n} | {np.corrcoef(x1, x2)[0,1]:+.3f} | {1/np.sqrt(n):.3f} |')
lines += ['', '## (2) continuum error with full bootstrap covariance vs diagonal (x form, 3 pairs, M=2)', '', '| c | u | a (full cov) | err | chi2 | a (diag) | err | corr(4->8, 8->16) | corr(4->8, 6->12) | corr(6->12, 8->16) |', '|---|---|---|---|---|---|---|---|---|---|']
for c in (0.3, 0.4):
    J = Joint(d, c, 2, [(4, 8), (6, 12), (8, 16)], [1.3, 1.6, 2.0, 2.4], nboot=1500)
    for iu, u in enumerate(J.targets):
        f = continuum(J, iu, [0, 1, 2], 'a+bx'); g = continuum(J, iu, [0, 1, 2], 'a+bx', diagonal=True)
        C, _ = J.cov(iu, [0, 1, 2]); R = C / np.sqrt(np.outer(np.diag(C), np.diag(C)))
        lines.append(f"| {c} | {u:g} | {f['a']:.4f} | {f['err']*1e4:.0f}e-4 | {f['chi2']:.1f} | {g['a']:.4f} | {g['err']*1e4:.0f}e-4 | {R[0,2]:+.2f} | {R[0,1]:+.2f} | {R[1,2]:+.2f} |")
open(sys.argv[2], 'w').write('\n'.join(lines) + '\n'); print('\n'.join(lines))
