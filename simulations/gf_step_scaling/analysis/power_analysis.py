#!/usr/bin/env python3
"""Power analysis for the step-scaling slope k1 in s(u) = s0 + k1 u + k2 u^2 (s0 = 2 b0 ln2 fixed), from EXISTING errors (no new MC).
Error model (calibrated on the existing ensembles, c=0.3, sep >= 5 so tau_int = 0.5): relative error of g2 = RHO/sqrt(N_meas), RHO = 0.075 (measured 0.0705-0.0824 for
L = 6..24, N = 300..6000). Pointwise shift s = 1/g2(L) - 1/g2(2L): err = hypot(rho_L/u, rho_2L/Sigma), Sigma = 1/(1/u - s).
Existing 6->12 and 8->16 pairs use their actual joint-fit errors (E_forms.md: 0.0005/0.0009 and 0.0007/0.0009 at u = 2.41/1.54), scaled as 1/u elsewhere
(0.0013/u, 0.0015/u).  Continuum value = weighted linear fit in x = 1/L^2 over the pairs available (6,8,12[,16]); errors of different pairs/u independent (optimistic:
shared ensembles and interpolation correlations ignored, as in the existing fits). Statistical only: extrapolation-form systematics NOT included.
usage: power_analysis.py OUT.md"""
import sys, numpy as np
RHO = 0.075; S0 = 2 * np.log(2) * 11 / (24 * np.pi ** 2); K1 = 0.0027
b0 = 11 / (24 * np.pi ** 2); b1 = 136 / 3 / (16 * np.pi ** 2) ** 2
def two(u, n=4000):
    x = 1 / u; h = np.log(2) / n
    for _ in range(n): x -= h * (2 * b0 + 2 * b1 / x)
    return 1 / u - x
def pair_err(u, N1, N2, s):
    Sig = 1 / (1 / u - s); return np.hypot(RHO / np.sqrt(N1) / u, RHO / np.sqrt(N2) / Sig)
def cont_err(es, Ls):
    x = np.array([1.0 / L ** 2 for L in Ls]); W = np.diag(1 / np.array(es) ** 2); A = np.column_stack([np.ones_like(x), x])
    return np.sqrt(np.linalg.inv(A.T @ W @ A)[0, 0])
def sigk1(us, sig, k2free):
    us = np.array(us); w = 1 / np.array(sig) ** 2
    A = np.column_stack([us, us ** 2]) if k2free else us[:, None]
    if k2free and len(us) < 3: return np.nan
    return np.sqrt(np.linalg.inv(A.T @ (w[:, None] * A))[0, 0])
def point(u, N12, N24, N16=None, N32=None, existing=False, e6=None, e8=None):
    s = two(u)
    es = [(e6 if e6 is not None else 0.0013 / u), (e8 if e8 is not None else 0.0015 / u), pair_err(u, N12, N24, s)]; Ls = [6, 8, 12]
    if N32: es.append(pair_err(u, N16, N32, s)); Ls.append(16)
    return cont_err(es, Ls), es
rows = []; out = []
def plan(name, pts):
    sig = [p[0] for p in pts]; us = [p[2] for p in pts]
    s2 = sigk1(us, sig, True); s1 = sigk1(us, sig, False)
    rows.append((name, us, sig, s1, s2))
# existing continuum errors at the two u's (E_forms c=0.3, 3-pair fit): 0.0015 (u=2.41), 0.0021 (u=1.54)
u1, u2 = 1.54, 2.41
mk = lambda u, N12, N24, e6=None, e8=None, N16=None, N32=None: (*point(u, N12, N24, N16, N32, e6=e6, e8=e8), u)
P0 = [mk(u1, 600, 300, 0.0009, 0.0009), mk(u2, 600, 300, 0.0005, 0.0007)]
P1 = [mk(u1, 600, 1200, 0.0009, 0.0009), mk(u2, 600, 1200, 0.0005, 0.0007)]
P1b = [mk(u1, 2400, 1200, 0.0009, 0.0009), mk(u2, 2400, 1200, 0.0005, 0.0007)]
extra = [mk(u, 1200, 300) for u in (1.0, 1.9, 2.9)]
P2 = P1b + extra
P3 = [mk(u1, 2400, 1200, 0.0009, 0.0009, 2000, 300), mk(u2, 2400, 1200, 0.0005, 0.0007, 2000, 300)] + extra
for nm, P in [('P0 current (2 u, 300 meas L=24)', P0), ('P1 4x L=24 (1200 meas) at the 2 beta', P1), ("P1' = P1 + 4x L=12 (2400 meas)", P1b), ("P2 = P1' + 12->24 at u=1.0, 1.9, 2.9 (300 meas L=24, 1200 L=12; 6->12, 8->16 at existing quality)", P2), ('P3 = P2 + 16->32 at the 2 original u (300 meas L=32, 2000 L=16)', P3)]:
    plan(nm, P)
sig4 = [x * 0.5 for x in [p[0] for p in P2]]; rows.append(('P2x4 = P2 with 4x all statistics (all pairs, all u)', [p[2] for p in P2], sig4, sigk1([p[2] for p in P2], sig4, False), sigk1([p[2] for p in P2], sig4, True)))
sig16 = [x * 0.25 for x in [p[0] for p in P2]]; rows.append(('P2x16 = P2 with 16x all statistics', [p[2] for p in P2], sig16, sigk1([p[2] for p in P2], sig16, False), sigk1([p[2] for p in P2], sig16, True)))
out.append(f'Model: rel. err(g2) = {RHO}/sqrt(N); s0 = {S0:.4f}; test slope k1 = {K1} (exact two-loop: s(1.54)={two(1.54):.4f}, s(2.41)={two(2.41):.4f}; its series slope 2 ln2 b1 = {2*np.log(2)*b1:.5f}, k2 ~ {(two(2.4)-S0-2*np.log(2)*b1*2.4)/2.4**2:.5f}).')
out.append(f'Check vs existing: model 3-pair continuum error at u=2.41, 1.54 with N24=300 / existing: {P0[1][0]:.4f}, {P0[0][0]:.4f} / 0.0015, 0.0021 (E_forms.md, c=0.3).\n')
out.append('| plan | u values | continuum error per u | sigma(k1), k2 = 0 fixed | sigma(k1), k2 free | k1=0.0027 vs k1=0 (sigma, k2 fixed) | (k2 free) |\n|---|---|---|---|---|---|---|')
for nm, us, sig, s1, s2 in rows:
    out.append(f'| {nm} | {", ".join(f"{u:g}" for u in us)} | {", ".join(f"{x:.4f}" for x in sig)} | {s1:.5f} | {"undetermined (2 points)" if np.isnan(s2) else f"{s2:.5f}"} | {K1/s1:.1f} | {"-" if np.isnan(s2) else f"{K1/s2:.1f}"} |')
open(sys.argv[1], 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))
