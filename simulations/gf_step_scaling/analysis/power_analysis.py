#!/usr/bin/env python3
"""Power analysis for the step-scaling slope k1 in s(u) = s0 + k1 u + k2 u^2 (s0 = 2 b0 ln2 fixed), from EXISTING errors (no new MC).
Error model (calibrated on the existing ensembles, c=0.3, sep >= 5 so tau_int = 0.5): relative error of g2 = RHO/sqrt(N_meas), RHO = 0.075 (measured 0.0705-0.0824 for
L = 6..24, N = 300..6000). Pointwise shift s = 1/g2(L) - 1/g2(2L): err = hypot(rho_L/u, rho_2L/Sigma), Sigma = 1/(1/u - s).
Existing 6->12 and 8->16 pairs use their actual joint-fit errors (E_forms.md: 0.0005/0.0009 and 0.0007/0.0009 at u = 2.41/1.54), scaled as 1/u elsewhere
(0.0013/u, 0.0015/u).  Continuum value = weighted linear fit in x = 1/L^2 over the pairs available (6,8,12[,16]); errors of different pairs/u independent (optimistic:
shared ensembles and interpolation correlations ignored, as in the existing fits). Statistical only: extrapolation-form systematics NOT included.
usage: power_analysis.py OUT.md [ACTUAL.json [TAG]]
With ACTUAL.json (written by stage3_final.py, 2026-10-18) the model table is followed by a section that uses the ACTUAL measured pair errors
(per ensemble variance components; interpolated old-u pairs split 50/50 between L and 2L with N_eff from the 0.075/sqrt(N) model) and
projects sigma(k1) (k2 free and k2 = 0; primary continuum form lin3 over 6->12, 8->16, 12->24) for further statistics, 16->32, and
the CPU-h-optimal allocation (water-filling, full refit of the continuum and slope fits at every step; statistical only)."""
import sys, os, numpy as np
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
if len(sys.argv) > 2:
    import json
    J = json.load(open(sys.argv[2])); TAG = sys.argv[3] if len(sys.argv) > 3 else 'nominal'; Pall = J[TAG]['P']
    COST = {6: 0.034, 8: 0.173, 12: 1.30, 16: 4.0, 24: 41.0, 32: 210.0}   # CPU-s per measurement (c <= 0.4), measured (prod3 stderr, stage E)
    TARGET = 0.0009; NEFF = {}
    def model(c, extra=None):
        """per u: list of (u, {L: [(key, var0, n0)]}) from the actual data"""
        pts = []
        for pt in Pall[str(c)]:
            pr = {}
            for L in ('6', '8', '12'):
                d = pt['pairs'][L]; comps = []
                for k in d['comp']:
                    key = (k['L'], str(k['beta']) if k['n'] else f"J{pt['un']}")
                    n0 = k['n'] if k['n'] else NEFF.setdefault(key, (RHO / pt['u']) ** 2 / k['var'])   # c-independent N_eff (set by c=0.3)
                    comps.append((key, k['var'], n0))
                pr[int(L)] = comps
            if extra and pt['un'] in extra: pr[16] = extra[pt['un']](pt['u'])
            pts.append((pt['u'], pr))
        return pts
    def sig(pts, n, k2free, Ls=(6, 8, 12)):
        us, es = [], []
        for u, pr in pts:
            LL = [L for L in Ls if L in pr] if 16 not in pr or 16 not in Ls else list(Ls)
            LL = [L for L in LL if L in pr]
            e = [np.sqrt(sum(v * n0 / n.get(k, n0) for k, v, n0 in pr[L])) for L in LL]
            us.append(u); es.append(cont_err(e, LL))
        return sigk1(us, es, k2free)
    def ens(pts):
        E = {}
        for u, pr in pts:
            for L, comps in pr.items():
                for k, v, n0 in comps: E[k] = n0
        return E
    def cost_extra(n, E): return sum(COST[k[0]] * (n[k] - E[k]) for k in n) / 3600
    def waterfill(ptsc, k2free, target=None, budget=None):
        """CPU-h-optimal extra statistics so that sigma(k1) <= target for EVERY scheme in ptsc (or best sigma for the budget)."""
        E = {}; [E.update(ens(p)) for p in ptsc]
        def alloc(lam):
            n = dict(E)
            for _ in range(3):   # fixed-point on the linearised importance a_k ~ d sigma^2 / d(1/n_k)
                for k in E:
                    a = 0
                    for p in ptsc:
                        s0 = sig(p, n, k2free) ** 2; m = dict(n); m[k] = n[k] * 1.01; a = max(a, (s0 - sig(p, m, k2free) ** 2) / (1 / n[k] - 1 / m[k]))
                    n[k] = max(E[k], lam * np.sqrt(max(a, 0) / COST[k[0]]))
            return n
        lo, hi = 1e-3, 1e9
        for _ in range(60):
            lam = np.sqrt(lo * hi); n = alloc(lam); worst = max(sig(p, n, k2free) for p in ptsc); cst = cost_extra(n, E)
            if (target is not None and worst > target) or (budget is not None and cst < budget): lo = lam
            else: hi = lam
        n = alloc(hi); return n, cost_extra(n, E), [sig(p, n, k2free) for p in ptsc], E
    P = {c: model(c) for c in (0.3, 0.4)}
    E = {}; [E.update(ens(p)) for p in P.values()]
    cur_cpu = sum(COST[k[0]] * n0 for k, n0 in E.items()) / 3600
    out.append(f'\n## Re-run with the ACTUAL measured errors (items 1-2 final data, `{os.path.basename(sys.argv[2])}`, errors: {TAG})\n')
    out.append(f'Ensembles entering the primary (lin3) k1 fits: {len(E)} (interpolated old-u pairs counted as 2 pseudo-ensembles each); their CPU cost at the measured rates: {cur_cpu:.1f} CPU-h.\n')
    out.append('| plan | sigma(k1) c=0.3, k2 free | c=0.4, k2 free | c=0.3, k2=0 | c=0.4, k2=0 | extra CPU-h (est.) |\n|---|---|---|---|---|---|')
    def row(nm, n, cst, extra=None, Ls=(6, 8, 12)):
        pp = {c: model(c, extra) for c in (0.3, 0.4)}
        v = [sig(pp[c], n, k2) for k2 in (True, False) for c in (0.3, 0.4)]
        out.append(f'| {nm} | {v[0]:.5f} | {v[1]:.5f} | {v[2]:.5f} | {v[3]:.5f} | {cst} |'); return v
    v0 = row('A0 actual (items 1-2 done)', E, '0')
    for F in (2, 4, 16):
        row(f'A{F}x: {F}x statistics on every ensemble', {k: F * x for k, x in E.items()}, f'{(F - 1) * cur_cpu:.0f}')
    Fneed = max((v0[0] / TARGET) ** 2, (v0[1] / TARGET) ** 2)
    out.append(f'| uniform factor needed for sigma(k1) <= {TARGET} at BOTH c (k2 free): {Fneed:.1f}x | | | | | {(Fneed - 1) * cur_cpu:.0f} |')
    # item-3-like: 16->32 at the two original u (300 meas L=32, 2000 L=16), model errors
    ext = {1.54: lambda u: [((16, 'new16_154'), (RHO / u) ** 2 / 2000, 2000), ((32, 'new32_154'), (RHO / u) ** 2 / 300, 300)],
           2.41: lambda u: [((16, 'new16_241'), (RHO / u) ** 2 / 2000, 2000), ((32, 'new32_241'), (RHO / u) ** 2 / 300, 300)]}
    for Ls, nm in (((6, 8, 12, 16), 'lin over 6,8,12,16'), ((8, 12, 16), 'lin over finest 3 = 8,12,16 at those u')):
        pp = {c: model(c, ext) for c in (0.3, 0.4)}
        v = [sig(pp[c], E, k2, Ls) for k2 in (True, False) for c in (0.3, 0.4)]
        out.append(f'| A-16->32 (P3/"item 3"): 16->32 at u=1.54, 2.41 (300 meas L=32, 2000 L=16), {nm} | {v[0]:.5f} | {v[1]:.5f} | {v[2]:.5f} | {v[3]:.5f} | ~{2 * (300 * 210 + 2000 * 4.0) / 3600 + 0.7:.0f} |')
    for k2free in (True, False):
        n, cst, ss, _ = waterfill([P[0.3], P[0.4]], k2free, target=TARGET)
        out.append(f'| optimal allocation to sigma(k1) <= {TARGET} at both c, k2 {"free" if k2free else "= 0"} (water-filling) | {ss[0]:.5f}{"" if k2free else " (k2=0 fit)"} | {ss[1]:.5f} | | | {cst:.0f} |')
        top = sorted(((COST[k[0]] * (n[k] - E[k]) / 3600, k, E[k], n[k]) for k in n), reverse=True)[:6]
        out.append('|   largest extra: ' + '; '.join(f'L={k[0]} {k[1]}: {x0:.0f} -> {x1:.0f} meas ({ch:.0f} CPU-h)' for ch, k, x0, x1 in top if ch > 0.05) + ' | | | | | |')
        n, cst, ss, _ = waterfill([P[0.3], P[0.4]], k2free, budget=70.0)
        out.append(f'| best within the 70 CPU-h cap, k2 {"free" if k2free else "= 0"} | {ss[0]:.5f} | {ss[1]:.5f} | | | {cst:.0f} |')
    out.append('\nReading: statistical only, fixed continuum form (lin3) and fixed u set; extrapolation-form spread and c=0.3/0.4 disagreement are NOT reduced by statistics in this model.')
open(sys.argv[1], 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))
