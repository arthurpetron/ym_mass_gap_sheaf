#!/usr/bin/env python3
"""prod6 pre-run analysis: A2 weak-coupling probe (L12, beta=30, twisted) and B beta tuning (twisted, u~2.0, c=0.3).
g2_TGF = t^2 <E_clover> / Nhat_T(c,L) (lattice tree-level, twist_norm.N_twist_lat), same convention as tw_analysis.py (prod5). MC evidence only."""
import sys, os, glob, json, numpy as np
A = '/Users/darthur/Dore Dropbox/Arthur Petron/codex/ym_mass_gap_sheaf/simulations/gf_step_scaling/analysis'
sys.path.insert(0, A)
from gfana import load_run, time_index, gamma_method, jackknife_binned
from twist_norm import N_twist_lat, N_twist_cont
R = '/Users/darthur/ym_numerics_runs/prod6'; R5 = '/Users/darthur/ym_numerics_runs/prod5'
CS = (0.3, 0.4); rng = np.random.default_rng(20261020)
def g2(f):
    r = load_run(f, 3)
    X = np.column_stack([r['times'][time_index(r, c)] ** 2 * r['E'][:, time_index(r, c), 0] / N_twist_lat(c, r['L']) for c in CS])
    return r, X
def bboot(x, B=10, NB=2000):
    n = len(x); k = int(np.ceil(n / B)); out = np.empty(NB)
    for i in range(NB):
        st = rng.integers(0, n - B + 1, size=k); out[i] = x[(st[:, None] + np.arange(B)).ravel()[:n]].mean()
    return out.std()
out = {}
print('=== A2 probe: su2_L12_b30_wcprobe ===')
r, X = g2(R + '/su2_L12_b30_wcprobe.csv'); b = r['beta']; g0 = 4.0 / b
print(f"L={r['L']} beta={b} N={len(X)} sweeps {r['sweep'][0]:.0f}..{r['sweep'][-1]:.0f}  g0^2=4/beta={g0:.5f}; plaq mean {r['plaq'].mean():.6f}")
A2 = {}
for i, c in enumerate(CS):
    x = X[:, i] / g0
    m, e, tau, W = gamma_method(x); jm, je, jb = jackknife_binned(x, 20); be = bboot(x, 10); be20 = bboot(x, 20)
    h = len(x) // 2; m1, e1, *_ = gamma_method(x[:h]); m2, e2, *_ = gamma_method(x[h:])
    q = len(x) // 10; m0, e0, *_ = gamma_method(x[:q])
    srel = x.std() / m
    A2[c] = dict(mean=m, gamma_err=e, tau=tau, W=W, jk_err=je, jk_bin=jb, boot_B10=be, boot_B20=be20, sig_rel_per_meas=srel,
                 sig_rel_eff=srel * np.sqrt(2 * tau), half1=(m1, e1), half2=(m2, e2), first10pct=(m0, e0), nlat_over_ncont=N_twist_lat(c, 12) / N_twist_cont(c))
    print(f"c={c}: g2/(4/beta) = {m:.5f} +- {e:.5f} (Gamma, tau_int={tau:.2f}, W={W}); jackknife(20 bins of {jb}) +- {je:.5f}; block-boot B10 +- {be:.5f}, B20 +- {be20:.5f}")
    print(f"      rel err {e/m*100:.3f}%  per-meas rel sigma {srel:.4f}, effective (x sqrt(2tau)) {srel*np.sqrt(2*tau):.4f}; halves {m1:.5f}({e1*1e5:.0f}) / {m2:.5f}({e2*1e5:.0f}) diff {(m2-m1)/np.hypot(e1,e2):+.1f} sig; first 10% {m0:.5f}({e0*1e5:.0f})")
d = X[:, 1] / X[:, 0]; print(f"corr(c0.3,c0.4) = {np.corrcoef(X.T)[0,1]:.3f}; Q rms at c=0.3 time: {np.sqrt(np.mean(r['E'][:, time_index(r,0.3), 2]**2)):.2e}")
out['A2'] = A2
print('\n=== B tuning (twisted, c=0.3 target u=2.0) ===')
T = {}
for f in sorted(glob.glob(R + '/tune_L*_tw.csv')):
    r, X = g2(f); L, b = r['L'], round(r['beta'], 4); row = []
    for i, c in enumerate(CS):
        m, e, tau, W = gamma_method(X[:, i]); be = bboot(X[:, i], 10)
        h = len(X) // 2; m1, e1, *_ = gamma_method(X[:h, i]); m2, e2, *_ = gamma_method(X[h:, i])
        row.append(dict(g2=m, err=max(e, be), gamma_err=e, boot=be, tau=tau, drift_sig=(m2 - m1) / np.hypot(e1, e2)))
    T.setdefault(L, {})[b] = row; print(f"L={L} beta={b} N={len(X)}: " + '; '.join(f"c={c}: g2={q['g2']:.4f}({q['gamma_err']*1e4:.0f}) boot({q['boot']*1e4:.0f}) tau={q['tau']:.2f} drift {q['drift_sig']:+.1f}sig" for c, q in zip(CS, row)))
# prod5 points for a cross-check of the beta dependence (pooled chains)
P5 = {}
for f in sorted(glob.glob(R5 + '/su2_L*_tw?.csv')):
    r, X = g2(f); L = r['L']
    if L not in (6, 8, 12): continue
    P5.setdefault((L, round(r['beta'], 4)), []).append(X)
BS = {}
print('\nInterpolation linear in 1/g2 vs beta between the two tune points (convention: g2_TGF c=0.3, lattice Nhat_T; error by MC over both points, independent):')
for L in sorted(T):
    (b1, r1), (b2, r2) = sorted(T[L].items())
    res = {}
    for i, c in enumerate(CS):
        for tgt in ((2.0,) if c == 0.3 else (2.0,)):
            y1, y2 = 1 / r1[i]['g2'], 1 / r2[i]['g2']
            bs = b1 + (1 / tgt - y1) * (b2 - b1) / (y2 - y1)
            s1 = np.abs(rng.normal(r1[i]['g2'], r1[i]['err'], 20000)); s2 = np.abs(rng.normal(r2[i]['g2'], r2[i]['err'], 20000))
            mc = b1 + (1 / tgt - 1 / s1) * (b2 - b1) / (1 / s2 - 1 / s1)
            slope = (y2 - y1) / (b2 - b1)
            res[c] = dict(beta_star=bs, err=float(np.std(mc)), slope_inv_g2_per_beta=slope, extrap=not (b1 <= bs <= b2))
    # quadratic fit incl. prod5 points (cross-check of curvature), c=0.3
    pts = [(b, 1 / q[0]['g2'], q[0]['err'] / q[0]['g2'] ** 2) for b, q in T[L].items()]
    for (LL, b), Xs in P5.items():
        if LL == L:
            x = np.vstack(Xs)[:, 0]; m, e, *_ = gamma_method(x); pts.append((b, 1 / m, e / m ** 2))
    pts = np.array(sorted(pts)); near = pts[np.argsort(np.abs(pts[:, 0] - res[0.3]['beta_star']))[:4]]
    w = 1 / near[:, 2] ** 2; cq = np.polyfit(near[:, 0], near[:, 1], 2, w=np.sqrt(w)); rts = np.roots(cq - np.array([0, 0, 0.5]))
    rts = [x.real for x in rts if abs(x.imag) < 1e-9 and 3 < x.real < 5]; bq = min(rts, key=lambda x: abs(x - res[0.3]['beta_star'])) if rts else float('nan')
    res['quad4_cross'] = bq; res['quad_pts'] = near[:, :2].tolist()
    BS[L] = res
    print(f"L={L}: tune betas {b1},{b2}: c=0.3 beta*(u=2.0) = {res[0.3]['beta_star']:.4f} +- {res[0.3]['err']:.4f}{' (EXTRAPOLATED)' if res[0.3]['extrap'] else ''}; "
          f"d(1/g2)/dbeta={res[0.3]['slope_inv_g2_per_beta']:.4f}; quad fit over 4 nearest betas (tune+prod5): {bq:.4f}; [c=0.4 beta(g2=2.0) {res[0.4]['beta_star']:.4f}]")
out['tune'] = {str(L): {str(b): v for b, v in d.items()} for L, d in T.items()}; out['beta_star'] = {str(L): {str(k): v for k, v in d.items()} for L, d in BS.items()}
json.dump(out, open(R + '/ana/prepro.json', 'w'), indent=1, default=float)
