#!/usr/bin/env python3
"""prod6 A2: weak-coupling check of the lattice tree-level twisted normalisation Nhat_T(c, L) (twist_norm.N_twist_lat), SU(2), twist n_12 = 1,
Wilson action + Wilson flow + clover E, cold (twist-eater) start, therm 500, sep 10.  R(L, beta, c) = g2_TGF / g0^2, g0^2 = 4/beta.
Weak-coupling expansion R - 1 = delta(L, c) + a(L, c) g0^2 + b(L, c) g0^4 + ...;  with g0^2 = 0.2 (beta 20) and 0.1 (beta 40):
    delta_meas(L) = 2 R40 - R20 - 1 = delta(L) - 0.02 b(L) + O(g0^6),     A(L) = (R20 - R40)/0.1 = a + 0.3 b.
delta(L) is the tree-level mismatch of Nhat_T at finite L (exactly 0 if Nhat_T is the correct lattice tree level); the L-independent part of 0.02 b is
not separable with two betas, so the test for an L-DEPENDENT normalisation error is the L dependence of delta_meas (constant fit, 1/L^2 fit, pairwise
differences). L=24: three independent chains per beta (wca/wcb/wcc) pooled. Errors: moving-block bootstrap (B=10 configs, same indices for c=0.3/0.4,
per chain) over independent ensembles; cross-checks: Gamma method (Wolff) and binned jackknife per ensemble; between-chain spread at L=24.
usage: a2_analysis.py OUTPREFIX [NBOOT] [B=10]      MC evidence only (not a proof, not a bound)."""
import sys, os, glob, json, re, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfana import load_run, time_index, gamma_method, jackknife_binned
from twist_norm import N_twist_lat, N_twist_cont
R6 = '/Users/darthur/ym_numerics_runs/prod6'; CS = (0.3, 0.4); LS = (8, 12, 16, 24); BETAS = (20.0, 40.0)
pref = sys.argv[1]; NB = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
B = next((int(a[2:]) for a in sys.argv[3:] if a.startswith('B=')), 10)
rng = np.random.default_rng(20261020)
def resample(n):
    k = int(np.ceil(n / B)); st = rng.integers(0, n - B + 1, size=k); return (st[:, None] + np.arange(B)[None, :]).ravel()[:n]
E = {}; CH = {}
for f in sorted(glob.glob(R6 + '/su2_L*_b[24]0_wc?.csv')):
    r = load_run(f, 3); L, b = r['L'], round(r['beta'], 6); g0 = 4.0 / b
    X = np.column_stack([r['times'][time_index(r, c)] ** 2 * r['E'][:, time_index(r, c), 0] / N_twist_lat(c, L) / g0 for c in CS])
    E.setdefault((L, b), []).append(X); CH.setdefault((L, b), []).append(os.path.basename(f)[:-4])
assert all((L, b) in E for L in LS for b in BETAS), sorted(E)
M0 = {k: np.vstack(v).mean(0) for k, v in E.items()}
BR = {k: np.empty((NB, 2)) for k in E}
for i in range(NB):
    for k, v in E.items(): BR[k][i] = np.vstack([c[resample(len(c))] for c in v]).mean(0)
md = ['# prod6 A2: weak-coupling check of the twisted tree-level normalisation Nhat_T(c, L) (a2_analysis.py)\n',
      f'MC evidence only -- not a proof, not a bound. R = g2_TGF/g0^2 with g2_TGF = t^2<E_clover>/Nhat_T(c,L), g0^2 = 4/beta. Bootstrap {NB} replicas, moving blocks of {B} configurations per chain (same indices for both c).\n',
      'delta_meas(L) = 2 R(beta=40) - R(beta=20) - 1 = delta_tree(L) - 0.02 b(L) + O(g0^6), where R - 1 = delta_tree + a g0^2 + b g0^4; A(L) = (R20 - R40)/0.1 = a + 0.3 b.\n',
      '## Ensembles: R per (L, beta), pooled chains; error comparison (bootstrap / Gamma / binned jackknife); tau_int per chain\n',
      '| L | beta | chains | N | R c=0.3 [boot] (Gamma) {jk} | R c=0.4 [boot] (Gamma) {jk} | tau_int c=0.3 / 0.4 per chain | rho(c) |', '|---|---|---|---|---|---|---|---|']
ENS = {}
for k in sorted(E):
    X = np.vstack(E[k]); be = BR[k].std(0); out = []
    for ic in range(2):
        # pooled Gamma / jackknife: combine per-chain errors (chains independent, weights n_i/N)
        gs = [gamma_method(c[:, ic]) for c in E[k]]; ns = np.array([len(c) for c in E[k]]); w = ns / ns.sum()
        ge = np.sqrt(sum((wi * g[1]) ** 2 for wi, g in zip(w, gs))); je = np.sqrt(sum((wi * jackknife_binned(c[:, ic], 20)[1]) ** 2 for wi, c in zip(w, E[k])))
        out.append(dict(mean=float(M0[k][ic]), boot=float(be[ic]), gamma=float(ge), jk=float(je), tau=[float(g[2]) for g in gs]))
    ENS[k] = out
    md.append(f"| {k[0]} | {k[1]:g} | {len(E[k])} | {len(X)} | " + ' | '.join(f"{o['mean']:.5f} [{o['boot']*1e5:.0f}] ({o['gamma']*1e5:.0f}) {{{o['jk']*1e5:.0f}}}" for o in out) +
              f" | {', '.join(f'{a:.2f}/{b_:.2f}' for a, b_ in zip(out[0]['tau'], out[1]['tau']))} | {np.corrcoef(X.T)[0,1]:.2f} |")
# L=24 between-chain spread
md.append('\n## L=24: chain means and between-chain consistency (chi2 of the chain means about their pooled mean, Gamma errors per chain)\n')
md.append('| beta | c | chain means (Gamma err) | chi2/dof | p | between-chain error of the pooled mean | bootstrap error |'); md.append('|---|---|---|---|---|---|---|')
from math import erf, exp, lgamma
def chi2_sf(x, k):  # survival function of chi2 with k dof (series, k small)
    from math import gamma as G
    import numpy as _n
    s = _n.linspace(0, x, 4001); f = s ** (k / 2 - 1) * _n.exp(-s / 2) / (2 ** (k / 2) * G(k / 2)); f[0] = f[1] if k < 2 else f[0]
    return float(max(0.0, 1 - getattr(_n, "trapezoid", getattr(_n, "trapz", None))(f, s)))
BETW = {}
for b in BETAS:
    k = (24, b)
    for ic, c in enumerate(CS):
        ms = np.array([x[:, ic].mean() for x in E[k]]); es = np.array([gamma_method(x[:, ic])[1] for x in E[k]])
        pm = M0[k][ic]; chi = float(((ms - pm) ** 2 / es ** 2).sum()); dof = len(ms) - 1; bce = float(ms.std(ddof=1) / np.sqrt(len(ms)))
        BETW[(b, c)] = dict(chi2=chi, dof=dof, p=chi2_sf(chi, dof), between=bce, boot=float(BR[k][:, ic].std()))
        md.append(f"| {b:g} | {c} | " + ', '.join(f'{m:.5f}({e*1e5:.0f})' for m, e in zip(ms, es)) + f" | {chi:.2f}/{dof} | {BETW[(b, c)]['p']:.3f} | {bce:.5f} | {BR[k][:, ic].std():.5f} |")
# delta(L), A(L)
D = {}; A = {}
for L in LS:
    for ic in range(2):
        r20 = np.concatenate([[M0[(L, 20.0)][ic]], BR[(L, 20.0)][:, ic]]); r40 = np.concatenate([[M0[(L, 40.0)][ic]], BR[(L, 40.0)][:, ic]])
        D[(L, ic)] = 2 * r40 - r20 - 1; A[(L, ic)] = (r20 - r40) / 0.1
err = lambda x: float(x[1:].std())
# L=24 inflated variant: scale the L=24 bootstrap fluctuation by max(1, sqrt(chi2/dof)) of the chain means (Birge), per beta and c
def infl(L, ic):
    if L != 24: return D[(L, ic)]
    s20 = max(1.0, np.sqrt(BETW[(20.0, CS[ic])]['chi2'] / BETW[(20.0, CS[ic])]['dof'])); s40 = max(1.0, np.sqrt(BETW[(40.0, CS[ic])]['chi2'] / BETW[(40.0, CS[ic])]['dof']))
    r20 = np.concatenate([[M0[(24, 20.0)][ic]], M0[(24, 20.0)][ic] + s20 * (BR[(24, 20.0)][:, ic] - BR[(24, 20.0)][:, ic].mean())])
    r40 = np.concatenate([[M0[(24, 40.0)][ic]], M0[(24, 40.0)][ic] + s40 * (BR[(24, 40.0)][:, ic] - BR[(24, 40.0)][:, ic].mean())])
    return 2 * r40 - r20 - 1
DI = {(L, ic): infl(L, ic) for L in LS for ic in range(2)}
md.append('\n## delta_meas(L) = 2 R40 - R20 - 1 and A(L) = (R20 - R40)/0.1  [central(bootstrap error)]\n')
md.append('| L | delta c=0.3 | z | delta c=0.4 | z | delta(0.4) - delta(0.3) corr. | A c=0.3 | A c=0.4 | L=24 Birge-inflated delta c=0.3 / 0.4 | Nhat_T/N_T - 1 (0.3 / 0.4): delta if the continuum N_T were the truth |')
md.append('|---|---|---|---|---|---|---|---|---|---|')
for L in LS:
    d3, d4 = D[(L, 0)], D[(L, 1)]; dd = d4 - d3
    md.append(f"| {L} | {d3[0]:+.4f}({err(d3)*1e4:.0f}) | {d3[0]/err(d3):+.1f} | {d4[0]:+.4f}({err(d4)*1e4:.0f}) | {d4[0]/err(d4):+.1f} | {dd[0]:+.4f}({err(dd)*1e4:.0f}) | "
              f"{A[(L,0)][0]:.4f}({err(A[(L,0)])*1e4:.0f}) | {A[(L,1)][0]:.4f}({err(A[(L,1)])*1e4:.0f}) | "
              + (f"{DI[(L,0)][0]:+.4f}({err(DI[(L,0)])*1e4:.0f}) / {DI[(L,1)][0]:+.4f}({err(DI[(L,1)])*1e4:.0f})" if L == 24 else '-') +
              f" | {N_twist_lat(0.3, L)/N_twist_cont(0.3)-1:+.4f} / {N_twist_lat(0.4, L)/N_twist_cont(0.4)-1:+.4f} |")
# fits over L (independent ensembles -> diagonal covariance per c)
FIT = {}
md.append('\n## Fits of delta_meas over L = 8, 12, 16, 24 (diagonal: ensembles independent)\n')
md.append('| c | errors | zero: chi2/4 (p) | constant d0: value, chi2/3 (p) | d0 + d2/L^2: d0, d2, chi2/2 (p) | d0 + d2/L^2: d2 z | max pairwise |delta(L)-delta(L\')| z |'); md.append('|---|---|---|---|---|---|---|')
for ic, c in enumerate(CS):
    for lab, DD in (('bootstrap', D), ('L24 Birge-inflated', DI)):
        y = np.array([DD[(L, ic)] for L in LS]); e = y[:, 1:].std(1); w = 1 / e ** 2; y0 = y[:, 0]
        chi0 = float((y0 ** 2 * w).sum())
        d0 = (y * w[:, None]).sum(0) / w.sum(); chic = float(((y0 - d0[0]) ** 2 * w).sum())
        X = np.column_stack([np.ones(4), 1.0 / np.array(LS) ** 2]); Wm = np.diag(w); G = np.linalg.inv(X.T @ Wm @ X) @ X.T @ Wm; p = G @ y
        res = y0 - X @ p[:, 0]; chil = float(res @ Wm @ res)
        pz = max(abs(y0[i] - y0[j]) / np.hypot(e[i], e[j]) for i in range(4) for j in range(i + 1, 4))
        FIT[(c, lab)] = dict(chi0=chi0, p0=chi2_sf(chi0, 4), d0=[float(d0[0]), float(d0[1:].std())], chic=chic, pc=chi2_sf(chic, 3), d0L=[float(p[0, 0]), float(p[0, 1:].std())], d2=[float(p[1, 0]), float(p[1, 1:].std())], chil=chil, pl=chi2_sf(chil, 2), pair_zmax=float(pz))
        F = FIT[(c, lab)]
        md.append(f"| {c} | {lab} | {chi0:.1f} ({F['p0']:.3f}) | {F['d0'][0]:+.4f}({F['d0'][1]*1e4:.0f}), {chic:.1f} ({F['pc']:.3f}) | {F['d0L'][0]:+.4f}({F['d0L'][1]*1e4:.0f}), {F['d2'][0]:+.3f}({F['d2'][1]*1e3:.0f}e-3), {chil:.1f} ({F['pl']:.3f}) | {F['d2'][0]/F['d2'][1]:+.1f} | {pz:.1f} |")
# alternative normalisations: how large delta would be under the continuum N_T (shows the sensitivity of the check)
md.append('\n## Sensitivity: delta_meas if g2 were normalised with the continuum N_T(c) instead (same data); the measured delta vs this alternative\n')
md.append('| L | c=0.3: delta(cont) | (cont - lattice)/sigma | c=0.4: delta(cont) | (cont - lattice)/sigma |'); md.append('|---|---|---|---|---|')
for L in LS:
    row = []
    for ic, c in enumerate(CS):
        q = N_twist_lat(c, L) / N_twist_cont(c); dc = (1 + D[(L, ic)]) * q - 1
        row.append(f"{dc[0]:+.4f}({err(dc)*1e4:.0f}) | {(dc[0]-D[(L,ic)][0])/err(D[(L,ic)]):+.1f}")
    md.append(f'| {L} | ' + ' | '.join(row) + ' |')
open(pref + '.md', 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))
json.dump(dict(NB=NB, B=B, ens={f'{k[0]}|{k[1]:g}': v for k, v in ENS.items()}, chains={f'{k[0]}|{k[1]:g}': v for k, v in CH.items()},
               between={f'{b:g}|{c}': v for (b, c), v in BETW.items()},
               delta={f'{L}|{CS[ic]}': [float(v[0]), err(v)] for (L, ic), v in D.items()}, delta_infl={f'{L}|{CS[ic]}': [float(v[0]), err(v)] for (L, ic), v in DI.items()},
               A={f'{L}|{CS[ic]}': [float(v[0]), err(v)] for (L, ic), v in A.items()}, fits={f'{c}|{lab}': v for (c, lab), v in FIT.items()}), open(pref + '.json', 'w'), indent=1, default=float)
