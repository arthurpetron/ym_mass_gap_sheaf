#!/usr/bin/env python3
"""Twisted-box GF coupling (Ramos TGF, SU(2), twist n_12 = 1, Wilson action + Wilson flow + clover E; prod5 *_tw*): step-scaling analysis.
g2_TGF = t^2 <E_clover> / Nhat_T(c, L) (twist_norm.N_twist_lat, exact lattice tree level, no zero modes).
Design: 3 u (nominal 1.5, 2.4, 2.9), pairs 6->12 (beta6), 8->16 (beta8), 12->24 (beta12) pointwise at matched beta; u of each (u, c) = g2(L=12, beta12);
6->12 / 8->16 shifts moved to that u with the exact two-loop slope (as in step34 / step2). c = 0.3 and 0.4 from the same flows (same configurations).
Errors: non-parametric moving-block bootstrap over configurations (block B, same indices for c = 0.3 and 0.4), all chains of an (L, beta) pooled;
the 21 ensembles are independent (no ensemble shared between pairs in this design), so all c-gaps carry the full c-correlation.
Continuum per (u, c): lin (a^2), quad (a^2 + a^4, exact with 3 pairs), HMS T<Gamma> = a^2 [gbar^2(1/a)]^Gamma (Gamma = 0.636, 1, 1.636 primary, 2.145),
Q1.636 (HMS + a^4, exact).  Slope s(u) = s0 + k1 u + k2 u^2, s0 = 2 b0 ln2 fixed, GLS with the bootstrap covariance over the 3 u; k2 free (1 dof) and k2 = 0.
Rule (ORIGINAL, unchanged): TWO-LOOP-consistent if BOTH c: |k1 - 0.0026| <= 2 sigma AND |k1| >= 3 sigma; ONE-LOOP-consistent if BOTH c: |k1| <= 2 sigma AND
|k1 - 0.0026| >= 3 sigma; else UNDECIDED. Precision requirements: sigma(k1) <= 0.0009; c=0.3/0.4 agree within 2 sigma (correlated); form spread < sigma.
usage: tw_analysis.py OUTPREFIX [NBOOT] [B=10] [drop=NAME:N,...] [norm=cont]   (norm=cont: divide by the continuum N_T(c) instead of the lattice Nhat_T(c,L);
  sensitivity to the lattice-normalisation convention -- the continuum limit must agree if the extrapolation absorbs the tree-level a^2 terms)      MC evidence only (not a proof, not a bound)."""
import sys, os, glob, json, re, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfana import load_run, time_index, gamma_method
from twist_norm import N_twist_lat, N_twist_cont
import step34 as S
R = '/Users/darthur/ym_numerics_runs/prod5'
RES_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results', 'followup')
TRIP = {1.5: (4.29, 4.44, 4.60), 2.4: (3.35, 3.47, 3.62), 2.9: (3.08, 3.21, 3.33)}
UN = sorted(TRIP); CS = (0.3, 0.4); LS = (6, 8, 12)
EXPECT = {24: 600, 16: 1200, 12: 1200, 8: 2000, 6: 2000}
S0 = 2 * S.b0 * np.log(2); K1_2L = 0.0026
FORMS = ['lin', 'quad', 'T0.636', 'T1', 'T1.636', 'T2.145', 'Q1.636']; PRIMARY = 'T1.636'; MAIN = ['lin', 'quad', 'T1.636', 'Q1.636']

NORM = {'f': N_twist_lat}
def load(drop):
    E = {}; names = {}
    for f in sorted(glob.glob(R + '/su2_L*_tw?.csv')):
        r = load_run(f, 3); L = r['L']; b = round(r['beta'], 6); nm = os.path.basename(f)[:-4]
        assert len(r['sweep']) == EXPECT[L], (nm, len(r['sweep']))
        X = np.column_stack([r['times'][time_index(r, c)] ** 2 * r['E'][:, time_index(r, c), 0] / NORM['f'](c, L) for c in CS])
        if nm in drop: X = X[drop[nm]:]
        E.setdefault((L, b), []).append(X); names.setdefault((L, b), []).append(nm)
    need = [(L, b) for t in UN for L, b in zip(LS, TRIP[t])] + [(2 * L, b) for t in UN for L, b in zip(LS, TRIP[t])]
    assert all(k in E for k in need), [k for k in need if k not in E]
    return E, names

def resample(c, rng, B):
    n = len(c); k = int(np.ceil(n / B)); st = rng.integers(0, n - B + 1, size=k)
    return (st[:, None] + np.arange(B)[None, :]).ravel()[:n]

def main(pref, NB, B, drop):
    E, names = load(drop)
    rng = np.random.default_rng(20261019)
    M0 = {k: np.vstack(v).mean(0) for k, v in E.items()}
    U12 = {t: M0[(12, TRIP[t][2])].copy() for t in UN}            # per c
    def shifts(M, same=False):
        out = {}
        for t in UN:
            for L, b in zip(LS, TRIP[t]):
                for ic in range(2):
                    u = M[(L, b)][ic]; sg = M[(2 * L, b)][ic]; tgt = U12[t][0] if same else U12[t][ic]
                    out[(t, L, ic)] = 1 / u - 1 / sg + S.dtwo(u) * (tgt - u)
        return out
    S0c = shifts(M0); S0s = shifts(M0, True); reps = []; repss = []; Mreps = []
    for _ in range(NB):
        Mk = {k: np.vstack([c[resample(c, rng, B)] for c in v]).mean(0) for k, v in E.items()}
        Mreps.append(Mk); reps.append(shifts(Mk)); repss.append(shifts(Mk, True))
    A = {k: np.array([S0c[k]] + [r[k] for r in reps]) for k in S0c}
    As = {k: np.array([S0s[k]] + [r[k] for r in repss]) for k in S0s}
    err = lambda x: x[1:].std(); ge = lambda x, d=4: f'{x[0]:+.{d}f}({err(x)*10**d:.0f})'; gp = lambda x: f'{x[0]:.4f}({err(x)*1e4:.0f})'
    md = ['# Twisted-box GF (TGF, n_12 = 1) step scaling: pair shifts, continuum, c-gap, k1 (tw_analysis.py)\n',
          f'MC evidence only -- not a proof, not a bound. Bootstrap replicas {NB}, moving blocks of {B} configurations (same indices for both c); dropped: {drop or "none"}; normalisation: {'continuum N_T(c)' if NORM['f'] is not N_twist_lat else 'lattice Nhat_T(c,L)'}. s0 = 2 b0 ln2 = {S0:.5f}.\n']
    # ensemble table + bootstrap vs Gamma error check
    md.append('## Ensembles (pooled chains): g2_TGF, Gamma-method error, bootstrap error\n')
    md.append('| L | beta | chains | N | g2 c=0.3 (Gamma) [boot] | g2 c=0.4 (Gamma) [boot] | rho(c) | Nhat_T/N_T - 1 (c=0.3, 0.4) |'); md.append('|---|---|---|---|---|---|---|---|')
    ENS = {}
    for k in sorted(E, key=lambda k: (k[0], -k[1])):
        X = np.vstack(E[k]); gs = [gamma_method(X[:, i])[1] for i in range(2)]; bs = [np.std([m[k][i] for m in Mreps]) for i in range(2)]
        ENS[f'{k[0]}|{k[1]}'] = dict(g2=[float(M0[k][i]) for i in range(2)], gamma_err=gs, boot_err=bs, n=len(X))
        md.append(f'| {k[0]} | {k[1]:g} | {len(E[k])} | {len(X)} | {M0[k][0]:.5f}({gs[0]*1e5:.0f}) [{bs[0]*1e5:.0f}] | {M0[k][1]:.5f}({gs[1]*1e5:.0f}) [{bs[1]*1e5:.0f}] | {np.corrcoef(X.T)[0,1]:.2f} | '
                  f'{N_twist_lat(0.3, k[0])/N_twist_cont(0.3)-1:+.4f}, {N_twist_lat(0.4, k[0])/N_twist_cont(0.4)-1:+.4f} |')
    two = {t: [S.two(U12[t][ic]) for ic in range(2)] for t in UN}
    md.append('\n## Pair shifts s = 1/u - 1/Sigma at the u of each (u, c)  [central(bootstrap error)]; two-loop exact and one-loop for reference\n')
    md.append('| u nom | c | u = g2(12, beta12) | 6->12 | 8->16 | 12->24 | two-loop | one-loop |'); md.append('|---|---|---|---|---|---|---|---|')
    for t in UN:
        for ic, c in enumerate(CS):
            md.append(f'| {t} | {c} | {U12[t][ic]:.4f} | ' + ' | '.join(gp(A[(t, L, ic)]) for L in LS) + f' | {two[t][ic]:.4f} | {S0:.4f} |')
    md.append('\n## Pair-level c-gap s(c=0.4) - s(c=0.3) (correlated; each c at its own u | c=0.4 moved to the c=0.3 u by the two-loop slope)\n')
    md.append('| u nom | 6->12 | 8->16 | 12->24 | same-u: 6->12 | 8->16 | 12->24 |'); md.append('|---|---|---|---|---|---|---|')
    for t in UN:
        md.append(f'| {t} | ' + ' | '.join(ge(A[(t, L, 1)] - A[(t, L, 0)]) for L in LS) + ' | ' + ' | '.join(ge(As[(t, L, 1)] - As[(t, L, 0)]) for L in LS) + ' |')
    # continuum
    CONT = {}; CHI = {}; CONTs = {}
    for t in UN:
        for ic in range(2):
            uc = U12[t][ic]
            for which, AA, CC in (('own', A, CONT), ('same', As, CONTs)):
                y = np.array([AA[(t, L, ic)] for L in LS]); e = y[:, 1:].std(1); ucc = uc if which == 'own' else U12[t][0]
                for form in FORMS:
                    Bm = np.array([S.basis(form, L, ucc) for L in LS]); W = np.diag(1 / e ** 2); C = np.linalg.inv(Bm.T @ W @ Bm)
                    CC[(t, ic, form)] = (C @ Bm.T @ W)[0] @ y
                    if which == 'own':
                        r = y[:, 0] - Bm @ (C @ Bm.T @ W @ y[:, 0]); CHI[(t, ic, form)] = (float(r @ W @ r), 3 - Bm.shape[1])
    md.append('\n## Continuum s per (u, c) and form  [central(bootstrap error)] [chi2/dof of the 3-pair fit]\n')
    md.append('| form | c | ' + ' | '.join(f'u~{t} ' for t in UN) + ' |'); md.append('|---|---|' + '---|' * len(UN))
    for form in FORMS:
        for ic, c in enumerate(CS):
            md.append(f'| {form} | {c} | ' + ' | '.join(f"{gp(CONT[(t, ic, form)])} [" + (f"{CHI[(t, ic, form)][0]:.1f}/{CHI[(t, ic, form)][1]}" if CHI[(t, ic, form)][1] else 'exact') + ']' for t in UN) + ' |')
    md.append('\nExact two-loop at those u: ' + '; '.join(f'u~{t}: c=0.3 {two[t][0]:.4f}, c=0.4 {two[t][1]:.4f}' for t in UN) + f'; one-loop {S0:.4f}.\n')
    md.append('## Continuum c-gap s(0.4) - s(0.3) (correlated) per u and error-weighted mean over u\n')
    md.append('| form | ' + ' | '.join(f'u~{t}' for t in UN) + ' | weighted mean | same-u variant: mean |'); md.append('|---|' + '---|' * (len(UN) + 2))
    GAP = {}
    for form in FORMS:
        G = [CONT[(t, 1, form)] - CONT[(t, 0, form)] for t in UN]; Gs = [CONTs[(t, 1, form)] - CONTs[(t, 0, form)] for t in UN]
        wt = np.array([1 / err(g) ** 2 for g in G]); wt /= wt.sum(); mg = sum(w * g for w, g in zip(wt, G)); mgs = sum(w * g for w, g in zip(wt, Gs))
        GAP[form] = dict(per_u={str(t): [float(g[0]), float(err(g))] for t, g in zip(UN, G)}, mean=[float(mg[0]), float(err(mg))], mean_same_u=[float(mgs[0]), float(err(mgs))])
        md.append(f'| {form} | ' + ' | '.join(ge(g) for g in G) + f' | {ge(mg)} ({mg[0]/err(mg):+.1f} sigma) | {ge(mgs)} ({mgs[0]/err(mgs):+.1f} sigma) |')
    # slope fits
    def slope(form, ics, k2free, joint=False):
        T = np.vstack([CONT[(t, ic, form)] - S0 for ic in ics for t in UN]); C = np.atleast_2d(np.cov(T[:, 1:]))
        us = np.array([U12[t][ic] for ic in ics for t in UN])
        if joint:
            cols = [us] + ([np.array([U12[t][ic2] ** 2 if ic2 == ic else 0.0 for ic2 in ics for t in UN]) for ic in ics] if k2free else [])
            Bm = np.column_stack(cols)
        else:
            Bm = np.column_stack([us, us ** 2]) if k2free else us[:, None]
        Ci = np.linalg.inv(C); G = np.linalg.inv(Bm.T @ Ci @ Bm) @ Bm.T @ Ci; p = G @ T; r = T[:, 0] - Bm @ p[:, 0]
        return p, float(r @ Ci @ r), T.shape[0] - Bm.shape[1]
    def classify(k):
        two_ = all(abs(v - K1_2L) <= 2 * s and abs(v) >= 3 * s for v, s in k); one_ = all(abs(v) <= 2 * s and abs(v - K1_2L) >= 3 * s for v, s in k)
        return 'TWO-LOOP-consistent' if two_ else ('ONE-LOOP-consistent' if one_ else 'UNDECIDED')
    md.append(f'\n## k1 (s0 = {S0:.4f} fixed; GLS with bootstrap covariance over the 3 u; k2 free leaves 1 dof); classification by the ORIGINAL rule\n')
    md.append('| form | k2 | k1(c=0.3) +- sig | z0 / z(0.0026) | k1(c=0.4) +- sig | z0 / z(0.0026) | k2(0.3), k2(0.4) | chi2 (dof) | k1(0.4)-k1(0.3) correlated | naive | rule |'); md.append('|---|---|---|---|---|---|---|---|---|---|---|')
    K = {}
    for form in FORMS:
        for k2free in (True, False):
            ps = [slope(form, [ic], k2free) for ic in range(2)]
            k = [(float(p[0][0, 0]), float(p[0][0, 1:].std())) for p in ps]; d = ps[1][0][0] - ps[0][0][0]
            cl = classify(k); K[(form, k2free)] = dict(k=k, d=(float(d[0]), float(d[1:].std())), dn=float(np.hypot(k[0][1], k[1][1])), cl=cl,
                                                      k2=[(float(p[0][1, 0]), float(p[0][1, 1:].std())) for p in ps] if k2free else None, chi=[(p[1], p[2]) for p in ps],
                                                      rho=float(np.corrcoef(ps[0][0][0, 1:], ps[1][0][0, 1:])[0, 1]))
            k2s = ', '.join(f'{v:+.4f}({s:.4f})' for v, s in K[(form, k2free)]['k2']) if k2free else '0'
            md.append(f"| {form} | {'free' if k2free else '0'} | {k[0][0]:+.5f} +- {k[0][1]:.5f} | {k[0][0]/k[0][1]:+.1f} / {(k[0][0]-K1_2L)/k[0][1]:+.1f} | {k[1][0]:+.5f} +- {k[1][1]:.5f} | {k[1][0]/k[1][1]:+.1f} / {(k[1][0]-K1_2L)/k[1][1]:+.1f} | {k2s} | {ps[0][1]:.1f}, {ps[1][1]:.1f} ({ps[0][2]}) | "
                      f"{d[0]:+.5f} +- {d[1:].std():.5f} ({d[0]/d[1:].std():+.1f} sig) | {d[0]/K[(form, k2free)]['dn']:+.1f} sig | {cl} |")
    md.append('\n## Joint fit, common k1 for both c (k1 is scheme independent), separate k2 per c, full 6x6 bootstrap covariance\n')
    md.append('| form | k2 | k1 +- sig | z0 / z(0.0026) | chi2/dof |'); md.append('|---|---|---|---|---|')
    J = {}
    for form in FORMS:
        for k2free in (True, False):
            p, chi2, dof = slope(form, [0, 1], k2free, joint=True); v, s = float(p[0, 0]), float(p[0, 1:].std()); J[(form, k2free)] = (v, s, chi2, dof)
            md.append(f"| {form} | {'free' if k2free else '0'} | {v:+.5f} +- {s:.5f} | {v/s:+.1f} / {(v-K1_2L)/s:+.1f} | {chi2:.1f}/{dof} |")
    # precision requirements (primary form, k2 free)
    P = K[(PRIMARY, True)]; sig_ok = all(s <= 0.0009 for _, s in P['k']); dz = P['d'][0] / P['d'][1]; c_ok = abs(dz) <= 2
    out = {}
    for ic in range(2):
        v = [K[(f, True)]['k'][ic][0] for f in FORMS]; out[ic] = (max(v) - min(v), P['k'][ic][1])
    form_ok = all(sp < s for sp, s in out.values())
    md.append(f'\n## Stopping rule (ORIGINAL) applied to the twisted data, primary form {PRIMARY}, k2 free (3 u only; the rule was specified on the 5-u periodic analysis)\n')
    md.append(f"* k1(c=0.3) = {P['k'][0][0]:+.4f} +- {P['k'][0][1]:.4f} ({P['k'][0][0]/P['k'][0][1]:+.1f} sigma from 0, {(P['k'][0][0]-K1_2L)/P['k'][0][1]:+.1f} sigma from 0.0026); "
              f"k1(c=0.4) = {P['k'][1][0]:+.4f} +- {P['k'][1][1]:.4f} ({P['k'][1][0]/P['k'][1][1]:+.1f} / {(P['k'][1][0]-K1_2L)/P['k'][1][1]:+.1f}). **Classification: {P['cl']}.**")
    md.append(f"* Precision 1, sigma(k1) <= 0.0009: {'PASS' if sig_ok else 'FAIL'} ({P['k'][0][1]:.4f} / {P['k'][1][1]:.4f}).")
    md.append(f"* Precision 2, c=0.3/0.4 agree within 2 sigma (correlated): Delta k1 = {P['d'][0]:+.4f} +- {P['d'][1]:.4f} ({dz:+.1f} sigma): {'PASS' if c_ok else 'FAIL'}.")
    md.append(f"* Precision 3, form spread of k1 over {FORMS} below sigma: c=0.3 spread {out[0][0]:.4f} vs {out[0][1]:.4f}, c=0.4 {out[1][0]:.4f} vs {out[1][1]:.4f}: {'PASS' if form_ok else 'FAIL'}.")
    md.append('* Classification for every form (k2 free / k2 = 0): ' + '; '.join(f"{f}: {K[(f, True)]['cl']} / {K[(f, False)]['cl']}" for f in FORMS))
    # comparison with periodic results
    md.append('\n## Comparison with the periodic-box results (different schemes: the O(u^2) term of s and the u^2 coefficient k2 are scheme dependent; s0 and k1 are universal)\n')
    try:
        s4 = json.load(open(os.path.join(RES_DIR, 'S4_step34.json'))); s5 = json.load(open(os.path.join(RES_DIR, 'S5_step2_final.json')))
        md.append('| form, k2 | twisted (3 u: 1.5, 2.4, 2.9) c=0.3 / 0.4 | periodic Wilson items 1-2 (5 u, step34) c=0.3 / 0.4 | periodic Wilson step-2 configs (3 u: 1.9, 2.41, 2.9) | periodic Zeuthen (3 u) |'); md.append('|---|---|---|---|---|')
        for f in ('lin', 'T1.636', 'quad'):
            for kf, kk in ((True, 'free'), (False, '0')):
                tw = K[(f, kf)]['k']; p4 = s4['k1'].get(f'{f}|{kf}', {}).get('k'); w5 = s5['k1'].get(f'{f}|{kk}|Wilson'); z5 = s5['k1'].get(f'{f}|{kk}|Zeuthen')
                fm = lambda kv: ' / '.join(f'{v:+.4f}({s*1e4:.0f})' for v, s in kv) if kv else '-'
                md.append(f'| {f}, k2 {kk} | {fm(tw)} | {fm(p4)} | {fm(w5)} | {fm(z5)} |')
        md.append('\nContinuum c-gap (weighted mean over the 3 u of each data set; correlated errors): ' + '; '.join(
            f"{f}: twisted {GAP[f]['mean'][0]:+.4f}({GAP[f]['mean'][1]*1e4:.0f}), periodic Wilson {s5['summary_gap'][f]['gapW'][0]:+.4f}({s5['summary_gap'][f]['gapW'][1]*1e4:.0f}), periodic Zeuthen {s5['summary_gap'][f]['gapZ'][0]:+.4f}({s5['summary_gap'][f]['gapZ'][1]*1e4:.0f})" for f in ('lin', 'T1.636', 'quad')))
        md.append('\nPer-u continuum values (T1.636) side by side: ' + '; '.join(
            f"u~{tu}/{pu}: twisted {CONT[(tu, 0, PRIMARY)][0]:.4f}({err(CONT[(tu, 0, PRIMARY)])*1e4:.0f}) / {CONT[(tu, 1, PRIMARY)][0]:.4f}({err(CONT[(tu, 1, PRIMARY)])*1e4:.0f}), periodic W {s5['cont'][f'{pu}|Wilson|0.3|T1.636'][0]:.4f}({s5['cont'][f'{pu}|Wilson|0.3|T1.636'][1]*1e4:.0f}) / {s5['cont'][f'{pu}|Wilson|0.4|T1.636'][0]:.4f}({s5['cont'][f'{pu}|Wilson|0.4|T1.636'][1]*1e4:.0f})"
            for tu, pu in ((2.4, '2.41'), (2.9, '2.9'))))
    except Exception as ex:
        md.append(f'(comparison files not readable: {ex})')
    open(pref + '.md', 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))
    json.dump(dict(NB=NB, B=B, drop=drop, U12={str(t): list(map(float, U12[t])) for t in UN}, ens=ENS,
                   shifts={f'{t}|{L}|{CS[ic]}': [float(v[0]), float(err(v))] for (t, L, ic), v in A.items()},
                   gap_pair={f'{t}|{L}': [float((A[(t, L, 1)] - A[(t, L, 0)])[0]), float(err(A[(t, L, 1)] - A[(t, L, 0)]))] for t in UN for L in LS},
                   cont={f'{t}|{CS[ic]}|{f}': [float(v[0]), float(err(v))] for (t, ic, f), v in CONT.items()}, chi={f'{t}|{CS[ic]}|{f}': v for (t, ic, f), v in CHI.items()},
                   gap=GAP, k1={f'{f}|{"free" if kf else "0"}': v for (f, kf), v in K.items()}, joint={f'{f}|{"free" if kf else "0"}': v for (f, kf), v in J.items()},
                   rule=dict(form=PRIMARY, cl=P['cl'], sig_ok=sig_ok, c_ok=c_ok, dz=dz, form_ok=form_ok, spread={str(CS[i]): out[i] for i in range(2)})),
              open(pref + '.json', 'w'), indent=1, default=float)

if __name__ == '__main__':
    pref = sys.argv[1]; NB = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    B = 10; drop = {}
    for a in sys.argv[3:]:
        if a.startswith('B='): B = int(a[2:])
        if a == 'norm=cont': NORM['f'] = lambda c, L: N_twist_cont(c)
        if a.startswith('drop='):
            for kv in a[5:].split(','): n, v = kv.split(':'); drop[n] = int(v)
    main(pref, NB, B, drop)
