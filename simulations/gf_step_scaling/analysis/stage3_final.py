#!/usr/bin/env python3
"""FINAL items 1-2 analysis under darthur's stopping rule (2026-10-18).
Classified quantity: k1 in s(u) = 1/u - 1/Sigma = s0 + k1 u + k2 u^2, s0 = 2 b0 ln2 FIXED, k2 FREE (primary); k2 = 0 also reported.
Continuum at each u: weighted linear fit in x = (a/L)^2 over the finest 3 pairs 6->12, 8->16, 12->24 (primary, 'lin3').
Form systematics: quad3 (a + b x + c x^2 through the 3 finest pairs, exact), lin4 / quad4 (adding the coarse 4->8 pair where it exists).
c = 0.3 and 0.4 separately. Errors: statistical (Gamma method; joint bootstrap for the interpolated old-u 6->12, 8->16 pairs), independent pairs/u
(L=12 beta=3.6/4.5 shared by 6->12 interpolation and 12->24 at the old u: neglected); c=0.3/0.4 correlation propagated linearly with the measured rho.
PDG option: the g2 error of the L=12 beta=3.6 ensemble is multiplied by sqrt(chi2/dof of its chain means) (per c) everywhere it enters.
Classification (rule): two-loop-consistent if BOTH c: |k1-0.0026| <= 2 sigma AND |k1| >= 3 sigma; one-loop-consistent if BOTH c: |k1| <= 2 sigma AND |k1-0.0026| >= 3 sigma; else UNDECIDED.
usage: stage3_final.py OUTPREFIX [NBOOT]  -> OUTPREFIX.md, OUTPREFIX.json"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stage3_analysis as A
from stage3_analysis import RUNS, series, two, dtwo, S0, K1_2L, DIRS, EXC
from joint_fit import Data, Joint
from gfana import gamma_method, time_index, N_lat
NEW = {1.0: (5.63, 5.74, 5.89), 1.9: (3.77, 3.88, 4.02), 2.9: (3.08, 3.19, 3.34)}
OLD = {1.54: 4.5, 2.41: 3.6}
CS = (0.3, 0.4); RHO_J = 0.93   # c-correlation assumed for interpolated (Joint) pairs = mean of the measured pointwise rho (0.93-0.94)
COST = {4: 0.01, 6: 0.034, 8: 0.173, 12: 1.30, 16: 4.0, 24: 41.0, 32: 210.0}   # CPU-s per measurement (c<=0.4; measured from stderr elapsed / stage E logs)

def chain_chi2(L, b, c):
    ms, es = [], []
    for n, r in RUNS.get((L, b), []):
        try: i = time_index(r, c)
        except AssertionError: continue
        x = r['times'][i] ** 2 * r['E'][:, i, 0] / N_lat(c, L); m, e, *_ = gamma_method(x); ms.append(m); es.append(e)
    ms, es = np.array(ms), np.array(es); w = 1 / es ** 2; mu = (w * ms).sum() / w.sum()
    return float(np.sum(((ms - mu) / es) ** 2) / (len(ms) - 1)), len(ms)

def ens_g2(L, b, scale=1.0):
    X = series(L, b, list(CS)); m = X.mean(0)
    e = np.array([gamma_method(X[:, i])[1] for i in range(X.shape[1])]) * scale
    return m, e, np.corrcoef(X.T)[0, 1], len(X)

def pair(L, b, scale):
    (u, eu, r1, n1), (sg, es, r2, n2) = ens_g2(L, b, scale.get((L, b), np.ones(2))), ens_g2(2 * L, b, scale.get((2 * L, b), np.ones(2)))
    s = 1 / u - 1 / sg; cL = eu / u ** 2; c2 = es / sg ** 2
    e = np.hypot(cL, c2); cov = cL[0] * cL[1] * r1 + c2[0] * c2[1] * r2
    return dict(u=u, s=s, e=e, comp=[(L, b, n1, cL), (2 * L, b, n2, c2)], rho=float(cov / (e[0] * e[1])))

def design(Ls, form):
    x = np.array([1.0 / L ** 2 for L in Ls])
    return np.column_stack([np.ones_like(x), x] + ([x ** 2] if form.startswith('quad') else []))

def cfit(Ls, y, e, form):
    Am = design(Ls, form); W = np.diag(1 / np.asarray(e) ** 2); C = np.linalg.inv(Am.T @ W @ Am); p = C @ Am.T @ W @ np.asarray(y)
    r = np.asarray(y) - Am @ p
    return float(p[0]), float(np.sqrt(C[0, 0])), float(r @ W @ r), len(Ls) - Am.shape[1], (C @ Am.T @ W)[0]

def slopew(us, e, k2free):
    us = np.asarray(us); w = 1 / np.asarray(e) ** 2
    Am = np.column_stack([us, us ** 2]) if k2free else us[:, None]
    C = np.linalg.inv(Am.T @ (w[:, None] * Am)); return C, C @ Am.T * w, Am

def classify(k):
    """k: {c: (k1, sig)}"""
    two_ = all(abs(v - K1_2L) <= 2 * s and abs(v) >= 3 * s for v, s in k.values())
    one_ = all(abs(v) <= 2 * s and abs(v - K1_2L) >= 3 * s for v, s in k.values())
    return 'TWO-LOOP-CONSISTENT' if two_ else ('ONE-LOOP-CONSISTENT' if one_ else 'UNDECIDED')

def build(scale, NB):
    D = Data(DIRS, obs='clover', norm='lat', excl=EXC)
    for (L, b), f in scale.items():          # PDG-scale the Joint input too
        for ic, c in enumerate(CS):
            g = D.g2(L, b, c)
            if g: D._cache[(L, b, c, 'clover', 'lat')] = (g[0], g[1] * f[ic], g[2], g[3])
    P = {c: [] for c in CS}
    for un in sorted(set(NEW) | set(OLD)):
        bset = {6: NEW[un][0], 8: NEW[un][1], 12: NEW[un][2]} if un in NEW else {12: OLD[un]}
        pp = {L: pair(L, b, scale) for L, b in bset.items()}
        for ic, c in enumerate(CS):
            u12 = float(pp[12]['u'][ic]); ent = {}
            for L in (4, 6, 8, 12):
                if L in pp:
                    p = pp[L]; sc = p['s'][ic] + dtwo(p['u'][ic]) * (u12 - p['u'][ic])
                    ent[L] = dict(s=float(sc), e=float(p['e'][ic]), rho=p['rho'], how=f'pointwise beta={bset[L]:g}, u_pair={p["u"][ic]:.4f}',
                                  comp=[dict(L=a, beta=bb, n=n, var=float(cc[ic] ** 2)) for a, bb, n, cc in p['comp']])
                else:
                    J = Joint(D, c, 2, [(L, 2 * L)], [u12], nboot=NB); v = J.S[1:, 0, 0]; v = v[~np.isnan(v)]
                    if np.isnan(J.S[0, 0, 0]) or len(v) < 50: continue
                    e = float(np.std(v))
                    ent[L] = dict(s=float(J.S[0, 0, 0]), e=e, rho=RHO_J, how='joint-bootstrap interpolation (M=2)',
                                  comp=[dict(L=L, beta='J%g' % un, n=None, var=e * e / 2), dict(L=2 * L, beta='J%g' % un, n=None, var=e * e / 2)])
            P[c].append(dict(un=un, u=u12, pairs=ent))
    return P

FORMSETS = {'lin3': [('lin', (6, 8, 12))], 'quad3': [('quad', (6, 8, 12))],
            'lin4': [('lin', (4, 6, 8, 12)), ('lin', (6, 8, 12))], 'quad4': [('quad', (4, 6, 8, 12)), ('quad', (6, 8, 12))]}

def analyse(P):
    R = {'cont': {}, 'k1': {}, 'w': {}}
    for c in CS:
        for fs, opts in FORMSETS.items():
            us, ys, es, ws, used = [], [], [], [], []
            for pt in P[c]:
                for form, Ls in opts:
                    if all(L in pt['pairs'] for L in Ls): break
                else: continue
                y = [pt['pairs'][L]['s'] for L in Ls]; e = [pt['pairs'][L]['e'] for L in Ls]
                a, ea, chi, dof, w = cfit(Ls, y, e, form)
                us.append(pt['u']); ys.append(a); es.append(ea); ws.append(dict(zip(Ls, w))); used.append(f'{form}{Ls}')
                R['cont'][(c, fs, pt['un'])] = (a, ea, chi, dof, list(Ls))
            for k2free in (True, False):
                C, Wk, Am = slopew(us, es, k2free); t = np.array(ys) - S0; p = Wk @ t
                chi = float(np.sum((t - Am @ p) ** 2 / np.array(es) ** 2))
                R['k1'][(c, fs, k2free)] = dict(k1=float(p[0]), sig=float(np.sqrt(C[0, 0])), k2=(float(p[1]), float(np.sqrt(C[1, 1]))) if k2free else None,
                                                chi2=chi, dof=len(us) - Am.shape[1], used=used)
                R['w'][(c, fs, k2free)] = [(P[c][[q['un'] for q in P[c]].index(un)]['un'], Wk[0][i], ws[i]) for i, un in enumerate([q['un'] for q in P[c] if any(all(L in q['pairs'] for L in Ls) for _, Ls in opts)])]
    return R

def k1_corr(P, R, fs, k2free):
    """cov(k1(0.3), k1(0.4)) by linear propagation over the pair shifts with the measured c-correlation."""
    cov = 0.0
    W3 = {un: (wk, w) for un, wk, w in R['w'][(0.3, fs, k2free)]}; W4 = {un: (wk, w) for un, wk, w in R['w'][(0.4, fs, k2free)]}
    for un in W3:
        if un not in W4: continue
        p3 = next(q for q in P[0.3] if q['un'] == un)['pairs']; p4 = next(q for q in P[0.4] if q['un'] == un)['pairs']
        for L in W3[un][1]:
            if L in W4[un][1]:
                cov += W3[un][0] * W3[un][1][L] * W4[un][0] * W4[un][1][L] * p3[L]['rho'] * p3[L]['e'] * p4[L]['e']
    return cov

def report(P, R, title):
    o = [f'### {title}\n', '**Pair shifts at the common u of each scheme (u = g2(L=12, beta12)); errors statistical**\n',
         '| u nom | c | u | 4->8 | 6->12 | 8->16 | 12->24 | how (6->12, 8->16) |', '|---|---|---|---|---|---|---|---|']
    f = lambda d: '-' if d is None else f"{d['s']:.4f}({d['e']*1e4:.0f})"
    for c in CS:
        for pt in P[c]:
            pp = pt['pairs']; o.append(f"| {pt['un']} | {c} | {pt['u']:.4f} | {f(pp.get(4))} | {f(pp.get(6))} | {f(pp.get(8))} | {f(pp.get(12))} | {pp[6]['how'].split(',')[0]} |")
    o += ['\n**Continuum value per u (x = (a/L)^2; primary = lin3)**\n', '| c | u nom | lin3 (chi2/1) | quad3 (exact) | lin4 incl. 4->8 (chi2/2) | quad4 incl. 4->8 (chi2/1) | one-loop | two-loop exact |', '|---|---|---|---|---|---|---|---|']
    for c in CS:
        for pt in P[c]:
            g = lambda fs: R['cont'].get((c, fs, pt['un']))
            h = lambda v, chi=True: '-' if v is None else (f'{v[0]:.4f}({v[1]*1e4:.0f})' + (f' {v[2]:.1f}' if chi and v[3] > 0 else '') + ('' if len(v[4]) == 4 or v is g('lin3') or v is g('quad3') else ' [no 4->8]'))
            o.append(f"| {c} | {pt['un']} | {h(g('lin3'))} | {h(g('quad3'), False)} | {h(g('lin4'))} | {h(g('quad4'))} | {S0:.4f} | {two(pt['u']):.4f} |")
    o += ['\n**Slope k1 (s0 = %.4f fixed; test values 0 and %.4f)**\n' % (S0, K1_2L), '| c | continuum form | k2 | k1 | sigma(k1) | k1/sigma | (k1-0.0026)/sigma | k2 | chi2/dof |', '|---|---|---|---|---|---|---|---|---|']
    for c in CS:
        for fs in FORMSETS:
            for k2free in (True, False):
                r = R['k1'][(c, fs, k2free)]
                o.append(f"| {c} | {fs} | {'free' if k2free else '0'} | {r['k1']:.5f} | {r['sig']:.5f} | {r['k1']/r['sig']:+.1f} | {(r['k1']-K1_2L)/r['sig']:+.1f} | {'%.5f(%.5f)' % r['k2'] if r['k2'] else '0'} | {r['chi2']:.1f}/{r['dof']} |")
    return o

def verdict(P, R):
    out = {}
    for k2free in (True, False):
        k = {c: (R['k1'][(c, 'lin3', k2free)]['k1'], R['k1'][(c, 'lin3', k2free)]['sig']) for c in CS}
        cv = k1_corr(P, R, 'lin3', k2free); d = k[0.4][0] - k[0.3][0]
        en = np.hypot(k[0.3][1], k[0.4][1]); ec = np.sqrt(max(k[0.3][1] ** 2 + k[0.4][1] ** 2 - 2 * cv, 1e-14))
        spread = {c: max(R['k1'][(c, fs, k2free)]['k1'] for fs in FORMSETS) - min(R['k1'][(c, fs, k2free)]['k1'] for fs in FORMSETS) for c in CS}
        out[k2free] = dict(k=k, cls=classify(k), sig_ok={c: k[c][1] <= 0.0009 for c in CS}, diff=d, err_naive=en, err_corr=ec, rho_k1=cv / (k[0.3][1] * k[0.4][1]),
                           cagree_naive=abs(d) <= 2 * en, cagree_corr=abs(d) <= 2 * ec, spread=spread, spread_ok={c: spread[c] < k[c][1] for c in CS},
                           forms={c: {fs: (R['k1'][(c, fs, k2free)]['k1'], R['k1'][(c, fs, k2free)]['sig']) for fs in FORMSETS} for c in CS})
    return out

def vtext(V):
    o = []
    for k2free in (True, False):
        v = V[k2free]; tag = 'k2 FREE (primary)' if k2free else 'k2 = 0'
        o.append(f"* **{tag}:** k1(c=0.3) = {v['k'][0.3][0]:.5f} +- {v['k'][0.3][1]:.5f}; k1(c=0.4) = {v['k'][0.4][0]:.5f} +- {v['k'][0.4][1]:.5f} -> **{v['cls']}**")
        o.append(f"  * sigma(k1) <= 0.0009: c=0.3 {'PASS' if v['sig_ok'][0.3] else 'FAIL'}, c=0.4 {'PASS' if v['sig_ok'][0.4] else 'FAIL'}")
        o.append(f"  * c agreement: k1(0.4)-k1(0.3) = {v['diff']:+.5f}; naive (independent) err {v['err_naive']:.5f} -> {v['diff']/v['err_naive']:+.1f} sigma ({'PASS' if v['cagree_naive'] else 'FAIL'}); with c-correlation (rho(k1) = {v['rho_k1']:.2f}) err {v['err_corr']:.5f} -> {v['diff']/v['err_corr']:+.1f} sigma ({'PASS' if v['cagree_corr'] else 'FAIL'})")
        o.append(f"  * extrapolation-form spread of k1 (lin3, quad3, lin4, quad4): c=0.3 {v['spread'][0.3]:.5f} vs sigma {v['k'][0.3][1]:.5f} ({'PASS' if v['spread_ok'][0.3] else 'FAIL'}); c=0.4 {v['spread'][0.4]:.5f} vs {v['k'][0.4][1]:.5f} ({'PASS' if v['spread_ok'][0.4] else 'FAIL'})")
        for c in CS: o.append(f"    * c={c}: " + ', '.join(f"{fs} {a:.5f}({s:.5f})" for fs, (a, s) in v['forms'][c].items()))
    return o

if __name__ == '__main__':
    pref = sys.argv[1]; NB = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    md = ['# Items 1-2 FINAL analysis (stage3_final.py)\n', 'MC evidence only; statistical errors; see status doc for caveats.\n']
    chi36 = [chain_chi2(12, 3.6, c) for c in CS]
    pdg = np.array([max(1.0, np.sqrt(x)) for x, _ in chi36])
    chis = {f'L12_b{b}': [chain_chi2(12, b, c) for c in CS] for b in (3.6, 4.5, 3.4, 3.8, 4.1, 5.0, 4.02, 3.34, 5.89)}
    md.append('Chain-mean chi2/dof (L=12, c=0.3 / c=0.4, #chains): ' + '; '.join(f"{k}: {v[0][0]:.2f}/{v[1][0]:.2f} ({v[0][1]})" for k, v in chis.items()) + '\n')
    md.append(f'PDG scale factor at L=12 beta=3.6: c=0.3 sqrt({chi36[0][0]:.2f}) = {pdg[0]:.3f}, c=0.4 sqrt({chi36[1][0]:.2f}) = {pdg[1]:.3f}\n')
    res = {}
    pdg334 = np.array([max(1.0, np.sqrt(chis['L12_b3.34'][i][0])) for i in range(2)])
    md.append(f'Extra (not part of the rule): PDG factor at L=12 beta=3.34 (u~2.9, 2 chains): {pdg334[0]:.3f} / {pdg334[1]:.3f}; variant pdg_all scales both 3.6 and 3.34.\n')
    for tag, scale in (('nominal', {}), ('pdg', {(12, 3.6): pdg}), ('pdg_all', {(12, 3.6): pdg, (12, 3.34): pdg334})):
        P = build(scale, NB); R = analyse(P); V = verdict(P, R)
        md += report(P, R, f'{tag} errors' + (' (L=12 beta=3.6 g2 errors x PDG factor)' if scale else '')) + ['\n**Stopping-rule verdict (%s)**\n' % tag] + vtext(V) + ['']
        res[tag] = dict(P=P, V={str(k): {kk: (vv if not isinstance(vv, dict) else {str(a): b for a, b in vv.items()}) for kk, vv in v.items()} for k, v in V.items()},
                        k1={f'{c}|{fs}|{k2}': v for (c, fs, k2), v in R['k1'].items()},
                        w={f'{c}|{fs}|{k2}': [(un, float(wk), {str(L): float(x) for L, x in w.items()}) for un, wk, w in v] for (c, fs, k2), v in R['w'].items()})
    res['pdg_factor'] = pdg.tolist(); res['chain_chi2'] = chis
    open(pref + '.md', 'w').write('\n'.join(md) + '\n'); json.dump(res, open(pref + '.json', 'w'), indent=1, default=float)
    print('\n'.join(md))
