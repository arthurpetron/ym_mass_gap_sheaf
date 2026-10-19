#!/usr/bin/env python3
"""Step 2 final: Zeuthen vs Wilson flow on the SAME configurations (prod4 *_z1p9/_z2p4/_z2p9), extending step2_analysis.py with
 (a) continuum Zeuthen - Wilson differences (per u, c, form) and of the continuum c-gap, configuration-correlated (same bootstrap replicas);
 (b) INDICATIVE slope fits s(u) = s0 + k1 u + k2 u^2 (s0 = 2 b0 ln2 fixed) per flow and c over the 3 step-2 u values (1.9, 2.41, 2.9), forms
     lin / T1.636 (HMS, primary) / quad, k2 free (1 dof) and k2 = 0; GLS with the bootstrap covariance; c-difference and Z-W difference of k1
     with correlated errors; the original rule's classification printed for reference (the rule itself is defined on the 5-u Wilson analysis);
 (c) sensitivity: discard the first DROP measurements of chosen runs (thermalisation check of the cold L=24 / L=16 u=1.9 chains).
Same bootstrap as step2_analysis.py (moving blocks of 3 configurations, same indices for both flows and both c; seed 777).
usage: step2_final.py OUTPREFIX [NBOOT] [drop=NAME:N,NAME:N]      MC evidence only."""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import step2_analysis as A2
import step34 as S
S0 = 2 * S.b0 * np.log(2); K1_2L = 0.0026
CS, LS, TRIP, UVAL = A2.CS, A2.LS, A2.TRIP, A2.UVAL
FL = ['Wilson', 'Zeuthen']; FORMS = ['lin', 'T1.636', 'quad']

def load(drop):
    E = A2.load()
    if drop:
        for k, chs in E.items():
            new = []
            for c, f in chs:
                nm = os.path.basename(f)[:-4]
                new.append((c[drop[nm]:] if nm in drop else c, f))
            E[k] = new
    # completeness on the raw files (row counts before dropping)
    raw = A2.load(); bad = [k for k, ch in raw.items() if any(len(c) < A2.EXPECT[k[1]] for c, f in ch)]
    assert not bad, bad
    return {k: [c for c, f in v] for k, v in E.items()}

def main(pref, NB, drop):
    E = load(drop)
    rng = np.random.default_rng(777)
    mean = lambda chs, idx=None: np.vstack(chs if idx is None else [c[i] for c, i in zip(chs, idx)]).mean(0)
    M0 = {k: mean(v) for k, v in E.items()}
    U12 = {(t, fl, ic): M0[(t, 12, TRIP[t][2])][2 * fl + ic] for t in TRIP for fl in (0, 1) for ic in range(2)}
    def shifts(M):
        return {(t, L, fl, ic): A2.pair_shift(M, t, L, b, U12[(t, fl, ic)], 2 * fl + ic)[0]
                for t in TRIP for L, b in zip(LS, TRIP[t]) for fl in (0, 1) for ic in range(2)}
    S0c = shifts(M0); reps = []
    for _ in range(NB):
        idx = {kk: [S.resample_idx([c], rng)[0] for c in v] for kk, v in E.items()}
        reps.append(shifts({kk: mean(v, idx[kk]) for kk, v in E.items()}))
    A = {k: np.array([S0c[k]] + [r[k] for r in reps]) for k in S0c}
    err = lambda x: x[1:].std()
    ge = lambda x: f'{x[0]:+.4f}({err(x)*1e4:.0f})'
    CONT = {}; CHI = {}
    for t in TRIP:
        for fl in (0, 1):
            for ic in range(2):
                uc = U12[(t, fl, ic)]; y = np.array([A[(t, L, fl, ic)] for L in LS]); e = y[:, 1:].std(1)
                for form in FORMS:
                    Bm = np.array([S.basis(form, L, uc) for L in LS]); W = np.diag(1 / e ** 2); C = np.linalg.inv(Bm.T @ W @ Bm)
                    CONT[(t, fl, ic, form)] = (C @ Bm.T @ W)[0] @ y
                    r = y[:, 0] - Bm @ (C @ Bm.T @ W @ y[:, 0]); CHI[(t, fl, ic, form)] = (float(r @ W @ r), 3 - Bm.shape[1])
    md = [f'# Step 2 final: Zeuthen vs Wilson, continuum differences and indicative k1 (step2_final.py)\n', f'bootstrap replicas {NB} (moving blocks of 3 configurations, same indices for both flows and both c); dropped: {drop or "none"}\n']
    md.append('## Pair shifts and their Zeuthen - Wilson difference (same configurations)\n')
    md.append('| u | c | pair | Wilson | Zeuthen | Z - W |'); md.append('|---|---|---|---|---|---|')
    for t in TRIP:
        for ic, c in enumerate(CS):
            for L in LS:
                w, z = A[(t, L, 0, ic)], A[(t, L, 1, ic)]
                md.append(f'| {UVAL[t]} | {c} | {L}->{2*L} | {ge(w)} | {ge(z)} | {ge(z-w)} |')
    md.append('\n## Continuum values, continuum Z - W and the continuum c-gap s(0.4) - s(0.3)  [central(bootstrap error), all correlated]\n')
    md.append('| u | form | W c=0.3 [chi2/dof] | Z c=0.3 [chi2/dof] | Z-W c=0.3 | W c=0.4 | Z c=0.4 | Z-W c=0.4 | gap W | gap Z | gap Z - gap W |'); md.append('|---|---|---|---|---|---|---|---|---|---|---|')
    GAP = {}
    for form in FORMS:
        for t in TRIP:
            g = lambda fl, ic: CONT[(t, fl, ic, form)]
            ch = lambda fl, ic: ('[%.1f/%d]' % CHI[(t, fl, ic, form)]) if CHI[(t, fl, ic, form)][1] > 0 else '[exact]'
            gw = g(0, 1) - g(0, 0); gz = g(1, 1) - g(1, 0); GAP[(t, form)] = (gw, gz)
            md.append(f'| {UVAL[t]} | {form} | {ge(g(0,0))} {ch(0,0)} | {ge(g(1,0))} {ch(1,0)} | {ge(g(1,0)-g(0,0))} | {ge(g(0,1))} {ch(0,1)} | {ge(g(1,1))} {ch(1,1)} | {ge(g(1,1)-g(0,1))} | {ge(gw)} | {ge(gz)} | {ge(gz-gw)} |')
    md.append('\nWeighted mean over the 3 u (independent ensembles per u; weights 1/var of the Wilson gap for all three columns so the difference is a fixed linear combination):\n')
    SUMM = {}
    for form in FORMS:
        wt = np.array([1 / err(GAP[(t, form)][0]) ** 2 for t in TRIP]); wt /= wt.sum()
        mw = sum(w * GAP[(t, form)][0] for w, t in zip(wt, TRIP)); mz = sum(w * GAP[(t, form)][1] for w, t in zip(wt, TRIP)); d = mz - mw
        SUMM[form] = dict(gapW=(mw[0], err(mw)), gapZ=(mz[0], err(mz)), dZW=(d[0], err(d)))
        md.append(f'* {form}: continuum gap Wilson {mw[0]:+.4f} +- {err(mw):.4f} ({mw[0]/err(mw):+.1f} sigma); Zeuthen {mz[0]:+.4f} +- {err(mz):.4f} ({mz[0]/err(mz):+.1f} sigma); gap_Z - gap_W {d[0]:+.5f} +- {err(d):.5f} ({d[0]/err(d):+.1f} sigma)')
    # ---- indicative slope fits
    def slope(form, fl, ic, k2free):
        T = np.array([CONT[(t, fl, ic, form)] - S0 for t in TRIP]); us = np.array([U12[(t, fl, ic)] for t in TRIP])
        Cv = np.cov(T[:, 1:]); Bm = np.column_stack([us, us ** 2]) if k2free else us[:, None]
        Ci = np.linalg.inv(Cv); G = np.linalg.inv(Bm.T @ Ci @ Bm) @ Bm.T @ Ci; p = G @ T
        r = T[:, 0] - Bm @ p[:, 0]; return p, float(r @ Ci @ r), len(TRIP) - Bm.shape[1]
    md.append('\n## INDICATIVE slope k1 (3 u only: 1.9, 2.41, 2.9; 3 pairs each; s0 = %.4f fixed; GLS with bootstrap covariance)\n' % S0)
    md.append('Not the stopping-rule input (the rule is defined on the 5-u Wilson analysis, u = 1.0-2.9); with k2 free there is 1 dof and k1, k2 are strongly degenerate over u = 1.9-2.9.\n')
    md.append('| form | k2 | flow | k1(c=0.3) +- sig | z0 / z2L | k1(c=0.4) +- sig | z0 / z2L | k2(0.3), k2(0.4) | chi2 (dof) | k1(0.4)-k1(0.3) corr | rule class. (if applied) |'); md.append('|---|---|---|---|---|---|---|---|---|---|---|')
    K = {}
    for form in FORMS:
        for k2free in (True, False):
            for fl in (0, 1):
                ps = [slope(form, fl, ic, k2free) for ic in range(2)]
                k = [(p[0][0, 0], p[0][0, 1:].std()) for p in ps]; K[(form, k2free, fl)] = ps
                d = ps[1][0][0] - ps[0][0][0]
                two_ = all(abs(v - K1_2L) <= 2 * s and abs(v) >= 3 * s for v, s in k); one_ = all(abs(v) <= 2 * s and abs(v - K1_2L) >= 3 * s for v, s in k)
                cl = 'TWO-LOOP' if two_ else ('ONE-LOOP' if one_ else 'UNDECIDED')
                k2s = ', '.join(f'{p[0][1,0]:+.4f}({p[0][1,1:].std():.4f})' for p in ps) if k2free else '0'
                md.append(f"| {form} | {'free' if k2free else '0'} | {FL[fl]} | {k[0][0]:+.5f} +- {k[0][1]:.5f} | {k[0][0]/k[0][1]:+.1f} / {(k[0][0]-K1_2L)/k[0][1]:+.1f} | {k[1][0]:+.5f} +- {k[1][1]:.5f} | {k[1][0]/k[1][1]:+.1f} / {(k[1][0]-K1_2L)/k[1][1]:+.1f} | {k2s} | {ps[0][1]:.1f}, {ps[1][1]:.1f} ({ps[0][2]}) | {d[0]:+.5f} +- {d[1:].std():.5f} ({d[0]/d[1:].std():+.1f} sig) | {cl} |")
    md.append('\nZeuthen - Wilson difference of k1 (same configurations, correlated):\n')
    for form in FORMS:
        for k2free in (True, False):
            s_ = []
            for ic, c in enumerate(CS):
                d = K[(form, k2free, 1)][ic][0][0] - K[(form, k2free, 0)][ic][0][0]; s_.append(f'c={c}: {d[0]:+.5f} +- {d[1:].std():.5f}')
            md.append(f"* {form}, k2 {'free' if k2free else '0'}: " + '; '.join(s_))
    open(pref + '.md', 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))
    out = {'summary_gap': SUMM, 'k1': {f'{f}|{"free" if k2 else "0"}|{FL[fl]}': [[float(p[0][0, 0]), float(p[0][0, 1:].std())] for p in K[(f, k2, fl)]] for (f, k2, fl) in K},
           'cont': {f'{UVAL[t]}|{FL[fl]}|{CS[ic]}|{form}': [float(v[0]), float(err(v))] for (t, fl, ic, form), v in CONT.items()}}
    json.dump(out, open(pref + '.json', 'w'), indent=1)

if __name__ == '__main__':
    pref = sys.argv[1]; NB = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    drop = {}
    for a in sys.argv[3:]:
        if a.startswith('drop='):
            for kv in a[5:].split(','): n, v = kv.split(':'); drop[n] = int(v)
    main(pref, NB, drop)
