#!/usr/bin/env python3
"""Step 2: Zeuthen flow vs Wilson flow on the SAME configurations (runs *_z1p9/_z2p4/_z2p9 in prod4: NAME.csv = Wilson flow, NAME.zeu.csv = Zeuthen flow, eps 0.1).
g2_W = t^2 E_c / N_lat(c,L),  g2_Z = t^2 E_c^(Zeuthen) / N_zeu(c,L).  Pairs 6->12 (beta6), 8->16 (beta8), 12->24 (beta12) pointwise, shifts moved to the
common u of each (flow, c) by the exact two-loop slope.  Configuration bootstrap (moving blocks of 3, same configs for both flows and both c).
Outputs: pair shifts, c-gap (0.4 - 0.3) per pair and flow, Zeuthen - Wilson differences, continuum values (lin3 / T1.636 / quad3), c-gap in the continuum, k1.
usage: step2_analysis.py OUTPREFIX [NBOOT]   (uses whatever is complete; pairs/u with missing ensembles are skipped)"""
import sys, os, glob, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfana import load_run, time_index, N_lat, gamma_method
from zeuthen_norm import N_zeu
import step34 as S
R = '/Users/darthur/ym_numerics_runs/prod4'
TRIP = {'1p9': (3.77, 3.88, 4.02), '2p4': (3.34, 3.45, 3.60), '2p9': (3.08, 3.19, 3.34)}
UVAL = {'1p9': 1.9, '2p4': 2.41, '2p9': 2.9}
CS = (0.3, 0.4); LS = (6, 8, 12); NAMES = ['W0.3', 'W0.4', 'Z0.3', 'Z0.4']

def load():
    E = {}
    for f in sorted(glob.glob(R + '/su2_L*_z*.csv')):
        if f.endswith('.zeu.csv') or f.endswith('.alt.csv'): continue
        zf = f[:-4] + '.zeu.csv'
        if not os.path.exists(zf): continue
        w = load_run(f, 3); z = load_run(zf, 3); n = min(len(w['sweep']), len(z['sweep']))
        if n < 20: continue
        tag = f.split('_z')[-1].replace('.csv', '').rstrip('ab'); L = w['L']; b = round(w['beta'], 6)
        cols = []
        for run, norm in ((w, N_lat), (z, N_zeu)):
            for c in CS:
                i = time_index(run, c); t = run['times'][i]; cols.append(t * t * run['E'][:n, i, 0] / norm(c, L))
        # completeness: keep only finished chains (all requested measurements) -> caller decides via nmeas in header? use row count vs expected
        E.setdefault((tag, L, b), []).append((np.column_stack(cols), f))
    return E

EXPECT = {24: 200, 16: 400, 12: 600, 8: 2000, 6: 3000}
def complete(E):
    out = {}
    for k, ch in E.items():
        L = k[1]; good = [c for c, f in ch if len(c) >= EXPECT[L]]
        if good: out[k] = good
    return out

def pair_shift(M, tag, L, b, u12c, col):
    u = M[(tag, L, b)][col]; sg = M[(tag, 2 * L, b)][col]
    return 1 / u - 1 / sg + S.dtwo(u) * (u12c - u), u

def run(pref, NB):
    E = complete(load())
    rng = np.random.default_rng(777)
    tags = [t for t in TRIP if all((t, L, TRIP[t][i]) in E for i, L in enumerate((12, 16, 12)))]  # placeholder check, refined per pair below
    def mean(chs, idx=None):
        return np.vstack(chs if idx is None else [c[i] for c, i in zip(chs, idx)]).mean(0)
    M0 = {k: mean(v) for k, v in E.items()}
    # which pairs are available
    avail = {}
    for t, (b6, b8, b12) in TRIP.items():
        d = {}
        for L, b in ((6, b6), (8, b8), (12, b12)):
            if (t, L, b) in E and (t, 2 * L, b) in E: d[L] = b
        if 12 in d: avail[t] = d
    if not avail: print('no complete pairs yet'); return
    def shifts(M, U12):
        out = {}
        for t, d in avail.items():
            for L, b in d.items():
                for fl in (0, 1):
                    for ic in range(2):
                        col = 2 * fl + ic
                        out[(t, L, fl, ic)] = pair_shift(M, t, L, b, U12[(t, fl, ic)], col)[0]
        return out
    U12 = {(t, fl, ic): M0[(t, 12, d[12])][2 * fl + ic] for t, d in avail.items() for fl in (0, 1) for ic in range(2)}
    S0c = shifts(M0, U12)
    reps = []
    for k in range(NB):
        idx = {kk: [S.resample_idx([c], rng)[0] for c in v] for kk, v in E.items()}
        Mk = {kk: mean(v, idx[kk]) for kk, v in E.items()}
        reps.append(shifts(Mk, U12))
    keys = list(S0c)
    A = {k: np.array([S0c[k]] + [r[k] for r in reps]) for k in keys}
    md = ['# Step 2: Zeuthen vs Wilson flow, same configurations (step2_analysis.py)\n', f'bootstrap replicas {NB}; complete ensembles: ' + ', '.join(f'{k[0]}:L{k[1]}b{k[2]:g}' for k in sorted(E)) + '\n']
    FL = ['Wilson', 'Zeuthen']
    md.append('## Pair shifts at the common u of each (flow, c)  [central (bootstrap error)]\n')
    md.append('| u | flow | c | u12 | 6->12 | 8->16 | 12->24 |'); md.append('|---|---|---|---|---|---|---|')
    for t in avail:
        for fl in (0, 1):
            for ic, c in enumerate(CS):
                md.append(f'| {UVAL[t]} | {FL[fl]} | {c} | {U12[(t, fl, ic)]:.4f} | ' + ' | '.join((f'{A[(t,L,fl,ic)][0]:.4f}({A[(t,L,fl,ic)][1:].std()*1e4:.0f})' if (t, L, fl, ic) in A else '-') for L in LS) + ' |')
    md.append('\n## c-gap of the pair shift: s(c=0.4) - s(c=0.3) [bootstrap error, correlated]  and  Zeuthen - Wilson per pair (same configs)\n')
    md.append('| u | pair | gap Wilson | gap Zeuthen | gap_Z - gap_W | Z-W (c=0.3) | Z-W (c=0.4) |'); md.append('|---|---|---|---|---|---|---|')
    ge = lambda x: f'{x[0]:+.4f}({x[1:].std()*1e4:.0f})'
    for t in avail:
        for L in LS:
            if (t, L, 0, 0) not in A: continue
            gw = A[(t, L, 0, 1)] - A[(t, L, 0, 0)]; gz = A[(t, L, 1, 1)] - A[(t, L, 1, 0)]
            md.append(f'| {UVAL[t]} | {L}->{2*L} | {ge(gw)} | {ge(gz)} | {ge(gz-gw)} | {ge(A[(t,L,1,0)]-A[(t,L,0,0)])} | {ge(A[(t,L,1,1)]-A[(t,L,0,1)])} |')
    # continuum values
    CONT = {}
    forms = ['lin', 'T1.636', 'quad']
    md.append('\n## Continuum extrapolation of the pair shifts (3 pairs per u where available)\n')
    md.append('| u | flow | c | form | continuum s | chi2/dof | two-loop exact |'); md.append('|---|---|---|---|---|---|---|')
    for t, d in avail.items():
        Ls = [L for L in LS if (t, L, 0, 0) in A]
        if len(Ls) < 3: continue
        for fl in (0, 1):
            for ic, c in enumerate(CS):
                uc = U12[(t, fl, ic)]; y = np.array([A[(t, L, fl, ic)] for L in Ls]); e = y[:, 1:].std(1)
                for form in forms:
                    Bm = np.array([S.basis(form, L, uc) for L in Ls]); W = np.diag(1 / e ** 2); C = np.linalg.inv(Bm.T @ W @ Bm); w = (C @ Bm.T @ W)[0]
                    cont = w @ y; CONT[(t, fl, ic, form)] = cont
                    r = y[:, 0] - Bm @ (C @ Bm.T @ W @ y[:, 0]); dof = 3 - Bm.shape[1]
                    md.append(f'| {UVAL[t]} | {FL[fl]} | {c} | {form} | {cont[0]:.4f}({cont[1:].std()*1e4:.0f}) | ' + (f'{float(r@W@r):.1f}/{dof}' if dof > 0 else 'exact') + f' | {S.two(uc):.4f} |')
    md.append('\n## Continuum c-gap  s(0.4) - s(0.3)  per u (lin3 | T1.636 | quad3) and error-weighted mean over u\n')
    md.append('| u | flow | lin | T1.636 | quad |'); md.append('|---|---|---|---|---|')
    for t in avail:
        for fl in (0, 1):
            if (t, fl, 0, 'lin') not in CONT: continue
            md.append(f'| {UVAL[t]} | {FL[fl]} | ' + ' | '.join(ge(CONT[(t, fl, 1, f)] - CONT[(t, fl, 0, f)]) for f in forms) + ' |')
    for fl in (0, 1):
        for f in forms:
            ts = [t for t in avail if (t, fl, 0, f) in CONT]
            if not ts: continue
            G = np.array([CONT[(t, fl, 1, f)] - CONT[(t, fl, 0, f)] for t in ts]); wt = 1 / G[:, 1:].var(1); mg = (wt[:, None] * G).sum(0) / wt.sum()
            md.append(f'* {FL[fl]} {f}: weighted-mean continuum gap over {len(ts)} u = {mg[0]:+.4f} +- {mg[1:].std():.4f} ({mg[0]/mg[1:].std():+.1f} sigma)')
    open(pref + '.md', 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))

if __name__ == '__main__':
    run(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 500)
