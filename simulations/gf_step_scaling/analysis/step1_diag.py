#!/usr/bin/env python3
"""Step 1 (2026-10-18 evening): diagnose the two L=12 beta=3.34 chains (chi2/dof 4.3/5.0) and re-check all multi-chain (L,beta) groups:
chain-to-chain scatter vs Gamma-method error. usage: step1_diag.py OUT.md"""
import sys, os, glob, re, numpy as np
from scipy import stats
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
R = '/Users/darthur/ym_numerics_runs'; DIRS = [R + '/prod', R + '/prod2', R + '/prod3', R + '/prod4']
out = sys.argv[1]; O = []
def P(s=''): O.append(s); print(s)

def series(r, c, L):
    i = time_index(r, c); t = r['times'][i]; return t * t * r['E'][:, i, 0] / N_lat(c, L)

def blocking(x):
    res = []; n = len(x); b = 1
    while n // b >= 8:
        k = n // b; xb = x[:k * b].reshape(k, b).mean(1); res.append((b, xb.std(ddof=1) / np.sqrt(k))); b *= 2
    return res

# ---- (A) the two beta=3.34 chains
P('## A. L=12 beta=3.34: the two chains'); P()
ch = {}
for x in 'ab':
    f = f'{R}/prod3/su2_L12_b3.34_u2p9{x}.csv'; ch[x] = load_run(f, 3)
P(f'rows: a={len(ch["a"]["sweep"])}, b={len(ch["b"]["sweep"])}; seeds 92168 / 92175 (distinct, cold start, therm 300 sweeps, sep 10); no resume events in stderr (single uninterrupted process each, 600/600).')
P(f'max |row-wise difference| of g2(c=0.3) between chains: {np.abs(series(ch["a"],0.3,12)-series(ch["b"],0.3,12)).max():.4f}; identical rows: {int((series(ch["a"],0.3,12)==series(ch["b"],0.3,12)).sum())}; sample correlation of the two series {np.corrcoef(series(ch["a"],0.3,12),series(ch["b"],0.3,12))[0,1]:+.3f}')
P()
P('| chain | obs | mean | Gamma err | tau_int | naive std/sqrt(N) | block-err b=1,2,4,8,16,32 | quarter means (4 x 150) | first/second half z | slope per 100 meas (err) | max&#124;Q&#124; |'); P('|---|---|---|---|---|---|---|---|---|---|---|')
for x in 'ab':
    r = ch[x]
    for lab, s in [('g2 c=0.3', series(r, 0.3, 12)), ('g2 c=0.4', series(r, 0.4, 12)), ('plaq', r['plaq'])]:
        m, e, tau, W = gamma_method(s); n = len(s); h = n // 2
        a, ea = gamma_method(s[:h])[:2]; b, eb = gamma_method(s[h:])[:2]
        bl = blocking(s); q = [s[i * 150:(i + 1) * 150].mean() for i in range(4)]
        sl = stats.linregress(np.arange(n) / 100., s)
        Q = np.abs(r['E'][:, time_index(r, 0.4), 2]).max()
        P(f'| {x} | {lab} | {m:.5f} | {e:.5f} | {tau:.2f} | {s.std(ddof=1)/np.sqrt(n):.5f} | ' + ', '.join(f'{v:.5f}' for _, v in bl[:6]) + f' | ' + ', '.join(f'{v:.4f}' for v in q) + f' | {(b-a)/np.hypot(ea,eb):+.2f} | {sl.slope:+.5f} ({sl.stderr:.5f}) | {Q:.3f} |')
P()
for lab, f in [('g2 c=0.3', lambda r: series(r, 0.3, 12)), ('g2 c=0.4', lambda r: series(r, 0.4, 12)), ('plaq', lambda r: r['plaq'])]:
    sa, sb = f(ch['a']), f(ch['b']); ma, ea = gamma_method(sa)[:2]; mb, eb = gamma_method(sb)[:2]
    d = ma - mb; z = d / np.hypot(ea, eb)
    # permutation test: pool the 1200 samples, split randomly into chains of 600 (valid when tau~0.5)
    rng = np.random.default_rng(1); pool = np.concatenate([sa, sb]); ds = []
    for _ in range(20000):
        pm = rng.permutation(pool); ds.append(pm[:600].mean() - pm[600:].mean())
    pp = np.mean(np.abs(ds) >= abs(d))
    # Welch t-test on raw samples
    tt = stats.ttest_ind(sa, sb, equal_var=False)
    # pair of 150-blocks as a check of 'sample-level' variance
    P(f'* {lab}: a-b = {d:+.5f}, z = {z:+.2f} (Gamma), permutation p = {pp:.4f}, Welch t p = {tt.pvalue:.4f}, variance ratio Var(a)/Var(b) = {sa.var(ddof=1)/sb.var(ddof=1):.3f}, KS p = {stats.ks_2samp(sa,sb).pvalue:.3f}')
# autocorrelation function
P(); P('Autocorrelation rho(1..8) of g2(c=0.3): ' + '; '.join(f'{x}: ' + ' '.join(f'{v:+.2f}' for v in (lambda s: [np.corrcoef(s[:-k], s[k:])[0, 1] for k in range(1, 9)])(series(ch[x], 0.3, 12))) for x in 'ab'))
P(f'1/sqrt(N)=0.041 is the 1-sigma scale of each lag; |rho(k)|>0.082 would be 2 sigma.')

# ---- (B) all multi-chain groups
P(); P('## B. Chain-to-chain scatter vs quoted (Gamma) errors for every (L,beta) with >= 2 independent chains'); P()
groups = {}
for d in DIRS:
    for f in sorted(glob.glob(d + '/su2_L*_b*.csv')):
        n = os.path.basename(f)
        if any(k in n for k in ('.alt', '.zeu', '_cold', '_tau', 'bad_', '_z1p', '_z2p')): continue
        mm = re.match(r'su2_L(\d+)_b([\d.]+?)(?:_|\.csv)', n)
        if not mm: continue
        L = int(mm.group(1)); b = float(mm.group(2)); r = load_run(f, 3)
        if len(r['sweep']) < 50: continue
        groups.setdefault((L, b, r['eps'], r['sep']), []).append((n, r))
P('| L | beta | #chains (n each) | c | chi2/dof | dof | p | pooled err (Gamma) | sample std of chain means | ratio scatter/predicted | notes |'); P('|---|---|---|---|---|---|---|---|---|---|---|')
allchi = []; 
for (L, b, eps, sep), runs in sorted(groups.items()):
    if len(runs) < 2: continue
    for c in (0.3, 0.4):
        ms, es, ns = [], [], []
        for n, r in runs:
            try: s = series(r, c, L)
            except AssertionError: continue
            m, e, tau, W = gamma_method(s); ms.append(m); es.append(e); ns.append(len(s))
        if len(ms) < 2: continue
        ms, es = np.array(ms), np.array(es); w = 1 / es ** 2; mw = (w * ms).sum() / w.sum(); chi = np.sum(((ms - mw) / es) ** 2); dof = len(ms) - 1
        p = stats.chi2.sf(chi, dof); allchi.append((chi, dof, p, L, b, c))
        P(f'| {L} | {b:g} | {len(ms)} ({min(ns)}-{max(ns)}) | {c} | {chi/dof:.2f} | {dof} | {p:.3f} | {1/np.sqrt(w.sum()):.5f} | {ms.std(ddof=1):.5f} | {ms.std(ddof=1)/np.sqrt(np.mean(es**2)):.2f} | eps={eps} sep={sep} |')
c3 = [a for a in allchi if a[5] == 0.3]
X = sum(a[0] for a in c3); D = sum(a[1] for a in c3)
P(); P(f'Global (c=0.3 groups, {len(c3)} groups): sum chi2 = {X:.1f} for {D} dof (chi2/dof = {X/D:.2f}, p = {stats.chi2.sf(X, D):.3f}); excluding L=12 beta=3.34: ' + (lambda l: f'sum chi2 = {sum(a[0] for a in l):.1f} for {sum(a[1] for a in l)} dof, p = {stats.chi2.sf(sum(a[0] for a in l), sum(a[1] for a in l)):.3f}')([a for a in c3 if not (a[3] == 12 and abs(a[4] - 3.34) < 1e-6)]))
ps = sorted(a[2] for a in c3); P('Sorted p-values (c=0.3): ' + ' '.join(f'{p:.3f}' for p in ps) + f'; fraction with p<0.05: {np.mean(np.array(ps)<0.05):.2f} (expected 0.05); Bonferroni-corrected p of the smallest: {min(1,min(ps)*len(ps)):.3f}')
open(out, 'w').write('\n'.join(O) + '\n')
