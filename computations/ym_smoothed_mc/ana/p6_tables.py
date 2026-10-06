import json, numpy as np, sys
RUNS = [('p5_b2.50_s2', 2.50, 2), ('p5_b2.60_s3', 2.60, 3), ('p5_b2.70_s4', 2.70, 4), ('p5_b2.85_s6', 2.85, 6), ('b2.95_s8', 2.95, 8), ('b3.00_s10_AB', 3.00, 10), ('b3.00_s10_A', 3.00, 10), ('b3.00_s10_B', 3.00, 10)]
def f(v, e, d=3):
    if v is None or not np.isfinite(v): return 'n/a'
    if not np.isfinite(e) or e == 0: return f"{v:.{d}f}"
    ed = max(1, int(np.ceil(-np.log10(e)))+1); ed = min(ed, 5)
    return f"{v:.{ed}f}({int(round(e*10**ed))})"
D = {r: json.load(open(f'runs/p6/{r}.json')) for r, _, _ in RUNS}
L = []
L.append("# P6 — window survival W = R(s+1)/R(s//2) under different vacuum-subtraction estimators\n")
L.append("Data: P5 rho-scan runs (beta 2.50-2.85, 24^3x32), b2.95 32^3x48 s8 (240 meas), b3.00 32^3x48 s10 streams A+B (2x170 meas; stream C still running, excluded). Spatial Wilson flow, rho=sqrt(6 t)/s; zero-momentum s x s loop operator averaged over 3 planes. Jackknife over bins (size chosen as max(5, 4*tau_int max), shown in col 'bin'); bins never straddle streams.\n")
L.append("Estimators: **E1** per-stream global vacuum subtraction C=<OO>_str-<O>_str^2 (pooled over streams by bin count); **E2** per-block (jackknife-bin) subtraction C=mean_b(<OO>_b-<O>_b^2); **E3f** far-lag (subtraction-free) C(n)=Q(n)-Q(Lt/2) (exact cancellation of <O>^2; bias = -C(Lt/2)); **E3d** differenced D(n)=Q(n)-Q(n+1), W_D=D(s+1)/D(s//2); **E3o** fit Q(n), n in [s//2, Lt/2], to A cosh-type single exponential + free constant K, W from the model (single-state, ignores excited states at lag s//2).\n")
L.append("**E1c** = E1 plus bias correction: E1 is biased low by Var(<O>_stream) (constant offset in C); estimated from the bin scatter as (C_E1-C_E2)/(nbins_stream-1). Valid only if bins are independent (tau plateaued).\n\nc0 = 2(1-W)/W, -2 log W given for E1. Sensitivity: spread = (max-min of W over E1,E1c,E2,E3f,E3d [and incl. E3o])/sigma_E1; max corr. pull = largest |W_X - W_E1| / sigma(W_X - W_E1) with the difference jackknifed (correlations kept), X in {E2,E3f,E3d} (E1c-E1 is a tiny near-deterministic shift, +0.001..0.03, so its pull is not meaningful).\n")
for rho in ['0.75', '1.00', '0.50', '1.25', '1.50', '0.00']:
    L.append(f"\n## rho = {rho}\n")
    L.append("| beta | s | bin | W E1 | W E1c | W E2 | W E3f | W E3d | W E3o (a m_fit) | c0 (E1) | -2logW (E1) | R(s)/R(0) | eps*s E1 | eps*s E2 | eps*s E3f | eps_shift*s E1 | spread/sigma_E1 (excl. E3o / incl.) | max corr. pull (which) |")
    L.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r, b, s in RUNS:
        d = D[r]; lv = d['levels'].get(rho)
        if lv is None: continue
        e = lv['est']; g = lambda k, i: (e[k][0][i], e[k][1][i])
        W1 = g('E1_stream', 0); Ws = [W1[0], g('E1c_biascorr', 0)[0], g('E2_block', 0)[0], g('E3_farlag', 0)[0], g('E3_diff', 0)[0]]
        Ws = [w for w in Ws if np.isfinite(w)]; Wo = Ws + [g('E3_offsetfit', 0)[0]]
        pl = {k_: abs(v[0])/v[1] for k_, v in lv['pulls'].items() if v[1] > 0 and k_ not in ('E3_offsetfit', 'E1c_biascorr')}
        pk = max(pl, key=pl.get); short = dict(E1c_biascorr='E1c', E2_block='E2', E3_farlag='E3f', E3_diff='E3d')
        c0 = 2*(1-W1[0])/W1[0]; c0e = 2*W1[1]/W1[0]**2; lw = -2*np.log(W1[0]); lwe = 2*W1[1]/W1[0]
        L.append(f"| {b:.2f} | {s}{'' if r.endswith(('AB','s2','s3','s4','s6','s8')) else ' ('+r[-1]+')'} | {d['binsize']} | {f(*W1)} | {f(*g('E1c_biascorr',0))} | {f(*g('E2_block',0))} | {f(*g('E3_farlag',0))} | {f(*g('E3_diff',0))} | {f(*g('E3_offsetfit',0))} ({f(*g('E3_offsetfit',1))}) | {f(c0,c0e)} | {f(lw,lwe)} | {f(*g('E1_stream',3))} | {f(*g('E1_stream',2))} | {f(*g('E2_block',2))} | {f(*g('E3_farlag',2))} | {f(*g('E1_stream',5))} | {(max(Ws)-min(Ws))/W1[1]:.1f} / {(max(Wo)-min(Wo))/W1[1]:.1f} | {pl[pk]:.1f} ({short[pk]}) |")
# Fejer
L.append("\n## Fejer time-box (Lean-type, radius M) smoothed state, E1 correlator: W_Y(M) = sum_{k,l<=M} R(s+1+k+l) / sum_{k,l<=M} R(s//2+k+l); only where s+1+2M <= Lt/2\n")
for rho in ['0.75', '1.00']:
    L.append(f"\n### rho = {rho}\n\n| beta | s | W (M=0) | M=1 | M=2 | M=s//2 | M=s |\n|---|---|---|---|---|---|---|")
    for r, b, s in RUNS[:6]:
        lv = D[r]['levels'][rho]; e = lv['est']['E1_stream']; Ms = lv['Ms_fejer']
        cells = {M: f(e[0][6+i], e[1][6+i]) for i, M in enumerate(Ms)}
        L.append(f"| {b:.2f} | {s} | {f(e[0][0], e[1][0])} | {cells.get(1,'')} | {cells.get(2,'')} | {cells.get(max(1,s//2),'')} | {cells.get(s,'')} |")
open('runs/P6_WINDOW_ESTIMATORS.md', 'w').write('\n'.join(L)+'\n')

# tau
T = ["# P6 — binning tau_int of the operator mean (main side), and jackknife error of W, eps vs bin size\n",
     "tau(b) = b*Var(bin means)/(2 Var(x)); for multi-stream, averaged over streams. FLAG = tau at largest bin still >15% above previous bin (not plateaued).\n",
     "| beta | s | N/stream | rho | tau(1) | tau(2) | tau(4) | tau(8) | tau(16) | tau(32) | flag |", "|---|---|---|---|---|---|---|---|---|---|---|"]
for r, b, s in RUNS:
    d = D[r]
    for rho, tc in d['tau'].items():
        ks = sorted(tc, key=int); v = [tc[k] for k in ks]
        flag = 'RISING' if len(v) >= 2 and v[-1] > 1.15*v[-2] else 'ok'
        cells = [f"{tc[str(k)]:.2f}" if str(k) in tc else '' for k in [1, 2, 4, 8, 16, 32]]
        T.append(f"| {b:.2f} | {s}{' ('+r[-1]+')' if r[-1] in 'AB' and not r.endswith('AB') else ''} | {d['N'][0]} | {rho} | " + ' | '.join(cells) + f" | {flag} |")
T.append("\n## Jackknife error of W (E1) and eps vs bin size b (rho 0.75, 1.00)\n\n| beta | s | rho | sigma_W(b=1,2,4,8,16,32) | sigma_eps(b=...) | W-error plateau? |\n|---|---|---|---|---|---|")
for r, b, s in RUNS:
    for rho, row in D[r]['binscan'].items():
        ks = sorted(row, key=int); sw = [row[k][0] for k in ks]; se = [row[k][1] for k in ks]
        pl = 'RISING' if len(sw) >= 2 and sw[-1] > 1.15*sw[-2] else 'ok'
        T.append(f"| {b:.2f} | {s}{' ('+r[-1]+')' if r[-1] in 'AB' and not r.endswith('AB') else ''} | {rho} | " + ', '.join(f"{x:.3f}" for x in sw) + " | " + ', '.join(f"{x:.4f}" for x in se) + f" (b={','.join(ks)}) | {pl} |")
open('runs/P6_TAU.md', 'w').write('\n'.join(T)+'\n')

# raw vs smoothed
R = ["# P6 — raw vs smoothed effective masses (main side s x s loop, same configs)\n",
     "m_eff(n) = ln C(n)/C(n+1), E1 correlator, jackknife errors; [D] = from differenced (subtraction-free) correlator. 'drown' = first lag n with C(n) < 2 sigma. Physical reference a*m0++ ~ 3.78*0.26/(sqrt(t0)/a).\n"]
st0 = {2.50: 1.9, 2.60: 2.5, 2.70: 3.2, 2.85: 4.2, 2.95: 5.548, 3.00: 6.422}
for r, b, s in RUNS[:6]:
    d = D[r]; R.append(f"\n## beta {b:.2f}, s={s}, Lt={d['hdr']['Lt']}\n")
    R.append("| rho | drown lag | " + " | ".join(f"n={n}" for n in range(len(d['levels']['0.00']['meff']))) + " |")
    R.append("|---|---|" + "---|"*len(d['levels']['0.00']['meff']))
    for rho, lv in d['levels'].items():
        C = np.array(lv['C']); Ce = np.array(lv['Ce']); dr = next((n for n in range(len(C)) if C[n] < 2*Ce[n]), None)
        R.append(f"| {rho} | {dr if dr is not None else '>'+str(len(C)-1)} | " + " | ".join(f(m, e) if (dr is None or n+1 < dr) else '–' for n, (m, e) in enumerate(zip(lv['meff'], lv['meffe']))) + " |")
    for rho in ['0.00', '1.00']:
        lv = d['levels'][rho]; C = np.array(lv['C']); Ce = np.array(lv['Ce'])
        R.append(f"| {rho} [D] | | " + " | ".join(f(m, e) if np.isfinite(m) and e < 1 else '–' for m, e in zip(lv['meffD'], lv['meffDe'])) + " |")
open('runs/P6_RAW_VS_SMOOTH.md', 'w').write('\n'.join(R)+'\n')
