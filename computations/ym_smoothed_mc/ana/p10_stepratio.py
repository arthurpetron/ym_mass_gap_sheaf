"""P10 exact-anchor step ratio from multilevel data (MC numerics only; not proof).
usage: p10_stepratio.py <ml rundir> [--bin 10] [--out md] [--label txt]
Y_j = timeslice plaquette sum with one-sided time box M=side: R_Y(n) = (M+1)^-2 sum_{a,b<=M} R(n+a+b) (the state consumed by ExprStepRatio, 9d58a5df).
c(k) = side*(1 - R_Y(k+1)/R_Y(k)) for k = 0..side/2 (E1: interior pairs, matched-mean subtraction); theta_k = (R_Y(k+1)/R_Y(k))^(side/2+1) vs W = R_Y(s+1)/R_Y(s/2).
c_D(k): same from the subtraction-free differenced D(n) = R_Y(n) - R_Y(n+1) over all pairs. Jackknife over bins; mono = largest increase c(k+1)-c(k) in sigma."""
import sys, os, json, numpy as np, argparse, time
ap = argparse.ArgumentParser(); ap.add_argument('rundir'); ap.add_argument('--bin', type=int, default=10); ap.add_argument('--out'); ap.add_argument('--label', default='')
A = ap.parse_args()
raw = open(f'{A.rundir}/data.bin', 'rb').read(); nl = raw.index(b'\n'); h = json.loads(raw[:nl]); Lt = h['Lt']; d = h['ml_d']; ns = h['ml_nsub']; nq = Lt//2
reclen = Lt + len(ns)*(Lt + Lt*Lt) + 2; a = np.frombuffer(raw[nl+1:], dtype='<f8'); N = len(a)//reclen; a = a[:N*reclen].reshape(N, reclen)
slab = np.array([t//d if t % d else -1-t for t in range(Lt)]); same = (slab[:, None] == slab[None, :]) & (slab[:, None] >= 0)
def Qof(C, S1, interior):
    Q, Am, Bm = [], [], []
    for n in range(nq+1):
        ts = [t for t in range(Lt) if not interior or (slab[t] >= 0 and slab[(t+n) % Lt] >= 0)]
        Q.append(np.mean([C[:, t, (t+n) % Lt] for t in ts], 0)); Am.append(S1[:, ts].mean(1)); Bm.append(S1[:, [(t+n) % Lt for t in ts]].mean(1))
    return np.stack(Am, 1), np.stack(Bm, 1), np.stack(Q, 1)
est = {}
for i, n in enumerate(ns):
    o = Lt + i*(Lt + Lt*Lt); S1 = a[:, o:o+Lt]; S2 = a[:, o+Lt:o+Lt+Lt*Lt].reshape(N, Lt, Lt); C = np.where(same[None], S2, S1[:, :, None]*S1[:, None, :])
    est[n] = (Qof(C, S1, True), Qof(C, S1, False)[2])
def boxR(r, M):
    e = np.concatenate([r, r[1:nq][::-1], r[:1]]); return np.array([sum(e[n+a_+b_] for a_ in range(M+1) for b_ in range(M+1))/(M+1)**2 if n+2*M <= Lt else np.nan for n in range(nq+1)])
SIDES = (2, 3, 4)
def quantities(q, qa, Ab, Bb):
    r = q - Ab*Bb; out = {}
    for s in SIDES:
        R = boxR(r, s); Ra = boxR(qa, s); D = Ra[:-1] - Ra[1:]; h2 = s//2
        c = np.array([s*(1 - R[k+1]/R[k]) for k in range(h2+1)]); cD = np.array([s*(1 - D[k+1]/D[k]) for k in range(h2+1)])
        th = np.array([(R[k+1]/R[k])**(h2+1) for k in range(h2+1)]); W = R[s+1]/R[h2]
        out[s] = np.concatenate([c, np.diff(c) if h2 > 0 else [], cD, th, [W, D[s+1]/D[h2]], R[:s+2]/R[0]])
    return out
def jk(n, B):
    (Am, Bm, Q), Qa = est[n]; nb = len(Q)//B; bn = lambda x: x[:nb*B].reshape(nb, B, *x.shape[1:]).mean(1)
    Ab, Bb, Qb, Qab = bn(Am), bn(Bm), bn(Q), bn(Qa)
    f = lambda m: quantities(Qb[m].mean(0), Qab[m].mean(0), Ab[m].mean(0), Bb[m].mean(0))
    full = f(np.ones(nb, bool)); js = [f(np.arange(nb) != i) for i in range(nb)]
    err = {s: np.sqrt((nb-1)/nb*((np.array([j[s] for j in js]) - np.mean([j[s] for j in js], 0))**2).sum(0)) for s in SIDES}
    return full, err, nb
fm = lambda v, e: f"{v:.3f}({e:.3f})" if np.isfinite(v) and np.isfinite(e) else "n/a"
B = A.bin
L = [f"# P10 exact-anchor step ratio c(k) on Y_j from the multilevel data — {time.strftime('%Y-%m-%d %H:%M %Z')}\n",
     "**MC numerics only; not proof.** Tests the open Lean input `ExprStepRatio tr ρ k` (ρ_j R_j(k_j) ≤ R_j(k_j+1); BF4WilsonAllNomeExprStepRatioWindowSurvival.lean:232, consumed by 9d58a5df) on the exact padded anchor Y_j = timeslice spatial-plaquette sum (unit coefficients) with one-sided time box M=side.\n",
     f"run `{A.rundir}` {A.label}: {h['Ls']}^3x{Lt}, beta {h['beta']}, multilevel d={d}, nsub {ns}, N={N} configs, bins of {B}. E1 = interior pairs + matched-mean subtraction; c_D = subtraction-free differenced correlator (all pairs). c(k) = side·(1 − R_Y(k+1)/R_Y(k)); θ_k = (R_Y(k+1)/R_Y(k))^(s/2+1); W = R_Y(s+1)/R_Y(s/2). mono = largest increase c(k+1)−c(k) in σ (jackknife of the difference; > +2 would flag a violation of monotonicity).\n"]
res = {n: jk(n, B) for n in ns}
L.append("| nsub | side | bins | " + " | ".join(f"c(k={k})" for k in range(3)) + " | mono (σ) | c_D(0) | c_D(s/2) | θ_0 | θ_{s/2} | W E1 | W E3d | R_Y(1)/R_Y(0) | R_Y(s/2)/R_Y(0) | R_Y(s+1)/R_Y(0) |")
L.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
summary = {}
for n in ns[::-1]:
    full, err, nb = res[n]
    for s in SIDES:
        h2 = s//2; v, e = full[s], err[s]; nc = h2+1; nd = h2
        cs = [fm(v[k], e[k]) if k <= h2 else "" for k in range(3)]
        mono = max(v[nc+i]/e[nc+i] for i in range(nd)) if nd else np.nan
        o = nc+nd; cD = v[o:o+nc]; eD = e[o:o+nc]; o2 = o+nc; th = v[o2:o2+nc]; eth = e[o2:o2+nc]; o3 = o2+nc
        W, eW, WD, eWD = v[o3], e[o3], v[o3+1], e[o3+1]; Rr = v[o3+2:]; eR = e[o3+2:]
        L.append(f"| {n} | {s} | {nb} | " + " | ".join(cs) + f" | {mono:+.1f} | {fm(cD[0], eD[0])} | {fm(cD[h2], eD[h2])} | {fm(th[0], eth[0])} | {fm(th[h2], eth[h2])} | {fm(W, eW)} | {fm(WD, eWD)} | {fm(Rr[1], eR[1])} | {fm(Rr[h2], eR[h2])} | {fm(Rr[s+1], eR[s+1])} |")
        summary[(n, s)] = (v[:nc], e[:nc], mono)
L.append("\n## Binning check (primary nsub): error of c(s/2) and c(0) vs bin size\n")
L.append("| nsub | bin | bins | " + " | ".join(f"σc(0) s={s} | σc(s/2) s={s}" for s in SIDES) + " |"); L.append("|---|---|---|" + "---|---|"*len(SIDES))
for Bb in (5, 10, 20, 40):
    if N//Bb < 8: continue
    full, err, nb = jk(ns[-1], Bb); L.append(f"| {ns[-1]} | {Bb} | {nb} | " + " | ".join(f"{err[s][0]:.3f} | {err[s][s//2]:.3f}" for s in SIDES) + " |")
L.append("\n## Comparison with P9 (beta 2.5, p8_hi 16^3x32 direct chain, 5400 meas; flow rho=1)\n")
L.append("| side | operator | c(0) | c(s/2) |"); L.append("|---|---|---|---|")
P9 = {2: [('flow rho=1 loop', '1.3963(46)', '1.249(15)'), ('Lean smoothed state (flow loop + box M=side)', '1.295(12)', '1.188(32)'), ('Y_j direct chain (P9)', '1.811(18)', '1.78(18)')],
      3: [('flow rho=1 loop', '1.8087(66)', '1.625(16)'), ('Lean smoothed state (flow loop + box M=side)', '1.665(21)', '1.565(46)'), ('Y_j direct chain (P9)', '2.735(41)', '2.63(45)')],
      4: [('flow rho=1 loop', '2.2438(92)', '1.990(38)'), ('Lean smoothed state (flow loop + box M=side)', '2.040(36)', '1.86(13)'), ('Y_j direct chain (P9)', '3.641(75)', '1.2(24)')]}
for s in SIDES:
    for nm, c0, ch in P9[s]: L.append(f"| {s} | {nm} | {c0} | {ch} |")
    c, e, mono = summary[(ns[-1], s)]; L.append(f"| {s} | **Y_j multilevel nsub={ns[-1]} (this run)** | {fm(c[0], e[0])} | {fm(c[s//2], e[s//2])} |")
out = '\n'.join(L) + '\n'; print(out)
if A.out: open(A.out, 'w').write(out)
