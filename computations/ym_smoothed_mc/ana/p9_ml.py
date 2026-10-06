"""P9 item 6: multilevel (Luscher-Weisz) pilot analysis for the zero-momentum plaquette correlator behind Y_j.
usage: p9_ml.py <ml rundir> [--direct <direct data.bin with side 1>] [--bin b] [--out md]
Record (bin/p4run_p9 --ml-d d --ml-nsub n1,..): P0[t] (level-0 config), then per n in ml_nsub: S1[t] = sub-average of P(t),
S2[t,u] = sub-average of P(t)P(u); then [level-0 sweep seconds, sub-update seconds (all nsub, incl. measurements)]."""
import sys, os, json, numpy as np, argparse, time
sys.path.insert(0, os.path.dirname(__file__)); from load import load
ap = argparse.ArgumentParser(); ap.add_argument('rundir'); ap.add_argument('--direct'); ap.add_argument('--bin', type=int, default=5); ap.add_argument('--out'); ap.add_argument('--skip', type=int, default=0)
A = ap.parse_args()
raw = open(f'{A.rundir}/data.bin', 'rb').read(); nl = raw.index(b'\n'); h = json.loads(raw[:nl]); Lt = h['Lt']; d = h['ml_d']; ns = h['ml_nsub']; nq = Lt//2
reclen = Lt + len(ns)*(Lt + Lt*Lt) + 2; a = np.frombuffer(raw[nl+1:], dtype='<f8'); N = len(a)//reclen; a = a[:N*reclen].reshape(N, reclen)[A.skip:]; N = len(a)
P0 = a[:, :Lt]; tl0 = a[:, -2]; tsub = a[:, -1]
slab = np.array([t//d if t % d else -1-t for t in range(Lt)])
same = (slab[:, None] == slab[None, :]) & (slab[:, None] >= 0)
def Qof(C, S1, interior=False):  # -> (A, B, Q) each [N, nq+1]: pair-set means of first/second member and of C(t,t+n)
    Q, Am, Bm = [], [], []
    for n in range(nq+1):
        ts = [t for t in range(Lt) if not interior or (slab[t] >= 0 and slab[(t+n) % Lt] >= 0)]
        Q.append(np.mean([C[:, t, (t+n) % Lt] for t in ts], 0)); Am.append(S1[:, ts].mean(1)); Bm.append(S1[:, [(t+n) % Lt for t in ts]].mean(1))
    return np.stack(Am, 1), np.stack(Bm, 1), np.stack(Q, 1)
est = {}
est['level-0 direct (same chain)'] = (*Qof(P0[:, :, None]*P0[:, None, :], P0), None)
for i, n in enumerate(ns):
    o = Lt + i*(Lt + Lt*Lt); S1 = a[:, o:o+Lt]; S2 = a[:, o+Lt:o+Lt+Lt*Lt].reshape(N, Lt, Lt)
    C = np.where(same[None], S2, S1[:, :, None]*S1[:, None, :]); est[f'ML nsub={n}'] = (*Qof(C, S1), n)
    est[f'ML nsub={n}, interior pairs only'] = (*Qof(C, S1, True), n)
B = A.bin
def binned(x): nb = len(x)//B; return x[:nb*B].reshape(nb, B, *x.shape[1:]).mean(1)
def boxR(r, M):
    e = np.concatenate([r, r[1:nq][::-1], r[:1]]); return np.array([sum(e[n+a_+b_] for a_ in range(M+1) for b_ in range(M+1))/(M+1)**2 if n+2*M <= Lt else np.nan for n in range(nq+1)])
def analyze(Am, Bm, Q):
    Ab, Bb, Qb = binned(Am), binned(Bm), binned(Q); nb = len(Qb)
    def f(mask):
        r = Qb[mask].mean(0) - Ab[mask].mean(0)*Bb[mask].mean(0); out = list(r)
        for s in (2, 3, 4): R = boxR(r, s); out += [R[s+1]/R[s//2], R[s//2], R[s+1]]
        return np.array(out)
    full = f(np.ones(nb, bool)); js = np.array([f(np.arange(nb) != i) for i in range(nb)])
    return full, np.sqrt((nb-1)/nb*((js-js.mean(0))**2).sum(0)), nb
res = {k: analyze(Am, Bm, Q) for k, (Am, Bm, Q, n) in est.items()}
# cost (seconds per config): level-0 sweeps + sub-updates (prorated to nsub); full-sweep time ts = tl0/interval; per-sub-update cost incl. measurement
interval = h['interval']; ts = np.median(tl0)/interval; tsu = np.median(tsub)/max(ns); f_sub = 1 - 3/(4*d); tmeas = max(tsu - f_sub*ts, 0.0)
cost = {k: (np.median(tl0) + (n or 0)*tsu) for k, (Am, Bm, Q, n) in est.items()}
L = [f"# P9 multilevel pilot — {time.strftime('%Y-%m-%d %H:%M %Z')}\n", f"run `{A.rundir}`: {h['Ls']}^3x{Lt}, beta {h['beta']}, slab thickness d={d} (frozen spatial links on t % {d} == 0), nsub checkpoints {ns}, interval {interval}, N={N} configs (skip {A.skip}), bins of {B}.",
     f"Timing (2 threads): full sweep {ts:.3f} s, sub-update+plaquette measurement {tsu:.3f} s (sub-sweep fraction {f_sub:.2f} of links; measurement ≈ {tmeas:.3f} s).\n"]
# direct reference from an independent pure direct chain (e.g. p8_hi): per-meas cost = interval sweeps + one measurement
if A.direct:
    hd, pl, Es, O = load(A.direct); Pd = O[200:, 0, hd['sides'].index(1)].mean(1); Md = np.repeat(Pd.mean(1)[:, None], nq+1, 1); Qd = np.stack([(Pd*np.roll(Pd, -n, axis=1)).mean(1) for n in range(nq+1)], 1)
    Bd = 20; Bsave = B; B = Bd; res['direct chain (' + os.path.basename(os.path.dirname(A.direct)) + f', bin {Bd})'] = analyze(Md, Md, Qd); B = Bsave
    cost['direct chain (' + os.path.basename(os.path.dirname(A.direct)) + f', bin {Bd})'] = hd['interval']*ts + tmeas
    dkey = [k for k in res if k.startswith('direct chain')][0]
lags = [0, 1, 2, 3, 4, 5, 6, 8, 10, 13]
L.append("## R(n) (E1) and its error; per-config cost; variance x cost (lower is better)\n")
L.append("| estimator | bins | cost/config (s) | " + " | ".join(f"R({n}) ×1e6" for n in lags) + " |"); L.append("|---|---|---|" + "---|"*len(lags))
for k, (v, e, nb) in res.items():
    L.append(f"| {k} | {nb} | {cost[k]:.3f} | " + " | ".join(f"{v[n]*1e6:.3f}({e[n]*1e6:.3f})" for n in lags) + " |")
if A.direct:
    L.append(f"\n## Variance-reduction factor at EQUAL COST vs the direct chain: VRF(n) = σ²_dir·T_dir / (σ²_ML·T_ML), T = N·cost/config (>1 = multilevel better)\n")
    vd, ed, nbd = res[dkey]; Td = nbd*Bd*cost[dkey]
    L.append("| estimator | " + " | ".join(f"n={n}" for n in lags) + " | W s=2 | W s=3 | W s=4 |"); L.append("|---|" + "---|"*(len(lags)+3))
    for k, (v, e, nb) in res.items():
        if k == dkey or not k.startswith('ML'): continue
        T = nb*B*cost[k]; vr = (ed**2*Td)/(e**2*T)
        L.append(f"| {k} | " + " | ".join(f"{vr[n]:.2f}" for n in lags) + " | " + " | ".join(f"{vr[nq+1+3*i]:.2f}" for i in range(3)) + " |")
    L.append("\n## W on Y_j (box M=side) and projected cost for ±0.02\n")
    L.append("| estimator | W s=2 | W s=3 | W s=4 | hours for ±0.02 at s=2 | s=3 | s=4 |"); L.append("|---|---|---|---|---|---|---|")
    for k, (v, e, nb) in res.items():
        T = nb*(Bd if k == dkey else B)*cost[k]; hrs = [T*(e[nq+1+3*i]/0.02)**2/3600 for i in range(3)]
        L.append(f"| {k} | " + " | ".join(f"{v[nq+1+3*i]:.3f}({e[nq+1+3*i]:.3f})" for i in range(3)) + " | " + " | ".join(f"{x:.0f}" for x in hrs) + " |")
out = '\n'.join(L) + '\n'; print(out)
if A.out: open(A.out, 'w').write(out)
