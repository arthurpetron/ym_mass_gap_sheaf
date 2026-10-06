"""P7 interim/final for b2.95 Ls=Lt=48 side 8. usage: p7_interim.py <rundir> <out.md>"""
import sys, os, json, numpy as np, time
sys.path.insert(0, os.path.dirname(__file__)); from load import load, load_poly
rundir, outp = sys.argv[1], sys.argv[2]; path = f'{rundir}/data.bin'
h, plaq, Es, O = load(path); P = load_poly(path); N = len(plaq); sides = h['sides']; sm = sides[len(sides)//2]; j = sides.index(sm)
tfl = h['tflow']; rhos = [np.sqrt(6*t)/sm for t in tfl]; k1 = int(np.argmin([abs(r-1) for r in rhos]))
Obar = O[:, :, j].mean(axis=(2, 3))  # [N, nlev] operator mean per meas
L = [f"# P7 {'interim' if 'INTERIM' in outp else 'final (auto)'}: beta 2.95, 48^3x48, side 8 — {time.strftime('%Y-%m-%d %H:%M %Z')}\n",
     f"Records: {N}/{h.get('meas', '?') if 'meas' in h else 240} (interval {h['interval']} sweeps, therm {h['therm']}). Reference: Ls=32 run b2.95_L32x48_s8 (240 meas, P6 numbers).\n"]
# --- flatness / discard
def berr(x, b):
    nb = len(x)//b; xb = x[:nb*b].reshape(nb, b).mean(1); return xb.std(ddof=1)/np.sqrt(nb) if nb > 1 else np.inf
x = Obar[:, k1]; bs = 10
L.append(f"## Thermalization: smoothed operator mean <O> (side {sm}, rho={rhos[k1]:.2f}) in blocks of {bs} meas\n")
L.append(' '.join(f"{x[i:i+bs].mean():.5f}" for i in range(0, N - N % bs, bs)) + "\n")
skip = None
for sk in range(0, N//2 + 1, 10):
    y = x[sk:]; n = len(y)
    if n < 40: break
    a, b = y[:n//2], y[n//2:]; e = np.hypot(berr(a, 5), berr(b, 5))
    slope = np.polyfit(np.arange(n), y, 1)[0]*n; es = 2*np.sqrt(3)*berr(y, 5)  # total linear drift over window vs its error
    if abs(a.mean()-b.mean()) < 1.5*e and abs(slope) < 2*es: skip = sk; break
if skip is None: skip = N//2; L.append(f"**Not flat** by the criterion (half-vs-half < 1.5 sigma and linear drift < 2 sigma) for any discard <= N/2; using discard N/2 = {skip} provisionally.\n")
else: L.append(f"Discard chosen: first **{skip}** measurements (smallest multiple of 10 with half-vs-half difference < 1.5 sigma and total linear drift < 2 sigma over the kept window).\n")
os.environ['P6_SKIP'] = str(skip)
from p6_window import analyze
r = analyze('p7', [path]); ref = json.load(open(os.path.join(os.path.dirname(__file__), '..', 'runs', 'p6', 'b2.95_s8.json')))
def fm(v, e):
    if not np.isfinite(v): return 'n/a'
    d = min(4, max(1, int(np.ceil(-np.log10(max(e, 1e-9))))+1)); return f"{v:.{d}f}({int(round(e*10**d))})"
L.append(f"\n## W = R(s+1)/R(s//2), eps*s (bin {r['binsize']}, N kept {r['N'][0]}); Ls=32 values in brackets\n")
L.append("| rho | W E1 | W E3f | W E3d | eps*s E1 | eps_shift*s | R(s)/R(0) |\n|---|---|---|---|---|---|---|")
for key, lv in r['levels'].items():
    e = lv['est']; rf = ref['levels'].get(key, {}).get('est')
    g = lambda est, k, i: fm(est[k][0][i], est[k][1][i]) if est else '–'
    L.append(f"| {key} | {g(e,'E1_stream',0)} [{g(rf,'E1_stream',0)}] | {g(e,'E3_farlag',0)} [{g(rf,'E3_farlag',0)}] | {g(e,'E3_diff',0)} [{g(rf,'E3_diff',0)}] | {g(e,'E1_stream',2)} [{g(rf,'E1_stream',2)}] | {g(e,'E1_stream',5)} [{g(rf,'E1_stream',5)}] | {g(e,'E1_stream',3)} [{g(rf,'E1_stream',3)}] |")
L.append("\n## Binning tau_int of the operator mean (kept window) vs Ls=32\n\n| rho | tau(b) Ls=48 | tau(b) Ls=32 |\n|---|---|---|")
for key in r['tau']:
    L.append(f"| {key} | {', '.join(f'b{b}:{v:.2f}' for b, v in r['tau'][key].items())} | {', '.join(f'b{b}:{v:.2f}' for b, v in ref['tau'].get(key, {}).items())} |")
L.append("\n## m_eff(n) (E1) at rho=1.00, Ls=48 [Ls=32]\n")
a1 = r['levels'].get('1.00'); b1 = ref['levels'].get('1.00')
if a1: L.append(' | '.join(f"n={n}: {fm(a1['meff'][n], a1['meffe'][n])} [{fm(b1['meff'][n], b1['meffe'][n]) if b1 else ''}]" for n in range(min(10, len(a1['meff'])))) + "\n")
# --- Polyakov
L.append("## Smeared spatial Polyakov loops (spatially flowed links), line means per measurement\n")
for kk in [k1, len(tfl)-1]:
    pp = P[:, kk, :3]; L.append(f"rho={rhos[kk]:.2f}: mean |P_d| over meas = {np.abs(pp).mean(0).round(4).tolist()}, mean P_d = {pp.mean(0).round(4).tolist()}, max |P| = {np.abs(pp).max():.4f}, sign changes per direction = {[(np.diff(np.sign(pp[:, d])) != 0).sum() for d in range(3)]}, <P^2> line avg = {P[:, kk, 3:].mean(0).round(5).tolist()}")
    L.append("  blocks of 10, max_d |P_d|: " + ' '.join(f"{np.abs(pp[i:i+10]).max():.3f}" for i in range(0, N - N % 10, 10)))
    c = np.corrcoef(x, np.abs(pp).max(1))[0, 1] if N > 3 else np.nan; L.append(f"  corr(<O>(rho~1), max_d|P_d|) = {c:.2f}\n")
# --- resources
rl = f'{rundir}/resources.log'
if os.path.exists(rl):
    rows = [l.split() for l in open(rl) if l[0] != '#' and len(l.split()) >= 11]; ev = [l.strip() for l in open(rl) if 'THROTTLE' in l or 'RESTORE' in l or 'EMERGENCY' in l]
    if rows:
        av = np.array([float(r_[2]) for r_ in rows]); l1 = np.array([float(r_[5]) for r_ in rows]); rss = np.array([float(r_[9]) for r_ in rows]); th = [r_[10] for r_ in rows]
        L.append(f"## Resources ({len(rows)} samples, 30 s)\nMemAvailable MB min/mean/max {av.min():.0f}/{av.mean():.0f}/{av.max():.0f}; load1 {l1.min():.2f}/{l1.mean():.2f}/{l1.max():.2f}; job RSS MB max {rss.max():.0f}; threads now {th[-1]}; throttle events: {len(ev)}" + (' — ' + '; '.join(ev[-5:]) if ev else ''))
log = open(f'{rundir}/run.log').read().strip().splitlines(); spm = [l for l in log if l.startswith('meas')]
if spm: L.append(f"\nLast log line: `{spm[-1][:160]}`")
open(outp, 'w').write('\n'.join(L) + '\n'); print('wrote', outp)
