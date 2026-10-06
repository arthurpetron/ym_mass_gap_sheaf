"""P9 items 3+4: step-ratio c(k) = side*(1-R(k+1)/R(k)) and Hankel/Hausdorff positivity on measured R(n), for
 (a) flow/NS smoothed loop psi (M=0), (b) the exact Lean smoothed state of 9d58a5df: Y = one-sided time box M=side of the
 centered expression psi (R_Y(n) = (M+1)^-2 sum_{a,b<=M} R_psi(n+a+b)), with psi = flow loop, and (c) the padded anchor Y_j
 (psi = zero-momentum plaquette sum) where side-1 data exist. E1 = per-stream vacuum subtraction; E3d = differenced.
usage: p9_full.py <out_stepratio.md> <out_positivity.md>"""
import sys, os, json, numpy as np, time
sys.path.insert(0, os.path.dirname(__file__)); from load import load
R_ = 'runs/'
# (label, beta, streams, main side, bin, skip, extra)
RUNS = [('P5 b2.50 24^3x32', 2.50, ['p5_b2.50_L24x32_s2'], 2, 6, 60),
        ('P4 b2.50 24^3x32', 2.50, ['b2.50_L24x32_s2'], 2, 6, 100),
        ('p8_hi b2.50 16^3x32', 2.50, ['p8_hi_b2.50_L16x32'], 2, 20, 0),
        ('P5 b2.60 24^3x32', 2.60, ['p5_b2.60_L24x32_s3'], 3, 7, 50),
        ('P5 b2.70 24^3x32', 2.70, ['p5_b2.70_L24x32_s4'], 4, 11, 50),
        ('P5 b2.85 24^3x32', 2.85, ['p5_b2.85_L24x32_s6'], 6, 12, 60),
        ('P6 b2.95 32^3x48', 2.95, ['b2.95_L32x48_s8'], 8, 10, 0),
        ('P7 b2.95 48^3x48', 2.95, ['b2.95_L48x48_s8'], 8, 10, 0),
        ('P6 b3.00 32^3x48 A+B', 3.00, ['b3.00_L32x48_s10_A', 'b3.00_L32x48_s10_B'], 10, 12, 0),
        ('P6 b3.00 32^3x48 A+B skip85', 3.00, ['b3.00_L32x48_s10_A', 'b3.00_L32x48_s10_B'], 10, 12, 85)]
if len(sys.argv) > 3: RUNS = [r for r in RUNS if any(x in r[0] for x in sys.argv[3].split(','))]
def perconf(X, nq): return X.mean(1), np.stack([(X*np.roll(X, -n, axis=1)).mean(1) for n in range(nq+1)], 1)
def binned(x, b): nb = len(x)//b; return x[:nb*b].reshape(nb, b, *x.shape[1:]).mean(1)
def boxR(r, M, Lt):
    nq = Lt//2; e = np.concatenate([r, r[1:nq][::-1], r[:1]])
    return np.array([sum(e[n+a+b] for a in range(M+1) for b in range(M+1))/(M+1)**2 if n+2*M <= Lt else np.nan for n in range(nq+1)])
def fm(v, e):
    if not (np.isfinite(v) and np.isfinite(e)): return 'n/a'
    d = min(4, max(1, int(np.ceil(-np.log10(max(abs(e), 1e-9))))+1)); return f"{v:.{d}f}({int(round(e*10**d))})"
def jk(fun, nb):
    full = fun(np.ones(nb, bool)); js = np.array([fun(np.arange(nb) != i) for i in range(nb)])
    return full, np.sqrt((nb-1)/nb*((js - js.mean(0))**2).sum(0)), js
SR, PO = [], []
def lagset(s): return sorted(set([0, 1, 2, max(0, s//4), s//2]))
for lab, beta, streams, s, B, skip in RUNS:
    data = [load(R_ + st + '/data.bin') for st in streams]; h = data[0][0]; Lt = h['Lt']; nq = Lt//2; sides = h['sides']; tfl = h['tflow']
    lv = h.get('linear_variants', [])
    ops = []  # (name, side, per-stream timeslice arrays, box M)
    for k, t in enumerate(tfl):
        for ss in sides:
            if ss == 1: continue
            rho = np.sqrt(6*t)/ss
            if any(abs(rho - r0) < 0.03 for r0 in (0.5, 1.0, 1.5)) and (abs(rho-1) < 0.03 or ss == s):
                X = [d[3][skip:, k, sides.index(ss)].mean(1) for d in data]
                ops.append((f"flow rho={rho:.2f} loop", ss, X, 0)); ops.append((f"flow rho={rho:.2f} loop + box M=side", ss, X, ss))
    if 1 in sides:
        X = [d[3][skip:, 0, sides.index(1)].mean(1) for d in data]
        for ss in sorted(set(sides) - {1}) or [s]:
            if 3*ss+1 <= nq: ops.append(("Y_j (plaquette + box M=side)", ss, X, ss))
    ops = [o for o in ops if 3*o[1]*(o[3] > 0) + 1 <= nq + 1]
    for name, ss, X, M in ops:
        Mb, Qb, sid = [], [], []
        for si, x in enumerate(X):
            m, q = perconf(x, nq); Mb.append(binned(m, B)); Qb.append(binned(q, B)); sid += [si]*len(Mb[-1])
        Mb = np.concatenate(Mb); Qb = np.concatenate(Qb); sid = np.array(sid); nb = len(Mb)
        def corr(mask, mode='E1'):
            if mode == 'E3d': q = Qb[mask].mean(0); return boxR(np.append(q[:-1] - q[1:], np.nan), M, Lt)
            cs, ws = [], []
            for si in range(len(X)):
                mm = mask & (sid == si)
                if mm.sum(): cs.append(Qb[mm].mean(0) - Mb[mm].mean()**2); ws.append(mm.sum())
            return boxR(np.average(cs, axis=0, weights=ws), M, Lt)
        ks = lagset(ss); h2 = ss//2; kq = max(0, ss//4)
        def sr(mask):
            r = corr(mask); d = corr(mask, 'E3d')
            c = [ss*(1 - r[k+1]/r[k]) for k in range(h2+1)]
            th = [(r[k+1]/r[k])**(h2+1) for k in ks]
            return np.array(c + th + [r[ss+1]/r[h2] if ss+1 <= nq else np.nan, ss*(1 - d[h2+1]/d[h2]), ss*np.log(r[kq]/r[h2])/(h2-kq) if h2 > kq else np.nan])
        f0, e0, js = jk(sr, nb); nc = h2+1
        # monotonicity of c(k) in k: largest positive jump c(k+1)-c(k) in sigma (jackknifed difference)
        dif = js[:, 1:nc] - js[:, :nc-1]; dfull = f0[1:nc] - f0[:nc-1]; de = np.sqrt((nb-1)/nb*((dif - dif.mean(0))**2).sum(0)) if nc > 1 else np.array([])
        z = (dfull/de) if nc > 1 else np.array([0.0]); worst = float(np.nanmax(z)) if len(z) else 0.0
        cells = [fm(f0[k], e0[k]) for k in ks]; thc = [fm(f0[nc+i], e0[nc+i]) for i in range(len(ks))]
        W = fm(f0[nc+len(ks)], e0[nc+len(ks)]); cd = fm(f0[nc+len(ks)+1], e0[nc+len(ks)+1]); cv = fm(f0[nc+len(ks)+2], e0[nc+len(ks)+2])
        SR.append((beta, lab, name, ss, M, ks, cells, thc, W, cd, cv, worst, nb))
        # ---- positivity
        def pos(mask):
            r = corr(mask); r = r/r[0]; out = []
            for l in (0, 1):
                rl = r.copy()
                for _ in range(l): rl = rl[:-1] - rl[1:]
                for N in (2, 3, 4):
                    for m in (0, 1):
                        if 2*(N-1)+m < len(rl) and np.all(np.isfinite(rl[:2*(N-1)+m+1])):
                            Hm = np.array([[rl[i+k+m] for k in range(N)] for i in range(N)]); out.append(np.linalg.eigvalsh(Hm)[0])
                        else: out.append(np.nan)
            # Hausdorff (-1)^l Delta^l R(n) >= 0, l = 0..4, n = 0..(min(nq, 3*ss+... ) ) ; keep n <= ss+1 (window range)
            for l in range(5):
                rl = r.copy()
                for _ in range(l): rl = rl[:-1] - rl[1:]
                out += [rl[n] if n < len(rl) else np.nan for n in range(ss+2)]
            return np.array(out)
        p0, pe, _ = jk(pos, nb); PO.append((beta, lab, name, ss, M, p0, pe))
    print('done', lab, flush=True)
# ---- write step ratio
L = [f"# P9: step-ratio constant c(k) = side·(1 − R(k+1)/R(k)), implied θ_k, monotonicity and convexity checks — {time.strftime('%Y-%m-%d %H:%M %Z')}\n",
     "Lean consumer: `ExprStepRatio tr ρ k` (BF4WilsonAllNomeExprStepRatioWindowSurvival.lean:232), used by `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC` (9d58a5df).",
     "It is stated on R_j(n) = B(Y_j, T^n Y_j) of the expression anchor's SMOOTHED state Y_j = exprSmoothedVector(ψ_j, M_j): the one-sided time box M_j of the centered expression ψ_j. For the padded anchor, M_j = side_j.",
     "So the 'exact Lean smoothed state' rows are '... + box M=side': R_Y(n) = (M+1)^-2 Σ_{a,b≤M} R_ψ(n+a+b), with ψ = flow-smoothed loop (an expression anchor; flow ≈ NS-k2, P7b) or ψ = the plaquette sum (the padded Y_j). The bare-loop rows (M=0) are the P9 template operator.",
     "E1 = per-stream vacuum subtraction; jackknife over bins (bin size per run in the table). θ_k = (R(k+1)/R(k))^(side/2+1), to compare with W = R(side+1)/R(side/2) (Lean: θ_k R(s/2) ≤ R(s+1) holds automatically once the ratio is monotone).",
     "mono = largest INCREASE c(k+1) − c(k) over k < side/2, in σ (a positive value > 2 flags a log-convexity violation). c_D(s/2) = the same from the differenced (subtraction-free) correlator. Convexity bound (log-convexity: r(k)=R(k+1)/R(k) nondecreasing ⇒ r(s/2)^(s/2−s/4) ≥ R(s/2)/R(s/4) ⇒ c(s/2) ≤ side·ln(R(s/4)/R(s/2))/(s/2−s/4), = 4 ln(R(s/4)/R(s/2)) for side ≡ 0 mod 4; the requested '4·R(s/4)/R(s/2)' is read as this log form, which it dominates).",
     "**Caveat:** MC numerics on smoothed and time-boxed operators. Not proof. Y_j rows are noise-limited (P8).\n"]
for beta, lab, name, ss, M, ks, cells, thc, W, cd, cv, worst, nb in SR:
    pass
hdr = "| beta | run | operator | side | bins | " + " | ".join(f"c(k={x})" for x in ['0', '1', '2', 's/4', 's/2']) + " | θ at k=s/2 | W measured | c_D(s/2) | conv. bound s·ln(R(s/4)/R(s/2))/(s/2−s/4) | mono (σ) |"
L += [hdr, "|" + "---|"*15]
for beta, lab, name, ss, M, ks, cells, thc, W, cd, cv, worst, nb in SR:
    h2 = ss//2; kq = max(0, ss//4); want = [0, 1, 2, kq, h2]
    cc = [cells[ks.index(k)] if (k in ks and k <= h2) else '' for k in want]
    L.append(f"| {beta:.2f} | {lab} | {name} | {ss} | {nb} | " + " | ".join(cc) + f" | {thc[ks.index(h2)]} | {W} | {cd} | {cv} | {worst:+.1f}{' **VIOLATION**' if worst > 2 else ''} |")
open(sys.argv[1], 'w').write('\n'.join(L) + '\n')
# ---- write positivity
P = [f"# P9: Hankel / Hausdorff positivity of measured R(n) (forms proven in d2710c09, BF4WilsonAllNomeResponseHankelPositivity) — {time.strftime('%Y-%m-%d %H:%M %Z')}\n",
     "R normalized to R(0)=1 (E1). Hankel: smallest eigenvalue λ_min of [R(i+k+m)]_{i,k<N} (l=0) and of [ΔR(i+k+m)] with ΔR(n)=R(n)−R(n+1) (l=1, Hausdorff-Hankel), N=2,3,4, m=0,1.",
     "Each entry is λ_min(err), with z=λ_min/σ in brackets; a violation means z < −2. Complete monotonicity: (−1)^l Δ^l R(n) ≥ 0 for l ≤ 4, n = 0..side+1. 'CM worst' is the most negative z over all l, n (and where); 'CM viol' counts entries with z < −2.\n"]
P.append("| beta | run | operator | side | " + " | ".join(f"H l={l} N={N} m={m}" for l in (0, 1) for N in (2, 3, 4) for m in (0, 1)) + " | Hankel worst z | Hankel viol (z<−2) / tested | CM worst z (l,n) | CM viol (z<−2) / tested |")
P.append("|" + "---|"*20)
for beta, lab, name, ss, M, p0, pe in PO:
    hk = [f"{p0[i]:.1e}({pe[i]:.0e}) [{p0[i]/pe[i]:+.1f}]" if np.isfinite(p0[i]) and pe[i] > 0 else 'n/a' for i in range(12)]
    cm = p0[12:]; ce = pe[12:]; zz = cm/np.where(ce > 0, ce, np.nan); n_ = ss+2
    valid = np.isfinite(zz); iw = int(np.nanargmin(np.where(valid, zz, np.inf))) if valid.any() else 0
    hz = np.array([p0[i]/pe[i] if np.isfinite(p0[i]) and pe[i] > 0 else np.nan for i in range(12)]); hv = np.isfinite(hz)
    P.append(f"| {beta:.2f} | {lab} | {name} | {ss} | " + " | ".join(hk) + f" | {np.nanmin(hz):+.1f} | {int((hz < -2).sum())}/{int(hv.sum())} | {zz[iw]:+.1f} (l={iw//n_},n={iw%n_}) | {int((zz < -2).sum())}/{int(valid.sum())} |")
open(sys.argv[2], 'w').write('\n'.join(P) + '\n'); print('wrote')
