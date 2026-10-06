"""P9 item 2: binning / tau_int checks for W on the exact anchor Y_j (p8_hi run), and the measurement count for +-0.02.
usage: p9_p8hi_bins.py <data.bin> <out.md> [skip]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); from load import load
path, outp = sys.argv[1], sys.argv[2]; h, pl, Es, O = load(path); skip = int(sys.argv[3]) if len(sys.argv) > 3 else len(pl)//10
Lt = h['Lt']; nq = Lt//2; sides = h['sides']; P = O[skip:, 0, sides.index(1)].mean(1); N = len(P)
M = P.mean(1); Q = np.stack([(P*np.roll(P, -n, axis=1)).mean(1) for n in range(nq+1)], 1)
def boxR(r, Mx):
    e = np.concatenate([r, r[1:nq][::-1], r[:1]]); return np.array([sum(e[n+a+b] for a in range(Mx+1) for b in range(Mx+1))/(Mx+1)**2 if n+2*Mx <= Lt else np.nan for n in range(nq+1)])
def Ws(q, m, mode='E1'):
    if mode == 'E1': r = q - m*m
    else: r = np.append(q[:-1] - q[1:], 0.0)
    out = []
    for s in (2, 3, 4):
        R = boxR(r, s); out.append(R[s+1]/R[s//2])
    R0 = r; out += [R0[1]/R0[0], R0[2]/R0[0]]
    return np.array(out)
def jk(b, mode='E1'):
    nb = N//b; Mb = M[:nb*b].reshape(nb, b).mean(1); Qb = Q[:nb*b].reshape(nb, b, -1).mean(1)
    full = Ws(Qb.mean(0), Mb.mean(), mode); js = np.array([Ws(np.delete(Qb, i, 0).mean(0), np.delete(Mb, i).mean(), mode) for i in range(nb)])
    return full, np.sqrt((nb-1)/nb*((js-js.mean(0))**2).sum(0)), nb
def tau(x, b):
    nb = len(x)//b; return 0.5*b*x[:nb*b].reshape(nb, b).mean(1).var(ddof=1)/x.var(ddof=1)
L = [f"# P9 item 2: binning and tau_int for the exact-anchor W (p8_hi, {N} meas after skip {skip})\n",
     "Jackknife error of W(Y_j, box M=side) and of R_x(1)/R_x(0), R_x(2)/R_x(0) (unboxed plaquette sum) vs bin size b. tau(b) = b·Var(bin means)/(2 Var) for the per-meas plaquette-sum mean <P> and for Q(n) at n = 2, 5.\n",
     "| b | bins | σ W s=2 (E1) | σ W s=3 | σ W s=4 | σ R(1)/R(0) | σ R(2)/R(0) | σ W s=2 (E3d) | tau <P> | tau Q(2) | tau Q(5) |", "|---|---|---|---|---|---|---|---|---|---|---|"]
errs = {}
for b in (1, 2, 5, 10, 20, 40, 80, 160):
    if N//b < 20: break
    f, e, nb = jk(b); fd, ed, _ = jk(b, 'E3d'); errs[b] = (f, e, nb)
    L.append(f"| {b} | {nb} | {e[0]:.4f} | {e[1]:.4f} | {e[2]:.4f} | {e[3]:.5f} | {e[4]:.5f} | {ed[0]:.4f} | {tau(M, b):.2f} | {tau(Q[:, 2], b):.2f} | {tau(Q[:, 5], b):.2f} |")
bs = sorted(errs); bp = 20  # tau(<P>) plateaus at ~0.7 from b=10; b=20 keeps 270 bins
f, e, nb = errs[bp]
L.append(f"\nPlateau choice b = {bp} ({nb} bins). W(Y_j) E1: s=2 {f[0]:.3f}({e[0]:.3f}), s=3 {f[1]:.3f}({e[1]:.3f}), s=4 {f[2]:.3f}({e[2]:.3f}).")
L.append("\n## Measurements needed for σ(W) = 0.02 (σ ∝ N^-1/2 at fixed bin size; interval 2 sweeps, same cost per meas)\n")
L.append("| side | σ(W) now | N now | N for ±0.02 | factor | wall time at 1.4 s/meas (2 threads) |"); L.append("|---|---|---|---|---|---|")
for i, s in enumerate((2, 3, 4)):
    Nn = N*(e[i]/0.02)**2; L.append(f"| {s} | {e[i]:.3f} | {N} | {Nn:.2e} | {Nn/N:.0f}x | {Nn*1.4/3600:.0f} h ({Nn*1.4/86400:.1f} d) |")
open(outp, 'w').write('\n'.join(L)+'\n'); print('\n'.join(L))
