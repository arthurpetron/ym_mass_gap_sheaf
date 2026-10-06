import numpy as np, sys, json
sys.path.insert(0, 'ana'); from load import load; from summary import sqrt_t0
from p6_window import perconf, binned
RUNS = [('p5_b2.50_L24x32_s2', 2.50, 6), ('p5_b2.60_L24x32_s3', 2.60, 7), ('p5_b2.70_L24x32_s4', 2.70, 11), ('p5_b2.85_L24x32_s6', 2.85, 12), ('b2.95_L32x48_s8', 2.95, 10)]
def f(v, e):
    if not np.isfinite(v) or not np.isfinite(e) or e > 2: return '–'
    ed = min(4, max(1, int(np.ceil(-np.log10(e)))+1)); return f"{v:.{ed}f}({int(round(e*10**ed))})"
out = ["\n# Raw (unsmoothed, rho=0) loops at every stored side vs smoothed main side, same configs\n",
       "m_eff(n)=ln C(n)/C(n+1) (E1), shown while C(n+1) > 2 sigma. Reference a*m0++ = 3.78*0.26/(sqrt(t0)/a) (lit. m0++/sqrt(sigma)=3.78, sqrt(sigma t0)~0.26).\n"]
def run(name, paths, b, B):
    sts = [load(p) for p in paths]; h = sts[0][0]; Lt = h['Lt']; sides = h['sides']; tfl = h['tflow']; sm = sides[len(sides)//2]
    ref = 3.78*0.26/sqrt_t0(b); out.append(f"\n## beta {b:.2f} (main s={sm}, a m0++ ref ~ {ref:.3f})\n\n| operator | drown lag | m_eff n=0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |\n|---|---|---|---|---|---|---|---|---|---|---|")
    combos = [(0, sd) for sd in sides] + [(k, sm) for k in range(1, len(tfl))]
    for k, sd in combos:
        Mb, Qb = [], []
        for st in sts:
            M, Q = perconf(st[3].mean(3)[:, k, sides.index(sd)]); Mb.append(binned(M, B)); Qb.append(binned(Q, B))
        Mb = np.concatenate(Mb); Qb = np.concatenate(Qb); nb = len(Mb)
        C = lambda m: Qb[m].mean(0) - Mb[m].mean()**2; full = np.ones(nb, bool)
        c0 = C(full); cj = np.array([C(np.arange(nb) != i) for i in range(nb)]); ce = np.sqrt((nb-1)/nb*((cj-cj.mean(0))**2).sum(0))
        with np.errstate(all='ignore'):
            me = lambda c: np.log(c[:9]/c[1:10]); m0 = me(c0); mj = np.array([me(c) for c in cj]); mer = np.sqrt((nb-1)/nb*((mj-mj.mean(0))**2).sum(0))
        dr = next((n for n in range(len(c0)) if c0[n] < 2*ce[n]), None)
        lab = f"raw {sd}x{sd}" if k == 0 else f"smoothed {sd}x{sd} rho={np.sqrt(6*tfl[k])/sm:.2f}"
        out.append(f"| {lab} | {dr} | " + " | ".join(f(m0[n], mer[n]) if (dr is None or n+1 < dr) else '–' for n in range(9)) + " |")
for r, b, B in RUNS: run(r, [f'runs/{r}/data.bin'], b, B)
run('b3.00_AB', ['runs/b3.00_L32x48_s10_A/data.bin', 'runs/b3.00_L32x48_s10_B/data.bin'], 3.00, 12)
# P4 production runs (independent configs, small flow)
for r, b, B in [('b2.50_L24x32_s2', 2.50, 6), ('b2.60_L24x32_s3', 2.60, 6), ('b2.70_L24x32_s4', 2.70, 6), ('b2.85_L24x32_s6', 2.85, 8)]:
    out.append(f"\n(P4 run {r}, independent configs)"); run(r, [f'runs/{r}/data.bin'], b, B)
open('runs/P6_RAW_VS_SMOOTH.md', 'a').write('\n'.join(out)+'\n')
