"""P7b: polynomial-normalized (Newton-Schulz) linear smearing vs flow vs plain linear, same configs. usage: p7b_ns.py <data.bin> <out.md>"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); from load import load, load_linnorm
from p6_window import perconf, binned
path, outp = sys.argv[1], sys.argv[2]
h, plaq, Es, O = load(path); NS = load_linnorm(path); N = len(plaq); sides = h['sides']; s = 2; j = sides.index(s); h2 = s//2; Lt = h['Lt']; nq = Lt//2
labs = [f"flow rho={np.sqrt(6*t)/s:.2f}" for t in h['tflow']]
for v in h['linear_variants']:
    for n in v['steps']: labs.append(f"linear a={v['alpha']} n={n} NS k={v['k']} rescale={v['rescale']}")
nflow = len(h['tflow']); skip = N//10; B = 8
kf = int(np.argmin([abs(np.sqrt(6*t)/s-1) for t in h['tflow']])); Of = O[skip:, kf, j].mean(axis=(1, 2))
def jk(fn, Mb, Qb):
    nb = len(Mb); f0 = fn(Mb.mean(), Qb.mean(0)); js = np.array([fn(np.delete(Mb, i).mean(), np.delete(Qb, i, 0).mean(0)) for i in range(nb)])
    return f0, np.sqrt((nb-1)/nb*((js-js.mean(0))**2).sum(0))
def der(m, q):
    c = q - m*m; far = q - q[nq]; d = q[:-1] - q[1:]
    with np.errstate(all='ignore'): return np.array([c[s+1]/c[h2], far[s+1]/far[h2], d[s+1]/d[h2], (1-c[1]/c[0])*s, c[s]/c[0], np.log(c[0]/c[1]), np.log(c[1]/c[2])])
def fm(v, e):
    if not (np.isfinite(v) and np.isfinite(e)): return "n/a"
    d = min(5, max(1, int(np.ceil(-np.log10(max(e, 1e-12))))+1)); return f"{v:.{d}f}({int(round(e*10**d))})"
L = [f"# P7b: Newton-Schulz-normalized linear smearing vs flow and plain linear (same configs)\n",
     f"beta {h['beta']}, {h['Ls']}^3x{Lt}, side {s}, seed {h['seed']}, N={N} meas (interval {h['interval']}), first {skip} discarded, bins of {B}. W = R(3)/R(1) (E1 global subtraction; E3f far-lag; E3d differenced). |V| stats are spatial links after the final step, averaged over meas (min/max are extremes over all meas).\n",
     "| operator | W E1 | W E3f | W E3d | eps*s | R(2)/R(0) | m_eff(0) | m_eff(1) | |V| mean | |V| std | |V| min | |V| max | corr(O, O_flow rho=1) |", "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
for k, lab in enumerate(labs):
    M, Q = perconf(O[skip:, k, j].mean(1)); sc = abs(M.mean()); M, Q = M/sc, Q/sc**2
    f0, e = jk(der, binned(M, B), binned(Q, B))
    if k >= nflow:
        st = NS[skip:, k-nflow]; ns = f"{st[:,0].mean():.4f} | {st[:,1].mean():.2e} | {st[:,2].min():.4f} | {st[:,3].max():.4f}"
    else: ns = "1 | 0 | 1 | 1"
    cc = np.corrcoef(O[skip:, k, j].mean(axis=(1, 2)), Of)[0, 1]
    L.append(f"| {lab} | " + " | ".join(fm(f0[i], e[i]) for i in range(7)) + f" | {ns} | {cc:.4f} |")
open(outp, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
