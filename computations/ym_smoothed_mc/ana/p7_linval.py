"""P7 f-ii: W from linear unprojected smearing vs Wilson flow, same configs. usage: p7_linval.py <data.bin> <out.md>"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); from load import load
from p6_window import perconf, binned, tau_curve
path, outp = sys.argv[1], sys.argv[2]
h, plaq, Es, O = load(path); N = len(plaq); sides = h['sides']; s = 2; j = sides.index(s); h2 = s//2; Lt = h['Lt']; nq = Lt//2
labels = [f"flow t={t:g} (rho={np.sqrt(6*t)/s:.2f})" for t in h['tflow']] + [f"linear a={h['linear_alpha']} n={n} (rho_eq={np.sqrt(6*n*h['linear_alpha']/4)/s:.2f})" for n in h['linear_steps']]
skip = N//10; B = 8
def jk(fn, Mb, Qb):
    nb = len(Mb); f0 = fn(Mb.mean(), Qb.mean(0)); js = np.array([fn(np.delete(Mb, i).mean(), np.delete(Qb, i, 0).mean(0)) for i in range(nb)])
    return f0, np.sqrt((nb-1)/nb*((js-js.mean(0))**2).sum(0))
def der(m, q):
    c = q - m*m; far = q - q[nq]; d = q[:-1] - q[1:]
    with np.errstate(all='ignore'):
        return np.array([c[s+1]/c[h2], far[s+1]/far[h2], d[s+1]/d[h2], (1-c[1]/c[0])*s, c[s]/c[0], np.log(c[0]/c[1]), np.log(c[1]/c[2]), np.log(c[2]/c[3])])
def fm(v, e):
    if not np.isfinite(v): return 'n/a'
    d = min(5, max(1, int(np.ceil(-np.log10(max(e, 1e-12))))+1)); return f"{v:.{d}f}({int(round(e*10**d))})"
L = [f"# P7 (f-ii): linear unprojected spatial smearing vs spatial Wilson flow, same configs\n",
     f"beta {h['beta']}, {h['Ls']}^3x{Lt}, side {s}, N={N} meas (interval {h['interval']}), first {skip} discarded, bins of {B}. W = R(s+1)/R(s//2) = R(3)/R(1). E1 = global subtraction, E3f = far-lag Q(n)-Q(Lt/2), E3d = differenced. rho_eq for linear = sqrt(6 t_eq)/s with t_eq = n*alpha/4 (stout-equivalence matching).\n",
     "| level | <O> (raw scale) | W E1 | W E3f | W E3d | eps*s | R(s)/R(0) | m_eff(0) | m_eff(1) | m_eff(2) | tau(O) b16 |", "|---|---|---|---|---|---|---|---|---|---|---|"]
for k, lab in enumerate(labels):
    M, Q = perconf(O[skip:, k, j].mean(1)); sc = abs(M.mean()); M, Q = M/sc, Q/sc**2  # rescale (linear loops shrink with link norms; ratios unaffected)
    f0, e = jk(der, binned(M, B), binned(Q, B)); tc = tau_curve([M]); tb = tc.get(16, tc[max(tc)])
    L.append(f"| {lab} | {sc:.4g} | " + " | ".join(fm(f0[i], e[i]) for i in range(8)) + f" | {tb:.2f} |")
open(outp, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
