"""Markdown tables for the P4 report. Usage: tables.py rundir... > tables.md"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from analyze import analyze, fmt
from summary import sqrt_t0, jk_samples, fit2
dirs = sys.argv[1:]; R = {d: analyze(d + '/data.bin') for d in dirs}
name = lambda d: os.path.basename(d.rstrip('/'))
def lev(r, rho):
    s = r['smain']; return [v for v in r['levels'].values() if v['side'] == s and abs(v['rho'] - rho) < 0.03][0]
print('### T1. Runs\n')
print('| run | beta | lattice | side s | sqrt(t0)/a [lit] | s·a/sqrt(t0) | Ls·a/sqrt(t0) | N meas | bin | nbins | tau_int(<O>) binning, largest bin | <plaq> |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|')
for d, r in R.items():
    h = r['hdr']; st = sqrt_t0(h['beta']); tm = r['taus']['M']; kmax = max(tm, key=lambda k: int(k))
    print(f"| {name(d)} | {h['beta']} | {h['Ls']}^3x{h['Lt']} | {r['smain']} | {st:.3f} | {r['smain']/st:.3f} | {h['Ls']/st:.2f} | {r['N']} | {r['binsize']} | {r['nbins']} | {tm[kmax]} (bin {kmax}) | {r['plaq']:.5f} |")
for rho in [0.0, 0.5, 0.7, 1.0]:
    print(f'\n### T2 (rho = {rho}). eps, survival, window budget\n')
    print('| run | s | eps = 1-R(1)/R(0) | eps·s | R(2u)/R(0) = R(s)/R(0) | R(4u)/R(2u) = R(2s)/R(s) | kappa_b (u=s/2) | Jensen floor (1-eps)^s |')
    print('|---|---|---|---|---|---|---|---|')
    for d, r in R.items():
        v = lev(r, rho); D, De = v['D'], v['De']
        print(f"| {name(d)} | {r['smain']} | " + ' | '.join(fmt(D[i], De[i]) for i in range(6)) + ' |')
for rho in [1.0, 0.5]:
    print(f'\n### T3 (rho = {rho}). R(n)/R(0), n = 0..2s\n')
    for d, r in R.items():
        v = lev(r, rho)
        print(f"- {name(d)} (s={r['smain']}): " + ', '.join(f"{n}: {fmt(x, e)}" for n, (x, e) in enumerate(zip(v['Rn'], v['Rne']))))
for rho in [0.0, 0.5, 1.0]:
    print(f'\n### T4 (rho = {rho}). MATH-NOTE-H1 quantities\n')
    print('| run | s | eps·s | eps_shift = 1-R(s+1)/R(s) | eps_shift·s | eps_half = 1-R(h+1)/R(h), h=floor(s/2) | eps_half·s | eps_box (Fejer M=s) | eps_box·s | eps_box·s, shifted T^{s/2} | a·m_eff = ln R(s)/R(s+1) | m_eff·L | lit m0++·L | lit 2m0++·L |')
    print('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    for d, r in R.items():
        v = lev(r, rho); D, De = v['D'], v['De']; s = r['smain']; mL = 3.78*0.26/sqrt_t0(r['hdr']['beta'])*s
        f = lambda i: fmt(D[i], De[i])
        print(f"| {name(d)} | {s} | {f(1)} | {f(8)} | {f(9)} | {f(10)} | {f(11)} | {f(12)} | {f(13)} | {f(15)} | {f(7)} | {fmt(D[7]*s, De[7]*s)} | {mL:.2f} | {2*mL:.2f} |")
for rho in [1.0, 0.7, 0.5]:
    print(f'\n### T5 (rho = {rho}). Physical-time collapse and continuum estimates of eps·s\n')
    print('| run | s | R(tau=1/s)/R(0) | tau=0.5 | tau=1 | tau=1.5 | tau=2 | 2-exp fit: w, m·L, E·L, chi2/dof | 2-exp limit w·mL+(1-w)·EL | slopes s(1-R(n)/R(0))/n, n=1,2,3 -> quad. extrap. |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    for d, r in R.items():
        s = r['smain']; v = lev(r, rho); k = list(r['levels'].values()).index(v) // len(r['hdr']['sides'])
        cells = [fmt(v['Rn'][1], v['Rne'][1])]
        for tau in [0.5, 1, 1.5, 2]:
            n = tau*s; cells.append(fmt(v['Rn'][int(n)], v['Rne'][int(n)]) if abs(n - round(n)) < 1e-9 else '-')
        rn, er = np.array(v['Rn']), np.array(v['Rne']); chi, (w, x, y) = fit2(rn, er, s)
        full, js = jk_samples(d + '/data.bin', k, s, r['binsize']); nb = len(js)
        ps = np.array([fit2(j[:2*s+1]/j[0], er, s)[1] for j in js]); pe = np.sqrt((nb-1)/nb*((ps-ps.mean(0))**2).sum(0))
        lims = ps[:,0]*ps[:,1] + (1-ps[:,0])*ps[:,2]; lime = np.sqrt((nb-1)/nb*((lims-lims.mean())**2).sum())
        Ds = lambda rr: np.array([(1-rr[n]/rr[0])*s/n for n in (1,2,3)]); ext = lambda D: 3*D[0]-3*D[1]+D[2]
        Df = Ds(full); Dj = np.array([Ds(j) for j in js]); De = np.sqrt((nb-1)/nb*((Dj-Dj.mean(0))**2).sum(0))
        E0j = np.array([ext(x_) for x_ in Dj]); E0e = np.sqrt((nb-1)/nb*((E0j-E0j.mean())**2).sum())
        cells += [f"{fmt(w,pe[0])}, {fmt(x,pe[1])}, {fmt(y,pe[2])}, {chi/max(1,2*s-3):.2f}", fmt(w*x+(1-w)*y, lime),
                  ', '.join(fmt(a, b) for a, b in zip(Df, De)) + f" -> {fmt(ext(Df), E0e)}" + (' (s=2: h up to 1.5, unreliable)' if s < 4 else '')]
        print(f"| {name(d)} | {s} | " + ' | '.join(cells) + ' |')
