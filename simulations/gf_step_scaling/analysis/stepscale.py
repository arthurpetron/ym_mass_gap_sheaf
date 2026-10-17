#!/usr/bin/env python3
"""SU(2) gradient-flow coupling and step-scaling analysis (MC measurement only; no proof content).
usage: stepscale.py RUNDIR [--pairs 4:8,6:12] [--targets 1.2,1.6,2.0,2.4] [--tag name]"""
import sys, os, glob, json, argparse
import numpy as np
from math import pi, log
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *

B0 = 11.0 / (24.0 * pi ** 2)       # SU(2), 1-loop, g^2 convention: mu dg/dmu = -b0 g^3
S0 = 2 * B0 * log(2.0)             # 2 b0 ln 2 : 1/Sigma = 1/u - S0
B1 = 22.0 / 3.0; B2 = 136.0 / 3.0  # L^2 dg^2/dL^2 = B1 g^4/(16pi^2) + B2 g^6/(16pi^2)^2   (SU(2), Nf=0)

def sigma_oneloop(u): return u / (1 - S0 * u)
def sigma_twoloop(u):
    k = 1 / (16 * pi ** 2)
    return u + log(4.0) * (B1 * k * u ** 2 + (B1 ** 2 * log(4.0) + B2) * k ** 2 * u ** 3)

def load_ensembles(rundir, prefix='su2_'):
    ens = {}
    for f in sorted(glob.glob(os.path.join(rundir, prefix + 'L*_b*.csv'))):
        if f.endswith('.alt.csv'): continue
        r = load_run(f, 3)
        if len(r['sweep']) < 10: continue
        ens[(r['L'], round(r['beta'], 6))] = dict(run=r, path=f)
    return ens

def series(r, c, kind='cont'):
    i = time_index(r, c); t = r['times'][i]
    return t * t * r['E'][:, i, 0]  # t^2 E_clover

def ens_g2(e, c, norm):
    r = e['run']; x = series(r, c)
    Nn = N_cont(c) if norm == 'cont' else N_lat(c, r['L'])
    m, err, tau, W = gamma_method(x / Nn)
    return m, err, tau * r['sep'], len(x)

def fit_inv(betas, g2, err, M):
    """1/g2 - beta/4 = sum_{m=0..M} c_m (4/beta)^m, weighted LSQ. returns coefficients and cov."""
    b = np.asarray(betas); y = 1.0 / np.asarray(g2) - b / 4.0
    dy = np.asarray(err) / np.asarray(g2) ** 2
    A = np.vstack([(4.0 / b) ** m for m in range(M + 1)]).T
    w = 1.0 / dy
    coef, *_ = np.linalg.lstsq(A * w[:, None], y * w, rcond=None)
    return coef

def inv_model(coef, b):
    b = np.asarray(b, float)
    return b / 4.0 + sum(c * (4.0 / b) ** m for m, c in enumerate(coef))  # 1/g^2

def solve_beta(coef, u, lo, hi):
    f = lambda b: inv_model(coef, b) - 1.0 / u
    from scipy.optimize import brentq
    return brentq(f, lo, hi)

def step_scaling(ens, L, c, norm, targets, M=2, nboot=400, rng=None):
    rng = rng or np.random.default_rng(1)
    bs1 = sorted(b for (l, b) in ens if l == L); bs2 = sorted(b for (l, b) in ens if l == 2 * L)
    common = [b for b in bs1 if b in bs2]
    if len(common) < M + 2: return None
    d1 = [ens_g2(ens[(L, b)], c, norm) for b in common]
    d2 = [ens_g2(ens[(2 * L, b)], c, norm) for b in common]
    m1 = np.array([d[0] for d in d1]); e1 = np.array([d[1] for d in d1])
    m2 = np.array([d[0] for d in d2]); e2 = np.array([d[1] for d in d2])
    lo, hi = min(common) - 1e-9, max(common) + 1e-9
    out = []
    for u in targets:
        vals = []
        for k in range(nboot + 1):
            a1 = m1 if k == 0 else m1 + rng.normal(size=len(m1)) * e1
            a2 = m2 if k == 0 else m2 + rng.normal(size=len(m2)) * e2
            try:
                c1 = fit_inv(common, a1, e1, M); c2 = fit_inv(common, a2, e2, M)
                bstar = solve_beta(c1, u, lo, hi)
                sig = 1.0 / inv_model(c2, bstar)
            except Exception:
                continue
            vals.append((bstar, sig))
        if len(vals) < nboot // 2: out.append((u, None)); continue
        v = np.array(vals)
        central = v[0]
        out.append((u, dict(beta=central[0], sigma=central[1], sigma_err=v[1:, 1].std(), beta_err=v[1:, 0].std(), samples=v[1:, 1])))
    # chi2 of fits
    c1 = fit_inv(common, m1, e1, M); c2 = fit_inv(common, m2, e2, M)
    chi1 = np.sum(((1 / inv_model(c1, common) - m1) / e1) ** 2) / max(1, len(common) - M - 1)
    chi2 = np.sum(((1 / inv_model(c2, common) - m2) / e2) ** 2) / max(1, len(common) - M - 1)
    rng_u = (float(np.min(m1)), float(np.max(m1)))
    return dict(betas=common, u=m1, ue=e1, S=m2, Se=e2, res=out, chi_L=chi1, chi_2L=chi2, urange=rng_u)

def run_all(rundir, outdir, pairs, targets, norm, cs=(0.3, 0.4), Ms=(2, 3), nboot=600):
    ens = load_ensembles(rundir)
    os.makedirs(outdir, exist_ok=True)
    rows = []; ext_rows = []; lines = []
    for c in cs:
        res = {}
        for (L, L2) in pairs:
            for M in Ms:
                r = step_scaling(ens, L, c, norm, targets, M=M, nboot=nboot)
                if r is None: continue
                res[(L, M)] = r
                lines.append(f"\n== {L}->{L2} c={c} norm={norm} M={M} betas={r['betas']} chi2/dof(L)={r['chi_L']:.2f} chi2/dof(2L)={r['chi_2L']:.2f}")
                for b, u, ue, S, Se in zip(r['betas'], r['u'], r['ue'], r['S'], r['Se']):
                    lines.append(f"   beta={b:.3f} u={u:.4f}({ue:.4f}) Sigma_raw={S:.4f}({Se:.4f})")
                for u, d in r['res']:
                    if d is None:
                        continue
                    sm = d['samples']; inv = 1 / u - 1 / sm
                    rows.append(dict(c=c, norm=norm, pair=f'{L}->{L2}', aL=1.0 / L, M=M, u=u, beta=d['beta'], beta_err=d['beta_err'], Sigma=d['sigma'], Sigma_err=d['sigma_err'],
                                     inv_shift=1 / u - 1 / d['sigma'], inv_shift_err=inv.std(), one_loop_shift=S0, Sigma_1loop=sigma_oneloop(u), Sigma_2loop=sigma_twoloop(u),
                                     chi_L=r['chi_L'], chi_2L=r['chi_2L']))
                    lines.append(f"   u={u:.3f} beta*={d['beta']:.3f}({d['beta_err']:.3f}) Sigma={d['sigma']:.4f}({d['sigma_err']:.4f}) 1/u-1/Sigma={1/u-1/d['sigma']:.4f}({inv.std():.4f}) [1-loop {S0:.4f}] Sigma_1loop={sigma_oneloop(u):.4f}")
        # continuum extrapolation (linear in (a/L)^2) using all pairs available at fixed M
        for M in Ms:
            for u in targets:
                pts = []
                for (L, L2) in pairs:
                    r = res.get((L, M))
                    if r is None: continue
                    d = dict(r['res']).get(u)
                    if d is None: continue
                    pts.append((1.0 / L ** 2, d['sigma'], d['samples']))
                if len(pts) < 2: continue
                x = np.array([p[0] for p in pts])
                n = min(len(p[2]) for p in pts)
                smp = np.array([p[2][:n] for p in pts])  # independent across pairs
                def fit(y):
                    A = np.vstack([np.ones_like(x), x]).T
                    return np.linalg.lstsq(A, y, rcond=None)[0]
                c0 = fit(np.array([p[1] for p in pts]))
                bs = np.array([fit(smp[:, k])[0] for k in range(n)])
                sig0 = c0[0]; sige = bs.std()
                inv = 1 / u - 1 / bs
                ext_rows.append(dict(c=c, norm=norm, M=M, npairs=len(pts), u=u, Sigma_cont=sig0, Sigma_cont_err=sige, inv_shift=1 / u - 1 / sig0, inv_shift_err=inv.std(),
                                     one_loop_shift=S0, Sigma_1loop=sigma_oneloop(u), slope=c0[1], note=('UNCONSTRAINED: 2 points, 2 parameters' if len(pts) == 2 else 'linear in (a/L)^2')))
    def wr(name, rs):
        if not rs: return
        keys = list(rs[0].keys())
        with open(os.path.join(outdir, name), 'w') as f:
            f.write(','.join(keys) + '\n')
            for r in rs: f.write(','.join(f'{r[k]:.6g}' if isinstance(r[k], float) else str(r[k]) for k in keys) + '\n')
    wr(f'stepscaling_{norm}.csv', rows); wr(f'continuum_{norm}.csv', ext_rows)
    open(os.path.join(outdir, f'stepscaling_{norm}.log'), 'w').write('\n'.join(lines) + '\n')
    return rows, ext_rows, lines

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('rundir'); ap.add_argument('outdir'); ap.add_argument('--pairs', default='4:8,6:12')
    ap.add_argument('--targets', default='1.3,1.6,2.0,2.4'); ap.add_argument('--norm', default='lat'); ap.add_argument('--nboot', type=int, default=600)
    a = ap.parse_args()
    pairs = [tuple(map(int, p.split(':'))) for p in a.pairs.split(',')]
    rows, ext, lines = run_all(a.rundir, a.outdir, pairs, [float(x) for x in a.targets.split(',')], a.norm, nboot=a.nboot)
    print('\n'.join(lines)); print()
    for r in ext: print({k: (round(v, 4) if isinstance(v, float) else v) for k, v in r.items()})
