"""Cross-beta summary for P4. Usage: summary.py run1 run2 ...  (run dirs). Writes JSON + markdown tables to stdout."""
import numpy as np, json, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from load import load
from analyze import analyze, per_config, binned, fmt
SQT0 = {2.42: 1.083, 2.5: 1.839, 2.6: 3.522, 2.7: 6.628, 2.8: 11.96, 2.85: 16.95}   # t0/a^2, Hirakida et al. arXiv:1811.02800 (t^2<E>=0.1)
def sqrt_t0(beta):
    b = round(beta, 2)
    if b in SQT0: return np.sqrt(SQT0[b])
    # extrapolate from beta=2.85 with the Hirakida quadratic fit slope (outside fit range [2.42,2.85])
    q = lambda x: 6.409*(x-2.6) - 0.7411*(x-2.6)**2
    return np.sqrt(16.95*np.exp(q(b)-q(2.85)))

def jk_samples(path, k, side, binsize):
    h, plaq, Es, O = load(path); A1 = O.mean(3); j = h['sides'].index(side)
    M, Q = per_config(A1[:, k, j]); Mb, Qb = binned(M, binsize), binned(Q, binsize); nb = len(Mb)
    C = lambda m, q: q - m*m
    full = C(Mb.mean(0), Qb.mean(0))
    js = np.array([C((Mb.sum(0)-Mb[i])/(nb-1), (Qb.sum(0)-Qb[i])/(nb-1)) for i in range(nb)])
    return full, js

X = np.linspace(0.05, 6, 120); Y = np.linspace(0.5, 60, 240)
def fit2(rn, err, s):
    """R(n)/R(0) = w e^{-x n/s} + (1-w) e^{-y n/s}, n=1..2s; grid in (x<y), w by weighted LS (0<=w<=1)."""
    n = np.arange(1, len(rn)); r = rn[1:]; wgt = 1/np.maximum(err[1:], 1e-6)**2
    A = np.exp(-np.outer(X, n)/s)[:, None, :]; B = np.exp(-np.outer(Y, n)/s)[None, :, :]
    D = A - B; T = r[None, None, :] - B
    w = np.clip((wgt*D*T).sum(-1)/np.maximum((wgt*D*D).sum(-1), 1e-300), 0, 1)
    chi = (wgt*(T - w[..., None]*D)**2).sum(-1)
    chi[Y[None, :] <= 1.2*X[:, None]] = np.inf
    i, j = np.unravel_index(np.argmin(chi), chi.shape)
    return chi[i, j], (w[i, j], X[i], Y[j])

def main(dirs, out_json=None):
    allres = {}
    for d in dirs:
        r = analyze(d + '/data.bin'); allres[d] = r
    rows = []
    for d, r in allres.items():
        h = r['hdr']; b = h['beta']; s = r['smain']; st = sqrt_t0(b)
        print(f"\n### {d}: beta={b} {h['Ls']}^3x{h['Lt']}  side={s}  sqrt(t0)/a={st:.3f}  side*a/sqrt(t0)={s/st:.3f}  Ls*a/sqrt(t0)={h['Ls']/st:.2f}  N={r['N']} bin={r['binsize']} nbins={r['nbins']} plaq={r['plaq']:.5f}")
        print(f"tau_int binning estimates (M=<O>, Q1=O(t)O(t+1)): {r['taus']}")
        print('| rho | t_flow | eps | eps*side | R(s)/R(0) = R(2u)/R(0) | R(2s)/R(s) = R(4u)/R(2u) | kappa_b(u=s/2) | Jensen (1-eps)^s |')
        print('|---|---|---|---|---|---|---|---|')
        for key, v in r['levels'].items():
            if v['side'] != s: continue
            D, De = v['D'], v['De']
            print(f"| {v['rho']:.2f} | {v['tflow']:.3f} | " + ' | '.join(fmt(D[i], De[i]) for i in [0,1,2,3,4,5]) + ' |')
        for key, v in r['levels'].items():
            if v['side'] != s or v['rho'] < 0.45: continue
            print(f"R(n)/R(0), rho={v['rho']:.2f}: " + ', '.join(f"{n}:{fmt(x,e)}" for n,(x,e) in enumerate(zip(v['Rn'], v['Rne']))))
        rows.append((d, r))
    # MATH-NOTE-H1 table: shifted anchors, box kernel, m_eff vs m L
    print('\n### Shifted-anchor / box-kernel eps (MATH-NOTE-H1 predictions); m L uses m_0++ = 3.78 sqrt(sigma), sqrt(sigma) sqrt(t0) = 0.26')
    print('| run | side | rho | eps*side | eps_shift=1-R(s+1)/R(s) | eps_shift*side | eps_half=1-R(h+1)/R(h), h=floor(s/2) | eps_half*side | eps_box (M=side) | eps_box*side | eps_box,shift(T^{s/2}) *side | a m_eff=ln R(s)/R(s+1) | m_eff*L (=a m_eff*side) | lit m0++ L | lit 2 m0++ L |')
    print('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    for d, r in rows:
        s = r['smain']; b = r['hdr']['beta']; asig = 0.26/sqrt_t0(b); mL = 3.78*asig*s
        for v in r['levels'].values():
            if v['side'] != s: continue
            D, De = v['D'], v['De']; f = lambda i: fmt(D[i], De[i])
            print(f"| {os.path.basename(d)} | {s} | {v['rho']:.2f} | {f(1)} | {f(8)} | {f(9)} | {f(10)} | {f(11)} | {f(12)} | {f(13)} | {f(15)} | {f(7)} | {fmt(D[7]*s, De[7]*s)} | {mL:.2f} | {2*mL:.2f} |")
    # collapse + fits for main side
    print('\n### Physical-time collapse: R(n)/R(0) at tau = n/side (main side)')
    for rho_t in [0.5, 0.7, 1.0]:
        print(f"\nrho={rho_t}")
        print('| run | side | tau=1/side (=1-eps) | tau=0.5 | tau=1 | tau=1.5 | tau=2 | 2-state fit w, x=m*side, y=E*side, chi2/dof | model lim eps*side = w x+(1-w) y | slopes s(1-R(n)/R(0))/n, n=1,2,3 -> quad. extrap. h=n/s->0 |')
        print('|---|---|---|---|---|---|---|---|---|---|')
        for d, r in rows:
            s = r['smain']; v = [v for v in r['levels'].values() if v['side'] == s and abs(v['rho']-rho_t) < 0.03][0]
            k = list(r['levels'].values()).index(v) // len(r['hdr']['sides'])
            cells = [fmt(v['Rn'][1], v['Rne'][1])]
            for tau in [0.5, 1, 1.5, 2]:
                n = tau*s; cells.append(fmt(v['Rn'][int(n)], v['Rne'][int(n)]) if abs(n-round(n)) < 1e-9 else '-')
            rn = np.array(v['Rn']); er = np.array(v['Rne'])
            chi, (w, x, y) = fit2(rn, er, s)
            full, js = jk_samples(d + '/data.bin', k, s, r['binsize'])
            ps = []
            for jsample in js:
                rr = jsample[:2*s+1]/jsample[0]; c2, p = fit2(rr, er, s); ps.append(p)
            ps = np.array(ps); nb = len(ps); pe = np.sqrt((nb-1)/nb*((ps-ps.mean(0))**2).sum(0))
            lim = w*x + (1-w)*y; lims = ps[:,0]*ps[:,1] + (1-ps[:,0])*ps[:,2]; lime = np.sqrt((nb-1)/nb*((lims-lims.mean())**2).sum())
            dof = max(1, 2*s - 3)
            cells.append(f"{fmt(w,pe[0])}, {fmt(x,pe[1])}, {fmt(y,pe[2])}, {chi/dof:.2f}"); cells.append(fmt(lim, lime))
            # finite-difference slopes D(h)=(1-R(n)/R(0))/h, h=n/s, and 3-point quadratic extrapolation to h=0
            Ds = lambda rr: np.array([(1-rr[n]/rr[0])*s/n for n in (1,2,3)])
            Dfull = Ds(full); Dj = np.array([Ds(x) for x in js]); ext = lambda D: 3*D[0]-3*D[1]+D[2]
            E0 = ext(Dfull); E0j = np.array([ext(x) for x in Dj]); E0e = np.sqrt((nb-1)/nb*((E0j-E0j.mean())**2).sum())
            De = np.sqrt((nb-1)/nb*((Dj-Dj.mean(0))**2).sum(0))
            cells.append(', '.join(fmt(a,b) for a,b in zip(Dfull, De)) + f" -> {fmt(E0,E0e)}")
            print(f"| {os.path.basename(d)} | {s} | " + ' | '.join(cells) + ' |')
    if out_json:
        json.dump({d: r for d, r in allres.items()}, open(out_json, 'w'), default=float, indent=1)

if __name__ == '__main__':
    args = sys.argv[1:]; oj = None
    if args and args[0].startswith('--json='): oj = args[0][7:]; args = args[1:]
    main(args, oj)
