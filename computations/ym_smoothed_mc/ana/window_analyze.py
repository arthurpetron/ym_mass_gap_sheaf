"""P4 analysis: R(n) = connected zero-momentum correlator of the A1 (plane-summed) smoothed
s x s spatial Wilson-loop timeslice sum. Jackknife over bins (binning handles autocorrelation)."""
import numpy as np, json, sys, os
sys.path.insert(0, os.path.dirname(__file__)); from load import load

def per_config(O):            # O: (N, Lt) -> M (N,), Q (N, Lt//2+1)
    N, Lt = O.shape; M = O.mean(1)
    Q = np.stack([(O * np.roll(O, -n, axis=1)).mean(1) for n in range(Lt//2+1)], 1)
    return M, Q

def jk(Mb, Qb, fn):
    nb = len(Mb); full = fn(Mb.mean(0), Qb.mean(0))
    js = np.array([fn((Mb.sum(0)-Mb[i])/(nb-1), (Qb.sum(0)-Qb[i])/(nb-1)) for i in range(nb)])
    err = np.sqrt((nb-1)/nb*((js-js.mean(0))**2).sum(0)); return np.asarray(full), err

def binned(x, b):
    nb = len(x)//b; return x[:nb*b].reshape(nb, b, *x.shape[1:]).mean(1)

def tau_int_bin(series, bmax=None):
    """binning estimate: tau_int = 0.5 * var_bin_mean*B / var_naive at the largest bin with >=20 bins"""
    n = len(series); v0 = series.var(ddof=1); out = {}
    for b in [1,2,4,8,16,32,64]:
        if n//b < 20: break
        xb = binned(series, b); out[b] = 0.5*b*xb.var(ddof=1)/v0
    return out

def analyze(path, skip=0, binsize=None):
    h, plaq, Es, O = load(path)
    plaq, Es, O = plaq[skip:], Es[skip:], O[skip:]
    N = len(plaq); Lt = h['Lt']; sides = h['sides']; tfl = h['tflow']
    smain = sides[len(sides)//2]
    res = dict(hdr=h, N=N, plaq=float(plaq.mean()), smain=smain, levels={})
    # autocorrelation on main side, mid flow level, operator mean
    A1 = O.mean(3)                                  # (N, nlev, nside, Lt)
    k_mid = min(3, len(tfl)-1); si = sides.index(smain)
    Mmid, Qmid = per_config(A1[:, k_mid, si]); 
    taus = {'M': tau_int_bin(Mmid), 'Q1': tau_int_bin(Qmid[:, 1]-Mmid**2)}
    if binsize is None:
        # pick bin size >= 2*tau_int (max over estimates at largest bin), at least 5, and >= 25 bins
        tmax = max([max(v.values()) for v in taus.values() if v] + [0.5])
        binsize = int(max(5, np.ceil(4*tmax)))
        binsize = max(1, min(binsize, N//25))
    res['taus'] = {k: {str(b): round(float(t), 2) for b, t in v.items()} for k, v in taus.items()}
    res['binsize'] = binsize; res['nbins'] = N//binsize
    for k, tf in enumerate(tfl):
        for j, s in enumerate(sides):
            M, Q = per_config(A1[:, k, j]); Mb, Qb = binned(M, binsize), binned(Q, binsize)
            C = lambda m, q: q - m*m
            nmax = min(2*s, Lt//2)
            R, Re = jk(Mb, Qb, lambda m, q: C(m, q)[:nmax+1])
            Rn, Rne = jk(Mb, Qb, lambda m, q: C(m, q)[:nmax+1]/C(m, q)[0])
            def derived(m, q):
                c = C(m, q); e = 1 - c[1]/c[0]
                S1 = c[s]/c[0] if s <= Lt//2 else np.nan
                S2 = c[2*s]/c[s] if 2*s <= Lt//2 else np.nan
                if s % 2 == 0:
                    u = s//2; kb = 1 - 2*sum(c[2*t]-c[2*t+1] for t in range(u, 2*u))/c[2*u]
                else: kb = np.nan
                jen = (1-e)**s
                meff1 = np.log(c[s]/c[s+1]) if c[s+1] > 0 and c[s] > 0 else np.nan
                # --- MATH-NOTE-H1 additions ---
                es = 1 - c[s+1]/c[s] if s+1 <= Lt//2 else np.nan          # anchor T^{s/2} x: eps_shift(side)
                h2 = s//2; eh = 1 - c[h2+1]/c[h2]                          # anchor T^{floor(s/2)/2} x: side/2-lag variant
                Mb_ = s                                                     # box/Fejer time kernel Y=p(T)x, M=side
                if 2*Mb_+1 <= Lt//2:
                    kk = np.add.outer(np.arange(Mb_+1), np.arange(Mb_+1))
                    BYY = c[kk].sum(); BYT = c[kk+1].sum(); eb = 1 - BYT/BYY
                else: eb = np.nan
                hs = s//2                                                   # box state shifted by T^{s/2}: lags k+l+2*hs
                if 2*Mb_+2*hs+1 <= Lt//2:
                    kk = np.add.outer(np.arange(Mb_+1), np.arange(Mb_+1)) + 2*hs
                    ebs = 1 - c[kk+1].sum()/c[kk].sum()
                else: ebs = np.nan
                W = c[s+1]/c[s//2] if s+1 <= Lt//2 else np.nan
                return np.array([e, e*s, S1, S2, kb, jen, -np.log(max(S1, 1e-300))/s, meff1, es, es*s, eh, eh*s, eb, eb*s, ebs, ebs*s, W, 2*(1-W)/W, -2*np.log(max(W,1e-300))])
            D, De = jk(Mb, Qb, derived)
            res['levels'][f'{k}/{s}'] = dict(tflow=tf, rho=float(np.sqrt(6*tf)/smain), side=s, R=R.tolist(), Re=Re.tolist(),
                Rn=Rn.tolist(), Rne=Rne.tolist(), D=D.tolist(), De=De.tolist(), Es=float(Es[:, k].mean()))
    return res

def fmt(x, e):
    if not np.isfinite(x): return '   nan   '
    if e == 0 or not np.isfinite(e): return f'{x:.4f}'
    d = max(0, min(5, int(-np.floor(np.log10(e))) + 1)); return f'{x:.{d}f}({int(round(e*10**d))})'

if __name__ == '__main__':
    for p in sys.argv[1:]:
        r = analyze(p); h = r['hdr']
        print(f"== {p}  beta={h['beta']} {h['Ls']}^3x{h['Lt']} N={r['N']} bin={r['binsize']} nbins={r['nbins']} plaq={r['plaq']:.5f} tau(binning)={r['taus']}")
        print(' rho  tflow side | eps          eps*side     R(s)/R(0)    R(2s)/R(s)   kappa_b(u=s/2)  (1-eps)^s   -lnS1/s  ln R(s)/R(s+1)')
        for key, v in r['levels'].items():
            D, De = v['D'], v['De']
            print(f" {v['rho']:.2f} {v['tflow']:6.3f}  {v['side']}  | " + ' '.join(f'{fmt(D[i], De[i]):12s}' for i in range(8)))
