"""P6: window survival W = R(s+1)/R(s//2) with several vacuum-subtraction estimators, Fejer time-box W,
binning tau_int, raw-vs-smoothed effective masses. Usage: p6_window.py <run_name> [more streams for same run...]
Writes runs/p6/<name>.json. Single-threaded numpy."""
import numpy as np, json, sys, os
sys.path.insert(0, os.path.dirname(__file__)); from load import load

def perconf(O):
    N, Lt = O.shape
    return O.mean(1), np.stack([(O*np.roll(O, -n, axis=1)).mean(1) for n in range(Lt//2+1)], 1)

def binned(x, b):
    nb = len(x)//b; return x[:nb*b].reshape(nb, b, *x.shape[1:]).mean(1)

def tau_curve(series_list):
    out = {}
    for b in [1, 2, 4, 8, 16, 32, 64]:
        vals = []
        for x in series_list:
            if len(x)//b < 12: vals = None; break
            vals.append(0.5*b*binned(x, b).var(ddof=1)/x.var(ddof=1))
        if vals is None: break
        out[b] = float(np.mean(vals))
    return out

GRID = np.linspace(0.005, 2.5, 500)
def offset_fit(q, n0, Lt, wts):
    n = np.arange(n0, Lt//2+1); y = q[n0:]; w = wts[n0:]
    best = (np.inf, None)
    for m in GRID:
        f = np.exp(-m*n) + np.exp(-m*(Lt-n)); X = np.c_[f, np.ones_like(f)]
        A = X.T @ (X*w[:, None]); bb = X.T @ (w*y)
        try: p = np.linalg.solve(A, bb)
        except np.linalg.LinAlgError: continue
        chi = (w*(y - X@p)**2).sum()
        if chi < best[0]: best = (chi, (m, p[0], p[1]))
    return best

def stats(samples, full):
    nb = len(samples); return full, np.sqrt((nb-1)/nb*((samples-samples.mean(0))**2).sum(0))

def analyze(name, paths, binsize=None, do_fit=True):
    SK = int(os.environ.get('P6_SKIP', '0')); streams = [(lambda t: (t[0], t[1][SK:], t[2][SK:], t[3][SK:]))(load(p)) for p in paths]; h = streams[0][0]; Lt = h['Lt']; sides = h['sides']; tfl = h['tflow']
    sm = sides[len(sides)//2]; s = sm; h2 = s//2; nq = Lt//2
    out = dict(name=name, hdr=h, N=[len(x[1]) for x in streams], smain=sm, levels={})
    # tau_int of operator mean (main side) for each level
    taus = {}
    for k, tf in enumerate(tfl):
        Ms = [perconf(st[3].mean(3)[:, k, sides.index(sm)])[0] for st in streams]
        taus[k] = tau_curve(Ms)
    out['tau'] = {f"{np.sqrt(6*tf)/sm:.2f}": taus[k] for k, tf in enumerate(tfl)}
    if binsize is None:
        tmax = max(max(v.values()) for v in taus.values() if v)
        binsize = int(max(5, np.ceil(4*tmax))); binsize = min(binsize, min(out['N'])//12)
    out['binsize'] = binsize
    for k, tf in enumerate(tfl):
        rho = float(np.sqrt(6*tf)/sm); j = sides.index(sm)
        Mb, Qb, sid = [], [], []
        for si, st in enumerate(streams):
            M, Q = perconf(st[3].mean(3)[:, k, j]); Mb.append(binned(M, binsize)); Qb.append(binned(Q, binsize)); sid += [si]*len(Mb[-1])
        Mb = np.concatenate(Mb); Qb = np.concatenate(Qb); sid = np.array(sid); nb = len(Mb); ns = len(streams)
        def corr_E1(mask):   # per-stream subtraction
            cs, ws = [], []
            for si in range(ns):
                mm = mask & (sid == si)
                if mm.sum() == 0: continue
                cs.append(Qb[mm].mean(0) - Mb[mm].mean()**2); ws.append(mm.sum())
            return np.average(cs, axis=0, weights=ws)
        def corr_E2(mask):   # per-block subtraction
            return (Qb[mask] - Mb[mask][:, None]**2).mean(0)
        def corr_Q(mask): return Qb[mask].mean(0)
        full = np.ones(nb, bool); masks = [np.arange(nb) != i for i in range(nb)]
        def W_of(c): return c[s+1]/c[h2]
        def fejer(c, M):
            if s+1+2*M > nq: return np.nan
            kk = np.add.outer(np.arange(M+1), np.arange(M+1))
            return c[kk+s+1].sum()/c[kk+h2].sum()
        Ms_fej = sorted(set([1, 2, max(1, h2), s]))
        def derived_C(c):
            r = [W_of(c), 1-c[1]/c[0], (1-c[1]/c[0])*s, c[s]/c[0], 1-c[s+1]/c[s], (1-c[s+1]/c[s])*s]
            r += [fejer(c, M) for M in Ms_fej]
            return np.array(r)
        def corr_E1c(mask):  # per-stream subtraction + bias correction Var(Mbar_stream) estimated from bin scatter
            cs, ws = [], []
            for si in range(ns):
                mm = mask & (sid == si); n_ = mm.sum()
                if n_ < 2: continue
                a = Qb[mm].mean(0) - Mb[mm].mean()**2; b_ = (Qb[mm] - Mb[mm][:, None]**2).mean(0)
                cs.append(a + (a - b_)/(n_ - 1)); ws.append(n_)
            return np.average(cs, axis=0, weights=ws)
        res = {}; JS = {}
        for lab, fn in [('E1_stream', corr_E1), ('E1c_biascorr', corr_E1c), ('E2_block', corr_E2)]:
            f0 = derived_C(fn(full)); js = np.array([derived_C(fn(m)) for m in masks]); res[lab] = stats(js, f0); JS[lab] = (f0[0], js[:, 0])
        # subtraction-free: far-lag (Q(n)-Q(Lt/2)) and differenced D(n)=Q(n)-Q(n+1)
        far = lambda m: corr_Q(m) - corr_Q(m)[nq]
        f0 = derived_C(far(full)); js = np.array([derived_C(far(m)) for m in masks]); res['E3_farlag'] = stats(js, f0); JS['E3_farlag'] = (f0[0], js[:, 0])
        def dW(m):
            q = corr_Q(m); d = q[:-1] - q[1:]
            return np.array([d[s+1]/d[h2] if s+1 < nq else np.nan, 1-d[1]/d[0]])
        f0 = dW(full); js = np.array([dW(m) for m in masks]); res['E3_diff'] = stats(js, f0); JS['E3_diff'] = (f0[0], js[:, 0])
        if do_fit:
            qjs = np.array([corr_Q(m) for m in masks]); qe = stats(qjs - qjs[:, [nq]], corr_Q(full) - corr_Q(full)[nq])[1]
            wts = 1/np.maximum(qe, 1e-30)**2; wts[nq] = wts[nq-1]
            def fitW(m):
                _, (mm, A, K) = offset_fit(corr_Q(m), h2, Lt, wts)
                g = lambda n: np.exp(-mm*n) + np.exp(-mm*(Lt-n))
                return np.array([g(s+1)/g(h2), mm])
            f0 = fitW(full); js = np.array([fitW(m) for m in masks]); res['E3_offsetfit'] = stats(js, f0); JS['E3_offsetfit'] = (f0[0], js[:, 0])
        # correlated jackknife pulls of W relative to E1
        pulls = {}
        for lab, (f0, js) in JS.items():
            if lab == 'E1_stream': continue
            dv, de = stats(js - JS['E1_stream'][1], f0 - JS['E1_stream'][0]); pulls[lab] = [float(dv), float(de)]
        # effective masses per lag (E1 and differenced) and signal/noise
        c1 = corr_E1(full); cjs = np.array([corr_E1(m) for m in masks]); _, ce = stats(cjs, c1)
        nmax = min(nq-1, 2*s+3)
        def meff(c): 
            with np.errstate(all='ignore'): return np.log(c[:nmax]/c[1:nmax+1])
        mf, mfe = stats(np.array([meff(c) for c in cjs]), meff(c1))
        def meffD(m):
            q = corr_Q(m); d = q[:-1]-q[1:]
            with np.errstate(all='ignore'): return np.log(d[:nmax]/d[1:nmax+1])
        mD, mDe = stats(np.array([meffD(m) for m in masks]), meffD(full))
        out['levels'][f"{rho:.2f}"] = dict(rho=rho, tflow=tf, Ms_fejer=Ms_fej,
            est={k_: [v[0].tolist(), v[1].tolist()] for k_, v in res.items()}, pulls=pulls,
            C=c1[:nmax+1].tolist(), Ce=ce[:nmax+1].tolist(), meff=mf.tolist(), meffe=mfe.tolist(), meffD=mD.tolist(), meffDe=mDe.tolist())
    # error-vs-binsize for W(E1) at rho~1 and rho~0.75
    out['binscan'] = {}
    for k, tf in enumerate(tfl):
        rho = np.sqrt(6*tf)/sm
        if min(abs(rho-1), abs(rho-0.75)) > 0.02: continue
        row = {}
        for b in [1, 2, 4, 8, 16, 32]:
            Mb, Qb = [], []
            for st in streams:
                M, Q = perconf(st[3].mean(3)[:, k, sides.index(sm)]); Mb.append(binned(M, b)); Qb.append(binned(Q, b))
            if min(len(x) for x in Mb) < 12: break
            Mb = np.concatenate(Mb); Qb = np.concatenate(Qb); nb = len(Mb)
            Wj = []; epsj = []
            for i in range(nb):
                m = np.arange(nb) != i; c = Qb[m].mean(0) - Mb[m].mean()**2; Wj.append(c[s+1]/c[h2]); epsj.append(1-c[1]/c[0])
            Wj = np.array(Wj); epsj = np.array(epsj)
            row[b] = [float(np.sqrt((nb-1)/nb*((Wj-Wj.mean())**2).sum())), float(np.sqrt((nb-1)/nb*((epsj-epsj.mean())**2).sum()))]
        out['binscan'][f"{rho:.2f}"] = row
    return out

if __name__ == '__main__':
    name = sys.argv[1]; paths = sys.argv[2:]
    r = analyze(name, paths)
    json.dump(r, open(f'runs/p6/{name}.json', 'w'), default=float)
    print('wrote', name, 'bin', r['binsize'], 'N', r['N'])
