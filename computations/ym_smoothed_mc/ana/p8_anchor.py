"""P8: window survival W = R(side+1)/R(side//2) on the Lean anchor Y_j (zero-momentum sum of spatial
fundamental plaquettes, vacuum-centered, one-sided time box lags 0..M, M = side, weights 1/(M+1);
R_Y(n) = (M+1)^-2 sum_{a,b<=M} R_x(n+a+b)) vs NS-k2 smeared loop and flow rho=1 loop on the same configs.
usage: p8_anchor.py <out.md> --data <data.bin> [--flowrec <P7 data.bin> --cfglist <cfglist>] --sides 2,3,4 [--skip k] [--bin b]"""
import sys, os, re, argparse, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); from load import load
ap = argparse.ArgumentParser(); ap.add_argument('out'); ap.add_argument('--data'); ap.add_argument('--flowrec'); ap.add_argument('--cfglist')
ap.add_argument('--sides'); ap.add_argument('--skip', type=int, default=None); ap.add_argument('--bin', type=int, default=None); ap.add_argument('--title', default='')
A = ap.parse_args()
h, plaq, Es, O = load(A.data); N = len(plaq); Lt = h['Lt']; nq = Lt//2; sidesH = h['sides']; tfl = h['tflow']
lv = h.get('linear_variants', []); lsteps = [(v, n) for v in lv for n in v['steps']]
skip = A.skip if A.skip is not None else (0 if h.get('from_cfgs') else N//10)
P = O[skip:, 0, sidesH.index(1)].mean(1)          # [N, Lt] zero-momentum spatial plaquette (avg over 3 planes & sites), unsmoothed
chan = {'Ylean': P}; flowrec = None
if A.flowrec:
    H2, p2, E2, O2 = load(A.flowrec); idx = [int(re.search(r'cfg_(\d+)', l).group(1)) - 1 for l in open(A.cfglist).read().split()][:N]
    flowrec = (H2, O2[idx][skip:])
sides = [int(x) for x in A.sides.split(',')]
for s in sides:
    # flow rho=1 loop of side s
    src = None
    if flowrec:
        H2, O2 = flowrec
        if s in H2['sides']:
            k = int(np.argmin([abs(np.sqrt(6*t)/s - 1) for t in H2['tflow']]))
            if abs(np.sqrt(6*H2['tflow'][k])/s - 1) < 0.02: src = O2[:, k, H2['sides'].index(s)].mean(1)
    if src is None and s in sidesH:
        ks = [i for i, t in enumerate(tfl) if abs(np.sqrt(6*t)/s - 1) < 0.02]
        if ks: src = O[skip:, ks[0], sidesH.index(s)].mean(1)
    if src is not None: chan[f'flow{s}'] = src
    # NS k=2 alpha=0.2 (or any NS variant) with n ~ (2/3) s^2 / alpha
    for li, (v, n) in enumerate(lsteps):
        if v['k'] >= 1 and abs(n - (2/3)*s*s/v['alpha']) <= max(1, 0.1*n) and s in sidesH:
            chan[f'ns{s}'] = O[skip:, len(tfl)+li, sidesH.index(s)].mean(1); break
N2 = next(iter(chan.values())).shape[0]
B = A.bin or max(1, min(8, N2//10))
def pc(X):
    M = X.mean(1); Q = np.stack([(X*np.roll(X, -n, axis=1)).mean(1) for n in range(nq+1)], 1); return M, Q
def binned(x): nb = len(x)//B; return x[:nb*B].reshape(nb, B, *x.shape[1:]).mean(1)
CB = {c: tuple(binned(a) for a in pc(X)) for c, X in chan.items()}; nb = len(next(iter(CB.values()))[0])
# cross-correlators plaquette-sum x smoothed reference F (factorization estimate of the plaquette ground-state overlap)
XB = {}
for c, F in chan.items():
    if c == 'Ylean': continue
    Q = np.stack([0.5*((P*np.roll(F, -n, axis=1)).mean(1) + (F*np.roll(P, -n, axis=1)).mean(1)) for n in range(nq+1)], 1)
    XB[c] = (binned(P.mean(1)), binned(F.mean(1)), binned(Q))
def ext(r):  # periodic extension R(n), n up to Lt
    return np.concatenate([r, r[1:nq][::-1], r[:1]])
def boxR(r, M):
    e = ext(r); return np.array([sum(e[n+a+b] for a in range(M+1) for b in range(M+1))/(M+1)**2 if n+2*M <= Lt else np.nan for n in range(nq+1)])
def stats_of(mask):
    out = {}
    for c, (Mb, Qb) in CB.items():
        q = Qb[mask].mean(0); m = Mb[mask].mean(); out[c] = (q - m*m, q[:-1] - q[1:])
    for c, (mp, mf, qx) in XB.items(): out['X'+c] = qx[mask].mean(0) - mp[mask].mean()*mf[mask].mean()
    return out
def derive(st):
    res = {}
    for s in sides:
        h2 = s//2; Mbox = s
        rows = {}
        for name, c, M in [('Y_j (box M=side)', 'Ylean', Mbox), ('Y_j unboxed (M=0)', 'Ylean', 0), ('NS k2 loop', f'ns{s}', 0), ('flow rho=1 loop', f'flow{s}', 0), ('flow rho=1 loop + box M=side', f'flow{s}', Mbox)]:
            if c not in st: continue
            r, d = st[c]; R = boxR(r, M); D = R[:-1] - R[1:]
            with np.errstate(all='ignore'):
                rows[name] = np.array([R[0], R[1]/R[0], R[h2]/R[0], R[s+1]/R[0], R[s+1]/R[h2], D[s+1]/D[h2], np.log(R[h2]/R[h2+1]), np.log(R[s]/R[s+1]), np.log(R[h2+1]/R[s+1])/(s-h2)])
        # lambda0 from the flow (or NS) channel: plateau m = log(R(s)/R(s+1)) at the largest window lag
        ref = 'flow rho=1 loop' if 'flow rho=1 loop' in rows else ('NS k2 loop' if 'NS k2 loop' in rows else None)
        if ref:
            m0 = rows[ref][8]; lam = np.exp(-m0)
            for name in list(rows):
                W = rows[name][4]; f0W = W / lam**(h2+1); f0far = rows[name][3] / lam**(s+1)
                rows[name] = np.concatenate([rows[name][:8], [m0, f0W, f0far]])
            # factorization: c0(x) = R_xF(n)^2 / R_FF(2n) (F = smoothed reference, ground-dominated); f0_x = c0/R_xx(0)
            cref = f'flow{s}' if ref == 'flow rho=1 loop' else f'ns{s}'; rx = st['X'+cref]; rF = st[cref][0]; rxx = st['Ylean'][0]
            f0x = [rx[n]**2/rF[2*n]/rxx[0] if 2*n <= nq else np.nan for n in (1, max(1, h2), s)]
            g0 = (1 - lam**(Mbox+1))/((Mbox+1)*(1 - lam)); RY = boxR(rxx, Mbox)
            c0 = rx[max(1, h2)]**2/rF[2*max(1, h2)] if 2*max(1, h2) <= nq else np.nan
            f0Y0 = c0*g0**2/RY[0]; f0Yh = c0*g0**2*lam**h2/RY[h2]; Wpred = c0*g0**2*lam**(s+1)/RY[h2]
            rows['__overlap'] = np.array(f0x + [g0**2, f0Y0, f0Yh, Wpred, f0Yh*lam**(h2+1)])
        res[s] = rows
    return res
full = derive(stats_of(np.ones(nb, bool))); jks = [derive(stats_of(np.arange(nb) != i)) for i in range(nb)]
def fm(v, e):
    if not (np.isfinite(v) and np.isfinite(e)): return 'n/a'
    d = min(5, max(1, int(np.ceil(-np.log10(max(abs(e), 1e-12))))+1)); return f"{v:.{d}f}({int(round(e*10**d))})"
cols = ['R(0)', 'R(1)/R(0)', 'R(s/2)/R(0)', 'R(s+1)/R(0)', '**W** E1', 'W E3d', 'm_eff a @s/2', 'm_eff a @s', 'm0 a (ref)', 'f0(s/2) = W/λ0^(s/2+1)', 'f0(0) ≈ R(s+1)/(λ0^(s+1) R(0))']
L = [f"# P8 anchor window survival {A.title}\n", f"data `{A.data}`, N={N2} configs used (skip {skip}), bins of {B} ({nb} bins), Lt={Lt}. E1 = vacuum subtraction (single stream); E3d = subtraction-free differenced. R(n) for n > Lt/2 uses the periodic value R(Lt-n). λ0 = exp(-m0 a), m0 a = log[R(s/2+1)/R(s+1)]/(s-s/2) of the flow rho=1 loop (NS if no flow), a multi-lag rate.\n"]
for s in sides:
    L.append(f"\n## side {s}  (W = R({s+1})/R({s//2}); Y_j box needs lags up to {3*s+1} {'(> Lt/2: periodic image enters!)' if 3*s+1 > nq else ''})\n")
    L.append("| operator | " + " | ".join(cols) + " |"); L.append("|---|" + "---|"*len(cols))
    ov = None
    for name, v in full[s].items():
        js = np.array([j[s][name] for j in jks]); e = np.sqrt((nb-1)/nb*((js - js.mean(0))**2).sum(0))
        if name == '__overlap': ov = (v, e); continue
        L.append(f"| {name} | " + " | ".join(fm(v[i], e[i]) if i < len(v) else '' for i in range(len(cols))) + " |")
    if ov:
        v, e = ov; oc = ['f0_x(n=1)', 'f0_x(n=s/2)', 'f0_x(n=s)', 'box gain g0^2', 'f0_Y(0)', 'f0_Y(s/2)', 'W_Y predicted (ground state only)', 'f0_Y(s/2)·λ0^(s/2+1)']
        L.append("\nGround-state overlap of the plaquette family x by factorization through the smoothed reference F: f0_x(n) = R_xF(n)^2/(R_FF(2n) R_xx(0)); after the box: c0(Y) = c0(x) g0^2, g0 = (1-λ0^(M+1))/((M+1)(1-λ0)); f0_Y(n) = c0(Y) λ0^n / R_Y(n). W_Y predicted = c0(Y) λ0^(s+1)/R_Y(s/2) (ground-state contribution only).\n")
        L.append("| " + " | ".join(oc) + " |"); L.append("|" + "---|"*len(oc))
        L.append("| " + " | ".join(fm(v[i], e[i]) for i in range(len(oc))) + " |")
open(A.out, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
