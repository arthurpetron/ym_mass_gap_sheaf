#!/usr/bin/env python3
"""Per-ensemble table: g^2_GF(c=0.3,0.4) with Gamma-method errors, tau_int (sweeps), plaquette tau_int,
thermalisation check, step-size check (eps 0.02 vs 0.01), topological-charge statistics.
usage: ensemble_table.py RUNDIR OUT.csv [su2|u1]"""
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *

def plaq_series(path, therm):
    d = np.array([[float(x) for x in l.split()] for l in open(path) if len(l.split()) == 2])
    _, idx = np.unique(d[:, 0], return_index=True)
    d = d[idx]
    return d[d[:, 0] > therm, 1]

def q_stats(Q):
    r = np.rint(Q); changes = int(np.sum(r[1:] != r[:-1]))
    vals, cnt = np.unique(r.astype(int), return_counts=True)
    near = float(np.mean(np.abs(Q - r) < 0.15))
    return dict(maxabsQ=float(np.max(np.abs(Q))), fracbig=float(np.mean(np.abs(Q) > 0.5)), Q2=float(np.mean(Q ** 2)), near_int=near, nchg=changes, hist={int(v): int(c) for v, c in zip(vals, cnt)})

def main(rundir, out, kind):
    ncol = 3 if kind == 'su2' else 2
    rows = []
    for f in sorted(glob.glob(os.path.join(rundir, f'{kind}_L*_b*.csv'))):
        if f.endswith('.alt.csv'): continue
        r = load_run(f, ncol)
        n = len(r['sweep'])
        if n < 20: continue
        L, beta, sep = r['L'], r['beta'], r['sep']
        row = dict(file=os.path.basename(f)[:-4], kind=kind, L=L, beta=beta, nmeas=n, sep=sep, therm=r['therm'], start=('cold' if '_cold' in f else 'hot' if kind == 'su2' else 'cold'))
        for c in (0.3, 0.4):
            i = time_index(r, c); t = r['times'][i]; x = t * t * r['E'][:, i, 0]
            Nc = N_cont(c) if kind == 'su2' else N_cont_u1(c)
            Nl = N_lat(c, L) if kind == 'su2' else N_lat_u1(c, L)
            m, e, tau, W = gamma_method(x)
            row[f'g2_c{c}'] = m / Nc; row[f'g2err_c{c}'] = e / Nc; row[f'tau_sw_c{c}'] = tau * sep
            row[f'g2ti_c{c}'] = m / Nl; row[f'g2tierr_c{c}'] = e / Nl
            h = n // 2
            m1, e1, *_ = gamma_method(x[:h]); m2, e2, *_ = gamma_method(x[h:])
            row[f'halfdiff_sigma_c{c}'] = (m1 - m2) / np.sqrt(e1 ** 2 + e2 ** 2 + 1e-300)
            # plaquette-definition E as cross-check
            xp = t * t * r['E'][:, i, 1]; mp, ep, *_ = gamma_method(xp)
            row[f'g2plaq_c{c}'] = mp / Nc
        pl = os.path.join(rundir, row['file'] + '.plaq')
        if os.path.exists(pl):
            p = plaq_series(pl, r['therm'])
            if len(p) > 50:
                pm, pe, ptau, _ = gamma_method(p)
                row['plaq'] = pm; row['plaq_err'] = pe; row['plaq_tau_sw'] = ptau
        # step-size check
        af = f[:-4] + '.alt.csv'
        if os.path.exists(af):
            try:
                a = load_run(af, ncol)
                idx = [int(k) for k in np.round(a['sweep']).astype(int)]
                sw = {int(s): j for j, s in enumerate(r['sweep'])}
                jj = [sw[s] for s in idx if s in sw]
                if jj:
                    rel = np.abs(a['E'][:len(jj), :, 0] / r['E'][jj, :, 0] - 1)
                    row['eps_check_maxrel'] = float(rel.max()); row['eps_check_n'] = len(jj)
            except Exception as ex:
                pass
        if kind == 'su2':
            for c in (0.4, 0.5):
                i = time_index(r, c); Q = r['E'][:, i, 2]
                qs = q_stats(Q)
                row[f'Q2_c{c}'] = qs['Q2']; row[f'maxabsQ_c{c}'] = qs['maxabsQ']; row[f'fracQgt0.5_c{c}'] = qs['fracbig']; row[f'Qnearint_c{c}'] = qs['near_int']; row[f'Qchanges_c{c}'] = qs['nchg']
                row[f'Qhist_c{c}'] = str(qs['hist']).replace(',', ';')
                m, e, tau, W = gamma_method(Q ** 2); row[f'Q2_tau_sw_c{c}'] = tau * sep
        rows.append(row)
    keys = []
    for r_ in rows:
        for k in r_:
            if k not in keys: keys.append(k)
    with open(out, 'w') as fo:
        fo.write(','.join(keys) + '\n')
        for r_ in rows:
            fo.write(','.join('' if k not in r_ else (f'{r_[k]:.6g}' if isinstance(r_[k], float) else str(r_[k])) for k in keys) + '\n')
    print(f'{len(rows)} ensembles -> {out}')

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'su2')
