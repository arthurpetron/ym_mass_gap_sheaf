#!/usr/bin/env python3
"""Compact U(1) Coulomb-phase control: g^2_GF(L) vs g^2_GF(2L) at the SAME beta (no running expected).
Uses the abelian normalisation (N_U1(c), and its lattice tree-level variant). usage: u1_control.py RUNDIR OUT.md PAIRS"""
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
from ensemble_table import read_plq
from scipy.stats import kurtosis, skew

def get(rundir, L, beta):
    f = os.path.join(rundir, f'u1_L{L}_b{beta:.2f}.csv')
    return load_run(f, 2) if os.path.exists(f) else None

def g2(r, c, tree):
    i = time_index(r, c); t = r['times'][i]; x = t * t * r['E'][:, i, 0]
    Nn = (N_lat_u1(c, r['L']) if tree else N_cont_u1(c))
    m, e, tau, W = gamma_method(x / Nn)
    return m, e, tau * r['sep']

def main(rundir, out, pairs):
    betas = sorted({round(float(os.path.basename(f).split('_b')[1][:-4]), 2) for f in glob.glob(os.path.join(rundir, 'u1_L*_b*.csv')) if '_tau' not in f and 'alt' not in f})
    lines = ['| pair | beta | c | u=g2(L) cont-N | g2(2L) cont-N | Sigma/u (cont-N) | Sigma/u (tree-impr. N) | (Sigma-u)/err | g2*beta (L, cont-N) | tau_sw L / 2L |', '|---|---|---|---|---|---|---|---|---|---|']
    plq = ['| L | beta | nmeas | plaq mean | plaq tau_int (sweeps) | plaq min | plaq max | excess kurtosis (bimodal if < ~ -1.2) |', '|---|---|---|---|---|---|---|---|']
    seen = set()
    for pair in pairs.split(','):
        L, L2 = map(int, pair.split(':'))
        for b in betas:
            a, d = get(rundir, L, b), get(rundir, L2, b)
            if a is None or d is None: continue
            for c in (0.3, 0.4):
                u, ue, ta = g2(a, c, False); S, Se, td = g2(d, c, False)
                ut, uet, _ = g2(a, c, True); St, Set, _ = g2(d, c, True)
                R = S / u; Re = R * np.hypot(ue / u, Se / S)
                Rt = St / ut; Rte = Rt * np.hypot(uet / ut, Set / St)
                lines.append(f'| {L}->{L2} | {b:.2f} | {c} | {u:.4f}({ue*1e4:.0f}e-4) | {S:.4f}({Se*1e4:.0f}e-4) | {R:.4f}({Re*1e4:.0f}e-4) | {Rt:.4f}({Rte*1e4:.0f}e-4) | {(R-1)/Re:+.1f} | {u*b:.3f} | {ta:.1f} / {td:.1f} |')
            for (LL, rr) in ((L, a), (L2, d)):
                if (LL, b) in seen: continue
                seen.add((LL, b))
                pf = os.path.join(rundir, f'u1_L{LL}_b{b:.2f}.plaq')
                p = np.array(read_plq(pf)); _, ix = np.unique(p[:, 0], return_index=True); p = p[ix]; p = p[p[:, 0] > rr['therm'], 1]
                pm, pe, pt, _ = gamma_method(p)
                plq.append(f'| {LL} | {b:.2f} | {len(rr["sweep"])} | {pm:.5f}({pe*1e5:.0f}e-5) | {pt:.1f} | {p.min():.4f} | {p.max():.4f} | {kurtosis(p):+.2f} |')
    open(out, 'w').write('\n'.join(lines) + '\n\n' + '\n'.join(plq) + '\n')
    print('\n'.join(lines)); print('\n'.join(plq))

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else '4:8')
