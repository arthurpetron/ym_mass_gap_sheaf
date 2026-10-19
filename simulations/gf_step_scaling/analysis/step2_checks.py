#!/usr/bin/env python3
"""Step 2 (Zeuthen vs Wilson flow, prod4 *_z1p9/_z2p4/_z2p9): completeness, thermalisation, autocorrelation and topology checks,
and CPU-hours.  usage: step2_checks.py OUT.md [RUNDIR] [JOBFILE]
Completeness per job: NAME.csv (Wilson flow) and NAME.zeu.csv (Zeuthen flow) each have exactly n_meas data rows, indices 0..n-1 unique
(duplicates after a resume must be bit-identical), one header pair, constant column count, last sweep = therm + (n-1) sep, identical
(meas, sweep, plaquette) columns in both files (same configurations), NAME.plaq has therm + (n-1) sep sweeps, stderr ends at meas=N/N.
Thermalisation: first- vs second-half z (Gamma-method errors) for g2 (both flows, c=0.3/0.4) and the plaquette; tau_int (samples);
max|Q| (flowed clover Q at c=0.3 and 0.4, both flows); cold-start plaquette history (.plaq: mean of the last 100 therm sweeps vs measurement mean).
MC evidence only."""
import sys, os, re, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfana import load_run, time_index, N_lat, gamma_method
from zeuthen_norm import N_zeu
out = sys.argv[1]
R = sys.argv[2] if len(sys.argv) > 2 else '/Users/darthur/ym_numerics_runs/prod4'
JF = sys.argv[3] if len(sys.argv) > 3 else os.path.join(R, 'jobs_step2.txt')
jobs = [l.strip().split('|', 1) for l in open(JF) if l.strip() and not l.startswith('#')]
md = ['# Step 2 checks: completeness, thermalisation, tau_int, topology, CPU-h (step2_checks.py)\n', f'run dir {R}, job file {JF}, {len(jobs)} jobs\n',
      '## Completeness\n', '| job | n_meas | rows W | rows Z | uniq idx W/Z | dup rows (identical?) | headers W/Z | ncol | last sweep (exp) | W/Z same configs | plaq sweeps (exp) | stderr last | elapsed s | OK |', '|---|---|---|---|---|---|---|---|---|---|---|---|---|---|']
allok = True; cpu = 0.0; T = []
def parse(path, ncol):
    hdr = 0; rows = []; ncols = set()
    for line in open(path):
        if line.startswith('#'): hdr += 1; continue
        if not line.strip(): continue
        f = line.split(); ncols.add(len(f)); rows.append(f)
    return hdr, rows, ncols
for name, cmd in jobs:
    a = dict(re.findall(r'--(\S+) (\S+)', cmd)); n = int(a['nmeas']); th = int(a['therm']); sep = int(a['sep'])
    w = os.path.join(R, name + '.csv'); z = os.path.join(R, name + '.zeu.csv'); p = os.path.join(R, name + '.plaq'); se = os.path.join(R, name + '.stderr')
    hw, rw, cw = parse(w, 3); hz, rz, cz = parse(z, 3)
    def uniq(rows):
        d = {}; dup = 0; same = True
        for f in rows:
            k = int(f[0])
            if k in d: dup += 1; same &= (d[k] == f)
            d[k] = f
        return d, dup, same
    dw, dupw, sw = uniq(rw); dz, dupz, sz = uniq(rz)
    idx_ok = sorted(dw) == list(range(n)) and sorted(dz) == list(range(n))
    last = int(dw[n - 1][1]) if (n - 1) in dw else -1; exp_last = th + (n - 1) * sep
    same_cfg = all(dw[k][:3] == dz[k][:3] for k in range(n)) if idx_ok else False
    np_ = sum(1 for _ in open(p)); exp_p = exp_last
    sl = [l for l in open(se) if l.strip()]; lastl = sl[-1].strip() if sl else ''
    m = re.search(r'meas=(\d+)/(\d+).*elapsed=([\d.]+)s', lastl); el = float(m.group(3)) if m else float('nan')
    st_ok = bool(m) and int(m.group(1)) == n == int(m.group(2)) and not any(('panic' in l or 'rror' in l) for l in sl)
    ok = (len(dw) == n and len(dz) == n and idx_ok and sw and sz and hw == 2 and hz == 2 and cw == {9} and cz == {9} and last == exp_last and same_cfg and np_ == exp_p and st_ok)
    allok &= ok; cpu += el if m else 0
    T.append((name, el))
    md.append(f"| {name} | {n} | {len(rw)} | {len(rz)} | {len(dw)}/{len(dz)} | {dupw}/{dupz} ({'yes' if sw and sz else 'NO'}) | {hw}/{hz} | {sorted(cw|cz)} | {last} ({exp_last}) | {'yes' if same_cfg else 'NO'} | {np_} ({exp_p}) | meas={m.group(1)}/{m.group(2)} | {el:.0f} | {'OK' if ok else 'FAIL'} |")
md.append(f"\n**All {len(jobs)} jobs complete: {'YES' if allok else 'NO'}.**\n")
byL = {}
for nm, el in T: L = int(re.search(r'L(\d+)', nm).group(1)); byL[L] = byL.get(L, 0) + el
md.append(f"CPU time (sum of per-process elapsed at the final stderr line; single-threaded niced processes, never throttled/paused per the guard log, so wall ~ CPU; upper bound): **{cpu/3600:.2f} CPU-h** (" + ', '.join(f'L={L}: {v/3600:.2f}' for L, v in sorted(byL.items(), reverse=True)) + ')\n')
# thermalisation
md.append('## Thermalisation / autocorrelation / topology (all jobs; L=24 first)\n')
md.append('| job | obs | mean | Gamma err | tau_int | 1st half | 2nd half | z | max|Q| W c=0.3/0.4 | max|Q| Z c=0.3/0.4 |'); md.append('|---|---|---|---|---|---|---|---|---|---|')
zs = []; therm_rows = []
for name, cmd in sorted(jobs, key=lambda j: -int(re.search(r'L(\d+)', j[0]).group(1))):
    rw = load_run(os.path.join(R, name + '.csv'), 3); rz = load_run(os.path.join(R, name + '.zeu.csv'), 3); L = rw['L']
    obs = []
    for lab, r, norm in (('W', rw, N_lat), ('Z', rz, N_zeu)):
        for c in (0.3, 0.4):
            i = time_index(r, c); t = r['times'][i]; obs.append((f'g2_{lab} c={c}', t * t * r['E'][:, i, 0] / norm(c, L)))
    obs.append(('plaquette', rw['plaq']))
    qW = [np.abs(rw['E'][:, time_index(rw, c), 2]).max() for c in (0.3, 0.4)]; qZ = [np.abs(rz['E'][:, time_index(rz, c), 2]).max() for c in (0.3, 0.4)]
    for lab, x in obs:
        n = len(x); h = n // 2
        mm, e, tau, W = gamma_method(x); a, ea = gamma_method(x[:h])[:2]; b, eb = gamma_method(x[h:])[:2]; zz = (b - a) / np.hypot(ea, eb); zs.append((name, lab, zz))
        md.append(f"| {name} | {lab} | {mm:.5f} | {e:.5f} | {tau:.2f} | {a:.5f}({ea*1e5:.0f}) | {b:.5f}({eb*1e5:.0f}) | {zz:+.2f} | {qW[0]:.1e}/{qW[1]:.1e} | {qZ[0]:.1e}/{qZ[1]:.1e} |")
    # cold-start plaquette history
    ph = np.loadtxt(os.path.join(R, name + '.plaq'))
    th = int(re.search(r'--therm (\d+)', cmd).group(1))
    therm_rows.append((name, ph[0, 1], ph[th - 100:th, 1].mean(), ph[th - 100:th, 1].std() / 10, rw['plaq'].mean(), gamma_method(rw['plaq'])[1],
                       ph[: th // 3, 1].mean(), ph[th // 3: 2 * th // 3, 1].mean(), ph[2 * th // 3: th, 1].mean()))
za = np.array([abs(z) for _, _, z in zs]); worst = sorted(zs, key=lambda t: -abs(t[2]))[:6]
md.append(f"\nFirst/second-half |z| over {len(zs)} (job, observable) values: max {za.max():.2f}, # with |z|>2: {(za>2).sum()} (expected ~{0.0455*len(za):.1f} for Gaussian noise, correlated observables), # with |z|>3: {(za>3).sum()}. Largest: " + ', '.join(f'{n} {l} {z:+.2f}' for n, l, z in worst))
md.append('\n## Cold-start plaquette history (.plaq, one value per sweep)\n')
md.append('| job | sweep 1 | therm thirds (mean) | last 100 therm sweeps | measurement mean (Gamma err) | last-100-therm minus meas |'); md.append('|---|---|---|---|---|---|')
for nm, p1, pl, pe, pm, pme, t1, t2, t3 in therm_rows:
    md.append(f'| {nm} | {p1:.4f} | {t1:.5f} / {t2:.5f} / {t3:.5f} | {pl:.5f} | {pm:.5f}({pme*1e5:.0f}) | {pl-pm:+.5f} |')
open(out, 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))
