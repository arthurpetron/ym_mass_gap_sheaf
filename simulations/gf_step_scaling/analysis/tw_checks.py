#!/usr/bin/env python3
"""Twisted-box GF production (prod5, jobs_tw.txt, 't Hooft twist n_12 = 1, Wilson action + Wilson flow + clover E, cold = twist-eater start):
completeness, thermalisation, autocorrelation, topology, CPU-h and guard-log resource summary.
usage: tw_checks.py OUTPREFIX [RUNDIR] [JOBFILE]
Completeness per job: NAME.csv has exactly n_meas data rows, indices 0..n-1 unique (duplicates after a resume must be bit-identical), one header pair
carrying twist=n12, constant 9 columns, last sweep = therm + (n-1) sep, NAME.plaq has therm + (n-1) sep sweeps, stderr ends at meas=N/N without errors,
and the queue.log 'finished NAME rc=' line (run_queue.py logs rc only for the jobs still running when the launch loop ends).
Thermalisation: first/second-half z (Gamma-method errors) of g2_TGF (c=0.3, 0.4) and plaquette, tau_int, quarter means (L=24), chain-vs-chain z for the
two L=24 chains per beta; topology: flowed clover Q at c=0.3/0.4 (max|Q|, fraction |round Q| >= 1, # sector changes); cold-start plaquette history.
g2_TGF = t^2 <E_clover> / Nhat_T(c, L) (twist_norm.N_twist_lat).  MC evidence only."""
import sys, os, re, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfana import load_run, time_index, gamma_method
from twist_norm import N_twist_lat
pref = sys.argv[1]
R = sys.argv[2] if len(sys.argv) > 2 else '/Users/darthur/ym_numerics_runs/prod5'
JF = sys.argv[3] if len(sys.argv) > 3 else os.path.join(R, 'jobs_tw.txt')
jobs = [l.strip().split('|', 1) for l in open(JF) if l.strip() and not l.startswith('#')]
qlog = open(os.path.join(R, 'queue.log')).read()
md = ['# Twisted-box GF production (prod5): completeness, thermalisation, topology, resources (tw_checks.py)\n', f'run dir {R}, job file {JF}, {len(jobs)} jobs. MC evidence only.\n',
      '## Completeness\n', '| job | n_meas | rows | uniq idx | dup rows (identical?) | headers (twist=n12) | ncol | last sweep (exp) | plaq sweeps (exp) | stderr last | elapsed s | queue.log | OK |', '|---|---|---|---|---|---|---|---|---|---|---|---|---|']
allok = True; cpu = 0.0; T = []; nofin = []
def parse(path):
    hdr = []; rows = []; ncols = set()
    for line in open(path):
        if line.startswith('#'): hdr.append(line); continue
        if not line.strip(): continue
        f = line.split(); ncols.add(len(f)); rows.append(f)
    return hdr, rows, ncols
for name, cmd in jobs:
    a = dict(re.findall(r'--(\S+) (\S+)', cmd)); n = int(a['nmeas']); th = int(a['therm']); sep = int(a['sep'])
    w = os.path.join(R, name + '.csv'); p = os.path.join(R, name + '.plaq'); se = os.path.join(R, name + '.stderr')
    hw, rw, cw = parse(w)
    d = {}; dup = 0; same = True
    for f in rw:
        k = int(f[0])
        if k in d: dup += 1; same &= (d[k] == f)
        d[k] = f
    idx_ok = sorted(d) == list(range(n))
    last = int(d[n - 1][1]) if (n - 1) in d else -1; exp_last = th + (n - 1) * sep
    np_ = sum(1 for l in open(p) if l.strip())
    sl = [l for l in open(se) if l.strip()]; lastl = sl[-1].strip() if sl else ''
    m = re.search(r'meas=(\d+)/(\d+).*elapsed=([\d.]+)s', lastl); el = float(m.group(3)) if m else float('nan')
    st_ok = bool(m) and int(m.group(1)) == n == int(m.group(2)) and not any(('panic' in l or 'rror' in l) for l in sl)
    tw_ok = len(hw) == 2 and 'twist=n12' in hw[0] and f'seed={a["seed"]}' in hw[0]
    fm = re.search(rf'finished {re.escape(name)} rc=(-?\d+)', qlog); ql = f'rc={fm.group(1)}' if fm else 'no finished line'
    if not fm: nofin.append(name)
    rc_ok = (fm is None) or fm.group(1) == '0'
    ok = len(d) == n and idx_ok and same and tw_ok and cw == {9} and last == exp_last and np_ == exp_last and st_ok and rc_ok
    allok &= ok; cpu += el if m else 0; T.append((name, el))
    md.append(f"| {name} | {n} | {len(rw)} | {len(d)} | {dup} ({'yes' if same else 'NO'}) | {len(hw)} ({'yes' if tw_ok else 'NO'}) | {sorted(cw)} | {last} ({exp_last}) | {np_} ({exp_last}) | meas={m.group(1)}/{m.group(2)} | {el:.0f} | {ql} | {'OK' if ok else 'FAIL'} |")
md.append(f"\n**All {len(jobs)} jobs complete from the outputs: {'YES' if allok else 'NO'}.** queue.log has a 'finished ... rc=' line for {len(jobs)-len(nofin)} of {len(jobs)} jobs (all rc=0); "
          f"no 'finished' line for {len(nofin)} jobs ({', '.join(nofin)}): run_queue.py only waits on (and logs) the jobs still running when its launch loop ends; the others were reaped by poll() without a log line, so their rc is not recorded and their completion rests on the outputs above.\n")
byL = {}
for nm, el in T: L = int(re.search(r'L(\d+)', nm).group(1)); byL[L] = byL.get(L, 0) + el
md.append(f"CPU time (sum of per-process elapsed at the final stderr line; single-threaded niced processes; upper bound since any SIGSTOP time would count): **{cpu/3600:.2f} CPU-h** (" + ', '.join(f'L={L}: {v/3600:.2f}' for L, v in sorted(byL.items(), reverse=True)) + ')\n')
# ---- guard log
G = [l for l in open(os.path.join(R, 'resource_guard_tw.log')) if not l.startswith('#')]
gl = [dict(re.findall(r'([\w,]+)=(\S+)', l)) for l in G]
ld = np.array([float(x['load1']) for x in gl]); fp = np.array([float(x['freepct']) for x in gl]); npc = np.array([int(x['nproc']) for x in gl]); stt = [x['state'] for x in gl]
pg = np.array([[int(v) for v in x['pages_free,inactive'].split(',')] for x in gl]); fi_gib = pg.sum(1) * 16384 / 2 ** 30
t0 = G[0][:19]; t1 = G[-1][:19]
cnt = {int(k): int((npc == k).sum()) for k in sorted(set(npc))}
gs = dict(samples=len(gl), first=t0, last=t1, load_min=ld.min(), load_max=ld.max(), load_mean=ld.mean(), load_gt16=int((ld > 16).sum()), free_min=fp.min(), free_max=fp.max(),
          freeinact_min_gib=fi_gib.min(), nproc_counts=cnt, run=stt.count('run'), throttled=sum(s.startswith('throttled') for s in stt), paused=sum(s.startswith('paused') for s in stt))
md.append(f"Guard log `resource_guard_tw.log` (30 s): {gs['samples']} samples {t0} - {t1} PDT; load1 min {gs['load_min']:.2f} / max {gs['load_max']:.2f} / mean {gs['load_mean']:.2f} (> 16 in {gs['load_gt16']} samples); "
          f"free RAM (memory_pressure) min {gs['free_min']:.0f}% / max {gs['free_max']:.0f}% (free+inactive pages >= {gs['freeinact_min_gib']:.1f} GiB); our processes: " + ', '.join(f'{k} in {v}' for k, v in cnt.items()) +
          f"; state run {gs['run']}, throttled {gs['throttled']} ({100*gs['throttled']/len(gl):.1f}%), paused {gs['paused']} ({100*gs['paused']/len(gl):.1f}%).\n")
# ---- thermalisation / topology
md.append('## Thermalisation / autocorrelation / topology (L=24 first)\n')
md.append('| job | obs | mean | Gamma err | tau_int | 1st half | 2nd half | z | quarter means (L=24) |'); md.append('|---|---|---|---|---|---|---|---|---|')
zs = []; TOP = []; therm_rows = []; L24 = {}
for name, cmd in sorted(jobs, key=lambda j: (-int(re.search(r'L(\d+)', j[0]).group(1)), j[0])):
    r = load_run(os.path.join(R, name + '.csv'), 3); L = r['L']; b = r['beta']
    obs = []
    for c in (0.3, 0.4):
        i = time_index(r, c); t = r['times'][i]; obs.append((f'g2 c={c}', t * t * r['E'][:, i, 0] / N_twist_lat(c, L)))
    obs.append(('plaquette', r['plaq']))
    if L == 24: L24.setdefault(b, []).append((name, obs))
    for lab, x in obs:
        n = len(x); h = n // 2
        mm, e, tau, W = gamma_method(x); a_, ea = gamma_method(x[:h])[:2]; b_, eb = gamma_method(x[h:])[:2]; zz = (b_ - a_) / np.hypot(ea, eb); zs.append((name, lab, zz))
        qm = ', '.join(f'{v:.4f}' for v in [x[k * n // 4:(k + 1) * n // 4].mean() for k in range(4)]) if L == 24 else ''
        md.append(f"| {name} | {lab} | {mm:.5f} | {e:.5f} | {tau:.2f} | {a_:.5f}({ea*1e5:.0f}) | {b_:.5f}({eb*1e5:.0f}) | {zz:+.2f} | {qm} |")
    for c in (0.3, 0.4):
        q = r['E'][:, time_index(r, c), 2]; rq = np.rint(q)
        TOP.append((name, c, np.abs(q).max(), float((np.abs(rq) >= 1).mean()), int((np.diff(rq) != 0).sum()), float(np.mean(q)), float(np.mean(q * q))))
    ph = np.loadtxt(os.path.join(R, name + '.plaq')); th = int(re.search(r'--therm (\d+)', cmd).group(1))
    therm_rows.append((name, ph[0, 1], ph[: th // 3, 1].mean(), ph[th // 3: 2 * th // 3, 1].mean(), ph[2 * th // 3: th, 1].mean(), ph[th - 100:th, 1].mean(), r['plaq'].mean(), gamma_method(r['plaq'])[1]))
za = np.array([abs(z) for _, _, z in zs]); worst = sorted(zs, key=lambda t: -abs(t[2]))[:8]
md.append(f"\nFirst/second-half |z| over {len(zs)} (job, observable) values: max {za.max():.2f}, # |z|>2: {(za>2).sum()} (expected ~{0.0455*len(za):.1f} for independent Gaussian noise; c=0.3/0.4 are strongly correlated), # |z|>3: {(za>3).sum()}. Largest: " + ', '.join(f'{n} {l} {z:+.2f}' for n, l, z in worst))
md.append('\n## L=24: the two independent chains per beta (twa/twb), chain-vs-chain z\n')
md.append('| beta | obs | chain a | chain b | z(b-a) |'); md.append('|---|---|---|---|---|')
CC = {}
for b, chs in sorted(L24.items()):
    if len(chs) < 2: continue
    for k in range(3):
        (na, oa), (nb, ob) = chs[0], chs[1]
        ma, ea = gamma_method(oa[k][1])[:2]; mb, eb = gamma_method(ob[k][1])[:2]; z = (mb - ma) / np.hypot(ea, eb); CC[(b, oa[k][0])] = z
        md.append(f'| {b:g} | {oa[k][0]} | {ma:.5f}({ea*1e5:.0f}) | {mb:.5f}({eb*1e5:.0f}) | {z:+.2f} |')
md.append('\n## Topology (flowed clover Q at t = c^2 L^2/8; with twist n_12 = 1 only, the twist Pfaffian n_12 n_34 = 0, so Q is integer-valued in the continuum; rounded Q is a sector proxy)\n')
md.append('| job | c | max|Q| | frac |round Q|>=1 | # sector changes | <Q> | <Q^2> |'); md.append('|---|---|---|---|---|---|---|')
for nm, c, mq, fr, ch, mQ, q2 in TOP: md.append(f'| {nm} | {c} | {mq:.2e} | {fr:.3f} | {ch} | {mQ:+.1e} | {q2:.1e} |')
md.append(f"\nmax|Q| over all jobs and both c: {max(t[2] for t in TOP):.3e}; at L=24: {max(t[2] for t in TOP if '_L24_' in t[0]):.3e}; jobs with any |round Q| >= 1: {sorted(set(t[0] for t in TOP if t[3] > 0)) or 'none'}")
md.append('\n## Cold (twist-eater) start: plaquette history (.plaq, one value per sweep)\n')
md.append('| job | sweep 1 | therm thirds (mean) | last 100 therm sweeps | measurement mean (Gamma err) | last-100-therm minus meas |'); md.append('|---|---|---|---|---|---|')
for nm, p1, t1_, t2_, t3_, pl, pm, pme in therm_rows:
    md.append(f'| {nm} | {p1:.4f} | {t1_:.5f} / {t2_:.5f} / {t3_:.5f} | {pl:.5f} | {pm:.5f}({pme*1e5:.0f}) | {pl-pm:+.5f} |')
open(pref + '.md', 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))
json.dump(dict(complete=bool(allok), no_finished_line=nofin, cpu_h=cpu / 3600, cpu_h_byL={str(k): v / 3600 for k, v in byL.items()}, guard=gs,
               zmax=float(za.max()), n_z_gt2=int((za > 2).sum()), n_z=len(za), worst=[(n, l, float(z)) for n, l, z in worst], chain_z={f'{b}|{o}': float(z) for (b, o), z in CC.items()},
               maxQ=float(max(t[2] for t in TOP)), maxQ24=float(max(t[2] for t in TOP if '_L24_' in t[0]))), open(pref + '.json', 'w'), indent=1, default=float)
