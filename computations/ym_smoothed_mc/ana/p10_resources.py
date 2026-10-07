"""Summarize a sampler resources.log (30-s samples): min/mean/max MemAvailable, load1, job CPU/RSS, threads, throttle/pause events."""
import sys, numpy as np
rows, ev = [], []
for l in open(sys.argv[1]):
    if l.startswith('# ') and any(k in l for k in ('THROTTLE', 'RESTORE', 'PAUSE', 'RESUME', 'ended')): ev.append(l[2:].strip())
    elif not l.startswith('#') and len(l.split()) == 11: rows.append(l.split())
av = np.array([int(r[2]) for r in rows]); l1 = np.array([float(r[4]) for r in rows]); cpu = np.array([float(r[7]) for r in rows]); rss = np.array([int(r[8]) for r in rows]); th = np.array([int(r[9]) for r in rows]); pz = np.array([int(r[10]) for r in rows])
print(f"| samples | span | MemAvailable min/mean/max (MB) | load1 min/mean/max | job CPU mean/max (%) | job RSS max (MB) | samples at reduced threads | samples paused |")
print("|---|---|---|---|---|---|---|---|")
print(f"| {len(rows)} | {rows[0][0]}–{rows[-1][0]} | {av.min()} / {av.mean():.0f} / {av.max()} | {l1.min():.2f} / {l1.mean():.2f} / {l1.max():.2f} | {cpu.mean():.0f} / {cpu.max():.0f} | {rss.max()} | {(th < th.max()).sum()} | {pz.sum()} |")
print("\nEvents: " + ("; ".join(ev) if ev else "none"))
