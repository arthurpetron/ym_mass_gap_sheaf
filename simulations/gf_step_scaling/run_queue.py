#!/usr/bin/env python3
"""Idempotent job queue: each line of JOBFILE is `name|args...`; runs `BIN args --out OUTDIR/name` with nice -n 19,
at most MAXP at once (default 3, never > 4). Binaries checkpoint and resume, finished jobs are no-ops.
Usage: run_queue.py JOBFILE OUTDIR [MAXP]"""
import subprocess, sys, time, os, shlex
jobfile, outdir = sys.argv[1], sys.argv[2]
maxp = min(4, int(sys.argv[3]) if len(sys.argv) > 3 else 3)
BIN = '/Users/darthur/ym_numerics_runs/target/release/'
os.makedirs(outdir, exist_ok=True)
jobs = [l.strip().split('|', 1) for l in open(jobfile) if l.strip() and not l.startswith('#')]
running = []
log = open(os.path.join(outdir, 'queue.log'), 'a')
def say(s): log.write(time.strftime('%F %T ') + s + '\n'); log.flush()
say(f'queue start jobs={len(jobs)} maxp={maxp}')
for name, cmd in jobs:
    while len(running) >= maxp:
        running = [(n, p) for n, p in running if p.poll() is None]
        time.sleep(5)
    exe, *rest = shlex.split(cmd)
    full = ['nice', '-n', '19', BIN + exe] + rest + ['--out', os.path.join(outdir, name)]
    p = subprocess.Popen(full, stdout=open(os.path.join(outdir, name + '.stdout'), 'a'), stderr=open(os.path.join(outdir, name + '.stderr'), 'a'))
    running.append((name, p)); say(f'launched {name} pid={p.pid}')
for n, p in running:
    p.wait(); say(f'finished {n} rc={p.returncode}')
say('queue end')
