"""ABK verdict, correlation mode: beta vs 4*kappa on vote-gated geometry.

The v2 band geometry passes ~71% of triple-consistency checks with a
systematic d2 defect (see miss_diag).  A per-config verdict is
therefore NOISY; this run measures the CORRELATION of Brown(q, B)
with 4*kappa mod 8 over a large sample, under both mirror conventions.
Random-mod-8 baseline for a match is 12.5%; for the even sublattice
(beta is always even here if q even...) baseline 25%.

Checkpointed; safe to kill and resume.
"""
import itertools as it
import json
import os
import random
import sys
import time
from collections import defaultdict

sys.path.insert(0, '/home/claude/ym_dig')

from scratch.abk_full import build_all, kap, adm, completes  # noqa: E402
from computations.kappa_system import decomposable  # noqa: E402
import scratch.band_geometry2 as bg  # noqa: E402
from scratch.linking_lift import brown_fixed  # noqa: E402

CKPT = '/home/claude/ym_dig/scratch/abk_verdict2_ckpt.json'

configs = []
spins = [0] * 24


def dfs(fi):
    if fi == 24:
        k = kap(spins)
        if k is not None and not decomposable(spins):
            configs.append((tuple(spins), k))
        return
    for v in (0, 1, 2):
        spins[fi] = v
        if all(adm(*(spins[x] for x in fs)) for _e, fs in completes[fi]):
            dfs(fi + 1)
    spins[fi] = 0


dfs(0)
random.seed(99)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 150) + random.sample(pos, 150)
random.shuffle(sample)

state = {"i": 0, "rows": []}
if os.path.exists(CKPT):
    state = json.load(open(CKPT))

t0 = time.time()
for idx in range(state["i"], len(sample)):
    sp, k = sample[idx]
    state["i"] = idx + 1
    row = {"kappa": k}
    try:
        R = build_all(list(sp))
    except Exception:
        row["fail"] = "build"
        state["rows"].append(row)
        continue
    if R is None or 'err' in R:
        row["fail"] = "build"
        state["rows"].append(row)
        continue
    n = R['b1']
    row["b1"] = n
    if n == 0:
        row["beta"] = 0
        state["rows"].append(row)
        continue
    if n > 12:
        row["fail"] = "b1_big"
        state["rows"].append(row)
        continue
    cache = {}
    g = R['gamma']
    qv = [bg.q_embedded(g[i2], R, cache) for i2 in range(n)]
    if any(v is None for v in qv):
        row["fail"] = "q"
        state["rows"].append(row)
        continue
    Bm = [[0] * n for _ in range(n)]
    ok = True
    for i2 in range(n):
        Bm[i2][i2] = qv[i2] % 2
        for j2 in range(i2 + 1, n):
            qs = bg.q_embedded(g[i2] ^ g[j2], R, cache)
            if qs is None or (qs - qv[i2] - qv[j2]) % 2:
                ok = False
                break
            Bm[i2][j2] = Bm[j2][i2] = ((qs - qv[i2] - qv[j2]) % 4) // 2
        if not ok:
            break
    if not ok:
        row["fail"] = "B"
        state["rows"].append(row)
        continue
    beta = brown_fixed(qv, Bm)
    if beta is None:
        row["fail"] = "nonpin"
        state["rows"].append(row)
        continue
    row["beta"] = beta
    state["rows"].append(row)
    if (idx + 1) % 10 == 0:
        json.dump(state, open(CKPT, 'w'))
        done = [r for r in state["rows"] if "beta" in r]
        mp = sum(1 for r in done if r["beta"] == (4 if r["kappa"] else 0))
        mm = sum(1 for r in done
                 if (8 - r["beta"]) % 8 == (4 if r["kappa"] else 0))
        print(f"[{time.time()-t0:.0f}s] {idx+1}/{len(sample)} "
              f"done={len(done)} beta=4k: {mp}/{len(done)} "
              f"mirror: {mm}/{len(done)}", flush=True)

json.dump(state, open(CKPT, 'w'))
done = [r for r in state["rows"] if "beta" in r]
hist = defaultdict(int)
for r in done:
    hist[(r["beta"], r["kappa"])] += 1
print("FINAL beta x kappa histogram:", dict(hist), flush=True)
mp = sum(1 for r in done if r["beta"] == (4 if r["kappa"] else 0))
mm = sum(1 for r in done if (8 - r["beta"]) % 8 == (4 if r["kappa"] else 0))
print(f"MATCH beta=4kappa: {mp}/{len(done)}   mirror: {mm}/{len(done)}",
      flush=True)
fails = defaultdict(int)
for r in state["rows"]:
    if "fail" in r:
        fails[r["fail"]] += 1
print("failures:", dict(fails), flush=True)
