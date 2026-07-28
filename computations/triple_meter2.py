"""Triple-consistency meter for the v2 band geometry (target 40/40+)."""
import itertools as it
import random
import sys
import time
from collections import defaultdict

sys.path.insert(0, '/home/claude/ym_dig')

from scratch.abk_full import build_all, kap, adm, completes  # noqa: E402
from computations.kappa_system import decomposable  # noqa: E402
from scratch.band_geometry2 import q_embedded  # noqa: E402

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
print(f"corpus: {len(configs)} configs "
      f"({sum(1 for c in configs if c[1]==1)} kappa-odd)", flush=True)

random.seed(21)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 60) + random.sample(pos, 60)

stats = defaultdict(int)
pair_checks = pair_ok = 0        # parity of B vs polarization oddness
triple_checks = triple_ok = 0
quad_checks = quad_ok = 0
t0 = time.time()
for sp, k in sample:
    try:
        R = build_all(list(sp))
    except Exception:
        stats['build_exc'] += 1
        continue
    if R is None or 'err' in R:
        stats['build_err'] += 1
        continue
    n = R['b1']
    if n == 0:
        stats['b1_0'] += 1
        continue
    if n > 10:
        stats['b1_big'] += 1
        continue
    cache = {}
    g = R['gamma']
    qv = [q_embedded(g[i], R, cache) for i in range(n)]
    if any(v is None for v in qv):
        stats['q_fail'] += 1
        continue
    Bm = [[0] * n for _ in range(n)]
    ok = True
    for i in range(n):
        Bm[i][i] = qv[i] % 2
        for j in range(i + 1, n):
            qs = q_embedded(g[i] ^ g[j], R, cache)
            if qs is None:
                ok = False
                break
            d = (qs - qv[i] - qv[j]) % 4
            if d % 2 != 0:
                ok = False
                stats['odd_polar'] += 1
                break
            pair_checks += 1
            pair_ok += 1
            Bm[i][j] = Bm[j][i] = (d // 2) % 2
        if not ok:
            break
    if not ok:
        stats['B_fail'] += 1
        continue
    stats['done'] += 1
    # triple consistency: q(x+y+z) fully determined by q's and B
    if n >= 3 and triple_checks < 120:
        for (i, j, l) in list(it.combinations(range(n), 3))[:4]:
            pred = (qv[i] + qv[j] + qv[l]
                    + 2 * (Bm[i][j] + Bm[i][l] + Bm[j][l])) % 4
            got = q_embedded(g[i] ^ g[j] ^ g[l], R, cache)
            if got is None:
                stats['triple_geom_fail'] += 1
                continue
            triple_checks += 1
            if got == pred:
                triple_ok += 1
            else:
                stats[f'triple_miss_d{(got-pred) % 4}'] += 1
    # quadruple spot check
    if n >= 4 and quad_checks < 40:
        for (i, j, l, r) in list(it.combinations(range(n), 4))[:2]:
            pred = (qv[i] + qv[j] + qv[l] + qv[r]
                    + 2 * (Bm[i][j] + Bm[i][l] + Bm[i][r]
                           + Bm[j][l] + Bm[j][r] + Bm[l][r])) % 4
            got = q_embedded(g[i] ^ g[j] ^ g[l] ^ g[r], R, cache)
            if got is None:
                continue
            quad_checks += 1
            if got == pred:
                quad_ok += 1
print(f"[{time.time()-t0:.0f}s] {dict(stats)}", flush=True)
print(f"PAIRS consistent (even polarization): {pair_ok}/{pair_checks}",
      flush=True)
print(f"TRIPLE CONSISTENCY: {triple_ok}/{triple_checks}", flush=True)
print(f"QUAD CONSISTENCY:   {quad_ok}/{quad_checks}", flush=True)
