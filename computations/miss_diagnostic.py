"""Which feature of the composite predicts the d2 triple miss?

For each triple (i,j,l): miss bit = (q_geo(x^y^z) - predicted) / 2 mod 2.
Candidate parity features of the composite representative (and of the
three pairs), all computed from the same traversal the geometry uses:

  A: # connectors with antipodal pushes (pd_in = -pd_out)
  P: # connectors with perpendicular pushes (pd_in . pd_out = 0)
  V: # revisited sheets (degree >= 4)
  C: # components
  K: # clashed seams crossed
  S: # seams crossed (arcs)

We test every small F2-linear combination of feature parities against
the miss bit, on every triple the geometry completes.
"""
import itertools as it
import random
import sys
import time
from collections import defaultdict

import numpy as np

sys.path.insert(0, '/home/claude/ym_dig')

from scratch.abk_full import build_all, kap, adm, completes  # noqa: E402
from computations.kappa_system import decomposable  # noqa: E402
import scratch.band_geometry2 as bg  # noqa: E402

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
random.seed(21)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 60) + random.sample(pos, 60)


def features(mask, R):
    cycles = bg.traverse(mask, R)
    A = P = V = K = S = 0
    zm = {e: (s, mid) for (e, s, mid) in R['zm_edges']}
    # revisited sheets
    deg = defaultdict(int)
    x = mask
    while x:
        b = x & (-x)
        e = b.bit_length() - 1
        x ^= b
        s, mid = zm[e]
        deg[s] += 1
    V = sum(1 for s, d in deg.items() if d >= 4)
    for arcs in cycles:
        nA = len(arcs)
        S += nA
        for ai, (s, m_in, m_out) in enumerate(arcs):
            s2 = arcs[(ai + 1) % nA][0]
            pd1 = bg.push_dir(*s)
            pd2 = bg.push_dir(*s2)
            d = float(np.dot(pd1, pd2))
            if d < -0.5:
                A += 1
            elif abs(d) < 0.5:
                P += 1
            K ^= bg.parity_of_edges(arcs, R) if ai == 0 else 0
        # K accumulated once per cycle via parity; recompute properly:
    # clash count (not parity) over all crossed seams
    K = 0
    for arcs in cycles:
        for (s, m_in, m_out) in arcs:
            K += R['seams'][m_out]['clash']
    C = len(cycles)
    return dict(A=A, P=P, V=V, C=C, K=K, S=S)


rows = []
t0 = time.time()
for sp, k in sample:
    try:
        R = build_all(list(sp))
    except Exception:
        continue
    if R is None or 'err' in R:
        continue
    n = R['b1']
    if n == 0 or n > 10:
        continue
    cache = {}
    g = R['gamma']
    qv = [bg.q_embedded(g[i], R, cache) for i in range(n)]
    if any(v is None for v in qv):
        continue
    Bm = [[0] * n for _ in range(n)]
    ok = True
    for i in range(n):
        Bm[i][i] = qv[i] % 2
        for j in range(i + 1, n):
            qs = bg.q_embedded(g[i] ^ g[j], R, cache)
            if qs is None or (qs - qv[i] - qv[j]) % 2:
                ok = False
                break
            Bm[i][j] = Bm[j][i] = ((qs - qv[i] - qv[j]) % 4) // 2
        if not ok:
            break
    if not ok:
        continue
    if n < 3:
        continue
    for (i, j, l) in list(it.combinations(range(n), 3))[:4]:
        comp = g[i] ^ g[j] ^ g[l]
        got = bg.q_embedded(comp, R, cache)
        if got is None:
            continue
        pred = (qv[i] + qv[j] + qv[l]
                + 2 * (Bm[i][j] + Bm[i][l] + Bm[j][l])) % 4
        miss = ((got - pred) % 4) // 2
        try:
            F = features(comp, R)
            # also pair and generator features, for difference features
            Fg = [features(g[t], R) for t in (i, j, l)]
        except ValueError:
            continue
        row = dict(miss=miss)
        for key in ('A', 'P', 'V', 'C', 'K', 'S'):
            row[key] = F[key]
            row['d' + key] = F[key] - sum(f[key] for f in Fg)
        rows.append(row)
        if len(rows) % 40 == 0:
            print(f"  ...{len(rows)} triples [{time.time()-t0:.0f}s]",
                  flush=True)

print(f"triples collected: {len(rows)}; misses: {sum(r['miss'] for r in rows)}",
      flush=True)
keys = [k for k in rows[0] if k != 'miss']
best = []
for r in range(1, 4):
    for combo in it.combinations(keys, r):
        good = sum(1 for row in rows
                   if sum(row[k] for k in combo) % 2 == row['miss'])
        best.append((good, combo))
best.sort(reverse=True)
for good, combo in best[:12]:
    print(f"  {good}/{len(rows)}  parity of {'+'.join(combo)}")
