"""Polarization architecture: geometry-only q and B, Brown vs kappa."""
import sys, math, random, time, cmath
sys.path.insert(0, '/home/claude/ym_dig')
from scratch.abk_full import build_all, kap, adm, completes
from scratch.linking_lift import band_polylines, stereo, polyline_lk, brown_fixed
from computations.kappa_system import decomposable
from collections import defaultdict

def components_of(mask, R):
    zm = {e: (s, mid) for (e, s, mid) in R['zm_edges']}
    edges = []
    x = mask
    while x:
        b = x & (-x); e = b.bit_length()-1; x ^= b
        if e in zm: edges.append(e)
    # union-find on nodes
    adj = defaultdict(list)
    for e in edges:
        s, mid = zm[e]
        adj[('z', s)].append((('m', mid), e))
        adj[('m', mid)].append((('z', s), e))
    comps = []
    unused = set(edges)
    while unused:
        e0 = next(iter(unused))
        # walk this component
        s, mid = zm[e0]
        node = ('z', s)
        cmask = 0
        cur = node
        while True:
            nxt = None
            for (n2, e) in adj[cur]:
                if e in unused:
                    nxt = (n2, e); break
            if nxt is None: break
            unused.discard(nxt[1])
            cmask |= (1 << nxt[1])
            cur = nxt[0]
        comps.append(cmask)
    return comps

def q_geo(mask, R, cache):
    if mask in cache: return cache[mask]
    total = 0
    for cm in components_of(mask, R):
        core, loops = band_polylines(cm, R)
        P = [stereo(p) for p in core]
        if len(loops) == 2:
            Q = [stereo(p) for p in loops[0]]
            lk = polyline_lk(P, Q)
            lki = round(lk)
            if abs(lk - lki) > 0.2: cache[mask] = None; return None
            total += 2*lki
        elif len(loops) == 1:
            Q = [stereo(p) for p in loops[0]]
            lk = polyline_lk(P, Q)
            lki = round(lk)
            if abs(lk - lki) > 0.2 or lki % 2 == 0:
                cache[mask] = None; return None
            total += lki
        else:
            cache[mask] = None; return None
    cache[mask] = total % 4
    return total % 4

configs = []
spins = [0]*24
def dfs(fi):
    if fi == 24:
        k = kap(spins)
        if k is not None and not decomposable(spins):
            configs.append((tuple(spins), k))
        return
    for v in (0, 1, 2):
        spins[fi] = v
        if all(adm(*(spins[x] for x in fs)) for _e, fs in completes[fi]):
            dfs(fi+1)
    spins[fi] = 0
dfs(0)
random.seed(21)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 60) + random.sample(pos, 60)

stats = defaultdict(int)
match = mmatch = 0
triple_checks = triple_ok = 0
t0 = time.time()
for sp, k in sample:
    try:
        R = build_all(list(sp))
    except Exception:
        stats['build_exc'] += 1; continue
    if R is None or 'err' in R: stats['build_err'] += 1; continue
    n = R['b1']
    if n == 0: stats['b1_0'] += 1; continue
    if n > 10: stats['b1_big'] += 1; continue
    cache = {}
    g = R['gamma']
    qv = [q_geo(g[i], R, cache) for i in range(n)]
    if any(v is None for v in qv): stats['q_fail'] += 1; continue
    Bm = [[0]*n for _ in range(n)]
    ok = True
    for i in range(n):
        Bm[i][i] = qv[i] % 2
        for j in range(i+1, n):
            qs = q_geo(g[i] ^ g[j], R, cache)
            if qs is None: ok = False; break
            d = (qs - qv[i] - qv[j]) % 4
            if d % 2 != 0: ok = False; break
            Bm[i][j] = Bm[j][i] = (d // 2) % 2
        if not ok: break
    if not ok: stats['B_fail'] += 1; continue
    # triple consistency spot check
    if n >= 3 and triple_checks < 40:
        import itertools as it
        for (i, j, l) in list(it.combinations(range(n), 3))[:2]:
            pred = (qv[i] + qv[j] + qv[l] + 2*(Bm[i][j] + Bm[i][l] + Bm[j][l])) % 4
            got = q_geo(g[i] ^ g[j] ^ g[l], R, cache)
            triple_checks += 1
            if got == pred: triple_ok += 1
    beta = brown_fixed(qv, Bm)
    if beta is None: stats['nonpin'] += 1; continue
    stats['done'] += 1
    target = 4 if k == 1 else 0
    if beta == target: match += 1
    if (8 - beta) % 8 == target: mmatch += 1
    stats[f'b{beta}_k{k}'] += 1
print(f"[{time.time()-t0:.0f}s] {dict(stats)}", flush=True)
print(f"TRIPLE CONSISTENCY: {triple_ok}/{triple_checks}", flush=True)
print(f"MATCH beta=4k: {match}/{stats['done']}   mirror: {mmatch}/{stats['done']}", flush=True)
