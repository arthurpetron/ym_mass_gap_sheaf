"""Final stage: Brown(q) with local-type lifts vs kappa."""
import sys, random, time, cmath, itertools
sys.path.insert(0, '/home/claude/ym_dig')
from scratch.abk_full import build_all, kap, adm, completes
from computations.kappa_system import decomposable
from computations.vertex_amplitude import sixj_sign_square
from collections import Counter, defaultdict

def brown(qb, Bm):
    """Brown invariant in Z8 of enhancement given by q on basis + B.
    Returns None if Gauss sum vanishes (not Pin-)."""
    n = len(qb)
    gens = [1 << i for i in range(n)]
    def B_of(u, v):
        t = 0
        for i in range(n):
            if (u >> i) & 1:
                for j in range(n):
                    if (v >> j) & 1:
                        t ^= Bm[i][j]
        return t
    def q_of(u):
        val = 0
        idx = [i for i in range(n) if (u >> i) & 1]
        for i in idx:
            val += qb[i]
        for a in range(len(idx)):
            for b in range(a+1, len(idx)):
                val += 2 * Bm[idx[a]][idx[b]]
        return val % 4
    phase = 0.0
    cur = list(gens)
    while cur:
        pair = None
        for i in range(len(cur)):
            for j in range(len(cur)):
                if i != j and B_of(cur[i], cur[j]) == 1:
                    pair = (i, j); break
            if pair: break
        if pair is None:
            for g in cur:
                term = 1 + 1j ** q_of(g)
                if abs(term) < 1e-9:
                    return None
                phase += cmath.phase(term)
            break
        i, j = pair
        x, y = cur[i], cur[j]
        qx, qy = q_of(x), q_of(y)
        blockG = 1 + 1j**qx + 1j**qy + 1j**((qx + qy + 2) % 4)
        if abs(blockG) < 1e-9:
            return None
        phase += cmath.phase(blockG)
        nxt = []
        for k in range(len(cur)):
            if k in (i, j): continue
            z = cur[k]
            if B_of(z, y): z ^= x
            if B_of(z, x): z ^= y
            if z: nxt.append(z)
        # ensure independence: reduce pairwise (cheap: skip; blocks handle)
        cur = nxt
    return round(phase / (2*cmath.pi) * 8) % 8

# gather configs
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
random.seed(11)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
train = random.sample(neg, 40) + random.sample(pos, 40)
valid = random.sample(neg, 200) + random.sample(pos, 200)

# preprocess
def prep(batch):
    out = []
    types = set()
    for sp, k in batch:
        try:
            r = build_all(list(sp))
        except Exception:
            continue
        if r is None or 'err' in r:
            continue
        if r['b1'] == 0:
            out.append((k, [], [[]], []))
            continue
        qb0 = [r['B'][i][i] for i in range(r['b1'])]   # Wu: q2 = diag B
        out.append((k, qb0, r['B'], r['tcounts']))
        for tc in r['tcounts']:
            types.update(tc.keys())
    return out, types

t0 = time.time()
train_p, types1 = prep(train)
valid_p, types2 = prep(valid)
types = sorted(types1 | types2, key=str)
T = len(types)
tid = {t: i for i, t in enumerate(types)}
print(f"prep: train {len(train_p)}, valid {len(valid_p)}, types {T} [{time.time()-t0:.0f}s]", flush=True)
print("types:", types, flush=True)

def test_candidate(rbits, batch):
    bad = 0; nonpin = 0
    for k, qb0, Bm, tcounts in batch:
        n = len(qb0)
        if n == 0:
            if k != 0: bad += 1
            continue
        qb = []
        for i in range(n):
            radd = 0
            for t, c in tcounts[i].items():
                if c & 1 and (rbits >> tid[t]) & 1:
                    radd ^= 1
            qb.append((qb0[i] + 2*radd) % 4)
        beta = brown(qb, Bm)
        if beta is None:
            nonpin += 1
            continue
        target = 4 if k == 1 else 0
        if beta != target:
            bad += 1
    return bad, nonpin

best = []
for rbits in range(1 << T):
    bad, nonpin = test_candidate(rbits, train_p)
    if bad + nonpin <= 8:
        best.append((bad, nonpin, rbits))
best.sort()
print(f"candidates with <=8 train errors: {len(best)}", flush=True)
for bad, nonpin, rbits in best[:6]:
    vb, vn = test_candidate(rbits, valid_p)
    print(f"  r={rbits:0{T}b}: train bad={bad} nonpin={nonpin} | "
          f"valid bad={vb} nonpin={vn} / {len(valid_p)}", flush=True)
if not best:
    # report best achievable
    scores = []
    for rbits in range(1 << T):
        bad, nonpin = test_candidate(rbits, train_p)
        scores.append((bad + nonpin, rbits))
    scores.sort()
    print("best train scores:", scores[:6], flush=True)
    # also: beta census for r=0
    cen = defaultdict(Counter)
    for k, qb0, Bm, tcounts in train_p:
        b = brown(qb0, Bm) if qb0 else 0
        cen[k][b] += 1
    print("beta census (r=0) by kappa:", {k: dict(v) for k, v in cen.items()}, flush=True)
