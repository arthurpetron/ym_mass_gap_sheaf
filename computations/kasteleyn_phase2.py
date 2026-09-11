"""Phase 2: skeleton-graph Kasteleyn ansatz, magnitude alphabet."""
import sys, random, itertools, time
sys.path.insert(0, '/home/claude/ym_dig')
from computations.vertex_amplitude import sixj_sign_square, vertex_labels, VERTS
from computations.hypercube4d_survey import hypercube

cx, faces, meta = hypercube()
edge_faces = {}
for fi, f in enumerate(faces):
    for ei, _o in f:
        edge_faces.setdefault(ei, []).append(fi)
for ei in edge_faces:
    edge_faces[ei] = sorted(edge_faces[ei])

def matchings_with_signs(n, edges):
    adj = {}
    for (i, j) in edges:
        adj.setdefault(i, set()).add(j)
        adj.setdefault(j, set()).add(i)
    out = []
    def rec(active, sign, acc):
        if not active:
            out.append((sign, tuple(acc)))
            return
        i = active[0]
        rest = active[1:]
        for j in [x for x in rest if x in adj.get(i, ())]:
            jpos = rest.index(j)
            rec([x for x in rest if x != j], sign * ((-1) ** jpos), acc + [(i, j)])
    rec(list(range(n)), 1, [])
    return out

edge_of_pair = {}
for ei, (a, b) in enumerate(cx.edges):
    edge_of_pair[(a, b)] = ei
    edge_of_pair[(b, a)] = ei
M2 = matchings_with_signs(16, [tuple(e) for e in cx.edges])
print(f"skeleton matchings: {len(M2)}", flush=True)

completes = [[] for _ in range(24)]
for ei, fs in edge_faces.items():
    completes[max(fs)].append((ei, fs))
def admissible_triple(a, b, c):
    return (a+b+c) % 2 == 0 and a <= b+c and b <= a+c and c <= a+b
configs = []
spins = [0]*24
def kap(sp):
    k = 0
    for v in VERTS:
        sg, _ = sixj_sign_square(vertex_labels(v, sp))
        if sg == 0:
            return None
        if sg < 0:
            k ^= 1
    return k
def dfs(fi):
    if fi == 24:
        k = kap(spins)
        if k is not None:
            configs.append((tuple(spins), k))
        return
    for v in (0, 1, 2):
        spins[fi] = v
        if all(admissible_triple(*(spins[x] for x in fs)) for _e, fs in completes[fi]):
            dfs(fi+1)
    spins[fi] = 0
dfs(0)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
random.seed(2026)
sample = (neg if len(neg) <= 1500 else random.sample(neg, 1500)) + random.sample(pos, 1500)
print(f"sample {len(sample)} (of {len(configs)}, {len(neg)} kappa=1)", flush=True)

# precompute per-config edge triples
def tri_of(sp, ei):
    return tuple(sp[fi] for fi in edge_faces[ei])
keyset = set()
cfg_keys = []
for sp, k in sample:
    ks = [ (ei, tri_of(sp, ei)) for ei in range(32) ]
    cfg_keys.append((ks, k))
    keyset.update(ks)
keys = sorted(keyset)
print(f"distinct (edge,triple) keys in sample: {len(keys)}", flush=True)
ALPHABET = (1, -1, 2, -2)

def pf_sign(table, ks):
    vals = [table[k] for k in ks]
    total = 0
    for sgn, m in M2:
        prod = sgn
        for (a, b) in m:
            prod *= vals[edge_of_pair[(a, b)]]
        total += prod
    return 0 if total == 0 else (1 if total > 0 else -1)

def score(table):
    bad = 0
    for ks, k in cfg_keys:
        s = pf_sign(table, ks)
        if s == 0 or (s < 0) != (k == 1):
            bad += 1
    return bad

best_global = None
for r in range(3):
    table = {k: random.choice(ALPHABET) for k in keys}
    cur = score(table)
    T = 3.0
    t0 = time.time()
    for it in range(800):
        k = random.choice(keys)
        old = table[k]
        table[k] = random.choice([a for a in ALPHABET if a != old])
        new = score(table)
        if new <= cur or random.random() < pow(2.718, -(new-cur)/max(T, 1e-3)):
            cur = new
        else:
            table[k] = old
        T *= 0.997
        if cur == 0:
            break
    print(f"restart {r}: mismatches {cur}/{len(sample)} [{time.time()-t0:.0f}s]", flush=True)
    if best_global is None or cur < best_global:
        best_global = cur
    if cur == 0:
        print("FOUND", flush=True)
        break
print(f"PHASE2-DONE best {best_global}/{len(sample)}", flush=True)
