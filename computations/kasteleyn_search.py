"""Edge-coupled Kasteleyn-Pfaffian search for kappa.

Ansatz 1 (dual): fermion per 3-cell (8), coupling per face f with value
  c(f, n_f) in {+1,-1}; A_{cell,cell'} = c(shared face).  Pf expands
  over perfect matchings of the cell graph (K8 minus opposite pairs).
Ansatz 2 (skeleton): fermion per vertex (16), coupling per edge e with
  value c(e, tri_e(n)); matchings of the 4-cube 1-skeleton (272).
Target: sign(Pf A(n)) = (-1)^{kappa(n)} on the exhaustive spins<=2
family (incl. all branched negatives).  Simulated annealing, multistart.
"""
import sys, random, itertools, time
sys.path.insert(0, '/home/claude/ym_dig')
from computations.vertex_amplitude import amplitude, sixj_sign_square, vertex_labels, VERTS
from computations.hypercube4d_survey import hypercube

cx, faces, meta = hypercube()

# ---------- build the two graphs and their signed matchings ----------
# cells: 8 half-spaces (d, side): cell contains faces not spanning d at coord side
cells = [(d, s) for d in range(4) for s in (0, 1)]
cell_idx = {c: i for i, c in enumerate(cells)}
def faces_of_cell(c):
    d, s = c
    out = []
    for fi, (p, d1, d2) in enumerate(meta):
        if d1 != d and d2 != d and p[d] == s:
            out.append(fi)
    return out
cell_faces = {c: set(faces_of_cell(c)) for c in cells}
# shared face between two cells
shared = {}
for i, j in itertools.combinations(range(8), 2):
    inter = cell_faces[cells[i]] & cell_faces[cells[j]]
    if len(inter) == 1:
        shared[(i, j)] = inter.pop()
assert len(shared) == 24

def matchings_with_signs(n, edges):
    """All perfect matchings with Pfaffian signs, via recursive expansion."""
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
        for pos, j in enumerate([x for x in active[1:] if x in adj.get(i, ())], start=0):
            # sign factor: (-1)^{position of j among remaining after i}
            rest = [x for x in active[1:]]
            jpos = rest.index(j)
            s2 = sign * ((-1) ** jpos)
            rec([x for x in rest if x != j], s2, acc + [(i, j)])
    rec(list(range(n)), 1, [])
    return out

cell_edges = list(shared.keys())
M1 = matchings_with_signs(8, cell_edges)
skel_edges = [tuple(e) for e in cx.edges]
M2 = matchings_with_signs(16, [(a, b) for a, b in skel_edges])
print(f"cell-graph matchings: {len(M1)}; skeleton matchings: {len(M2)}", flush=True)

edge_faces = {}
for fi, f in enumerate(faces):
    for ei, _o in f:
        edge_faces.setdefault(ei, []).append(fi)
for ei in edge_faces:
    edge_faces[ei] = sorted(edge_faces[ei])

# ---------- config family: exhaustive spins<=2, with kappa ----------
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
print(f"family: {len(configs)} configs, {len(neg)} kappa=1", flush=True)
random.seed(1330)
sample = neg[:] if len(neg) <= 1500 else random.sample(neg, 1500)
sample += random.sample(pos, min(len(pos), 1500))
print(f"training sample: {len(sample)}", flush=True)

# ---------- ansatz evaluation ----------
def pf_sign_cells(table, sp):
    # table: dict (face, n) -> +-1
    total = 0
    for sgn, m in M1:
        prod = sgn
        for (i, j) in m:
            f = shared[(i, j)] if (i, j) in shared else shared[(j, i)]
            prod *= table[(f, sp[f])]
        total += prod
    return 0 if total == 0 else (1 if total > 0 else -1)

def score_cells(table, sample):
    bad = 0
    for sp, k in sample:
        s = pf_sign_cells(table, sp)
        if s == 0 or (s < 0) != (k == 1):
            bad += 1
    return bad

def anneal_cells(iters, restarts):
    keys = [(f, n) for f in range(24) for n in (0, 1, 2)]
    best_global = None
    for r in range(restarts):
        table = {k: random.choice((1, -1)) for k in keys}
        cur = score_cells(table, sample)
        T = 2.0
        for it in range(iters):
            k = random.choice(keys)
            table[k] = -table[k]
            new = score_cells(table, sample)
            if new <= cur or random.random() < pow(2.718, -(new-cur)/max(T, 1e-3)):
                cur = new
            else:
                table[k] = -table[k]
            T *= 0.999
            if cur == 0:
                break
        print(f"  cells restart {r}: best mismatches {cur}/{len(sample)}", flush=True)
        if best_global is None or cur < best_global[0]:
            best_global = (cur, dict(table))
        if cur == 0:
            break
    return best_global

t0 = time.time()
best = anneal_cells(iters=1500, restarts=4)
print(f"ANSATZ 1 (dual-graph, face-keyed): best mismatches {best[0]}/{len(sample)} [{time.time()-t0:.0f}s]", flush=True)
if best[0] == 0:
    import json
    json.dump({str(k): v for k, v in best[1].items()}, open("scratch/kasteleyn_cells.json", "w"))
    print("FOUND — verifying on full family...", flush=True)
    bad = sum(1 for sp, k in configs
              if (lambda s: s == 0 or (s < 0) != (k == 1))(pf_sign_cells(best[1], sp)))
    print(f"full-family mismatches: {bad}/{len(configs)}", flush=True)
print("PHASE1-DONE", flush=True)
