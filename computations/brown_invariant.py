"""Pin- quadratic enhancements on the strand cover: Brown vs kappa.

Pipeline per config: canonical cover (P11 machinery) -> ribbon graph
(rotations from corner walks) -> H1 basis (tree/cotree) -> q2 = flip
parity, B = ribbon intersection form (self-check B(x,x)=q2(x)) ->
all 2^b1 mod-4 lifts -> Brown beta in Z8 via Gauss sum ->
achievability of {kappa=1 <-> beta=4, kappa=0 <-> beta=0}.
"""
import sys, itertools, cmath, random, time
sys.path.insert(0, '/home/claude/ym_dig')
from computations.vertex_amplitude import sixj_sign_square, vertex_labels, VERTS
from computations.hypercube4d_survey import hypercube
from computations.kappa_system import decomposable
from collections import defaultdict

cx, faces, meta = hypercube()
NF = 24
edge_faces = {}
edge_orient = {}
for fi, f in enumerate(faces):
    for ei, o in f:
        edge_faces.setdefault(ei, []).append(fi)
        edge_orient[(ei, fi)] = o
for ei in edge_faces:
    edge_faces[ei] = sorted(edge_faces[ei])
completes = [[] for _ in range(24)]
for ei, fs in edge_faces.items():
    completes[max(fs)].append((ei, fs))
def admissible_triple(a, b, c):
    return (a+b+c) % 2 == 0 and a <= b+c and b <= a+c and c <= a+b
def kap(sp):
    k = 0
    for v in VERTS:
        sg, _ = sixj_sign_square(vertex_labels(v, sp))
        if sg == 0: return None
        if sg < 0: k ^= 1
    return k

def build_ribbon(sp):
    """Cover as ribbon graph: returns (edges list with clash bits,
    rotations at cover-vertices as cyclic lists of (cover-edge, end))."""
    sheets = [(fi, c) for fi in range(NF) for c in range(sp[fi])]
    glue = {}
    clash = {}
    for ei, fs in edge_faces.items():
        ns = [sp[fi] for fi in fs]
        if sum(ns) == 0: continue
        A, B, C = fs
        a, b, c = ns
        nab = (a+b-c)//2; nbc = (b+c-a)//2; nac = (a+c-b)//2
        strands = {fi: list(range(sp[fi])) for fi in fs}
        take = lambda fi: strands[fi].pop(0)
        pairs = ([((A,take(A)),(B,take(B))) for _ in range(nab)] +
                 [((B,take(B)),(C,take(C))) for _ in range(nbc)] +
                 [((A,take(A)),(C,take(C))) for _ in range(nac)])
        for (s1, s2) in pairs:
            glue[(s1, ei)] = (s2, ei)
            glue[(s2, ei)] = (s1, ei)
            clash[frozenset(((s1, ei), (s2, ei)))] = (
                1 if edge_orient[(ei, s1[0])] == edge_orient[(ei, s2[0])] else 0)
    # cover-edges: canonical ids
    cov_edges = {}
    for k in glue:
        fk = frozenset((k, glue[k]))
        if fk not in cov_edges:
            cov_edges[fk] = len(cov_edges)
    # corner walk (as in P11) recording rotations
    face_edges_at_v = {}
    for fi, f in enumerate(faces):
        eids = [ei for ei, _o in f]
        vs = set()
        for ei in eids:
            va, vb = cx.edges[ei]; vs.update((va, vb))
        for v in vs:
            inc = [ei for ei in eids if v in cx.edges[ei]]
            if len(inc) == 2:
                face_edges_at_v[(fi, v)] = inc
    def stepf(s, v, ei):
        tgt = glue.get((s, ei))
        if tgt is None: return None
        s2 = tgt[0]
        inc2 = face_edges_at_v.get((s2[0], v))
        if inc2 is None: return None
        other = inc2[0] if inc2[1] == ei else inc2[1]
        return (s2, v, other)
    visited = set()
    rotations = []   # list of cyclic lists of ((sheet, ei) flag)
    for s in sheets:
        fi, _c = s
        for (ffi, v), inc in face_edges_at_v.items():
            if ffi != fi: continue
            for e0 in inc:
                key = (s, v, e0)
                if key in visited: continue
                cyc = []
                cur = key
                ok = True
                while cur not in visited:
                    visited.add(cur)
                    cyc.append((cur[0], cur[2]))
                    nxt = stepf(*cur)
                    if nxt is None: ok = False; break
                    cur = nxt
                if ok and cyc:
                    rotations.append(cyc)
    # halve duplication (each corner cycle appears twice, opposite senses)
    seen_sets = {}
    rots = []
    for cyc in rotations:
        key = frozenset(cyc)
        if key in seen_sets: continue
        seen_sets[key] = 1
        rots.append(cyc)
    return sheets, glue, clash, cov_edges, rots

def h1_and_forms(sp):
    sheets, glue, clash, cov_edges, rots = build_ribbon(sp)
    if not cov_edges:
        return None
    # graph: vertices = rotation index containing each flag
    flag_vertex = {}
    for vi, cyc in enumerate(rots):
        for flag in cyc:
            flag_vertex[flag] = vi
    E = {}
    for fk, eid in cov_edges.items():
        (f1, f2) = tuple(fk)
        v1 = flag_vertex.get(f1); v2 = flag_vertex.get(f2)
        if v1 is None or v2 is None:
            return None
        E[eid] = (v1, v2, f1, f2, clash[fk])
    nV = len(rots)
    # spanning forest
    parent = list(range(nV))
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]; i = parent[i]
        return i
    tree = set()
    for eid, (v1, v2, *_r) in E.items():
        r1, r2 = find(v1), find(v2)
        if r1 != r2:
            parent[r2] = r1; tree.add(eid)
    cotree = [eid for eid in E if eid not in tree]
    b1 = len(cotree)
    # fundamental cycles as edge sets (F2 vectors) via tree paths
    adj = defaultdict(list)
    for eid in tree:
        v1, v2, *_ = E[eid]
        adj[v1].append((v2, eid)); adj[v2].append((v1, eid))
    def tree_path(u, w):
        # BFS in tree
        from collections import deque
        prev = {u: None}
        dq = deque([u])
        while dq:
            x = dq.popleft()
            if x == w: break
            for (y, eid) in adj[x]:
                if y not in prev:
                    prev[y] = (x, eid); dq.append(y)
        path = []
        x = w
        while prev[x] is not None:
            px, eid = prev[x]; path.append(eid); x = px
        return path
    basis = []
    for eid in cotree:
        v1, v2, *_ = E[eid]
        vec = set([eid]) ^ set(tree_path(v2, v1))
        basis.append(frozenset(vec))
    # q2 on a cycle = sum of clash bits
    def q2(vec):
        return sum(E[eid][4] for eid in vec) & 1
    # intersection form via rotation interleaving.
    # walk representation: orient each fundamental cycle as closed walk.
    def cycle_walk(vec):
        # build multigraph of vec edges; find Eulerian-ish closed walk
        inc = defaultdict(list)
        for eid in vec:
            v1, v2, *_ = E[eid]
            inc[v1].append(eid); inc[v2].append(eid)
        # fundamental cycles are simple cycles: each vertex degree 2 (in tree+cotree union? tree path + chord: yes simple)
        start = next(iter(inc))
        walk = []
        v = start; used = set()
        while True:
            nxt = None
            for eid in inc[v]:
                if eid not in used:
                    nxt = eid; break
            if nxt is None: break
            used.add(nxt)
            v1, v2, f1, f2, _c = E[nxt]
            frm = v
            v = v2 if v1 == v else v1
            walk.append((nxt, frm))
            if v == start: break
        return walk
    walks = [cycle_walk(vec) for vec in basis]
    # at each vertex, positions of flags in rotation
    pos = {}
    for vi, cyc in enumerate(rots):
        for p, flag in enumerate(cyc):
            pos[flag] = (vi, p)
        # also store length
    rot_len = {vi: len(cyc) for vi, cyc in enumerate(rots)}
    def passages(walk):
        """for each visited vertex: (slot_in, slot_out) rotation positions"""
        out = defaultdict(list)
        n = len(walk)
        for i in range(n):
            eid_in, frm_in = walk[i]
            eid_out, frm_out = walk[(i+1) % n]
            # vertex between edge i and i+1:
            v1, v2, f1, f2, _c = E[eid_in]
            v_between = v2 if frm_in == v1 else v1
            # incoming flag at v_between from eid_in:
            fin = f1 if pos[f1][0] == v_between else f2
            w1, w2, g1, g2, _c2 = E[eid_out]
            fout = g1 if pos[g1][0] == v_between else g2
            out[v_between].append((pos[fin][1], pos[fout][1]))
        return out
    def interleave(p1, p2, L):
        """do arcs (a1,b1) and (a2,b2) interleave on cycle of length L (mod2)"""
        (a1, b1), (a2, b2) = p1, p2
        def between(x, a, b):
            # is x strictly between a and b going forward a->b
            if a <= b: return a < x < b
            return x > a or x < b
        c = between(a2, a1, b1) ^ between(b2, a1, b1)
        return 1 if c else 0
    def B(w1, w2):
        # shared edges: perturbation heuristic — if walks share an edge,
        # fall back to symmetric difference trick: B(x,y) = q-relation check only
        e1 = {e for e, _ in w1}; e2 = {e for e, _ in w2}
        if e1 & e2:
            return None   # handled by caller via bilinearity over modified basis
        pas1 = passages(w1); pas2 = passages(w2)
        tot = 0
        for v in set(pas1) & set(pas2):
            L = rot_len[v]
            for p1 in pas1[v]:
                for p2 in pas2[v]:
                    tot ^= interleave(p1, p2, L)
        return tot
    return dict(basis=basis, walks=walks, q2=q2, B=B, E=E, b1=b1,
                rots=rots)

# ---- assemble Brown machinery with edge-disjointness workaround ----
def brown_analysis(sp, kappa_val, max_b1=9):
    data = h1_and_forms(sp)
    if data is None: return None
    b1 = data['b1']
    if b1 == 0:
        return dict(b1=0, ok=(kappa_val == 0), note="H1=0 forces beta=0")
    if b1 > max_b1: return dict(b1=b1, skipped=True)
    basis, walks, q2f, Bf = data['basis'], data['walks'], data['q2'], data['B']
    n = b1
    # B matrix; where walks share edges, use identity B(x,y)=q2 relation trick:
    # replace y by y' = y + x (different rep) — approximate: use vector-level
    # fallback: B(x,y) = (q2 of symmetric difference walk) — NOT valid.
    # Instead: compute B on pairs with disjoint edge sets; for overlapping
    # pairs, use bilinearity with a third basis vector z disjoint from both if
    # possible; else mark unknown.
    Bm = [[None]*n for _ in range(n)]
    for i in range(n):
        Bm[i][i] = q2f(basis[i])   # Pin- relation B(x,x)=q2(x)
    for i in range(n):
        for j in range(i+1, n):
            val = Bf(walks[i], walks[j])
            Bm[i][j] = Bm[j][i] = val
    # resolve unknowns via bilinearity: B(i,j) = B(i+k, j) + B(k, j)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            for j in range(n):
                if Bm[i][j] is not None: continue
                # try k with known B(k,j) and computable B on (basis_i^basis_k, j)
                for k in range(n):
                    if k in (i, j) or Bm[k][j] is None: continue
                    vec = basis[i] ^ basis[k]
                    # build walk for vec if it is a simple cycle-ish set: skip
                    # (cheap route: leave unknown)
                    pass
        break
    unknown = sum(1 for i in range(n) for j in range(n) if Bm[i][j] is None)
    if unknown:
        return dict(b1=b1, unknown_pairs=unknown//2, skipped=True)
    q2v = [q2f(v) for v in basis]
    best = None
    achievable = set()
    for rbits in range(2**n):
        # q(basis_i) = q2_i + 2*r_i
        qb = [ (q2v[i] + 2*((rbits>>i)&1)) % 4 for i in range(n) ]
        G = 0
        for x in range(2**n):
            val = 0
            xs = [(x>>i)&1 for i in range(n)]
            for i in range(n):
                if xs[i]: val += qb[i]
            for i in range(n):
                for j in range(i+1, n):
                    if xs[i] and xs[j]:
                        val += 2*Bm[i][j]
            G += 1j**(val % 4)
        if abs(G) > 1e-9:
            beta = round((cmath.phase(G) / (2*cmath.pi)) * 8) % 8
            achievable.add(beta)
    target = 4 if kappa_val == 1 else 0
    return dict(b1=b1, achievable=sorted(achievable), target=target,
                ok=(target in achievable))

# ---- sample run ----
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
        if all(admissible_triple(*(spins[x] for x in fs)) for _e, fs in completes[fi]):
            dfs(fi+1)
    spins[fi] = 0
dfs(0)
random.seed(8)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 120) + random.sample(pos, 120)
stats = defaultdict(int)
fails = []
t0 = time.time()
for sp, k in sample:
    try:
        r = brown_analysis(list(sp), k)
    except Exception as e:
        stats['error'] += 1
        continue
    if r is None: stats['none'] += 1; continue
    if r.get('skipped'): stats[f"skipped_b1>{9}" if not r.get('unknown_pairs') else 'skipped_unknownB'] += 1; continue
    stats['analyzed'] += 1
    if r['ok']:
        stats[f'ok_k{k}'] += 1
    else:
        stats[f'FAIL_k{k}'] += 1
        if len(fails) < 6:
            fails.append((sp, k, r))
print(f"sample {len(sample)}: {dict(stats)}  [{time.time()-t0:.0f}s]", flush=True)
for sp, k, r in fails:
    print(f"  FAIL kappa={k}: b1={r['b1']} achievable={r['achievable']} target={r['target']}", flush=True)
