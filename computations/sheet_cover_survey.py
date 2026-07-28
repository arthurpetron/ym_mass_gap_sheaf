"""Construct the canonical strand cover Sigma(n) for spins<=2 configs
and test whether kappa is an invariant of its topology.

Cover cells: sheets = (face, copy<n_f); sides glue at complex edges by
the canonical SU(2) pair counts:
  (a,b,c) admissible: #A-B pairs = (a+b-c)/2 etc.
Deterministic tie-break: strands indexed 0..n-1 per face; pairs formed
in index order (caveat flagged; ambiguity-free configs tracked
separately).  chi = sheets - sidepairs + corner-cycles; orientability
via gluing-compatibility cycles; components via union-find.
"""
import sys, itertools
sys.path.insert(0, '/home/claude/ym_dig')
from computations.vertex_amplitude import sixj_sign_square, vertex_labels, VERTS
from computations.hypercube4d_survey import hypercube
from collections import Counter, defaultdict

cx, faces, meta = hypercube()
NF = 24
edge_faces = {}
edge_orient = {}   # (ei, fi) -> +1 if face traverses edge forward
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
        if sg == 0:
            return None
        if sg < 0:
            k ^= 1
    return k

def build_cover(sp):
    """Return (chi, orientable, components, ambiguous) of Sigma(sp)."""
    sheets = [(fi, c) for fi in range(NF) for c in range(sp[fi])]
    sid = {s: i for i, s in enumerate(sheets)}
    if not sheets:
        return (0, True, 0, False)
    ambiguous = False
    # side gluings per complex edge
    glue = {}   # (sheet, ei) -> (sheet', ei)
    orient_clash = []  # edges of clash graph: (i, j, clash?)
    for ei, fs in edge_faces.items():
        ns = [sp[fi] for fi in fs]
        if sum(ns) == 0:
            continue
        A, B, C = fs
        a, b, c = ns
        nab = (a + b - c) // 2
        nbc = (b + c - a) // 2
        nac = (a + c - b) // 2
        if a*b*c != 0 and (nab > 1 or nbc > 1 or nac > 1):
            ambiguous = True
        if max(ns) == 2 and sorted(ns) == [0, 2, 2]:
            ambiguous = True   # two parallel pairs: 2 pairings
        # deterministic strand assignment in index order
        strands = {fi: list(range(sp[fi])) for fi in fs}
        def take(fi):
            return strands[fi].pop(0)
        pairs = []
        for _ in range(nab):
            pairs.append(((A, take(A)), (B, take(B))))
        for _ in range(nbc):
            pairs.append(((B, take(B)), (C, take(C))))
        for _ in range(nac):
            pairs.append(((A, take(A)), (C, take(C))))
        for (s1, s2) in pairs:
            glue[(s1, ei)] = (s2, ei)
            glue[(s2, ei)] = (s1, ei)
            # orientation clash: compatible iff faces traverse e oppositely
            clash = 1 if edge_orient[(ei, s1[0])] == edge_orient[(ei, s2[0])] else 0
            orient_clash.append((sid[s1], sid[s2], clash))
    n_sidepairs = len({tuple(sorted((k[0], v[0]))) + (k[1],) for k, v in glue.items()}) // 1
    n_sidepairs = len(glue) // 2
    # corner cycles: corners = (sheet, vertex-of-face); walk around vertices.
    # each sheet's face fi has corners at the 4 complex-vertices of fi;
    # at a corner (sheet, v), the two sides of fi meeting v are the two
    # edges of fi incident to v.  Corner-adjacency: cross a side gluing
    # to the neighboring sheet at the same complex vertex.
    face_edges_at_v = {}
    for fi, f in enumerate(faces):
        eids = [ei for ei, _o in f]
        vs = set()
        for ei in eids:
            va, vb = cx.edges[ei]
            vs.update((va, vb))
        for v in vs:
            inc = [ei for ei in eids if v in cx.edges[ei]]
            if len(inc) == 2:
                face_edges_at_v[(fi, v)] = inc
    corners = []
    for s in sheets:
        fi, _c = s
        for (ffi, v), inc in face_edges_at_v.items():
            if ffi == fi:
                corners.append((s, v))
    corner_set = set(corners)
    # half-edge walk: from (sheet, v) exit via one of its 2 sides, glue.
    def step(s, v, ei):
        tgt = glue.get((s, ei))
        if tgt is None:
            return None
        s2 = tgt[0]
        inc2 = face_edges_at_v.get((s2[0], v))
        if inc2 is None:
            return None
        other = inc2[0] if inc2[1] == ei else inc2[1]
        return (s2, v, other)
    visited = set()
    n_cycles = 0
    for (s, v) in corner_set:
        inc = face_edges_at_v[(s[0], v)]
        for e0 in inc:
            key = (s, v, e0)
            if key in visited:
                continue
            cur = key
            cycle_nodes = []
            closed = True
            while cur not in visited:
                visited.add(cur)
                cycle_nodes.append(cur)
                nxt = step(*cur)
                if nxt is None:
                    closed = False
                    break
                cur = nxt
            if closed and cycle_nodes:
                n_cycles += 1
    # each corner counted from both its sides -> each geometric corner cycle
    # traversed twice (once per direction of entry); halve.
    n_corner_cycles = n_cycles // 2
    # components + orientability via union-find with parity
    parent = list(range(len(sheets)))
    parity = [0]*len(sheets)
    def find(i):
        p = []
        while parent[i] != i:
            p.append(i); i = parent[i]
        # path compress with parity
        return i
    def findp(i):
        pr = 0
        while parent[i] != i:
            pr ^= parity[i]; i = parent[i]
        return i, pr
    nonorient_roots = set()
    for i, j, clash in orient_clash:
        ri, pi = findp(i)
        rj, pj = findp(j)
        if ri == rj:
            if (pi ^ pj) != clash:
                nonorient_roots.add(ri)
        else:
            parent[rj] = ri
            parity[rj] = pi ^ pj ^ clash
    roots = {findp(i)[0] for i in range(len(sheets))}
    n_comp = len(roots)
    orientable = all((findp(i)[0] not in nonorient_roots) for i in range(len(sheets)))
    chi = len(sheets) - n_sidepairs + n_corner_cycles
    return (chi, orientable, n_comp, ambiguous)

# sweep: branched configs (non-decomposable), crosstab kappa vs cover topology
from computations.kappa_system import decomposable
tab = defaultdict(Counter)
tab_unamb = defaultdict(Counter)
spins = [0]*24
n_done = 0
def dfs(fi):
    global n_done
    if fi == 24:
        k = kap(spins)
        if k is None:
            return
        if decomposable(spins):
            return   # unbranched cone: kappa=0 always (support law)
        chi, ori, comp, amb = build_cover(spins)
        key = (chi % 4, ori, comp % 2)
        tab[key][k] += 1
        if not amb:
            tab_unamb[key][k] += 1
        n_done += 1
        return
    for v in (0, 1, 2):
        spins[fi] = v
        if all(admissible_triple(*(spins[x] for x in fs)) for _e, fs in completes[fi]):
            dfs(fi+1)
    spins[fi] = 0
dfs(0)
print(f"branched configs analyzed: {n_done}", flush=True)
print("ALL branched: (chi%4, orientable, comp%2) -> kappa census")
for k in sorted(tab, key=str):
    print(f"  {k}: {dict(tab[k])}")
mixed = sum(1 for v in tab.values() if len(v) > 1)
print(f"mixed keys: {mixed}/{len(tab)}")
print("UNAMBIGUOUS only:")
for k in sorted(tab_unamb, key=str):
    print(f"  {k}: {dict(tab_unamb[k])}")
mixedu = sum(1 for v in tab_unamb.values() if len(v) > 1)
print(f"mixed keys (unambiguous): {mixedu}/{len(tab_unamb)}")
