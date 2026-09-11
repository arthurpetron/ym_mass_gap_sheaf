"""Full ABK pipeline: cover -> triangulation -> H1/H^1 -> cup-product B
-> Pin- enhancements with local-type lifts -> Brown -> compare to kappa."""
import sys, itertools, cmath, random, time
sys.path.insert(0, '/home/claude/ym_dig')
from computations.vertex_amplitude import sixj_sign_square, vertex_labels, VERTS
from computations.hypercube4d_survey import hypercube
from computations.kappa_system import decomposable
from collections import defaultdict, Counter

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
def adm(a, b, c):
    return (a+b+c) % 2 == 0 and a <= b+c and b <= a+c and c <= a+b
def kap(sp):
    k = 0
    for v in VERTS:
        sg, _ = sixj_sign_square(vertex_labels(v, sp))
        if sg == 0: return None
        if sg < 0: k ^= 1
    return k
plane = {fi: (meta[fi][1], meta[fi][2]) for fi in range(NF)}
face_verts_cyc = {}
for fi, f in enumerate(faces):
    # cyclic vertex order from oriented edge path
    seq = []
    for ei, o in f:
        a, b = cx.edges[ei]
        seq.append((a, b) if o == 1 else (b, a))
    vs = [seq[0][0]]
    for s, t in seq:
        vs.append(t)
    face_verts_cyc[fi] = vs[:4]

def rank_f2(rows):
    piv = {}
    basis = []
    for r in rows:
        x = r
        for p, pr in piv.items():
            if (x >> p) & 1:
                x ^= pr
        if x:
            piv[x.bit_length()-1] = x
            basis.append(x)
    return piv, basis

def solve_in_span(piv_list, target):
    """reduce target by pivots; return residual"""
    x = target
    for p, pr in piv_list.items():
        if (x >> p) & 1:
            x ^= pr
    return x

def build_all(sp):
    sheets = [(fi, c) for fi in range(NF) for c in range(sp[fi])]
    sid = {s: i for i, s in enumerate(sheets)}
    glue = {}
    seams = {}   # cover-edge id -> dict(side0=(s,ei), side1=..., clash, type data)
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
            mid = len(seams)
            cl = 1 if edge_orient[(ei, s1[0])] == edge_orient[(ei, s2[0])] else 0
            copl = 1 if plane[s1[0]] == plane[s2[0]] else 0
            ttype = (tuple(sorted(ns)), tuple(sorted((sp[s1[0]], sp[s2[0]]))), copl)
            seams[mid] = dict(sides=(s1, s2), ei=ei, clash=cl, type=ttype)
            glue[(s1, ei)] = mid
            glue[(s2, ei)] = mid
    # corner classes: union-find on (sheet, vertex)
    corners = {}
    def cid(x):
        if x not in corners:
            corners[x] = x
        while corners[x] != x:
            corners[x] = corners[corners[x]]
            x = corners[x]
        return x
    def cunion(x, y):
        rx, ry = cid(x), cid(y)
        if rx != ry:
            corners[ry] = rx
    for mid, sm in seams.items():
        (s1, ei1), (s2, ei2) = (sm['sides'][0][0], sm['ei']), (sm['sides'][1][0], sm['ei'])
        sh1, sh2 = sm['sides']
        va, vb = cx.edges[sm['ei']]
        for v in (va, vb):
            cunion((sh1, v), (sh2, v))
    # vertex ids
    vid = {}
    def V(key):
        if key not in vid:
            vid[key] = len(vid)
        return vid[key]
    for i, s in enumerate(sheets):
        V(('z', s))
    for mid in seams:
        V(('m', mid))
    corner_ids = {}
    for s in sheets:
        for v in face_verts_cyc[s[0]]:
            r = cid((s, v))
            corner_ids[(s, v)] = V(('c', r))
    nV = len(vid)
    # triangles per sheet
    E = {}
    def Eid(u, w):
        key = (u, w) if u < w else (w, u)
        if key not in E:
            E[key] = len(E)
        return E[key]
    tris = []
    tri_sheet = []
    for s in sheets:
        fi = s[0]
        vsc = face_verts_cyc[fi]
        z = vid[('z', s)]
        for k in range(4):
            v1, v2 = vsc[k], vsc[(k+1) % 4]
            # which complex edge is between v1,v2
            eik = None
            for ei, _o in faces[fi]:
                if set(cx.edges[ei]) == {v1, v2}:
                    eik = ei
                    break
            mid = glue[(s, eik)]
            m = vid[('m', mid)]
            c1 = corner_ids[(s, v1)]
            c2 = corner_ids[(s, v2)]
            for tri in ((z, c1, m), (z, m, c2)):
                tt = tuple(sorted(tri))
                if len(set(tt)) < 3:
                    return None   # degenerate; skip config
                tris.append(tt)
                tri_sheet.append(s)
                Eid(tt[0], tt[1]); Eid(tt[1], tt[2]); Eid(tt[0], tt[2])
    nE = len(E)
    nT = len(tris)
    # delta1: edges -> triangles ; d2: triangles -> edges ; d1: edges -> vertices
    d2_rows = []
    for tt in tris:
        r = (1 << Eid(tt[0], tt[1])) | (1 << Eid(tt[1], tt[2])) | (1 << Eid(tt[0], tt[2]))
        d2_rows.append(r)
    # H^1: cocycles c (edge masks) with delta c = 0: for each triangle sum of its 3 edges even
    # solve kernel of matrix rows= per-triangle edge-triples over edge space
    # kernel via row reduce of constraint matrix transposed: use standard method
    # constraints: nT rows over nE cols
    piv_c, _ = rank_f2(d2_rows)   # row space of constraints? need kernel of edge->F2^T map
    # kernel: edges e with columns; do Gaussian on constraint matrix in column space:
    # build column bitmasks: col[e] = mask over triangles containing e
    col = [0]*nE
    for ti, tt in enumerate(tris):
        for (u, w) in ((tt[0], tt[1]), (tt[1], tt[2]), (tt[0], tt[2])):
            col[Eid(u, w)] |= (1 << ti)
    # kernel of col-map: vectors x (edge mask) with xor of col[e] over e in x == 0
    pivots = {}
    kernel_basis = []
    reps = {}
    for e in range(nE):
        x = col[e]
        track = 1 << e
        for p in sorted(pivots, reverse=True):
            if (x >> p) & 1:
                x ^= pivots[p][0]; track ^= pivots[p][1]
        if x:
            pivots[x.bit_length()-1] = (x, track)
        else:
            kernel_basis.append(track)   # cocycle
    # im delta0: for each vertex, star cochain
    star = [0]*nV
    for (u, w), eidx in E.items():
        star[u] |= (1 << eidx); star[w] |= (1 << eidx)
    piv_im, _ = rank_f2(star)
    # H^1 basis: kernel basis reduced mod im delta0
    h1_piv = dict(piv_im)
    h1_basis = []
    for kvec in kernel_basis:
        x = kvec
        for p in sorted(h1_piv, reverse=True):
            if (x >> p) & 1:
                x ^= h1_piv[p]
        if x:
            h1_piv[x.bit_length()-1] = x
            h1_basis.append(kvec)   # store original cocycle rep
    bH1 = len(h1_basis)
    # H_1 cycles from dual graph (z-m edges), quotient corner disks
    zm_edges = []
    for s in sheets:
        z = vid[('z', s)]
        fi = s[0]
        for ei, _o in faces[fi]:
            mid = glue[(s, ei)]
            m = vid[('m', mid)]
            zm_edges.append((Eid(min(z, m), max(z, m)), s, mid))
    # dual graph on centers+mids with these edges; fundamental cycles
    dg_adj = defaultdict(list)
    for eidx, s, mid in zm_edges:
        u, w = vid[('z', s)], vid[('m', mid)]
        dg_adj[u].append((w, eidx)); dg_adj[w].append((u, eidx))
    # spanning forest
    seen = {}
    treeE = set()
    for start in list(dg_adj):
        if start in seen: continue
        seen[start] = None
        stack = [start]
        while stack:
            u = stack.pop()
            for (w, eidx) in dg_adj[u]:
                if w not in seen:
                    seen[w] = (u, eidx)
                    treeE.add(eidx)
                    stack.append(w)
    def tree_path_mask(u, w):
        # climb to roots collecting edges (masks over EDGE ids)
        def anc(x):
            path = {}
            mask = 0
            while seen[x] is not None:
                px, eidx = seen[x]
                path[x] = (px, eidx)
                x = px
            return x, path
        r1, p1 = anc(u); r2, p2 = anc(w)
        m1 = 0; x = u
        while seen[x] is not None:
            px, eidx = seen[x]; m1 ^= (1 << eidx); x = px
        m2 = 0; x = w
        while seen[x] is not None:
            px, eidx = seen[x]; m2 ^= (1 << eidx); x = px
        return m1 ^ m2
    fund = []
    for eidx, s, mid in zm_edges:
        if eidx in treeE: continue
        u, w = vid[('z', s)], vid[('m', mid)]
        fund.append((1 << eidx) ^ tree_path_mask(u, w))
    # corner-disk boundaries in zm-edge space
    corner_members = defaultdict(list)
    for s in sheets:
        for v in face_verts_cyc[s[0]]:
            corner_members[cid((s, v))].append((s, v))
    disks = []
    for r, mems in corner_members.items():
        mask = 0
        for (s, v) in mems:
            fi = s[0]
            inc = [ei for ei, _o in faces[fi] if v in cx.edges[ei]]
            for ei in inc:
                mid = glue[(s, ei)]
                z, m = vid[('z', s)], vid[('m', mid)]
                mask ^= (1 << Eid(min(z, m), max(z, m)))
        disks.append(mask)
    piv_d, _ = rank_f2(disks)
    hom_piv = dict(piv_d)
    gamma = []
    for fmask in fund:
        x = fmask
        for p in sorted(hom_piv, reverse=True):
            if (x >> p) & 1:
                x ^= hom_piv[p]
        if x:
            hom_piv[x.bit_length()-1] = x
            gamma.append(fmask)
    bH_1 = len(gamma)
    if bH_1 != bH1:
        return dict(err=f"dim mismatch H1={bH_1} H^1={bH1}")
    b1 = bH1
    if b1 == 0:
        return dict(b1=0)
    # pairing and dual cocycles
    P = [[bin(h1_basis[a] & gamma[k]).count("1") & 1 for k in range(b1)] for a in range(b1)]
    # invert P over F2 via Gauss-Jordan (rows of P over columns k)
    n = b1
    rows = [sum(P[a][k] << k for k in range(n)) for a in range(n)]
    aug = [(rows[a] | (1 << (n + a))) for a in range(n)]
    # forward eliminate to RREF on low n bits
    pivot_of = {}
    for r in range(n):
        row = aug[r]
        # reduce by existing pivots
        for pc, pr in pivot_of.items():
            if (row >> pc) & 1:
                row ^= pr
        low = row & ((1 << n) - 1)
        if not low:
            return dict(err="pairing singular")
        pc = low.bit_length() - 1
        # clear this pivot from previous rows
        for pc2 in list(pivot_of):
            if (pivot_of[pc2] >> pc) & 1:
                pivot_of[pc2] ^= row
        pivot_of[pc] = row
    # now pivot_of[k] has low = e_k exactly; high bits = combination
    alpha = [0]*n
    for k, row in pivot_of.items():
        hi = row >> n
        acc = 0
        for a in range(n):
            if (hi >> a) & 1:
                acc ^= h1_basis[a]
        alpha[k] = acc
    # verify duality
    for i in range(n):
        for k in range(n):
            if (bin(alpha[i] & gamma[k]).count("1") & 1) != (1 if i == k else 0):
                return dict(err="duality check failed")
    # cup product B_ij
    Bm = [[0]*n for _ in range(n)]
    tri_e = []
    for tt in tris:
        tri_e.append((Eid(tt[0], tt[1]), Eid(tt[1], tt[2])))
    for i in range(n):
        ai = alpha[i]
        for j in range(n):
            aj = alpha[j]
            tot = 0
            for (e01, e12) in tri_e:
                tot ^= ((ai >> e01) & 1) & ((aj >> e12) & 1)
            Bm[i][j] = tot
    sym_ok = all(Bm[i][j] == Bm[j][i] for i in range(n) for j in range(n))
    # q2 and type counts on gamma (zm-edge masks)
    einfo = {}
    for eidx, s, mid in zm_edges:
        sm = seams[mid]
        ref = sm['sides'][0]
        rho = 0 if (s == ref[0] if isinstance(ref, tuple) and not isinstance(ref[0], tuple) else s == ref[0]) else sm['clash']
        # ref side: sides=(s1,s2) where s1=(face,copy): compare full sheet
        rho = 0 if s == sm['sides'][0][0:2] or s == sm['sides'][0] else sm['clash']
        einfo[eidx] = (rho if s != sm['sides'][0] else 0, sm['type'])
    def q2_of(mask):
        tot = 0
        x = mask
        while x:
            b = x & (-x); e = b.bit_length()-1; x ^= b
            tot ^= einfo[e][0]
        return tot
    def types_of(mask):
        cnt = Counter()
        x = mask
        while x:
            b = x & (-x); e = b.bit_length()-1; x ^= b
            cnt[einfo[e][1]] ^= 1   # mod 2 (each seam crossing uses 2 zm-edges; type counted per edge -> per crossing parity handled by /1... count per edge; crossing uses 2 edges of same seam type -> contributes 0? FIX: halve by seam)
        return cnt
    # better: count per SEAM crossings: a crossing at seam mid uses both zm-edges at m
    def seam_crossings(mask):
        per_m = Counter()
        x = mask
        while x:
            b = x & (-x); e = b.bit_length()-1; x ^= b
            per_m[zm_edges_lookup[e]] += 1
        return per_m
    zm_edges_lookup = {}
    for eidx, s, mid in zm_edges:
        zm_edges_lookup[eidx] = mid
    def crossing_types(mask):
        per_m = Counter()
        x = mask
        while x:
            b = x & (-x); e = b.bit_length()-1; x ^= b
            per_m[zm_edges_lookup[e]] += 1
        cnt = Counter()
        for mid, c in per_m.items():
            if c == 2:
                cnt[seams[mid]['type']] += 1
            elif c == 1:
                cnt[('half', seams[mid]['type'])] += 1
        return cnt
    qc = [q2_of(g) for g in gamma]
    diag_ok = all(Bm[i][i] == qc[i] for i in range(n))
    tcounts = [crossing_types(g) for g in gamma]
    return dict(b1=n, B=Bm, q2=qc, tcounts=tcounts, sym_ok=sym_ok, diag_ok=diag_ok)

# quick smoke test on 12 configs
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
random.seed(3)
test = random.sample(configs, 12)
for sp, k in test:
    t0 = time.time()
    try:
        r = build_all(list(sp))
    except Exception as ex:
        print("EXC", type(ex).__name__, str(ex)[:80], flush=True)
        continue
    if r is None:
        print("degenerate-skip", flush=True); continue
    if 'err' in r:
        print("ERR:", r['err'], flush=True); continue
    print(f"b1={r.get('b1')} sym={r.get('sym_ok')} diag(B=q2)={r.get('diag_ok')} "
          f"[{time.time()-t0:.1f}s]", flush=True)
