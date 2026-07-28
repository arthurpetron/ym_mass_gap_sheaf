"""The linking lift: q(gamma) in Z4 from embedded band framing, then Brown vs kappa."""
import sys, math, random, time, cmath
sys.path.insert(0, '/home/claude/ym_dig')
from scratch.abk_full import build_all, kap, adm, completes
from computations.kappa_system import decomposable
from computations.hypercube4d_survey import hypercube
from collections import defaultdict

cx, faces, meta = hypercube()
import itertools
VERTS4 = list(itertools.product((0,1), repeat=4))
VC = {i: v for i, v in enumerate(VERTS4)}
# vertex coords: cx built its own ids; reconstruct mapping: brick_complex_nd used
# iproduct order over ranges -> vertex i corresponds to VERTS4[i]? brick used
# product over (range(n+1) for dims) = same lexicographic order as itertools.product((0,1)^4) YES.
import numpy as np

ETA, EPS, DELT = 0.10, 0.025, 0.16

def vec(t): return np.array(t, dtype=float)
def face_center(fi):
    p, d1, d2 = meta[fi]
    c = vec(p)
    c[d1] += 0.5; c[d2] += 0.5
    return c
def edge_mid_dir(ei):
    a, b = cx.edges[ei]
    pa, pb = vec(VC[a]), vec(VC[b])
    return (pa + pb) / 2, (pb - pa)
def push_dir(fi, copy):
    p, d1, d2 = meta[fi]
    others = [d for d in range(4) if d not in (d1, d2)]
    d = others[copy % 2]
    return (1 - 2*p[d]) * np.eye(4)[d]
def face_plane(fi):
    p, d1, d2 = meta[fi]
    return np.eye(4)[d1], np.eye(4)[d2]

def stereo(x4):
    y = x4 - 0.5
    s = y / np.linalg.norm(y)
    if s[3] > 0.999:
        s = s - 1e-6
        s = s / np.linalg.norm(s)
    return s[:3] / (1 - s[3])

def polyline_lk(P, Q):
    """Gauss linking number of closed polylines P, Q (lists of 3d points)."""
    total = 0.0
    nP, nQ = len(P), len(Q)
    for i in range(nP):
        a1, a2 = P[i], P[(i+1) % nP]
        for j in range(nQ):
            b1, b2 = Q[j], Q[(j+1) % nQ]
            r13 = b1 - a1; r14 = b2 - a1; r23 = b1 - a2; r24 = b2 - a2
            def ncross(u, v):
                w = np.cross(u, v)
                n = np.linalg.norm(w)
                return w / n if n > 1e-14 else None
            n1 = ncross(r13, r14); n2 = ncross(r14, r24)
            n3 = ncross(r24, r23); n4 = ncross(r23, r13)
            if any(x is None for x in (n1, n2, n3, n4)):
                continue
            def asin_dot(u, v):
                return math.asin(max(-1.0, min(1.0, np.dot(u, v))))
            om = asin_dot(n1, n2) + asin_dot(n2, n3) + asin_dot(n3, n4) + asin_dot(n4, n1)
            a = a2 - a1; b = b2 - b1
            sgn = 1.0 if np.dot(np.cross(a, b), r13) > 0 else -1.0
            total += om * sgn
    return total / (4 * math.pi)

def cycle_geometry(mask, R):
    """Ordered traversal of a dual-graph cycle mask -> list of arcs
    (sheet, seam_in, seam_out).  R = build_all result dict."""
    zm = {e: (s, mid) for (e, s, mid) in R['zm_edges']}
    edges = []
    x = mask
    while x:
        b = x & (-x); e = b.bit_length()-1; x ^= b
        if e in zm:
            edges.append((e,) + zm[e])
    # adjacency: node keys ('z',sheet) and ('m',mid)
    adj = defaultdict(list)
    for e, s, mid in edges:
        adj[('z', s)].append((('m', mid), e))
        adj[('m', mid)].append((('z', s), e))
    start = edges[0]
    node = ('z', start[1])
    walk_nodes = [node]
    used = set()
    while True:
        nxt = None
        for (n2, e) in adj[node]:
            if e not in used:
                nxt = (n2, e); break
        if nxt is None: break
        used.add(nxt[1])
        node = nxt[0]
        walk_nodes.append(node)
        if node == walk_nodes[0]: break
    # sequence: z,m,z,m,... arcs = (sheet, seam_prev, seam_next)
    seq = walk_nodes[:-1]
    arcs = []
    L = len(seq)
    for i, nd in enumerate(seq):
        if nd[0] == 'z':
            m_prev = seq[(i-1) % L]; m_next = seq[(i+1) % L]
            arcs.append((nd[1], m_prev[1], m_next[1]))
    return arcs

def seam_anchor(R, mid):
    sm = R['seams'][mid]
    m4, edir = edge_mid_dir(sm['ei'])
    # offset multiple seams on same complex edge
    same = sorted(m for m in R['seams'] if R['seams'][m]['ei'] == sm['ei'])
    k = same.index(mid)
    off = (k - (len(same)-1)/2.0) * DELT
    e_unit = edir / np.linalg.norm(edir)
    return m4 + off * e_unit, e_unit

def band_polylines(mask, R):
    """core polyline + two strand chains; returns (core, loops) with loops
    the chained band-boundary loop(s)."""
    arcs = cycle_geometry(mask, R)
    core = []
    strand_pts = {}   # (arc_idx, 'in'/'out', sign) -> point
    strand_segs = []  # list of (key_in, key_out) in-face connections
    for ai, (s, m_in, m_out) in enumerate(arcs):
        fi, copy = s
        pd = ETA * push_dir(fi, copy)
        a_in, e_in = seam_anchor(R, m_in)
        a_out, e_out = seam_anchor(R, m_out)
        fc = face_center(fi)
        cpt = 0.5*fc + 0.25*(a_in + a_out)
        core += [a_in + pd, cpt + pd, a_out + pd]
        # in-face side transport in the (d1,d2) plane
        u1, u2 = face_plane(fi)
        def to2d(v): return np.array([np.dot(v, u1), np.dot(v, u2)])
        din = to2d(cpt - a_in); dout = to2d(a_out - cpt)
        ein2, eout2 = to2d(e_in), to2d(e_out)
        def cross2(a, b): return a[0]*b[1] - a[1]*b[0]
        for sg_in in (+1, -1):
            side_in = 1 if cross2(din, sg_in*ein2) > 0 else -1
            # choose sg_out preserving side w.r.t. outgoing direction
            sg_out = +1 if (1 if cross2(dout, eout2) > 0 else -1) == side_in else -1
            pin = a_in + EPS*sg_in*e_in + pd
            pout = a_out + EPS*sg_out*e_out + pd
            # mid offset: keep off the core
            moff = (sg_in*e_in + sg_out*e_out)
            n = np.linalg.norm(moff)
            if n < 1e-9:
                w = sg_in*e_in
            else:
                w = moff / n
            pmid = cpt + EPS*w + pd
            strand_pts[(ai, 'in', sg_in)] = pin
            strand_pts[(ai, 'out', sg_out)] = pout
            strand_segs.append(((ai, 'in', sg_in), (ai, 'out', sg_out), [pin, pmid, pout]))
    # chain strands across seams: arc ai 'out' at seam m_out connects to arc ai+1 'in'
    # matching sign of e-offset (same ±e_unit anchor side)
    nA = len(arcs)
    succ = {}
    for ai in range(nA):
        for sg in (+1, -1):
            succ[((ai, 'out', sg))] = ((ai+1) % nA, 'in', sg)
    seg_by_in = {}
    for kin, kout, pts in strand_segs:
        seg_by_in[kin] = (kout, pts)
    loops = []
    visited = set()
    for kin0 in list(seg_by_in):
        if kin0 in visited: continue
        pts_all = []
        k = kin0
        while True:
            visited.add(k)
            kout, pts = seg_by_in[k]
            pts_all += pts
            k = succ[kout]
            if k == kin0: break
        loops.append(pts_all)
    return core, loops

def q_linking(mask, R, expect_parity):
    core, loops = band_polylines(mask, R)
    P = [stereo(p) for p in core]
    if len(loops) == 2:
        if expect_parity != 0: return None, "loopcount!=parity"
        Q = [stereo(p) for p in loops[0]]
        lk = polyline_lk(P, Q)
        lki = round(lk)
        if abs(lk - lki) > 0.15: return None, f"lk not integral {lk:.3f}"
        return (2*lki) % 4, None
    elif len(loops) == 1:
        if expect_parity != 1: return None, "loopcount!=parity"
        Q = [stereo(p) for p in loops[0]]
        lk = polyline_lk(P, Q)
        lki = round(lk)
        if abs(lk - lki) > 0.15: return None, f"lk not integral {lk:.3f}"
        if lki % 2 != 1: return None, f"moebius lk even {lki}"
        return lki % 4, None
    return None, f"{len(loops)} loops"

def brown_fixed(qb, Bm):
    n = len(qb)
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
        for i in idx: val += qb[i]
        for a in range(len(idx)):
            for b in range(a+1, len(idx)):
                val += 2*Bm[idx[a]][idx[b]]
        return val % 4
    def indep(vecs):
        piv = {}
        out = []
        for v in vecs:
            x = v
            for p, pr in piv.items():
                if (x >> p) & 1: x ^= pr
            if x:
                piv[x.bit_length()-1] = x
                out.append(v)
        return out
    cur = indep([1 << i for i in range(n)])
    phase = 0.0
    while cur:
        pair = None
        for i in range(len(cur)):
            for j in range(len(cur)):
                if i != j and B_of(cur[i], cur[j]) == 1:
                    pair = (i, j); break
            if pair: break
        if pair is None:
            for g in cur:
                qg = q_of(g)
                if qg == 2: return None
                if qg % 2 == 1: return None  # shouldn't happen on radical
                phase += 0.0
            break
        i, j = pair
        x, y = cur[i], cur[j]
        qx, qy = q_of(x), q_of(y)
        blockG = 1 + 1j**qx + 1j**qy + 1j**((qx+qy+2) % 4)
        if abs(blockG) < 1e-9: return None
        phase += cmath.phase(blockG)
        rest = []
        for k in range(len(cur)):
            if k in (i, j): continue
            z = cur[k]
            if B_of(z, y): z ^= x
            if B_of(z, x): z ^= y
            if z: rest.append(z)
        cur = indep(rest)
    return round(phase/(2*math.pi)*8) % 8

# ---- run ----
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
random.seed(4)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 100) + random.sample(pos, 100)
stats = defaultdict(int)
match_plus = match_minus = 0
t0 = time.time()
for sp, k in sample:
    try:
        R = build_all(list(sp))
    except Exception:
        stats['build_exc'] += 1; continue
    if R is None or 'err' in R:
        stats['build_err'] += 1; continue
    n = R['b1']
    if n == 0:
        stats['b1_0'] += 1
        continue
    # Wu-forced correction: diagonal of B = clash parity (= geometric parity)
    for i in range(n):
        R['B'][i][i] = R['q2'][i]
    qb = []
    fail = None
    for i, g in enumerate(R['gamma']):
        par = R['q2'][i]
        qv, err = q_linking(g, R, par)
        if qv is None:
            fail = err; break
        qb.append(qv)
    if fail:
        stats['geom_'+fail.split()[0]] += 1
        continue
    beta = brown_fixed(qb, R['B'])
    if beta is None:
        stats['nonpin'] += 1; continue
    stats['done'] += 1
    target = 4 if k == 1 else 0
    if beta == target: match_plus += 1
    if (8 - beta) % 8 == target: match_minus += 1
    stats[f'beta{beta}_k{k}'] += 1
print(f"[{time.time()-t0:.0f}s] {dict(stats)}", flush=True)
print(f"MATCH (beta=4k): {match_plus}/{stats['done']}   MATCH mirror (-beta): {match_minus}/{stats['done']}", flush=True)
