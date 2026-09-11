"""Hardened band geometry for the ABK pipeline (v2).

Fixes over scratch/linking_lift.py, targeting the triple-consistency
meter (was 27/40):

  F1. REVISITED SHEETS.  The old cycle walk assumed every sheet node
      has degree 2 in the cycle mask; composite classes (x^y, x^y^z)
      routinely revisit a sheet (degree 4+), and the walk silently
      truncated.  v2 pairs the incident seams at every sheet by
      NON-CROSSING chords in the face disk (angular order around the
      face center) — the embedded-on-Sigma resolution — and walks the
      resulting deterministic transition maps.  Any leftover edge is a
      hard failure, never a silent truncation.

  F2. CROSS-COMPONENT LINKING.  A composite class usually embeds as a
      multi-component curve.  The Z4 refinement of a multi-component
      representative is NOT the sum of the component q's: the
      standard formula (Guillou-Marin / Kirby-Melvin) adds the mutual
      linking of the pushed components,

          q(C1 u ... u Ck) = sum_i q(Ci) + 2 * sum_{i<j} lk(Ci, Cj).

      v2 adds the 2*lk cross terms (cores after the same eta-push).

  F3. PARITY PER COMPONENT.  Orientability (annulus vs Moebius band)
      is decided per component from the seam clash parities
      (einfo_rho), not per total mask.
"""
import itertools
import math
import sys

sys.path.insert(0, '/home/claude/ym_dig')

import numpy as np
from collections import defaultdict

from scratch.abk_full import build_all, kap, adm, completes  # noqa: E402
from computations.hypercube4d_survey import hypercube  # noqa: E402

cx, faces, meta = hypercube()
VERTS4 = list(itertools.product((0, 1), repeat=4))
VC = {i: v for i, v in enumerate(VERTS4)}

ETA, EPS, DELT = 0.05, 0.02, 0.16


def vec(t):
    return np.array(t, dtype=float)


def face_center(fi):
    p, d1, d2 = meta[fi]
    c = vec(p)
    c[d1] += 0.5
    c[d2] += 0.5
    return c


def edge_mid_dir(ei):
    a, b = cx.edges[ei]
    pa, pb = vec(VC[a]), vec(VC[b])
    return (pa + pb) / 2, (pb - pa)


def push_dir(fi, copy):
    p, d1, d2 = meta[fi]
    others = [d for d in range(4) if d not in (d1, d2)]
    d = others[copy % 2]
    return (1 - 2 * p[d]) * np.eye(4)[d]


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
    """Gauss linking number of closed 3D polylines."""
    total = 0.0
    nP, nQ = len(P), len(Q)
    for i in range(nP):
        a1, a2 = P[i], P[(i + 1) % nP]
        for j in range(nQ):
            b1, b2 = Q[j], Q[(j + 1) % nQ]
            r13 = b1 - a1
            r14 = b2 - a1
            r23 = b1 - a2
            r24 = b2 - a2

            def ncross(u, v):
                w = np.cross(u, v)
                nn = np.linalg.norm(w)
                return w / nn if nn > 1e-14 else None

            n1 = ncross(r13, r14)
            n2 = ncross(r14, r24)
            n3 = ncross(r24, r23)
            n4 = ncross(r23, r13)
            if any(x is None for x in (n1, n2, n3, n4)):
                continue

            def asin_dot(u, v):
                return math.asin(max(-1.0, min(1.0, float(np.dot(u, v)))))

            om = (asin_dot(n1, n2) + asin_dot(n2, n3)
                  + asin_dot(n3, n4) + asin_dot(n4, n1))
            a = a2 - a1
            b = b2 - b1
            sgn = 1.0 if np.dot(np.cross(a, b), r13) > 0 else -1.0
            total += om * sgn
    return total / (4 * math.pi)


def seam_anchor(R, mid):
    sm = R['seams'][mid]
    m4, edir = edge_mid_dir(sm['ei'])
    same = sorted(m for m in R['seams'] if R['seams'][m]['ei'] == sm['ei'])
    k = same.index(mid)
    off = (k - (len(same) - 1) / 2.0) * DELT
    e_unit = edir / np.linalg.norm(edir)
    return m4 + off * e_unit, e_unit


# ---------------------------------------------------------------------------
# F1: deterministic non-crossing traversal.
# ---------------------------------------------------------------------------


def traverse(mask, R):
    """Decompose an edge mask into embedded cycles.

    Returns a list of cycles, each a list of arcs (sheet, m_in, m_out).
    Raises ValueError on any structural failure (odd degree, leftover
    edges) — silence is the enemy.
    """
    zm = {e: (s, mid) for (e, s, mid) in R['zm_edges']}
    edges = []
    x = mask
    while x:
        b = x & (-x)
        e = b.bit_length() - 1
        x ^= b
        if e not in zm:
            raise ValueError(f"edge {e} not a zm-edge")
        edges.append((e,) + zm[e])

    at_sheet = defaultdict(list)   # sheet -> [(edge, mid)]
    at_seam = defaultdict(list)    # mid -> [(edge, sheet)]
    for e, s, mid in edges:
        at_sheet[s].append((e, mid))
        at_seam[mid].append((e, s))

    # transition maps: partner[edge, node] = next edge through node
    partner = {}
    for mid, inc in at_seam.items():
        if len(inc) != 2:
            raise ValueError(f"seam {mid} degree {len(inc)} != 2")
        (e1, _s1), (e2, _s2) = inc
        partner[(e1, ('m', mid))] = e2
        partner[(e2, ('m', mid))] = e1
    for s, inc in at_sheet.items():
        if len(inc) % 2:
            raise ValueError(f"sheet {s} odd degree {len(inc)}")
        if len(inc) == 2:
            (e1, _m1), (e2, _m2) = inc
            partner[(e1, ('z', s))] = e2
            partner[(e2, ('z', s))] = e1
            continue
        # non-crossing chords by angular order of seam anchors
        fi, _copy = s
        u1, u2 = face_plane(fi)
        fc = face_center(fi)
        ang = []
        for e, mid in inc:
            a4, _eu = seam_anchor(R, mid)
            d = a4 - fc
            ang.append((math.atan2(float(np.dot(d, u2)),
                                   float(np.dot(d, u1))), e))
        ang.sort()
        order = [e for _a, e in ang]
        for k in range(0, len(order), 2):
            e1, e2 = order[k], order[k + 1]
            partner[(e1, ('z', s))] = e2
            partner[(e2, ('z', s))] = e1

    # walk cycles: an edge is (sheet -- seam); traverse alternately
    cycles = []
    unused = {e for e, _s, _m in edges}
    einfo = {e: (s, mid) for e, s, mid in edges}
    while unused:
        e0 = next(iter(unused))
        s0, m0 = einfo[e0]
        # arcs recorded at sheets: enter via seam, leave via seam
        arcs = []
        e = e0
        enter_node = ('m', m0)  # we treat e0 as arriving at sheet s0 from m0
        while True:
            unused.discard(e)
            s, mid = einfo[e]
            if enter_node[0] == 'm':
                # arriving at the sheet: leave via sheet partner
                e_next = partner[(e, ('z', s))]
                _s2, mid_out = einfo[e_next]
                arcs.append((s, enter_node[1], mid_out))
                enter_node = ('z', s)
                e = e_next
            else:
                # arriving at the seam: leave via seam partner
                e_next = partner[(e, ('m', mid))]
                enter_node = ('m', mid)
                e = e_next
            if e == e0 and enter_node == ('m', m0):
                break
        cycles.append(arcs)
    return cycles


# ---------------------------------------------------------------------------
# Band construction per cycle (unchanged geometry, hardened plumbing).
# ---------------------------------------------------------------------------


def band_polylines(arcs, R):
    core = []
    strand_segs = []
    for ai, (s, m_in, m_out) in enumerate(arcs):
        fi, copy = s
        pd = ETA * push_dir(fi, copy)
        a_in, e_in = seam_anchor(R, m_in)
        a_out, e_out = seam_anchor(R, m_out)
        fc = face_center(fi)
        mid = 0.5 * (a_in + a_out)
        cpt = 0.75 * mid + 0.25 * fc
        core += [a_in + pd, cpt + pd, a_out + pd]
        u1, u2 = face_plane(fi)

        def to2d(v):
            return np.array([np.dot(v, u1), np.dot(v, u2)])

        din = to2d(cpt - a_in)
        dout = to2d(a_out - cpt)
        ein2, eout2 = to2d(e_in), to2d(e_out)

        def cross2(a, b):
            return a[0] * b[1] - a[1] * b[0]

        for sg_in in (+1, -1):
            side_in = 1 if cross2(din, sg_in * ein2) > 0 else -1
            sg_out = (+1 if (1 if cross2(dout, eout2) > 0 else -1) == side_in
                      else -1)
            pin = a_in + EPS * sg_in * e_in + pd
            pout = a_out + EPS * sg_out * e_out + pd
            moff = sg_in * e_in + sg_out * e_out
            nn = np.linalg.norm(moff)
            w = (sg_in * e_in) if nn < 1e-9 else moff / nn
            pmid = cpt + EPS * w + pd
            strand_segs.append(((ai, 'in', sg_in), (ai, 'out', sg_out),
                                [pin, pmid, pout]))
    nA = len(arcs)
    succ = {}
    for ai in range(nA):
        for sg in (+1, -1):
            succ[(ai, 'out', sg)] = ((ai + 1) % nA, 'in', sg)
    seg_by_in = {}
    for kin, kout, pts in strand_segs:
        seg_by_in[kin] = (kout, pts)
    loops = []
    visited = set()
    for kin0 in list(seg_by_in):
        if kin0 in visited:
            continue
        pts_all = []
        k = kin0
        while True:
            visited.add(k)
            kout, pts = seg_by_in[k]
            pts_all += pts
            k = succ[kout]
            if k == kin0:
                break
        loops.append(pts_all)
    return core, loops


def parity_of_edges(arcs, R):
    """Orientation-reversal parity of one cycle from seam clashes."""
    tot = 0
    # each consecutive arc pair crosses one seam; a cycle of arcs
    # crosses seams m_out(i) = m_in(i+1); parity = xor of clash over
    # crossed seams where the two sides differ in orientation class.
    # einfo_rho is defined per zm-edge; a crossing uses two zm-edges of
    # the same seam whose rho values xor to the seam clash.
    # Reconstruct per-crossing parity directly from seam clash:
    for ai, (s, m_in, m_out) in enumerate(arcs):
        sm = R['seams'][m_out]
        tot ^= sm['clash']
    return tot


def q_component(arcs, R):
    """Z4 value and pushed core for one embedded cycle."""
    par = parity_of_edges(arcs, R)
    core, loops = band_polylines(arcs, R)
    P = [stereo(p) for p in core]
    if len(loops) == 2 and par == 0:
        Q = [stereo(p) for p in loops[0]]
        lk = polyline_lk(P, Q)
        lki = round(lk)
        if abs(lk - lki) > 0.2:
            return None, None, f"lk not integral {lk:.3f}"
        return (2 * lki) % 4, P, None
    if len(loops) == 1 and par == 1:
        Q = [stereo(p) for p in loops[0]]
        lk = polyline_lk(P, Q)
        lki = round(lk)
        if abs(lk - lki) > 0.2:
            return None, None, f"lk not integral {lk:.3f}"
        if lki % 2 != 1:
            return None, None, f"moebius lk even {lki}"
        return lki % 4, P, None
    return None, None, f"loops {len(loops)} vs parity {par}"


def _q_once(mask, R):
    cycles = traverse(mask, R)
    total = 0
    cores = []
    for arcs in cycles:
        qv, P, err = q_component(arcs, R)
        if qv is None:
            return None
        total += qv
        cores.append(P)
    for i in range(len(cores)):
        for j in range(i + 1, len(cores)):
            lk = polyline_lk(cores[i], cores[j])
            lki = round(lk)
            if abs(lk - lki) > 0.2:
                return None
            total += 2 * lki
    return total % 4


def q_embedded(mask, R, cache):
    """Z4 refinement with a push-scale stability vote (F4): the value
    must agree at two different eta/eps scales, else FAIL loudly."""
    global ETA, EPS
    if mask in cache:
        return cache[mask]
    if mask == 0:
        cache[mask] = 0
        return 0
    try:
        v1 = _q_once(mask, R)
        ETA, EPS = ETA * 0.7, EPS * 0.7
        try:
            v2 = _q_once(mask, R)
        finally:
            ETA, EPS = ETA / 0.7, EPS / 0.7
    except ValueError:
        cache[mask] = None
        return None
    out = v1 if (v1 is not None and v1 == v2) else None
    cache[mask] = out
    return out
