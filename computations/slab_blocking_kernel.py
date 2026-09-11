"""DP.2 — the genuine 2x2 blocking kernel on the slab.

**Object.**  The 2x2x1 slab block (vertices (x,y,z), x,y in {0,1,2},
z in {0,1}) carries fine heat-kernel activities on its twelve "column"
faces: the four top tiles (z=1 horizontal plaquettes), the four bottom
tiles (z=0), and the four interior walls around the central 4-valent
vertical edge.  (The eight perimeter walls belong to the neighboring
blocks' columns and stay at spin 0.)  Coarse readout: a Wilson loop
chi_n around the top-tile perimeter and chi_m around the bottom.

Bivalence forces every top tile to spin n and every bottom tile to
spin m (each tile owns two perimeter edges shared only with its loop);
the interior wall spins w = (w1..w4) are the only sum, and it is
*exactly finite*: fusion at the cross edges gives w_i <= 2*min(n,m),
w_i even.  The blocked kernel is therefore the exact s-polynomial

  T[n,m](s) = (d_n s^{C(n)})^4 (d_m s^{C(m)})^4
              * sum_w  prod_i d_{w_i} s^{C(w_i)}  *  N(n, m, w),

with N(n,m,w) the certified Haar network value of the decorated slab
and C(n) = n(n+2) the (4x) Casimir.

**2D gate (must be exact).**  With walls frozen (w = 0) the network
splits into two disconnected 2D disks and character calculus gives
N(n,m,0) = d_n^{-3} d_m^{-3}, hence the classic 2D blocking rule
c'_n = c_n^4 / d_n^3 = d_n s^{4C(n)}: the flow is s' = s^4 with
corridor width EXACTLY zero.  The 3D defect from that baseline —
measured on the full kernel — is the DP.2 saturation quantity.

**Measurements.**
  1. entrywise sign of T on s in (0,1), Sturm-certified;
  2. Birkhoff/Hilbert projective diameter of T's columns and the
     contraction bound q = tanh(Delta/4), at several couplings;
  3. the flowed envelope: v = T e_s with e_m = d_m s^{C(m)}; fit s'
     from log(v_n/d_n) against C(n); the residual corridor width is
     the saturation number to compare with the wheel readout's 2.23
     (cutoff 5) from P18.

Run:  python -m computations.slab_blocking_kernel [cutoff]
"""

from __future__ import annotations

import itertools
import math
import sys
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from computations.exact_haar_network import (
    SPoly,
    brick_complex,
    casimir4,
    chi,
    dim,
    sign_on_unit_interval,
    sp_str,
)

Frac = Fraction


# ---------------------------------------------------------------------------
# Geometry: the slab block with its two coarse perimeter loops.
# ---------------------------------------------------------------------------


def _build():
    cx, faces = brick_complex(2, 2, 1)
    # vertex id map must mirror brick_complex's insertion order
    vid: Dict[Tuple[int, int, int], int] = {}
    for x in range(3):
        for y in range(3):
            for z in range(2):
                vid[(x, y, z)] = len(vid)
    eidx: Dict[Tuple[int, int], int] = {}
    for ei, (a, b) in enumerate(cx.edges):
        eidx[(a, b)] = ei

    def edge(pa, pb):
        a, b = vid[pa], vid[pb]
        if (a, b) in eidx:
            return eidx[(a, b)], 1
        return eidx[(b, a)], -1

    coords = {v: p for p, v in vid.items()}

    def face_kind(f):
        vs = set()
        for ei, _o in f:
            a, b = cx.edges[ei]
            vs.add(coords[a])
            vs.add(coords[b])
        xs = {v[0] for v in vs}
        ys = {v[1] for v in vs}
        zs = {v[2] for v in vs}
        if len(zs) == 1:
            return ("horiz", min(zs))
        if len(xs) == 1:
            return ("xwall", min(xs), min(ys))
        return ("ywall", min(ys), min(xs))

    top, bottom, walls = [], [], []
    for fi, f in enumerate(faces):
        k = face_kind(f)
        if k[0] == "horiz":
            (top if k[1] == 1 else bottom).append(fi)
        elif k[0] == "xwall" and k[1] == 1:
            walls.append(fi)
        elif k[0] == "ywall" and k[1] == 1:
            walls.append(fi)
    assert len(top) == 4 and len(bottom) == 4 and len(walls) == 4

    def perimeter(z):
        pts = [(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (1, 2), (0, 2), (0, 1)]
        loop = []
        for i in range(8):
            pa = pts[i] + (z,)
            pb = pts[(i + 1) % 8] + (z,)
            loop.append(edge(pa, pb))
        return loop

    # -- adapted gauge: spanning tree holding 7 of 8 perimeter edges per
    #    layer, so each coarse loop holonomy is a SINGLE free link.  The
    #    default BFS tree makes the loop networks explode (P18 lesson:
    #    frame choice is the whole game for contraction cost).
    pts = [(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (1, 2), (0, 2), (0, 1)]
    tree_edges = set()
    for z in (0, 1):
        for i in range(7):  # leave pts[7] -> pts[0] free
            ei, _o = edge(pts[i] + (z,), pts[i + 1] + (z,))
            tree_edges.add(ei)
        ei, _o = edge((1, 0, z), (1, 1, z))  # reach the layer center
        tree_edges.add(ei)
    ei, _o = edge((0, 0, 0), (0, 0, 1))  # connect the layers
    tree_edges.add(ei)
    assert len(tree_edges) == 17
    # verify spanning + acyclic via union-find
    parent = list(range(18))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for ei in tree_edges:
        a, b = cx.edges[ei]
        ra, rb = find(a), find(b)
        assert ra != rb, "cycle in adapted tree"
        parent[rb] = ra
    assert len({find(v) for v in range(18)}) == 1, "tree does not span"
    cx.tree = tree_edges
    cx.free = [ei for ei in range(len(cx.edges)) if ei not in tree_edges]

    return cx, faces, top, bottom, walls, perimeter(1), perimeter(0)


_CX, _FACES, _TOP, _BOTTOM, _WALLS, _LOOP_TOP, _LOOP_BOT = _build()


# ---------------------------------------------------------------------------
# The decorated network value N(n, m, w).
# ---------------------------------------------------------------------------


def network_value(n: int, m: int, w: Sequence[int]) -> SPoly:
    factors = []
    for fi in _TOP:
        if n > 0:
            factors.append(chi(n, _CX.holonomy_of(_FACES[fi])))
    for fi in _BOTTOM:
        if m > 0:
            factors.append(chi(m, _CX.holonomy_of(_FACES[fi])))
    for fi, wi in zip(_WALLS, w):
        if wi > 0:
            factors.append(chi(wi, _CX.holonomy_of(_FACES[fi])))
    if n > 0:
        factors.append(chi(n, _CX.holonomy_of(_LOOP_TOP)))
    if m > 0:
        factors.append(chi(m, _CX.holonomy_of(_LOOP_BOT)))
    if not factors:
        from computations.exact_haar_network import P_ONE

        factors = [dict(P_ONE)]
    return _CX.contract_invariant(factors)


def _wall_orbit_reps(wmax: int):
    """Dihedral (D4) orbit representatives of cyclic wall 4-tuples."""
    seen = set()
    reps = []
    for w in itertools.product(range(0, wmax + 1, 2), repeat=4):
        if w in seen:
            continue
        orbit = set()
        for k in range(4):
            r = w[k:] + w[:k]
            orbit.add(r)
            orbit.add(r[::-1])
        seen |= orbit
        reps.append((w, len(orbit)))
    return reps


def kernel_entry_frozen(n: int, m: int, verbose: bool = False) -> SPoly:
    """T[n,m] in the frozen-side scheme (12 column faces only).

    FINDING (recorded, not a bug): at slab thickness one, every
    interior wall owns an outer vertical edge whose only other faces
    are the frozen perimeter walls — univalence kills every w > 0
    term.  The frozen-side scheme is therefore EXACTLY the 2D
    blocking: T = c_n^4/d_n^3 x c_m^4/d_m^3, rank one, s' = s^4,
    corridor zero.  Transverse fluctuation requires the block to own
    its perimeter-wall fluctuations (kernel_entry below).
    """
    out: SPoly = {}
    wmax = 2 * min(n, m)
    pref = Frac(dim(n) ** 4 * dim(m) ** 4)
    base = 4 * casimir4(n) + 4 * casimir4(m)
    for w, mult in _wall_orbit_reps(wmax):
        val = network_value(n, m, w)
        if not val:
            continue
        assert set(val) == {0}
        c = pref * mult * val[0]
        for wi in w:
            c *= dim(wi)
        p = base + sum(casimir4(wi) for wi in w)
        out[p] = out.get(p, Frac(0)) + c
        if verbose:
            print(f"    walls {w} x{mult}: N = {val[0]}", flush=True)
    return {p: c for p, c in out.items() if c}


def _p_mul_reduced(a, b, budget: int = 2_000_000):
    """Exact product with unit reduction applied chunkwise.

    Multiplication distributes over monomial chunks and unit reduction
    is linear, so reducing chunk products before accumulation changes
    nothing mathematically while capping peak monomial counts.
    """
    from computations.exact_haar_network import (
        p_add_into,
        p_mul,
        p_reduce_units,
    )

    if len(a) > len(b):
        a, b = b, a
    if not a or not b:
        return p_mul(a, b)
    chunk = max(1, budget // max(1, len(a)))
    if len(b) <= chunk:
        return p_reduce_units(p_mul(a, b))
    items = list(b.items())
    acc = {}
    for i in range(0, len(items), chunk):
        part = dict(items[i:i + chunk])
        piece = p_reduce_units(p_mul(a, part))
        p_add_into(acc, piece)
    return p_reduce_units(acc)


def _eliminate_all(factors):
    """Greedy per-link elimination with unit reduction after every
    integration.  Uses only public engine primitives; unit reduction
    (|q|^2 = 1 on each link sphere) never changes a Haar integral, so
    exactness is preserved while intermediates stay small."""
    from computations.exact_haar_network import (
        MAX_RESULT_MONOMIALS,
        P_ONE,
        integrate_link,
        p_links,
        p_mul,
        p_reduce_units,
        scalar,
    )

    facs = [f for f in factors]
    todo = set()
    for f in facs:
        todo |= p_links(f)
    todo &= set(_CX.free)
    while todo:
        best, best_cost = None, None
        for link in todo:
            cost = 1
            for f in facs:
                if link in p_links(f):
                    cost *= max(1, len(f))
            if best_cost is None or cost < best_cost:
                best, best_cost = link, cost
        touched = sorted(
            (f for f in facs if best in p_links(f)), key=len
        )
        rest = [f for f in facs if best not in p_links(f)]
        merged = dict(P_ONE)
        for f in touched:
            # fold smallest-first; chunked multiply with unit reduction
            # inside the product keeps peak size bounded
            merged = _p_mul_reduced(merged, f)
        res = p_reduce_units(integrate_link(merged, best))
        facs = rest + [res]
        todo.discard(best)
    out = dict(P_ONE)
    for f in facs:
        out = p_mul(out, f)
    return scalar(out)


def _free_link_stages():
    """Partition the free links: bottom-layer, top-layer, vertical."""
    coords = {}
    i = 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                coords[i] = (x, y, z)
                i += 1
    bottom, top, vert = [], [], []
    for ei in _CX.free:
        a, b = _CX.edges[ei]
        if coords[a][2] != coords[b][2]:
            vert.append(ei)
        elif coords[a][2] == 0:
            bottom.append(ei)
        else:
            top.append(ei)
    return bottom, top, vert


def kernel_entry(n: int, m: int, M: int) -> SPoly:
    """T[n,m] in the owned-boundary scheme, truncation M.

    Heat-kernel activities on ALL 20 slab faces (top/bottom tiles,
    interior walls, perimeter walls), coarse loops chi_n (top
    perimeter) and chi_m (bottom).  The perimeter walls make the top
    perimeter edges trivalent, so tile spins are no longer forced:
    the full transverse fluctuation of the block is integrated.  M is
    a scheme parameter (activity truncation); measurements must be
    reported with their M-stability.

    Contraction is STAGED (bottom links, then top, then verticals)
    with unit-sphere reduction of intermediates between stages —
    p_reduce_units replaces components modulo |q|^2 = 1, which leaves
    every Haar integral unchanged, so exactness is preserved.
    """
    from computations.exact_haar_network import (
        contract,
        heat_activity,
        p_links,
        p_reduce_units,
        scalar,
    )

    factors = []
    for fi in range(len(_FACES)):
        factors.append(
            p_reduce_units(heat_activity(_CX.holonomy_of(_FACES[fi]), M))
        )
    if n > 0:
        factors.append(chi(n, _CX.holonomy_of(_LOOP_TOP)))
    if m > 0:
        factors.append(chi(m, _CX.holonomy_of(_LOOP_BOT)))

    return _eliminate_all(factors)


# ---------------------------------------------------------------------------
# Skeleton decomposition: the tractable exact route to the full kernel.
#
# Corner vertical edges are bivalent in perimeter walls, forcing the
# eight walls into four corner-linked classes q1..q4 (one per corner,
# cyclic).  Fixing the transverse skeleton (q1..q4; interior walls
# w1..w4) leaves only the eight tile activities + two loops — a small
# contraction per skeleton.  The skeleton sum is finite at truncation
# M and inherits the D4 symmetry of the slab.
# ---------------------------------------------------------------------------

# perimeter wall faces by side, ordered (side y=0, x=2, y=2, x=0) so
# that corner i couples class q_i between side i-1 and side i.


def _perimeter_wall_faces():
    coords = {}
    i = 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                coords[i] = (x, y, z)
                i += 1

    def kind(fi):
        vs = set()
        for ei, _o in _FACES[fi]:
            a, b = _CX.edges[ei]
            vs.add(coords[a])
            vs.add(coords[b])
        xs = {v[0] for v in vs}
        ys = {v[1] for v in vs}
        zs = {v[2] for v in vs}
        if len(zs) == 1:
            return None
        if len(xs) == 1 and min(xs) in (0, 2):
            return ("x", min(xs), min(ys))
        if len(ys) == 1 and min(ys) in (0, 2):
            return ("y", min(ys), min(xs))
        return None

    walls = {}
    for fi in range(len(_FACES)):
        k = kind(fi)
        if k:
            walls[k] = fi
    # classes: q1 owns walls (y=0, x∈[0,1]) and (x=0, y∈[0,1]);
    # cyclically: q_i = the two walls meeting at corner i.
    classes = [
        (walls[("y", 0, 0)], walls[("x", 0, 0)]),  # corner (0,0)
        (walls[("y", 0, 1)], walls[("x", 2, 0)]),  # corner (2,0)
        (walls[("y", 2, 1)], walls[("x", 2, 1)]),  # corner (2,2)
        (walls[("y", 2, 0)], walls[("x", 0, 1)]),  # corner (0,2)
    ]
    return classes


_PWALL_CLASSES = _perimeter_wall_faces()
# interior wall sides in cyclic order matching the classes: the wall
# between corners i and i+1 (side y=0 couples q1,q2, etc.)


def _interior_wall_by_side():
    coords = {}
    i = 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                coords[i] = (x, y, z)
                i += 1
    info = {}
    for fi in _WALLS:
        vs = set()
        for ei, _o in _FACES[fi]:
            a, b = _CX.edges[ei]
            vs.add(coords[a])
            vs.add(coords[b])
        xs = {v[0] for v in vs}
        ys = {v[1] for v in vs}
        if len(xs) == 1:  # xwall at x=1, y in [y0, y0+1]
            info[("x", min(ys))] = fi
        else:
            info[("y", min(xs))] = fi
    # side order: y=0 (q1,q2): wall x=1 y∈[0,1] -> ("x",0);
    # x=2 (q2,q3): wall y=1 x∈[1,2] -> ("y",1);
    # y=2 (q3,q4): wall x=1 y∈[1,2] -> ("x",1);
    # x=0 (q4,q1): wall y=1 x∈[0,1] -> ("y",0).
    return [info[("x", 0)], info[("y", 1)], info[("x", 1)], info[("y", 0)]]


_IWALL_SIDES = _interior_wall_by_side()


def _triad_ok(a: int, b: int, c: int) -> bool:
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


def skeleton_value(n: int, m: int, q: Sequence[int], w: Sequence[int],
                   M: int) -> SPoly:
    """Engine value of the slab with fixed transverse skeleton.

    Tiles carry summed heat activities (<= M); perimeter classes q and
    interior walls w are fixed characters; loops chi_n / chi_m.
    """
    from computations.exact_haar_network import (
        contract,
        heat_activity,
        p_links,
        p_reduce_units,
        scalar,
    )

    factors = []
    for fi in _TOP + _BOTTOM:
        factors.append(
            p_reduce_units(heat_activity(_CX.holonomy_of(_FACES[fi]), M))
        )
    for qi, (fa, fb) in zip(q, _PWALL_CLASSES):
        if qi > 0:
            factors.append(chi(qi, _CX.holonomy_of(_FACES[fa])))
            factors.append(chi(qi, _CX.holonomy_of(_FACES[fb])))
    for wi, fi in zip(w, _IWALL_SIDES):
        if wi > 0:
            factors.append(chi(wi, _CX.holonomy_of(_FACES[fi])))
    if n > 0:
        factors.append(chi(n, _CX.holonomy_of(_LOOP_TOP)))
    if m > 0:
        factors.append(chi(m, _CX.holonomy_of(_LOOP_BOT)))

    return _eliminate_all(factors)


def _skeletons(M: int):
    """Admissible transverse skeletons (q1..q4, w1..w4), prefiltered."""
    out = []
    for q in itertools.product(range(M + 1), repeat=4):
        wchoice = []
        ok = True
        for i in range(4):
            qa, qb = q[i], q[(i + 1) % 4]
            ws = [w for w in range(M + 1) if _triad_ok(qa, qb, w)]
            if not ws:
                ok = False
                break
            wchoice.append(ws)
        if not ok:
            continue
        for w in itertools.product(*wchoice):
            if sum(w) % 2:
                continue  # central 4-valent edge parity
            out.append((q, w))
    return out


def _canon(q, w):
    """Canonical form under D4 acting cyclically on (q, w) together.

    Rotation by k sends q -> q[k:]+q[:k], w -> w[k:]+w[:k]; reflection
    reverses corners and re-aligns sides (side i couples q_i, q_{i+1};
    after reversal side i couples the reversed pair, index shift).
    """
    best = None
    for k in range(4):
        qq = q[k:] + q[:k]
        ww = w[k:] + w[:k]
        for refl in (False, True):
            if refl:
                q2 = (qq[0],) + tuple(reversed(qq[1:]))
                w2 = tuple(reversed(ww))
            else:
                q2, w2 = qq, ww
            cand = (q2, w2)
            if best is None or cand < best:
                best = cand
    return best


def kernel_entry_skeleton(n: int, m: int, M: int,
                          progress: bool = False) -> SPoly:
    """T[n,m] via the skeleton sum (owned-boundary scheme)."""
    kernel_entry_skeleton.last_unreached = []
    # group skeletons by canonical class
    classes: Dict[Tuple, List[Tuple]] = {}
    for q, w in _skeletons(M):
        classes.setdefault(_canon(q, w), []).append((q, w))
    def _layer_feasible(nn: int, q, w) -> bool:
        """Exists tile assignment a1..a4 <= M with all edge triads?"""
        cand = [[a for a in range(M + 1) if _triad_ok(nn, qi, a)]
                for qi in q]
        if any(not c for c in cand):
            return False

        def rec(i, chosen):
            if i == 4:
                return _triad_ok(chosen[3], chosen[0], w[3])
            for a in cand[i]:
                if i > 0 and not _triad_ok(chosen[-1], a, w[i - 1]):
                    continue
                if rec(i + 1, chosen + [a]):
                    return True
            return False

        return rec(0, [])

    out: SPoly = {}
    done = 0
    for rep, members in classes.items():
        q, w = rep
        if not _layer_feasible(n, q, w) or not _layer_feasible(m, q, w):
            continue
        import signal

        def _alarm(_sig, _frm):
            raise TimeoutError("skeleton wall-clock budget exceeded")

        old_h = signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(120)
        try:
            val = skeleton_value(n, m, q, w, M)
        except Exception as exc:
            kernel_entry_skeleton.last_unreached.append((q, w, str(exc)))
            continue
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old_h)
        done += 1
        if progress and done % 10 == 0:
            print(f"    ...{done} skeleton classes", flush=True)
        if not val:
            continue
        weight_pow = sum(2 * casimir4(qi) for qi in q) + sum(
            casimir4(wi) for wi in w
        )
        weight_c = Frac(1)
        for qi in q:
            weight_c *= dim(qi) ** 2
        for wi in w:
            weight_c *= dim(wi)
        for p, c in val.items():
            key = p + weight_pow
            out[key] = out.get(key, Frac(0)) + c * weight_c * len(members)
    return {p: c for p, c in out.items() if c}


def kernel_entry_2d_gate(n: int, M: int) -> SPoly:
    """Top tiles + top loop only: must equal d_n s^{4 C(n)} exactly."""
    from computations.exact_haar_network import heat_activity

    factors = [heat_activity(_CX.holonomy_of(_FACES[fi]), M) for fi in _TOP]
    if n > 0:
        factors.append(chi(n, _CX.holonomy_of(_LOOP_TOP)))
    return _CX.contract_invariant(factors)


def eval_spoly(p: SPoly, s: Fraction) -> Fraction:
    return sum(c * s**k for k, c in p.items())


# ---------------------------------------------------------------------------
# Measurements.
# ---------------------------------------------------------------------------


def hilbert_diameter(cols: List[List[Fraction]]) -> float:
    worst = Frac(1)
    for a in range(len(cols)):
        for b in range(a + 1, len(cols)):
            r1 = max(x / y for x, y in zip(cols[a], cols[b]))
            r2 = max(y / x for x, y in zip(cols[a], cols[b]))
            if r1 * r2 > worst:
                worst = r1 * r2
    return math.log(float(worst))


def flow_fit(v: Dict[int, Fraction]):
    """Fit log(v_n/d_n) = a + log(s') C(n); return (s', corridor width)."""
    xs = [casimir4(n) for n in v]
    ys = [math.log(float(val / dim(n))) for n, val in v.items()]
    k = len(xs)
    xb = sum(xs) / k
    yb = sum(ys) / k
    slope = sum((x - xb) * (y - yb) for x, y in zip(xs, ys)) / sum(
        (x - xb) ** 2 for x in xs
    )
    resid = [y - (yb + slope * (x - xb)) for x, y in zip(xs, ys)]
    return math.exp(slope), max(resid) - min(resid)


def main() -> None:
    cutoff = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    print(f"DP.2 slab blocking kernel, coarse spins <= {cutoff}, "
          f"activity truncation M = {M}")

    print("=" * 72)
    print("GATE 1 — 2D limit: N(n,m,0) must equal d_n^-3 d_m^-3 exactly")
    ok = True
    for n in range(cutoff + 1):
        for m in range(n, cutoff + 1):
            val = network_value(n, m, (0, 0, 0, 0))
            want = Frac(1, dim(n) ** 3 * dim(m) ** 3)
            good = val and set(val) == {0} and val[0] == want
            ok &= bool(good)
            tag = "OK" if good else f"FAIL (got {val}, want {want})"
            print(f"  N({n},{m},0) : {tag}")
    print(f"  gate 1: {'PASSED' if ok else 'FAILED'}")

    print("=" * 72)
    print("GATE 2 — bivalence forcing: one non-uniform tile must vanish")
    factors = []
    spins = [1, 1, 1, 3]
    for fi, a in zip(_TOP, spins):
        factors.append(chi(a, _CX.holonomy_of(_FACES[fi])))
    factors.append(chi(1, _CX.holonomy_of(_LOOP_TOP)))
    val = _CX.contract_invariant(factors)
    print(f"  mixed-tile network value: {val if val else 0}  "
          f"({'OK' if not val else 'FAIL'})")

    print("=" * 72)
    print("GATE 3 — frozen-side scheme collapses to exact 2D blocking")
    ok3 = True
    for n in range(min(cutoff, 2) + 1):
        for m in range(n, min(cutoff, 2) + 1):
            e = kernel_entry_frozen(n, m)
            want = {4 * casimir4(n) + 4 * casimir4(m):
                    Frac(dim(n) * dim(m))}
            want = {k: v for k, v in want.items() if v}
            good = e == want
            ok3 &= good
            print(f"  frozen T[{n},{m}] = {sp_str(e) if e else 0}  "
                  f"({'= d_n d_m s^(4C_n+4C_m), OK' if good else 'FAIL'})")
    print(f"  gate 3 (univalence death of walls => pure 2D): "
          f"{'PASSED' if ok3 else 'FAILED'}")

    print("=" * 72)
    print("GATE 4 — 2D open-disk gate: top tiles + loop = d_n s^{4C(n)}")
    ok4 = True
    for n in range(cutoff + 1):
        e = kernel_entry_2d_gate(n, min(M, 2 * 2))
        want = {4 * casimir4(n): Frac(dim(n))}
        want = {k: v for k, v in want.items() if v}
        good = e == want
        ok4 &= good
        print(f"  c'_{n} = {sp_str(e) if e else 0}  "
              f"({'OK' if good else 'FAIL, want ' + sp_str(want)})")
    print(f"  gate 4: {'PASSED' if ok4 else 'FAILED'}")

    print("=" * 72)
    print(f"Kernel entries T[n,m] (owned-boundary scheme), n,m <= {cutoff}")
    T: Dict[Tuple[int, int], SPoly] = {}
    for n in range(cutoff + 1):
        for m in range(n, cutoff + 1):
            try:
                e = kernel_entry(n, m, M)
            except Exception as exc:  # ContractionTooLarge -> UNREACHED
                print(f"  T[{n},{m}]: UNREACHED ({exc})", flush=True)
                return
            T[(n, m)] = e
            T[(m, n)] = e
            verdict = sign_on_unit_interval(e) if e else "zero"
            nterm = len(e)
            print(f"  T[{n},{m}]: {nterm} terms, "
                  f"low {min(e) if e else '-'} high {max(e) if e else '-'}; "
                  f"sign on (0,1): {verdict}", flush=True)

    print("=" * 72)
    print("Birkhoff diameter of columns (rows n >= 1 kept; several s)")
    idx = list(range(1, cutoff + 1))
    for sv in (Frac(1, 4), Frac(1, 2), Frac(3, 4)):
        cols = []
        usable = True
        for m in idx:
            col = [eval_spoly(T[(n, m)], sv) for n in idx]
            if any(v <= 0 for v in col):
                usable = False
            cols.append(col)
        if not usable or len(cols) < 2:
            print(f"  s={sv}: sector not strictly positive; skipped")
            continue
        d = hilbert_diameter(cols)
        print(f"  s={sv}: Delta = {d:.4f}, q = tanh(D/4) = {math.tanh(d/4):.6f}")

    print("=" * 72)
    print("Flowed envelope: v = T e_s; fit s'; corridor width  "
          "(2D baseline: s' = s^4, width 0)")
    for sv in (Frac(1, 4), Frac(1, 2), Frac(3, 4)):
        v = {}
        good = True
        for n in idx:
            acc = Frac(0)
            for m in range(cutoff + 1):
                e_m = Frac(dim(m)) * sv ** casimir4(m)
                acc += eval_spoly(T[(n, m)], sv) * e_m
            if acc <= 0:
                good = False
                break
            v[n] = acc
        if not good or len(v) < 2:
            print(f"  s={sv}: flowed image not positive; skipped")
            continue
        sp, width = flow_fit(v)
        print(f"  s={sv}: fitted s' = {sp:.6f}  (s^4 = {float(sv)**4:.6f})  "
              f"corridor log-width = {width:.4f}")


if __name__ == "__main__":
    main()
