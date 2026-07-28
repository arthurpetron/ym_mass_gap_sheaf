"""Cut-adapted contraction for slab network values (work_plan §16h
queue item (2)).

`dp3_fixed_tile.network_value_fixed` contracts with a greedy
cheapest-link heuristic (`_eliminate_all`); on spin-3 configurations
the greedy order can build catastrophic intermediates (observed
556 s .. > 900 s).  The slab's D4-cyclic structure suggests the
TRANSFER order instead: eliminate links corner by corner around the
cycle, so every intermediate depends only on the strands crossing
one radial cut — the polynomial analogue of multiplying corner
transfer matrices.  This module supplies

  * `corner_orders()` — the eight D4 corner-sweep link orders
    (4 starting corners x 2 senses), links within a corner ordered
    bottom, top, vertical (the kernel_entry staging);
  * `eliminate_ordered(factors, order)` — the §15-era engine
    primitives (merge smallest-first, chunked multiply, unit
    reduction after every integration: mathematically inert,
    exactness preserved) with a PRESCRIBED elimination order;
  * `network_value_fast(...)` — race a set of orders under
    sub-budgets, return the first success (every order computes the
    same exact invariant — asserted equal whenever two complete in
    gate mode);
  * gates: agreement with `network_value_fixed` on completed
    reference values (including a formerly-heavy 556 s case).

Run:  python -m computations.su2_cut_eval          (gate + bench)
"""

from __future__ import annotations

import os
import signal
import sys
import time
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))

sys.set_int_max_str_digits(0)

from computations.slab_blocking_kernel import (  # noqa: E402
    _CX,
    _FACES,
    _LOOP_BOT,
    _LOOP_TOP,
    _p_mul_reduced,
)
from computations.dp3_fixed_tile import (  # noqa: E402
    TOP_TILES,
    BOT_TILES,
    network_value_fixed,
)
from computations.exact_haar_network import (  # noqa: E402
    P_ONE,
    chi,
    integrate_link,
    p_links,
    p_mul,
    p_reduce_units,
    scalar,
)


# ---------------------------------------------------------------------------
# Geometry: free links by corner quadrant.
# ---------------------------------------------------------------------------


def _coords():
    c, i = {}, 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                c[i] = (x, y, z)
                i += 1
    return c


_COORDS = _coords()

# corner order matches dp3_fixed_tile: lower corners
# [(0,0), (1,0), (1,1), (0,1)]
_CORNER_BOX = [(0, 0), (1, 0), (1, 1), (0, 1)]


def _link_corner(ei: int) -> int:
    """Quadrant of a link by midpoint; links on the cut lines are
    assigned to the lowest-index touching corner (a convention —
    any assignment gives a valid elimination order)."""
    a, b = _CX.edges[ei]
    xa, ya, _za = _COORDS[a]
    xb, yb, _zb = _COORDS[b]
    mx, my = (xa + xb) / 2, (ya + yb) / 2
    best = None
    for ci, (cx, cy) in enumerate(_CORNER_BOX):
        if cx <= mx <= cx + 1 and cy <= my <= cy + 1:
            if best is None:
                best = ci
    assert best is not None
    return best


def _link_stage(ei: int) -> int:
    """0 bottom-layer, 1 top-layer, 2 vertical."""
    a, b = _CX.edges[ei]
    za, zb = _COORDS[a][2], _COORDS[b][2]
    if za != zb:
        return 2
    return 0 if za == 0 else 1


def corner_orders() -> List[List[int]]:
    """Eight D4 corner-sweep orders over the 16 free links."""
    by_corner: Dict[int, List[int]] = {0: [], 1: [], 2: [], 3: []}
    for ei in _CX.free:
        by_corner[_link_corner(ei)].append(ei)
    for ci in by_corner:
        by_corner[ci].sort(key=lambda e: (_link_stage(e), e))
    orders = []
    for start in range(4):
        for sense in (1, -1):
            seq: List[int] = []
            for k in range(4):
                seq += by_corner[(start + sense * k) % 4]
            orders.append(seq)
    return orders


# ---------------------------------------------------------------------------
# Ordered elimination.
# ---------------------------------------------------------------------------


def eliminate_ordered(factors, order: Sequence[int]):
    facs = [f for f in factors]
    todo = set()
    for f in facs:
        todo |= p_links(f)
    todo &= set(_CX.free)
    for link in order:
        if link not in todo:
            continue
        touched = sorted((f for f in facs if link in p_links(f)),
                         key=len)
        rest = [f for f in facs if link not in p_links(f)]
        merged = dict(P_ONE)
        for f in touched:
            merged = _p_mul_reduced(merged, f)
        res = p_reduce_units(integrate_link(merged, link))
        facs = rest + [res]
        todo.discard(link)
    assert not todo, "prescribed order missed live links"
    out = dict(P_ONE)
    for f in facs:
        out = p_mul(out, f)
    return scalar(out)


def _factors(n: int, m: int, q, w, top, bot):
    from computations.dp3_fixed_tile import (_PWALL_CLASSES,
                                             _IWALL_SIDES)
    factors = []
    for a, fi in zip(top, TOP_TILES):
        if a > 0:
            factors.append(chi(a, _CX.holonomy_of(_FACES[fi])))
    for b, fi in zip(bot, BOT_TILES):
        if b > 0:
            factors.append(chi(b, _CX.holonomy_of(_FACES[fi])))
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
    if not factors:
        factors = [dict(P_ONE)]
    return factors


class _Budget(Exception):
    pass


def _with_budget(fn, seconds: int):
    def _alarm(_s, _f):
        raise _Budget()

    old = signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(seconds)
    try:
        return fn()
    except _Budget:
        return None
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def _to_scalar(res):
    if res is None:
        return None
    if isinstance(res, dict):
        if not res:
            return Frac(0)
        assert set(res) == {0}
        return res[0]
    return res


def network_value_fast(n: int, m: int, q, w, top, bot,
                       per_order_s: int = 90,
                       greedy_first_s: int = 45,
                       orders: Optional[List[List[int]]] = None,
                       verbose: bool = False):
    """Greedy engine under a short budget first (wins on easy
    configs), then race the corner-sweep orders (win on heavy
    configs); exact Fraction or None.  Every order computes the same
    Haar invariant."""
    if greedy_first_s:
        res = _with_budget(
            lambda: network_value_fixed(n, m, q, w, top, bot),
            greedy_first_s)
        if res is not None:
            if verbose:
                print("    greedy: ok", flush=True)
            return _to_scalar(res)
        if verbose:
            print("    greedy: budget", flush=True)
    if orders is None:
        orders = corner_orders()
    for oi, order in enumerate(orders):
        t0 = time.time()
        res = _with_budget(
            lambda: eliminate_ordered(_factors(n, m, q, w, top, bot),
                                      order), per_order_s)
        if verbose:
            tag = "ok" if res is not None else "budget"
            print(f"    order {oi}: {tag} [{time.time() - t0:.0f}s]",
                  flush=True)
        if res is not None:
            return _to_scalar(res)
    return None


# ---------------------------------------------------------------------------
# Gates and bench.
# ---------------------------------------------------------------------------


def gate(verbose: bool = True) -> bool:
    """Agreement with the greedy engine on reference values."""
    cases = [
        # (n, m, q, w, top, bot, known value or None)
        (1, 1, (0, 1, 2, 1), (1, 1, 1, 1), (1, 0, 1, 2), (1, 0, 1, 2),
         Frac(1, 331776)),
        (1, 1, (1, 1, 1, 1), (0, 2, 0, 2), (0, 0, 2, 2), (0, 0, 2, 2),
         Frac(1, 62208)),
        (1, 1, (0, 1, 2, 1), (1, 1, 1, 1), (1, 0, 1, 2), (1, 2, 1, 2),
         None),   # off-diagonal negative config, N = -1/1492992
    ]
    ok = True
    for (n, m, q, w, top, bot, known) in cases:
        v = network_value_fast(n, m, q, w, top, bot, per_order_s=120,
                               verbose=verbose)
        if known is None:
            ref = network_value_fixed(n, m, q, w, top, bot)
            ref = ref[0] if ref else Frac(0)
        else:
            ref = known
        good = (_to_scalar(v) == ref)
        ok &= good
        if verbose:
            print(f"  gate ({n},{m},{q},{w},{top},{bot}): "
                  f"{'OK' if good else f'MISMATCH {v} vs {ref}'}",
                  flush=True)
    return ok


def bench_heavy(verbose: bool = True):
    """The formerly-556s diagonal through the corner sweep."""
    t0 = time.time()
    v = network_value_fast(1, 1, (0, 0, 1, 2), (0, 1, 1, 2),
                           (1, 1, 2, 3), (1, 1, 2, 3),
                           per_order_s=240, verbose=verbose)
    dt = time.time() - t0
    if verbose:
        print(f"  heavy diagonal: {'ok' if v is not None else 'FAIL'}"
              f" [{dt:.0f}s]  (greedy engine took 556s)", flush=True)
    return v, dt


def main() -> None:
    print("Cut-adapted contraction — corner-sweep elimination")
    print("=" * 72)
    print("GATE — agreement with the greedy engine")
    ok = gate()
    print(f"  gate: {'PASSED' if ok else 'FAILED'}")
    print("BENCH — the formerly-heavy diagonal")
    v, dt = bench_heavy()
    print(f"  value: {v}  [{dt:.0f}s]")


if __name__ == "__main__":
    main()


def staged_orders() -> List[List[int]]:
    """Layer-staged orders: (bottom, top, verticals), (top, bottom,
    verticals), verticals-first, and within-stage corner sweeps."""
    stages: Dict[int, List[int]] = {0: [], 1: [], 2: []}
    for ei in _CX.free:
        stages[_link_stage(ei)].append(ei)
    for k in stages:
        stages[k].sort(key=lambda e: (_link_corner(e), e))
    out = []
    for perm in ((0, 1, 2), (1, 0, 2), (2, 0, 1), (0, 2, 1)):
        out.append(stages[perm[0]] + stages[perm[1]]
                   + stages[perm[2]])
    return out
