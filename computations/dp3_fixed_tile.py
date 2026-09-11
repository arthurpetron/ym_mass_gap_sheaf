"""Fixed-tile refinement of the DP.2 skeleton sum.

`slab_blocking_kernel.skeleton_value` contracts the slab with the eight
tile faces carrying full truncated heat-kernel activities (polynomial
factors).  Because

    heat_activity(U, M) = sum_{a <= M} d_a s^{C(a)} chi_a(U),

that value equals a sum over FIXED tile labellings of pure-character
network values:

    skeleton_value(n, m, q, w, M)
      = sum_{top, bot}  prod_i d_{a_i} s^{C(a_i)} d_{b_i} s^{C(b_i)}
                        * N(n, m, q, w, top, bot),

with N the Haar value of a network all of whose factors are single
characters.  Each such contraction is far smaller than the polynomial
one, so classes that exceed the wall-clock budget in the polynomial
scheme become reachable here.

More importantly for DP.3-(i): the fixed-tile form exposes the SIGN
question at its natural granularity.  Every weight above is strictly
positive, so a negative coefficient in T[n,m] can only originate in a
negative pure-network value N — i.e. in signed 6j recoupling
interference.  Auditing the N's directly is therefore the sharp test,
and it is per-configuration rigorous: each N is an exact rational,
independent of whether any other class was reached.

Tile indexing.  Corner/cyclic order matches `_PWALL_CLASSES` and
`_IWALL_SIDES` of the kernel module: corner i in
[(0,0), (2,0), (2,2), (0,2)], so tile i is the z-layer plaquette with
lower corner [(0,0), (1,0), (1,1), (0,1)][i], and interior wall w_i
separates tiles i and i+1.  This correspondence is not assumed: the
`gate()` below rebuilds `skeleton_value` from the fixed-tile sum and
demands exact polynomial equality.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, Sequence

from computations.exact_haar_network import casimir4, chi, dim
from computations.slab_blocking_kernel import (
    _CX,
    _FACES,
    _IWALL_SIDES,
    _LOOP_BOT,
    _LOOP_TOP,
    _PWALL_CLASSES,
    _eliminate_all,
    skeleton_value,
)

Frac = Fraction
SPoly = Dict[int, Fraction]


def _coords():
    c, i = {}, 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                c[i] = (x, y, z)
                i += 1
    return c


def _tiles_in_corner_order(z: int):
    """The four z-layer horizontal faces, in corner order."""
    coords = _coords()
    want = [(0, 0), (1, 0), (1, 1), (0, 1)]
    found = {}
    for fi, f in enumerate(_FACES):
        vs = set()
        for ei, _o in f:
            a, b = _CX.edges[ei]
            vs.add(coords[a])
            vs.add(coords[b])
        zs = {v[2] for v in vs}
        if len(zs) != 1 or min(zs) != z:
            continue
        found[(min(v[0] for v in vs), min(v[1] for v in vs))] = fi
    return [found[p] for p in want]


TOP_TILES = _tiles_in_corner_order(1)
BOT_TILES = _tiles_in_corner_order(0)


def network_value_fixed(n: int, m: int, q: Sequence[int], w: Sequence[int],
                        top: Sequence[int], bot: Sequence[int]) -> SPoly:
    """Pure-character Haar value N(n, m, q, w, top, bot) (no s-weights)."""
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
        from computations.exact_haar_network import P_ONE
        factors = [dict(P_ONE)]
    return _eliminate_all(factors)


def _triad_ok(a, b, c):
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


def layer_labellings(loop: int, q, w, M: int):
    import itertools
    cand = [[a for a in range(M + 1) if _triad_ok(loop, qi, a)] for qi in q]
    out = []
    for tiles in itertools.product(*cand):
        if all(_triad_ok(tiles[i - 1], tiles[i], w[i - 1]) for i in range(4)):
            out.append(tiles)
    return out


def skeleton_value_fixed(n: int, m: int, q, w, M: int, collect=None) -> SPoly:
    """Rebuild skeleton_value as a sum over fixed tile labellings.

    If `collect` is a list, each (top, bot, N) with N != 0 is appended —
    the per-configuration data the sign audit consumes.
    """
    out: SPoly = {}
    for top in layer_labellings(n, q, w, M):
        for bot in layer_labellings(m, q, w, M):
            N = network_value_fixed(n, m, q, w, top, bot)
            if not N:
                continue
            assert set(N) == {0}, "pure-character network must be a scalar"
            val = N[0]
            if collect is not None:
                collect.append((tuple(top), tuple(bot), val))
            c = val
            for a in top:
                c *= dim(a)
            for b in bot:
                c *= dim(b)
            e = (sum(casimir4(a) for a in top)
                 + sum(casimir4(b) for b in bot))
            out[e] = out.get(e, Frac(0)) + c
    return {k: v for k, v in out.items() if v}


def gate(cases, M: int = 2, verbose: bool = True) -> bool:
    """Fixed-tile sum must equal skeleton_value exactly on `cases`."""
    ok = True
    for (n, m, q, w) in cases:
        mine = skeleton_value_fixed(n, m, q, w, M)
        theirs = skeleton_value(n, m, q, w, M)
        good = mine == theirs
        ok &= good
        if verbose:
            print(f"  gate n={n} m={m} q={q} w={w}: "
                  f"{'OK' if good else f'MISMATCH {mine} vs {theirs}'}",
                  flush=True)
    return ok
