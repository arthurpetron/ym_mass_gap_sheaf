"""Vertex-amplitude product formula for trivalent-edge complexes (DP.1).

**The formula.**  On the 4-cube boundary — where every edge of the
complex is trivalent, so every SU(2) intertwiner space is
multiplicity-free — the exact dual amplitude of ANY admissible
plaquette-spin assignment factorizes completely:

    Z(assignment)  =  prod_{v in 16 vertices}  {6j}_v ,

where {6j}_v is the Wigner symbol of the six incident face spins in
the vertex-link tetrahedron arrangement

    {  j_xy  j_xz  j_xt  ;  j_zt  j_yt  j_yz  }   (labels j = n/2),

with NO face, edge, theta, or phase corrections of any kind.  The
Wigner 6j's tetrahedral symmetry makes the slot order canonical, and
intertwiner phase gauges cancel because each edge's intertwiner
appears in exactly two vertex tetrahedra.

**Certification.**  The formula was not assumed; it was fitted and then
over-verified against the certified moment-engine corpus: all 128
binary surfaces and their doublings, plus all 693 exact
intersecting-pair evaluations — 949/949 exact matches including signs.
Where the formula disagreed with a *hand census* (support-12 surfaces),
direct moment integration sided with the formula: those surfaces are
disjoint unions of two spheres (chi = 4), and Z = 2^{chi-F} = 1/256.

**What it buys.**  Amplitude evaluation drops from hours of monomial
contraction to sixteen memoized 6j lookups.  It closed the 109th orbit
(the full double-torus collision):

    Z  =  prod of sixteen (+1/6)  =  6^{-16}  =  1/2821109907456  > 0,

completing the 4D pair survey at 109/109, all positive — and it turns
exhaustive higher-spin sweeps (triples, quadruples of surfaces) from
impossible to routine.

Speed/provenance split: squared 6j data has moment-engine provenance
(computations/su2_recoupling_data.py: K4 = {6j}^2, 181/181 vs sympy);
signs come from sympy's Wigner conventions, memoized.  Arithmetic in
the hot path is pure Fraction + integer square roots.

Run:  python -m computations.vertex_amplitude
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction
from functools import lru_cache
from typing import Dict, List, Optional, Sequence, Tuple

from computations.hypercube4d_survey import (
    hypercube,
    kernel_basis,
    surfaces,
)

# ---------------------------------------------------------------------------
# Vertex incidence of the 4-cube boundary.
# ---------------------------------------------------------------------------

_CX, _FACES, _META = hypercube()
NF = len(_FACES)
VERTS: List[Tuple[int, int, int, int]] = list(itertools.product((0, 1), repeat=4))

_PLANES = [(0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2)]  # xy xz xt zt yt yz


def _faces_at_vertex(v) -> Dict[Tuple[int, int], int]:
    out = {}
    for fi, (p, d1, d2) in enumerate(_META):
        if all(p[d] == v[d] for d in range(4) if d not in (d1, d2)):
            out[(d1, d2)] = fi
    assert len(out) == 6
    return out


VERTEX_FACES: Dict[Tuple[int, int, int, int], Dict[Tuple[int, int], int]] = {
    v: _faces_at_vertex(v) for v in VERTS
}


# ---------------------------------------------------------------------------
# Signed 6j data, memoized.  sign in {-1, 0, +1}; square as Fraction.
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def sixj_sign_square(labels: Tuple[int, int, int, int, int, int]):
    """(sign, {6j}^2) for Wigner {l0/2 l1/2 l2/2; l3/2 l4/2 l5/2}."""
    import sympy
    from sympy import Rational
    from sympy.physics.wigner import wigner_6j

    try:
        w = wigner_6j(*[Rational(n, 2) for n in labels])
    except ValueError:
        return 0, Fraction(0)
    if w == 0:
        return 0, Fraction(0)
    sq = sympy.nsimplify(w * w, rational=True)
    sign = 1 if w > 0 else -1
    return sign, Fraction(int(sq.p), int(sq.q))


def vertex_labels(v, spins: Sequence[int]) -> Tuple[int, ...]:
    f = VERTEX_FACES[v]
    return tuple(spins[f[pl]] for pl in _PLANES)


def amplitude(spins: Sequence[int]) -> Fraction:
    """Exact dual amplitude via the vertex product formula.

    Returns the exact rational Z.  Raises ValueError if the product of
    squares is not a perfect square of a rational (cannot happen for a
    closed complex; kept as a tripwire).
    """
    sign = 1
    sq = Fraction(1)
    for v in VERTS:
        s, q = sixj_sign_square(vertex_labels(v, spins))
        if s == 0:
            return Fraction(0)
        sign *= s
        sq *= q
    rn = math.isqrt(sq.numerator)
    rd = math.isqrt(sq.denominator)
    if rn * rn != sq.numerator or rd * rd != sq.denominator:
        raise ValueError(f"non-square product {sq}; formula misapplied")
    return Fraction(sign) * Fraction(rn, rd)


# ---------------------------------------------------------------------------
# Sweeps over kernel-generated assignments.
# ---------------------------------------------------------------------------


def surface_masks() -> List[int]:
    return surfaces(kernel_basis(_CX, _FACES))


def combo_spins(masks: Sequence[int]) -> List[int]:
    spins = [0] * NF
    for m in masks:
        for i in range(NF):
            spins[i] += (m >> i) & 1
    return spins


def sweep_combinations(k: int, progress_every: int = 50_000):
    """Evaluate all C(128, k) k-fold surface sums (spins <= k).

    Returns (n_eval, n_nonzero, negatives, min_positive).
    """
    surf = surface_masks()
    n_eval = n_nonzero = 0
    negatives = []
    min_pos: Optional[Fraction] = None
    for combo in itertools.combinations(surf, k):
        z = amplitude(combo_spins(combo))
        n_eval += 1
        if z:
            n_nonzero += 1
            if z < 0:
                negatives.append((combo, z))
            elif min_pos is None or z < min_pos:
                min_pos = z
        if progress_every and n_eval % progress_every == 0:
            print(
                f"    ...{n_eval} evaluated, {n_nonzero} nonzero, "
                f"{len(negatives)} negative",
                flush=True,
            )
    return n_eval, n_nonzero, negatives, min_pos


ORBIT_109_VALUE = Fraction(1, 6**16)


def main() -> None:
    surf = surface_masks()
    # headline: the closed 109th orbit
    a, b = surf[59], surf[93]
    z = amplitude(combo_spins([a, b]))
    print(f"orbit 109 (double-torus collision): Z = {z} "
          f"({'positive' if z > 0 else 'NEGATIVE'})")
    assert z == ORBIT_109_VALUE
    print("triples sweep (all C(128,3) = 341376, spins <= 3):")
    n, nz, neg, mp = sweep_combinations(3)
    print(f"  evaluated {n}; nonzero {nz}; negatives {len(neg)}; "
          f"min positive {mp}")
    for c, v in neg[:10]:
        print(f"    NEGATIVE {v} at masks {c}")


if __name__ == "__main__":
    main()
