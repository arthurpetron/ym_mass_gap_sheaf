"""SU(2) recoupling data extracted from the certified moment engine.

Milestone DP.1, data layer (work_plan.md §15).  The TL-channel
contraction engine needs exact 6j/θ data.  Rather than importing
formulas, we *derive* the squared data from the already-certified
quaternion moment integrator, so the channel engine's arithmetic has
the same provenance as everything else in this program:

    K4(A,B,C,D,E,F)
      := ∫ Π_v dg_v  χ_A(g1 g2⁻¹) χ_B(g1 g3⁻¹) χ_C(g1 g4⁻¹)
                     χ_D(g2 g3⁻¹) χ_E(g2 g4⁻¹) χ_F(g3 g4⁻¹)

is the complete-graph spin model on K4.  Integrating each vertex
inserts the projector onto invariants of its three incident spins
(rank ≤ 1 for SU(2)); the closed contraction pairs the four
orthonormal trivalent intertwiners into a tetrahedral network and its
mirror, giving *exactly* the squared Wigner 6j symbol:

    K4(A,B,C,D,E,F) = {A/2 B/2 C/2; F/2 E/2 D/2}²

(slot matching: vertex triads (A,B,C), (A,D,E), (B,D,F), (C,E,F) map
to the Wigner triads (j1,j2,j3), (j1,j5,j6), (j4,j2,j6), (j4,j5,j3)
with j1..j6 = A,B,C,F,E,D).  Labels are integers n = 2j throughout.

This module computes K4 exactly from moments and cross-pins it against
``sympy.physics.wigner.wigner_6j``.  Signs — pure convention/gauge at a
single tetrahedron, physical only in closed chains — are the next
layer (Biedenharn–Elliott + orthogonality propagation); see the DP.1
milestone.

Run:  python -m computations.su2_recoupling_data
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, Optional, Tuple

from computations.exact_haar_network import (
    P_ONE,
    chi,
    contract,
    q_conj,
    q_link,
    q_mul,
    scalar,
)

# K4 edge order: (12), (13), (14), (23), (24), (34)
K4_EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def k4_value(spins: Tuple[int, int, int, int, int, int]) -> Fraction:
    """Exact K4 spin-model value from quaternion moments.

    Gauge freedom: g4 may be frozen to the identity (right-invariance
    of Haar), which the integrator exploits implicitly by simply not
    integrating a fourth link; we keep all four for transparency —
    the cost is negligible at these sizes.
    """
    g = [q_link(i) for i in range(4)]
    factors = []
    for n, (u, v) in zip(spins, K4_EDGES):
        if n > 0:
            factors.append(chi(n, q_mul(g[u], q_conj(g[v]))))
    if not factors:
        factors = [dict(P_ONE)]
    val = scalar(contract(factors, [0, 1, 2, 3]))
    if not val:
        return Fraction(0)
    assert set(val) == {0}
    return val[0]


def wigner_6j_squared(spins: Tuple[int, int, int, int, int, int]):
    """Reference {6j}² from sympy, in the K4 slot convention.

    K4(A,B,C,D,E,F) should equal {A/2 B/2 C/2; F/2 E/2 D/2}².
    Returns an exact sympy Rational.
    """
    import sympy
    from sympy import Rational
    from sympy.physics.wigner import wigner_6j

    A, B, C, D, E, F = spins
    try:
        w = wigner_6j(
            Rational(A, 2), Rational(B, 2), Rational(C, 2),
            Rational(F, 2), Rational(E, 2), Rational(D, 2),
        )
    except ValueError:
        # sympy raises on violated triangle conditions; the amplitude
        # is then exactly zero.
        return sympy.Integer(0)
    return sympy.nsimplify(w**2, rational=False).expand()


def triads_ok(spins: Tuple[int, int, int, int, int, int]) -> bool:
    A, B, C, D, E, F = spins
    for x, y, z in ((A, B, C), (A, D, E), (B, D, F), (C, E, F)):
        if (x + y + z) % 2 == 1:
            return False
        if x > y + z or y > x + z or z > x + y:
            return False
    return True


def sixj_squared_table(nmax: int) -> Dict[Tuple[int, ...], Fraction]:
    """Exact table of squared 6j data (K4 values) for labels <= nmax."""
    out: Dict[Tuple[int, ...], Fraction] = {}
    for spins in itertools.product(range(nmax + 1), repeat=6):
        if not triads_ok(spins):
            continue
        v = k4_value(spins)
        if v:
            out[spins] = v
    return out


def main() -> None:
    import sympy

    print("K4 = {6j}^2 cross-certification, labels <= 3")
    n_checked = n_nonzero = 0
    mismatches = []
    for spins in itertools.product(range(4), repeat=6):
        if not triads_ok(spins):
            continue
        k4 = k4_value(spins)
        ref = wigner_6j_squared(spins)
        n_checked += 1
        if k4:
            n_nonzero += 1
        lhs = sympy.Rational(k4.numerator, k4.denominator)
        if sympy.simplify(lhs - ref) != 0:
            mismatches.append((spins, k4, ref))
    print(f"  admissible assignments checked: {n_checked}; nonzero: {n_nonzero}")
    print(f"  mismatches vs sympy wigner_6j^2: {len(mismatches)}")
    for m in mismatches[:5]:
        print("   MISMATCH", m)
    ex = (2, 2, 2, 2, 2, 2)
    print(f"  example: K4{ex} = {k4_value(ex)}   ({{1 1 1; 1 1 1}}^2 = 1/36)")


if __name__ == "__main__":
    main()
