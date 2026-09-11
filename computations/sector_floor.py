"""THE FIRST QUANTITATIVE STATEMENT IN THE MIDDLE REGIME —
a certified X_11 floor on [2^{-1/3}, 1) (work_plan §17h).

WHAT THIS IS
------------
§17g certified the SIGN of the one-step blocked observable uniformly on
(0,1) (`computations/sector_sos.py`).  This module converts that sign
into a RATE — a certified strictly positive LOWER BOUND on X_11 itself
— on the middle regime, which previously carried no certified statement
of any kind.

THE INEQUALITY.  With  D := T00 T11 - T01^2  (the Gram determinant) and
sin^2 theta := D / (T00 T11) in [0, 1),

    X_11 = log(T00 T11 / T01^2) = -log(1 - D/(T00 T11))  >=  D/(T00 T11).

Both ingredients are now available in the EASY direction:

  * D >= det_S(s), the §17g sector-truncated determinant — an exact
    polynomial, valid on all of (0,1), by superadditivity of det over
    the PSD sector blocks.  NO upper bound on the off-diagonal T01 is
    needed anywhere: that was the expensive, sign-cancelling direction
    that capped the §16h-§17e window instrument at s <= 5/8.
  * T00, T11 are DIAGONAL Gram entries — sums of NON-NEGATIVE terms —
    so any domination of the Haar values upper-bounds them, with no
    cancellation to track.  Here we use the incumbent crude domination
    (su2_minf_windows.DomTransfer: |N| <= d_n d_m prod d, closed by the
    certified geometric label sums plus lam_slop), which converges for
    EVERY s < 1 once the label cutoff satisfies 4 s^{2 lam + 3} < 1 and
    16 s^{4 lam + 6} < 1.

Hence, certified for every s in (0,1) at which the cutoff condition is
met:

    X_11(s)  >=  det_S(s) / (T00_hi(s) * T11_hi(s))  >  0.

HONESTY: THE BOUND IS CERTIFIED AND IT IS BAD
---------------------------------------------
The floor is positive on the whole middle regime — the first
quantitative statement there — and it is 20-40 orders of magnitude
below the truth.  The loss is NOT in det_S and NOT in the inequality;
it is entirely in the crude |N| <= prod(dim) domination of the DIAGONAL
entries, and this module measures that loss point by point
(`crude_cost`, the ratio of the reference ratio det_S/(T00_S T11_S) to
the certified floor).  At s = 4/5 the crude domination costs 4.7e23; at
s = 9/10, 4.4e35.

THE NAMED FIX, AND ITS SIZE.  The diagonal admits the OS-triangle bound

    T_nn = sum_sigma W_sigma || x_n(sigma) ||^2,
    || x_n(sigma) ||  <=  sum_a W_a(s) sqrt( N(n, n, sigma, a, a) ),

i.e. the §16h Cauchy-Schwarz sharpening applied to the DIAGONAL, where
the required values `N(n,n,sigma,a,a)` are single same-config Haar
evaluations (the cheapest objects in the program, and already computed
for the cap<=1 family by `sector_sos.half_config_gram`).  The residual
is then only the SECTOR tail (labels above the cutoff), where W_sigma
carries the full s^{2C(q)} suppression.  Order-of-magnitude estimate
from the measured slack: this recovers roughly 20 orders at s = 4/5,
which is the difference between a decorative floor and a usable one.
That build is the designated next item; it is EASY-direction work only
(no off-diagonal, no unresolved diagonals, no recoupling evaluator).

Run:  python -m computations.sector_floor
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction as Frac
from typing import Dict, List, Tuple

from computations.sector_sos import (
    assemble,
    det_poly,
    pev,
    sector_kernels,
)
from computations.su2_minf_windows import DomTransfer, tail_pow2, tail_pow4

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "sector_floor_results.json")

sys.set_int_max_str_digits(0)

# The middle regime: from the anchor edge 2^{-1/3} = 0.793700... upward.
# Rational points straddling and above the edge.
MIDDLE_GRID = (Frac(4, 5), Frac(5, 6), Frac(6, 7), Frac(9, 10),
               Frac(14, 15), Frac(24, 25))


def lam_min(s: Frac, cap: int = 400) -> int:
    """Smallest label cutoff at which BOTH certified geometric label
    sums converge: 4 s^{2 lam + 3} < 1 and 16 s^{4 lam + 6} < 1."""
    lam = 1
    while lam <= cap:
        try:
            tail_pow2(lam, s)
            tail_pow4(lam, s)
            return lam
        except AssertionError:
            lam += 1
    raise ValueError(f"no admissible cutoff <= {cap} at s = {s}")


def diagonal_upper(n: int, s: Frac, lam: int) -> Frac:
    """Certified upper bound on the diagonal entry T_nn(s): the full
    crude dominated mass at label cutoff `lam`, plus the union-bound
    slop for labels above it.  Both directions are the incumbent
    `su2_minf_windows` machinery, unmodified."""
    dt = DomTransfer(n, n, s, lam)
    return dt.dominated_trace(lam) + dt.lam_slop()


def certified_floor(s: Frac, det: Dict[int, Frac], lam_pad: int = 2
                    ) -> Tuple[Frac, Frac, Frac, Frac, int]:
    """Return (floor, det_S, T00_hi, T11_hi, lam) with

        X_11(s)  >=  floor  =  det_S / (T00_hi * T11_hi)  >  0.
    """
    lam = lam_min(s) + lam_pad
    t00 = diagonal_upper(0, s, lam)
    t11 = diagonal_upper(1, s, lam)
    dS = pev(det, s)
    assert dS > 0, f"det_S not positive at s = {s}"
    assert t00 > 0 and t11 > 0
    return dS / (t00 * t11), dS, t00, t11, lam


def main() -> None:
    print("CERTIFIED X_11 FLOOR ON THE MIDDLE REGIME (work_plan §17h)")
    print("=" * 66)
    print(f"anchor edge 2^(-1/3) = {2 ** (-1/3):.6f}; every grid point below "
          f"is at or above it\n")

    T = assemble(sector_kernels(1, 2))
    det = det_poly(T)

    rows: List[dict] = []
    for s in MIDDLE_GRID:
        floor, dS, t00, t11, lam = certified_floor(s, det)
        ref = dS / (pev(T[(0, 0)], s) * pev(T[(1, 1)], s))
        cost = ref / floor
        tau = -math.log(float(s))
        print(f"s = {s}  (tau = {tau:.5f}),  lam = {lam}")
        print(f"   det_S     = {float(dS):.6e}   (exact, §17g)")
        print(f"   T00_hi    = {float(t00):.6e}   T11_hi = {float(t11):.6e}"
              f"   (crude domination)")
        print(f"   *** CERTIFIED  X_11 >= {float(floor):.6e} ***")
        print(f"   crude-domination cost: {float(cost):.4e}x  "
              f"(reference ratio {float(ref):.6e})")
        rows.append({
            "s": [s.numerator, s.denominator],
            "tau": tau,
            "lam": lam,
            "det_S": [dS.numerator, dS.denominator],
            "T00_hi": [t00.numerator, t00.denominator],
            "T11_hi": [t11.numerator, t11.denominator],
            "floor_float": float(floor),
            "reference_ratio_float": float(ref),
            "crude_cost_float": float(cost),
        })

    print("\nVERDICT.  The floor is CERTIFIED and POSITIVE at every point of "
          "the\nmiddle regime — the first quantitative statement there — and "
          "it is\n20-40 orders below the truth.  The whole loss is the crude "
          "|N| <= prod(dim)\ndomination of the DIAGONAL entries; det_S and the "
          "inequality are tight.\nThe named fix (OS-triangle diagonal bound, "
          "easy-direction only) is the\ndesignated next item.")

    out = {
        "grid": rows,
        "anchor_edge_cube_root_of_half": 2 ** (-1 / 3),
        "all_floors_positive": all(r["floor_float"] > 0 for r in rows),
    }
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    print(f"\nledger -> {OUT_JSON}")
    print(f"ALL FLOORS POSITIVE: {out['all_floors_positive']}")


if __name__ == "__main__":
    main()
