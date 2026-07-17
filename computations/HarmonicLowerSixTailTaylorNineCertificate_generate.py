#!/usr/bin/env python3
"""Generate the exact integer T9 tensor-Bernstein table used by Lean.

This script imports the authoritative symbolic definition from
``lower_six_tail_second_flux_certificate.py`` and performs only exact integer
and ``Fraction`` arithmetic.  It verifies both the tensor-Bernstein
reconstruction and the homogeneous physical chart identity before printing
the dense Lean rows.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lower_six_tail_second_flux_certificate as source  # noqa: E402


CHART_BASE = source.DENOMINATOR_CHART_BASE
FACTORIAL_NINE = factorial(9)
CHART_QUOTIENT = 1470 * CHART_BASE**8
TABLE_SCALE = FACTORIAL_NINE * CHART_QUOTIENT


def main() -> None:
    power, homogeneous_degree = source.low_step_power_coefficients(
        source.sp.Poly(source.L9NUM, source.D, source.n)
    )
    degree_x = max(i for i, _ in power)
    degree_y = max(j for _, j in power)
    assert (homogeneous_degree, degree_x, degree_y) == (9, 8, 9)

    bernstein = source.bernstein_coefficients(power, degree_x, degree_y)
    rows: list[list[int]] = []
    for i in range(degree_x + 1):
        row: list[int] = []
        for j in range(degree_y + 1):
            scaled = bernstein[i, j] * TABLE_SCALE
            assert scaled.denominator == 1
            assert scaled.numerator >= 0
            row.append(scaled.numerator)
        rows.append(row)

    x, z = source.sp.symbols("x z")
    reconstructed = source.sp.expand(
        sum(
            Fraction(rows[i][j], TABLE_SCALE)
            * comb(degree_x, i)
            * x**i
            * (1 - x) ** (degree_x - i)
            * comb(degree_y, j)
            * z**j
            * (1 - z) ** (degree_y - j)
            for i in range(degree_x + 1)
            for j in range(degree_y + 1)
        )
    )
    power_expr = source.sp.expand(
        sum(value * x**i * z**j for (i, j), value in power.items())
    )
    assert source.sp.expand(reconstructed - power_expr) == 0

    cleared = source.sp.expand(FACTORIAL_NINE * source.L9NUM)
    homogeneous = source.sp.expand(
        sum(
            rows[i][j]
            * comb(degree_x, i)
            * CHART_BASE**i
            * (source.D - CHART_BASE) ** (degree_x - i)
            * comb(degree_y, j)
            * source.n**j
            * (source.D - source.n) ** (degree_y - j)
            for i in range(degree_x + 1)
            for j in range(degree_y + 1)
        )
    )
    assert source.sp.expand(
        homogeneous - CHART_QUOTIENT * source.D**8 * cleared
    ) == 0

    body = ["def tailTaylor9BernsteinRows : List (List Int) := ["]
    for row in rows:
        body.append("  [" + ", ".join(str(value) for value in row) + "],")
    body.append("]")
    if "--write" not in sys.argv:
        print(f"-- table scale = {TABLE_SCALE}")
        print(f"-- chart quotient = {CHART_QUOTIENT}")
        print("\n".join(body))
        return
    output = (
        Path(__file__).resolve().parents[1]
        / "lean/YMGap/Continuum/HarmonicLowerSixTailTaylorNineCertificateRows.lean"
    )
    body_text = "\n".join(body)
    output.write_text(f'''/-
# Exact dense Bernstein rows for the lower-six T9 certificate

These 9 by 10 nonnegative integers are generated exactly by
`computations/HarmonicLowerSixTailTaylorNineCertificate_generate.py` from the
authoritative symbolic `L9NUM`.  The scale is

  `9! * 1470 * {CHART_BASE}^8`.

The binomial factors of the tensor Bernstein basis are supplied by
`homogeneousTensorExpr`, not duplicated in these entries.
-/

import YMGap.Continuum.TensorBernsteinHomogeneousCertificate

namespace YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificateRows

def tailTaylor9ChartBase : Nat :=
  {CHART_BASE}

def tailTaylor9TableScale : Int :=
  {TABLE_SCALE}

def tailTaylor9ChartQuotient : Int :=
  {CHART_QUOTIENT}

{body_text}

end YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificateRows
''')
    print(f"wrote {output}")


if __name__ == "__main__":
    main()
