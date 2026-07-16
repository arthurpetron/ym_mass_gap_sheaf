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


CHART_BASE = 8191
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

    print(f"-- table scale = {TABLE_SCALE}")
    print(f"-- chart quotient = {CHART_QUOTIENT}")
    print("def tailTaylor9BernsteinRows : List (List Int) := [")
    for row in rows:
        print("  [" + ", ".join(str(value) for value in row) + "],")
    print("]")


if __name__ == "__main__":
    main()
