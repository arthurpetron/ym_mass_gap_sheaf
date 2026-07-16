#!/usr/bin/env python3
"""Generate exact data for the high-branch lower-six Base certificate.

The authoritative polynomial and chart transform are imported from
``lower_six_tail_second_flux_certificate.py``.  All operations use SymPy
rationals, Python integers, and ``Fraction``.  The emitted table is scaled by
the least common denominator of its native tensor-Bernstein coefficients.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import comb, lcm
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lower_six_tail_second_flux_certificate as source  # noqa: E402


CLEAR_SCALE = 178605
ROW_SHARD_SIZE = 7
TERM_SHARD_SIZE = 100
BLOCK_ROW_SIZE = 7
BLOCK_TERM_SHARD_SIZE = 80


def exact_data(verify_reconstruction: bool):
    power, homogeneous_degree = source.high_base_power_coefficients(
        source.BASE_FULL_NUM
    )
    degree_x = max(i for i, _ in power)
    degree_y = max(j for _, j in power)
    assert (homogeneous_degree, degree_x, degree_y) == (50, 41, 22)
    bernstein = source.bernstein_coefficients(power, degree_x, degree_y)
    table_scale = lcm(*(value.denominator for value in bernstein.values()))
    assert table_scale % CLEAR_SCALE == 0
    chart_quotient = table_scale // CLEAR_SCALE

    rows: list[list[int]] = []
    for i in range(degree_x + 1):
        row: list[int] = []
        for j in range(degree_y + 1):
            scaled = bernstein[i, j] * table_scale
            assert scaled.denominator == 1
            assert scaled.numerator >= 0
            row.append(scaled.numerator)
        rows.append(row)

    cleared = source.sp.Poly(
        source.sp.expand(CLEAR_SCALE * source.BASE_FULL_NUM.as_expr()),
        source.D,
        source.n,
    )
    terms: list[tuple[int, int, int]] = []
    for (degree_d, degree_n), coefficient in cleared.terms():
        value = source.exact_fraction(coefficient)
        assert value.denominator == 1
        terms.append((degree_d, degree_n, value.numerator))

    if verify_reconstruction:
        # Exact table reconstruction at the power-coefficient level.  This is
        # the defining Bernstein transform inverted by polynomial expansion.
        x, z = source.sp.symbols("x z")
        reconstructed = source.sp.Poly(
            source.sp.expand(
                sum(
                    Fraction(rows[i][j], table_scale)
                    * source.comb(degree_x, i)
                    * x**i
                    * (1 - x) ** (degree_x - i)
                    * source.comb(degree_y, j)
                    * z**j
                    * (1 - z) ** (degree_y - j)
                    for i in range(degree_x + 1)
                    for j in range(degree_y + 1)
                )
            ),
            x,
            z,
        )
        expected = source.sp.Poly(
            source.sp.expand(
                sum(value * x**i * z**j
                    for (i, j), value in power.items())
            ),
            x,
            z,
        )
        assert reconstructed == expected

        aggregate: dict[tuple[int, int], int] = {}
        for block in range((len(rows) + BLOCK_ROW_SIZE - 1) // BLOCK_ROW_SIZE):
            for degree_d, degree_n, coefficient in block_physical_terms(
                rows, block
            ):
                key = (degree_d, degree_n)
                aggregate[key] = aggregate.get(key, 0) + coefficient
        aggregate = {
            key: coefficient
            for key, coefficient in aggregate.items()
            if coefficient
        }
        expected_physical = {
            (degree_d + 13, degree_n): coefficient * chart_quotient
            for degree_d, degree_n, coefficient in terms
        }
        assert aggregate == expected_physical
        separable_rows(table_scale, rows)

    return table_scale, chart_quotient, rows, terms


def block_physical_terms(
    rows: list[list[int]], block: int
) -> list[tuple[int, int, int]]:
    """Expand one consecutive Bernstein row block after chart substitution.

    The four homogeneous coordinates are exactly
    ``8191, D - 8191, n - D, 2*D - n``.  Expansion is performed directly
    with integer binomial identities; no floating-point arithmetic enters.
    """
    degree_x = len(rows) - 1
    degree_y = len(rows[0]) - 1
    start = block * BLOCK_ROW_SIZE
    stop = min(start + BLOCK_ROW_SIZE, len(rows))
    assert start < stop
    power: dict[tuple[int, int], int] = {}
    for i in range(start, stop):
        x1_degree = degree_x - i
        for j, coefficient in enumerate(rows[i]):
            y1_degree = degree_y - j
            prefactor = coefficient * comb(degree_x, i) * comb(degree_y, j)
            prefactor *= 8191**i
            for d_from_x1 in range(x1_degree + 1):
                x_value = (
                    prefactor
                    * comb(x1_degree, d_from_x1)
                    * (-8191) ** (x1_degree - d_from_x1)
                )
                for n_from_y0 in range(j + 1):
                    y0_value = (
                        comb(j, n_from_y0) * (-1) ** (j - n_from_y0)
                    )
                    for n_from_y1 in range(y1_degree + 1):
                        y1_value = (
                            comb(y1_degree, n_from_y1)
                            * (-1) ** n_from_y1
                            * 2 ** (y1_degree - n_from_y1)
                        )
                        degree_d = (
                            d_from_x1
                            + (j - n_from_y0)
                            + (y1_degree - n_from_y1)
                        )
                        degree_n = n_from_y0 + n_from_y1
                        key = (degree_d, degree_n)
                        power[key] = power.get(key, 0) + (
                            x_value * y0_value * y1_value
                        )
    return [
        (degree_d, degree_n, coefficient)
        for (degree_d, degree_n), coefficient in sorted(
            power.items(), reverse=True
        )
        if coefficient
    ]


def separable_rows(
    table_scale: int, bernstein_rows: list[list[int]]
) -> tuple[list[list[int]], list[list[int]]]:
    """Return scaled power rows and their x-Pascal pass."""
    power, _ = source.high_base_power_coefficients(source.BASE_FULL_NUM)
    degree_x = len(bernstein_rows) - 1
    degree_y = len(bernstein_rows[0]) - 1
    scaled_power = [[0 for _ in range(degree_y + 1)]
                    for _ in range(degree_x + 1)]
    for (degree_x_power, degree_y_power), coefficient in power.items():
        scaled = coefficient * table_scale
        assert scaled.denominator == 1
        scaled_power[degree_x_power][degree_y_power] = scaled.numerator

    x_pascal = [[0 for _ in range(degree_y + 1)]
                for _ in range(degree_x + 1)]
    for i in range(degree_x + 1):
        for b in range(degree_y + 1):
            x_pascal[i][b] = sum(
                scaled_power[a][b] * comb(degree_x - a, i - a)
                for a in range(i + 1)
            )

    for i in range(degree_x + 1):
        for j in range(degree_y + 1):
            transformed = sum(
                x_pascal[i][b] * comb(degree_y - b, j - b)
                for b in range(j + 1)
            )
            weighted = (
                bernstein_rows[i][j]
                * comb(degree_x, i)
                * comb(degree_y, j)
            )
            assert transformed == weighted

    cleared_rows = cleared_coefficient_rows()
    chart_quotient = table_scale // CLEAR_SCALE
    for a in range(degree_x + 1):
        for b in range(degree_y + 1):
            raw_shift = 0
            for j in range(b, degree_y + 1):
                degree_d = 50 - a - j
                if degree_d < 0 or degree_d >= len(cleared_rows):
                    continue
                raw_shift += (
                    chart_quotient
                    * cleared_rows[degree_d][j]
                    * comb(j, b)
                )
            assert scaled_power[a][b] * 8191**a == raw_shift

    return scaled_power, x_pascal


def cleared_coefficient_rows() -> list[list[int]]:
    cleared_poly = source.sp.Poly(
        source.sp.expand(CLEAR_SCALE * source.BASE_FULL_NUM.as_expr()),
        source.D,
        source.n,
    )
    degree_d = cleared_poly.degree(source.D)
    degree_n = cleared_poly.degree(source.n)
    rows = [[0 for _ in range(degree_n + 1)]
            for _ in range(degree_d + 1)]
    for (power_d, power_n), coefficient in cleared_poly.terms():
        value = source.exact_fraction(coefficient)
        assert value.denominator == 1
        rows[power_d][power_n] = value.numerator
    return rows


def print_rows(rows: list[list[int]], shard: int) -> None:
    start = shard * ROW_SHARD_SIZE
    selected = rows[start : start + ROW_SHARD_SIZE]
    assert selected
    print(f"def tailBaseBernsteinRows{shard} : List (List Int) := [")
    for row in selected:
        print("  [" + ", ".join(str(value) for value in row) + "],")
    print("]")


def print_terms(terms: list[tuple[int, int, int]], shard: int) -> None:
    start = shard * TERM_SHARD_SIZE
    selected = terms[start : start + TERM_SHARD_SIZE]
    assert selected
    print(f"def tailBaseClearedTerms{shard} : List (Nat × Nat × Int) := [")
    for degree_d, degree_n, coefficient in selected:
        print(f"  ({degree_d}, {degree_n}, {coefficient}),")
    print("]")


def balanced_sum(expressions: list[str], indent: str = "  ") -> str:
    assert expressions
    if len(expressions) == 1:
        return expressions[0]
    midpoint = len(expressions) // 2
    left = balanced_sum(expressions[:midpoint], indent + "  ")
    right = balanced_sum(expressions[midpoint:], indent + "  ")
    return f".add\n{indent}({left})\n{indent}({right})"


def print_block_file(rows: list[list[int]], block: int) -> None:
    terms = block_physical_terms(rows, block)
    pieces = [
        terms[start : start + BLOCK_TERM_SHARD_SIZE]
        for start in range(0, len(terms), BLOCK_TERM_SHARD_SIZE)
    ]
    print("/-")
    print(f"# Exact sparse physical contribution for Base Bernstein block {block}")
    print("")
    print("Generated by `computations/HarmonicLowerSixTailBaseCertificate_generate.py`.")
    print("-/")
    print("")
    print("import YMGap.Continuum.TensorBernsteinHomogeneousCertificate")
    print("")
    print("namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificateBlockTerms")
    print("")
    print("open YMGap.Continuum.TensorBernsteinHomogeneousCertificate")
    print("")
    for part, selected in enumerate(pieces):
        name = f"tailBaseBlockPhysicalTerms{block}_{part}"
        print(f"def {name} : List (Nat × Nat × Int) := [")
        for degree_d, degree_n, coefficient in selected:
            print(f"  ({degree_d}, {degree_n}, {coefficient}),")
        print("]")
        print("")
    expressions = [
        f"bivariatePowerExpr tailBaseBlockPhysicalTerms{block}_{part}"
        for part in range(len(pieces))
    ]
    print(f"def tailBaseBlockPhysicalExpr{block} : RingNormaliser.PolyExpr :=")
    print("  " + balanced_sum(expressions).replace("\n", "\n  "))
    print("")
    print("end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateBlockTerms")


def print_separable_rows_file(
    table_scale: int, rows: list[list[int]], shard: int
) -> None:
    scaled_power, x_pascal = separable_rows(table_scale, rows)
    start = shard * ROW_SHARD_SIZE
    stop = start + ROW_SHARD_SIZE
    assert scaled_power[start:stop]
    print("/-")
    print(f"# Exact separable Base coefficient rows {shard}")
    print("")
    print("Generated by `computations/HarmonicLowerSixTailBaseCertificate_generate.py`.")
    print("-/")
    print("")
    print("import YMGap.Continuum.TensorBernsteinSeparableReconstruction")
    print("")
    print("namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows")
    print("")
    for label, matrix in [
        ("ScaledPower", scaled_power),
        ("XPascal", x_pascal),
    ]:
        print(f"def tailBase{label}Rows{shard} : List (List Int) := [")
        for row in matrix[start:stop]:
            print("  [" + ", ".join(str(value) for value in row) + "],")
        print("]")
        print("")
    print("end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows")


def print_cleared_rows_file(shard: int) -> None:
    rows = cleared_coefficient_rows()
    start = shard * ROW_SHARD_SIZE
    selected = rows[start : start + ROW_SHARD_SIZE]
    assert selected
    print("/-")
    print(f"# Exact cleared Base power rows {shard}")
    print("")
    print("Generated by `computations/HarmonicLowerSixTailBaseCertificate_generate.py`.")
    print("-/")
    print("")
    print("import YMGap.Continuum.TensorBernsteinSeparableReconstruction")
    print("")
    print("namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificateClearedRows")
    print("")
    print(f"def tailBaseClearedRows{shard} : List (List Int) := [")
    for row in selected:
        print("  [" + ", ".join(str(value) for value in row) + "],")
    print("]")
    print("")
    print("end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateClearedRows")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rows", type=int)
    parser.add_argument("--terms", type=int)
    parser.add_argument("--block-summary", action="store_true")
    parser.add_argument("--block-file", type=int)
    parser.add_argument("--separable-rows-file", type=int)
    parser.add_argument("--cleared-rows-file", type=int)
    args = parser.parse_args()
    table_scale, chart_quotient, rows, terms = exact_data(
        args.rows is None and args.terms is None and args.block_file is None
        and args.separable_rows_file is None
        and args.cleared_rows_file is None
    )
    if args.block_file is not None:
        print_block_file(rows, args.block_file)
    elif args.separable_rows_file is not None:
        print_separable_rows_file(table_scale, rows, args.separable_rows_file)
    elif args.cleared_rows_file is not None:
        print_cleared_rows_file(args.cleared_rows_file)
    elif args.block_summary:
        for block in range((len(rows) + BLOCK_ROW_SIZE - 1) // BLOCK_ROW_SIZE):
            print(f"block={block} terms={len(block_physical_terms(rows, block))}")
    elif args.rows is not None:
        print_rows(rows, args.rows)
    elif args.terms is not None:
        print_terms(terms, args.terms)
    else:
        print(f"table_scale={table_scale}")
        print(f"chart_quotient={chart_quotient}")
        print(f"rows={len(rows)} row_width={len(rows[0])}")
        print(f"terms={len(terms)}")


if __name__ == "__main__":
    main()
