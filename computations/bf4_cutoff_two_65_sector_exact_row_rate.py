"""Exact diagnostic for the cutoff-two mass-normalized row rate.

The script reads the already Lean-checked 65 by 65 raw kernel table and its
row sums, then evaluates the scale-invariant conditional row distance

    h(row) = sum_column |K(row,column) - d(row)d(column)/M| / d(row),

where ``d`` is the raw row sum and ``M = sum d`` is the canonical component
mass in the same raw normalization.  Its maximum is the table presentation of
the sharp finite scalar ``h_2``.  This Python computation is an untrusted
diagnostic; any claimed theorem still requires a Lean-checked certificate.
"""

from __future__ import annotations

import json
import re
from fractions import Fraction
from pathlib import Path


SIZE = 65
ROOT = Path(__file__).resolve().parents[1]
RAW_DATA = (
    ROOT
    / "lean"
    / "YMGap"
    / "Continuum"
    / "BF4PhysicalBoundaryCutoffTwoSectorRawKernelData.lean"
)

_Q_LITERAL = re.compile(
    r"\((?:0|1)\s*:\s*Q'\)|\(\u27e8(-?\d+),\s*(\d+)\u27e9\s*:\s*Q'\)"
)


def _fraction(literal: re.Match[str]) -> Fraction:
    text = literal.group(0)
    if text.startswith("(0"):
        return Fraction(0)
    if text.startswith("(1"):
        return Fraction(1)
    # Direct Q' structure literals store the predecessor of the denominator.
    return Fraction(int(literal.group(1)), int(literal.group(2)) + 1)


def _array(source: str, start: str, end: str) -> tuple[Fraction, ...]:
    body = source.split(start, 1)[1].split(end, 1)[0]
    return tuple(_fraction(match) for match in _Q_LITERAL.finditer(body))


def main() -> None:
    source = RAW_DATA.read_text(encoding="utf-8")
    kernel_values = _array(
        source,
        "def cutoffTwoSectorRawKernelData : Array Q' := #[",
        "def cutoffTwoSectorRawRowSumData : Array Q' := #[",
    )
    row_sums = _array(
        source,
        "def cutoffTwoSectorRawRowSumData : Array Q' := #[",
        "def cutoffTwoSectorRawKernel (row column : Nat)",
    )
    if len(kernel_values) != SIZE * SIZE:
        raise AssertionError(
            f"expected {SIZE * SIZE} kernel entries, found {len(kernel_values)}"
        )
    if len(row_sums) != SIZE:
        raise AssertionError(f"expected {SIZE} row sums, found {len(row_sums)}")

    kernel = tuple(
        kernel_values[row * SIZE : (row + 1) * SIZE]
        for row in range(SIZE)
    )
    if any(kernel[row][column] != kernel[column][row]
           for row in range(SIZE) for column in range(SIZE)):
        raise AssertionError("raw table is not symmetric")
    recomputed = tuple(sum(row, Fraction(0)) for row in kernel)
    if recomputed != row_sums:
        mismatch = next(
            row for row in range(SIZE) if recomputed[row] != row_sums[row]
        )
        raise AssertionError(
            "stored row sums do not match the raw table at row "
            f"{mismatch}: recomputed={recomputed[mismatch]}, "
            f"stored={row_sums[mismatch]}"
        )
    if any(weight <= 0 for weight in row_sums):
        raise AssertionError("canonical component has a nonpositive row mass")

    mass = sum(row_sums, Fraction(0))
    rates = tuple(
        sum(
            (
                abs(kernel[row][column]
                    - row_sums[row] * row_sums[column] / mass)
                for column in range(SIZE)
            ),
            Fraction(0),
        )
        / row_sums[row]
        for row in range(SIZE)
    )
    maximum = max(rates)
    maximizing_rows = tuple(
        row for row, rate in enumerate(rates) if rate == maximum
    )
    witness_row = maximizing_rows[0]
    cleared_distance = sum(
        (
            abs(mass * kernel[witness_row][column]
                - row_sums[witness_row] * row_sums[column])
            for column in range(SIZE)
        ),
        Fraction(0),
    )
    print(json.dumps({
        "component_mass": str(mass),
        "cleared_distance_at_witness": str(cleared_distance),
        "exact_rate": str(maximum),
        "exact_rate_decimal": float(maximum),
        "maximizing_rows": maximizing_rows,
        "raw_row_sum_at_witness": str(row_sums[witness_row]),
        "rate_lt_one": maximum < 1,
        "rate_le_49_over_50": maximum <= Fraction(49, 50),
        "minimum_row_rate_decimal": float(min(rates)),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
