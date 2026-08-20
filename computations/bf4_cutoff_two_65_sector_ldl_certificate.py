"""Generate the exact cutoff-two 65-sector mean-zero LDL Lean certificate.

The producer is intentionally untrusted.  It contracts the exact physical
factor graph, forms the 64-dimensional marginal-mean-zero restriction of
``(49/50) D - K``, computes an exact rational ``L D L^T`` factorization, and
emits literal data for Lean's generic certificate checker.
"""

from __future__ import annotations

import argparse
import multiprocessing
import os
import sys
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from math import lcm
from pathlib import Path

from computations.bf4_cutoff_two_65_sector_spectrum_scout import (
    _elimination_order,
    _entry_task,
    _mean_zero_restriction,
    sector_states,
)

sys.set_int_max_str_digits(0)


def _exact_kernel(coupling: Fraction, jobs: int) -> tuple[
    list[list[Fraction]], tuple[Fraction, ...]
]:
    states = sector_states()
    order, _width = _elimination_order(coupling)
    tasks = tuple(
        (str(coupling), left, right, order)
        for left in range(len(states))
        for right in range(left, len(states))
    )
    if jobs == 1:
        results = tuple(_entry_task(task) for task in tasks)
    else:
        context = multiprocessing.get_context("spawn")
        with ProcessPoolExecutor(max_workers=jobs, mp_context=context) as pool:
            results = tuple(pool.map(_entry_task, tasks, chunksize=1))
    kernel = [[Fraction(0) for _ in states] for _ in states]
    for _pid, left, right, value in results:
        kernel[left][right] = value
        kernel[right][left] = value
    row_sums = tuple(sum(row, Fraction(0)) for row in kernel)
    if any(row_sum <= 0 for row_sum in row_sums):
        raise AssertionError("nonpositive row sum")
    return kernel, row_sums


def _exact_ldl(
    matrix: list[list[Fraction]],
) -> tuple[list[list[Fraction]], tuple[Fraction, ...]]:
    size = len(matrix)
    lower = [[Fraction(0) for _ in range(size)] for _ in range(size)]
    diagonal: list[Fraction] = []
    for column in range(size):
        lower[column][column] = Fraction(1)
        pivot = matrix[column][column] - sum(
            (lower[column][k] * lower[column][k] * diagonal[k]
             for k in range(column)),
            Fraction(0),
        )
        if pivot <= 0:
            raise AssertionError(
                f"LDL pivot {column} is not strictly positive: {pivot}"
            )
        diagonal.append(pivot)
        for row in range(column + 1, size):
            residual = matrix[row][column] - sum(
                (lower[row][k] * lower[column][k] * diagonal[k]
                 for k in range(column)),
                Fraction(0),
            )
            lower[row][column] = residual / pivot
    for row in range(size):
        for column in range(size):
            reconstructed = sum(
                (lower[row][k] * diagonal[k] * lower[column][k]
                 for k in range(size)),
                Fraction(0),
            )
            if reconstructed != matrix[row][column]:
                raise AssertionError("exact LDL reconstruction failed")
    return lower, tuple(diagonal)


def _lean_q(value: Fraction) -> str:
    numerator = value.numerator
    denominator_pred = value.denominator - 1
    if denominator_pred == 0:
        return f"({numerator} : Q')"
    return f"(⟨{numerator}, {denominator_pred}⟩ : Q')"


def _array_definition(name: str, values: list[Fraction]) -> str:
    lines = [f"def {name} : Array Q' := #["]
    width = 3
    for start in range(0, len(values), width):
        chunk = ", ".join(_lean_q(value) for value in values[start:start + width])
        suffix = "," if start + width < len(values) else ""
        lines.append(f"  {chunk}{suffix}")
    lines.append("]")
    return "\n".join(lines)


def _nat_array_definition(name: str, values: list[int]) -> str:
    lines = [f"def {name} : Array Nat := #["]
    width = 3
    for start in range(0, len(values), width):
        chunk = ", ".join(str(value) for value in values[start:start + width])
        suffix = "," if start + width < len(values) else ""
        lines.append(f"  {chunk}{suffix}")
    lines.append("]")
    return "\n".join(lines)


def render_certificate_bundle(
    *, coupling: Fraction, jobs: int
) -> tuple[str, tuple[tuple[str, ...], ...], tuple[str, ...], str]:
    kernel, row_sums = _exact_kernel(coupling, jobs)
    matrix = _mean_zero_restriction(kernel, row_sums, Fraction(49, 50))
    lower, diagonal = _exact_ldl(matrix)
    size = len(matrix)
    matrix_values = [matrix[row][column]
                     for row in range(size) for column in range(size)]
    lower_values = [lower[row][column]
                    for row in range(size) for column in range(row + 1)]
    diagonal_values = list(diagonal)
    common_values = [
        lcm(
            (matrix[row][column].denominator
             if matrix[row][column].numerator != 0 else 1),
            *(diagonal[k].denominator
              * lower[row][k].denominator
              * lower[column][k].denominator
              for k in range(size)
              if diagonal[k].numerator
              * lower[row][k].numerator
              * lower[column][k].numerator != 0),
        )
        for row in range(size)
        for column in range(size)
    ]
    print(
        "common denominator bits: "
        f"min={min(value.bit_length() for value in common_values)} "
        f"max={max(value.bit_length() for value in common_values)}"
    )
    data_source = f'''/-
# Exact cutoff-two 65-sector mean-zero LDL data

Generated by `computations.bf4_cutoff_two_65_sector_ldl_certificate.py`.
The untrusted producer used exact rational arithmetic.  Separate row modules
recheck the entire 64 by 64 identity; the root certificate also rechecks all
64 strictly positive pivots.
-/

import YMGap.Continuum.FiniteRationalLDLCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

{_array_definition("cutoffTwoSectorMeanZeroMatrixData", matrix_values)}

{_array_definition("cutoffTwoSectorLowerTriangleData", lower_values)}

{_array_definition("cutoffTwoSectorDiagonalData", diagonal_values)}

{_nat_array_definition("cutoffTwoSectorCommonDenominatorData", common_values)}

def cutoffTwoSectorMeanZeroMatrix (row column : Nat) : Q' :=
  cutoffTwoSectorMeanZeroMatrixData.getD (row * {size} + column) 0

def cutoffTwoSectorLowerIndex (row column : Nat) : Nat :=
  row * (row + 1) / 2 + column

def cutoffTwoSectorLower (row column : Nat) : Q' :=
  if column ≤ row then
    cutoffTwoSectorLowerTriangleData.getD
      (cutoffTwoSectorLowerIndex row column) 0
  else 0

theorem cutoffTwoSectorLower_upper_zero
    (row column : Nat) (hupper : row < column) :
    cutoffTwoSectorLower row column = 0 := by
  unfold cutoffTwoSectorLower
  rw [if_neg (Nat.not_le_of_lt hupper)]

def cutoffTwoSectorDiagonal (index : Nat) : Q' :=
  cutoffTwoSectorDiagonalData.getD index 0

def cutoffTwoSectorCommonDenominator (row column : Nat) : Nat :=
  cutoffTwoSectorCommonDenominatorData.getD (row * {size} + column) 1

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate
'''

    chunk_size = 4
    chunk_columns = tuple(
        tuple(range(start, min(start + chunk_size, size)))
        for start in range(0, size, chunk_size)
    )
    chunk_sources = tuple(tuple(f'''/- Generated LDL row {row}, columns {columns[0]}..{columns[-1]}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteClearedRationalSumCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow{row:02d}Chunk{chunk:02d}_checked :
    [{", ".join(map(str, columns))}].all (fun column =>
      decide (ClearedSumValid
        (cutoffTwoSectorMeanZeroMatrix {row} column)
        (finiteLDLPrefixTerms cutoffTwoSectorLower
          cutoffTwoSectorDiagonal {row} column)
        (cutoffTwoSectorCommonDenominator {row} column))) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow{row:02d}Chunk{chunk:02d}_checked
''' for chunk, columns in enumerate(chunk_columns)) for row in range(size))

    row_sources_list: list[str] = []
    for row in range(size):
        chunk_imports = "\n".join(
            "import YMGap.Continuum."
            f"BF4PhysicalBoundaryCutoffTwoSectorLDLChunks."
            f"Row{row:02d}Chunk{chunk:02d}"
            for chunk in range(len(chunk_columns))
        )
        chunk_theorems = ",\n    ".join(
            f"cutoffTwoSectorLDLRow{row:02d}Chunk{chunk:02d}_checked"
            for chunk in range(len(chunk_columns))
        )
        decomposition = " ++ ".join(
            f"[{', '.join(map(str, columns))}]"
            for columns in chunk_columns
        )
        row_sources_list.append(f'''/- Generated exact LDL row {row}; composed from column chunks. -/
{chunk_imports}

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow{row:02d}_checked :
    finiteLDLClearedRowCheck {size}
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator {row} = true := by
  unfold finiteLDLClearedRowCheck
  rw [show List.range {size} = {decomposition} by decide]
  simp only [List.all_append,
    {chunk_theorems}]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow{row:02d}_checked
''')
    row_sources = tuple(row_sources_list)

    imports = "\n".join(
        "import YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row{row:02d}"
        for row in range(size)
    )
    row_theorems = ",\n    ".join(
        f"cutoffTwoSectorLDLRow{row:02d}_checked" for row in range(size)
    )
    indices = ", ".join(map(str, range(size)))
    root_source = f'''/-
# Exact cutoff-two 65-sector mean-zero LDL certificate

The 64 independently compiled row checks and the pivot-sign check compose the
exact rational `L D L^T` certificate.  External arithmetic proposes the
tables only; Lean's kernel validates every entry and sign.
-/

{imports}

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRows_checked :
    finiteLDLClearedRowsCheck {size}
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator = true := by
  unfold finiteLDLClearedRowsCheck
  rw [show List.range {size} = [{indices}] by decide]
  simp only [List.all_cons, List.all_nil,
    {row_theorems}]
  decide

theorem cutoffTwoSectorLDLDiagonal_checked :
    finiteLDLDiagonalCheck {size} cutoffTwoSectorDiagonal = true := by
  decide

theorem cutoffTwoSectorMeanZeroMatrixQuadratic_nonnegative
    (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic {size}
      cutoffTwoSectorMeanZeroMatrix coefficient :=
  finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
    cutoffTwoSectorLDLRows_checked
    cutoffTwoSectorLower_upper_zero
    cutoffTwoSectorLDLDiagonal_checked coefficient

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRows_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorMeanZeroMatrixQuadratic_nonnegative
'''
    return data_source, chunk_sources, row_sources, root_source


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coupling", default="1/2")
    parser.add_argument("--jobs", type=int, default=min(16, os.cpu_count() or 1))
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(
            "lean/YMGap/Continuum"
        ),
    )
    arguments = parser.parse_args()
    data_source, chunk_sources, row_sources, root_source = render_certificate_bundle(
        coupling=Fraction(arguments.coupling), jobs=arguments.jobs
    )
    output_dir = arguments.output_dir
    rows_dir = output_dir / "BF4PhysicalBoundaryCutoffTwoSectorLDLRows"
    chunks_dir = output_dir / "BF4PhysicalBoundaryCutoffTwoSectorLDLChunks"
    rows_dir.mkdir(parents=True, exist_ok=True)
    chunks_dir.mkdir(parents=True, exist_ok=True)
    data_path = output_dir / "BF4PhysicalBoundaryCutoffTwoSectorLDLData.lean"
    root_path = output_dir / "BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.lean"
    def write_if_changed(path: Path, source: str) -> None:
        if path.exists() and path.read_text() == source:
            return
        path.write_text(source)

    write_if_changed(data_path, data_source)
    for row, source in enumerate(row_sources):
        write_if_changed(rows_dir / f"Row{row:02d}.lean", source)
    for row, sources in enumerate(chunk_sources):
        for chunk, source in enumerate(sources):
            write_if_changed(
                chunks_dir / f"Row{row:02d}Chunk{chunk:02d}.lean", source
            )
    write_if_changed(root_path, root_source)
    total_bytes = (len(data_source) + len(root_source)
                   + sum(map(len, row_sources))
                   + sum(len(source) for sources in chunk_sources
                         for source in sources))
    print(
        f"wrote {data_path}, {sum(map(len, chunk_sources))} column chunks, "
        f"{len(row_sources)} row shards, and {root_path} "
        f"({total_bytes} bytes)"
    )


if __name__ == "__main__":
    main()
