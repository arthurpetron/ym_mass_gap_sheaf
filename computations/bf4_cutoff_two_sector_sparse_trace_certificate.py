"""Emit one Lean-checkable sparse trace for a nonzero 65-sector entry.

The Python contraction proposes 24 sparse intermediate tables.  Lean checks
each local bucket equation against the genuine 140-factor physical graph and
then identifies the resulting physical reflected-kernel entry with the exact
raw table literal.  The producer is untrusted.

This single-entry generator is also a cost pilot for a later batched producer.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

from computations.bf4_cutoff_two_65_sector_spectrum_scout import (
    EXPECTED_FIXED_FACE_IDS,
    _common_factors,
    _elimination_order,
    _lower_heat_factor,
    _source_link_factors,
    sector_states,
)
from computations.bf4_cutoff_two_vacuum_column import _eliminate


def _lean_q(value: Fraction) -> str:
    if value < 0:
        raise ValueError("physical sparse trace unexpectedly contains a negative value")
    if value.denominator == 1:
        return f"({value.numerator} : Q')"
    return (
        f"Q'.mkPos {value.numerator} {value.denominator} (by decide)"
    )


def _list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def _sparse_entries(table: tuple[Fraction, ...]) -> str:
    entries = [
        f"({index}, {_lean_q(value)})"
        for index, value in enumerate(table) if value != 0
    ]
    return "[" + ", ".join(entries) + "]"


def _tag(row: int, column: int) -> str:
    return f"R{row:02d}C{column:02d}"


def compute_trace(row: int, column: int) -> dict[str, object]:
    if not 0 <= row < 65 or not 0 <= column < 65:
        raise ValueError("row and column must lie in 0..64")
    states = sector_states()
    coupling = Fraction(1, 2)
    order, width = _elimination_order(coupling)
    factors = (
        _common_factors(coupling)
        + _source_link_factors(states[row])
        + _source_link_factors(states[column])
    )
    steps = []
    for variable in order:
        factors, step, _pids = _eliminate(factors, variable, None, 1)
        steps.append(step)
    interface = Fraction(1)
    for factor in factors:
        if factor.scope:
            raise AssertionError("terminal trace retained a live scope")
        interface *= factor.table[0]
    lower_pair = (
        _lower_heat_factor(coupling, states[row])
        * _lower_heat_factor(coupling, states[column])
    )
    raw = lower_pair * interface
    if raw == 0:
        raise ValueError("the selected entry is zero; use the local-zero certificate")
    actual_order = tuple(EXPECTED_FIXED_FACE_IDS[index] for index in order)
    expected_order = (
        38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50,
        13, 4, 41, 2, 11, 20, 65, 29, 59, 49, 68, 67,
    )
    if actual_order != expected_order or width != 5:
        raise AssertionError("audited width-five elimination order drifted")
    return {
        "row": row,
        "column": column,
        "steps": tuple(steps),
        "interface": interface,
        "lower_pair": lower_pair,
        "raw": raw,
        "width": width,
    }


def render_data(trace: dict[str, object]) -> str:
    row = int(trace["row"])
    column = int(trace["column"])
    tag = _tag(row, column)
    steps = trace["steps"]
    assert isinstance(steps, tuple)
    data = []
    for step in steps:
        scope = tuple(EXPECTED_FIXED_FACE_IDS[index]
                      for index in step.result.scope)
        data.append(
            "    { scope := " + _list(scope)
            + ", nonzeroEntries := "
            + _sparse_entries(step.result.table) + " }"
        )
    return f'''/- Generated untrusted sparse trace data for sector ({row}, {column}). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data

open YMGap.Constructive
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def sparseTrace{tag}TableData : List SparseEliminationDatum :=
  [
{",\n".join(data)}
  ]

theorem sparseTrace{tag}TableData_count :
    sparseTrace{tag}TableData.length = 24 := by
  decide

def sparseTrace{tag}Datum (index : Nat) : SparseEliminationDatum :=
  sparseTrace{tag}TableData.getD index
    {{ scope := [], nonzeroEntries := [] }}

def sparseTrace{tag}ExpectedInterface : Q' :=
  {_lean_q(trace["interface"])}

def sparseTrace{tag}ExpectedLowerPair : Q' :=
  {_lean_q(trace["lower_pair"])}

def sparseTrace{tag}ExpectedRaw : Q' :=
  {_lean_q(trace["raw"])}

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data
'''


def render_shard(trace: dict[str, object], shard: int) -> str:
    row = int(trace["row"])
    column = int(trace["column"])
    tag = _tag(row, column)
    start = 4 * shard
    end = start + 4
    namespace = f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Shard{shard:02d}"
    if shard == 0:
        import_module = (
            f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data"
        )
        previous_open = ""
        initial = f'''
def sparseTrace{tag}Factors0 : List ScopedQFactor :=
  cutoffTwoSectorPairInterfaceFactors
    (cutoffTwoSectorLocalZeroStateAt {row})
    (cutoffTwoSectorLocalZeroStateAt {column})
'''
    else:
        import_module = (
            f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}."
            f"Shard{shard - 1:02d}"
        )
        previous_namespace = (
            "YMGap.Continuum."
            f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Shard"
            f"{shard - 1:02d}"
        )
        previous_open = f"open {previous_namespace}\n"
        initial = ""
    pieces = [f'''/- Generated sparse trace {tag}, shard {shard}. -/
import YMGap.Continuum.{import_module}

namespace YMGap.Continuum.{namespace}

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
{previous_open}
local infix:50 " ≈ " => Q'.eqv
{initial}''']
    order = (38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50,
             13, 4, 41, 2, 11, 20, 65, 29, 59, 49, 68, 67)
    for index in range(start, end):
        pieces.append(f'''
def sparseTrace{tag}Step{index} : CheckedScopedEliminationStep 2
    {order[index]}
    (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
    sparseTrace{tag}Factors{index} where
  bucketResult :=
    {{ result := (sparseTrace{tag}Datum {index}).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }}
  result_scope_remaining_checked := by decide

def sparseTrace{tag}Factors{index + 1} : List ScopedQFactor :=
  sparseTrace{tag}Step{index}.afterFactors
''')
    chain = "\n".join(
        f'''    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
        sparseTrace{tag}Factors{index + 1} := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sparseTrace{tag}Step{index}.partitionSum_eqv_after'''
        for index in range(start, end)
    )
    pieces.append(f'''
theorem sparseTrace{tag}Shard{shard:02d}_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {start})
        sparseTrace{tag}Factors{start} ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {end})
        sparseTrace{tag}Factors{end} := by
  calc
{chain}

end YMGap.Continuum.{namespace}

#print axioms
  YMGap.Continuum.{namespace}.sparseTrace{tag}Shard{shard:02d}_partitionSum_eqv
''')
    return "".join(pieces)


def render_root(trace: dict[str, object]) -> str:
    row = int(trace["row"])
    column = int(trace["column"])
    tag = _tag(row, column)
    opens = "\n".join(
        "open YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Shard{shard:02d}"
        for shard in range(6)
    )
    chain = f"sparseTrace{tag}Shard05_partitionSum_eqv"
    for shard in reversed(range(5)):
        chain = (
            f"Q'.eqv_trans _ _ _ sparseTrace{tag}Shard{shard:02d}_partitionSum_eqv "
            f"({chain})"
        )
    return f'''/- Complete sparse certificate for nonzero sector entry ({row}, {column}). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
{opens}

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {{a a' b b' : Q'}} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem sparseTrace{tag}Terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        sparseTrace{tag}Factors24 ≈
      sparseTrace{tag}ExpectedInterface := by
  decide

theorem sparseTrace{tag}InterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        sparseTrace{tag}Factors0 ≈
      sparseTrace{tag}ExpectedInterface := by
  exact Q'.eqv_trans _ _ _ ({chain})
    sparseTrace{tag}Terminal_partitionSum_eqv_expected

theorem sparseTrace{tag}InterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        sparseTrace{tag}Factors0 ≈
      sparseTrace{tag}ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct sparseTrace{tag}Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    sparseTrace{tag}InterfacePartitionSum_ordered_eqv

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_{tag}_eqv_raw :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt {row})
      (cutoffTwoSectorLocalZeroStateAt {column}) ≈
        cutoffTwoSectorRawKernel {row} {column} := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorLocalZeroStateAt {row})
      (cutoffTwoSectorLocalZeroStateAt {column})
      (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
      (cutoffTwoSectorLocalZeroStateAt_mem (by decide))) ?_
  exact Q'.eqv_trans _ _ _
    (q_mul_congr
      (show cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt {row}) *
          cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt {column}) ≈
        sparseTrace{tag}ExpectedLowerPair by decide)
      sparseTrace{tag}InterfacePartitionSum_eqv)
    (show sparseTrace{tag}ExpectedLowerPair *
          sparseTrace{tag}ExpectedInterface ≈
        cutoffTwoSectorRawKernel {row} {column} by decide)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_{tag}_eqv_raw
'''


def _write_if_changed(path: Path, source: str) -> None:
    if path.exists() and path.read_text() == source:
        return
    path.write_text(source)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row", type=int, default=1)
    parser.add_argument("--column", type=int, default=1)
    parser.add_argument(
        "--output-dir", type=Path, default=Path("lean/YMGap/Continuum")
    )
    arguments = parser.parse_args()
    trace = compute_trace(arguments.row, arguments.column)
    tag = _tag(arguments.row, arguments.column)
    output_dir = arguments.output_dir
    shard_dir = output_dir / f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}"
    shard_dir.mkdir(parents=True, exist_ok=True)
    _write_if_changed(
        output_dir / f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data.lean",
        render_data(trace),
    )
    for shard in range(6):
        _write_if_changed(
            shard_dir / f"Shard{shard:02d}.lean",
            render_shard(trace, shard),
        )
    _write_if_changed(
        output_dir
        / f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Certificate.lean",
        render_root(trace),
    )
    steps = trace["steps"]
    assert isinstance(steps, tuple)
    print(
        f"generated sparse trace {tag}: width={trace['width']}, "
        f"nonzero-table-entries={sum(sum(value != 0 for value in step.result.table) for step in steps)}, "
        f"raw={trace['raw']}"
    )


if __name__ == "__main__":
    main()
