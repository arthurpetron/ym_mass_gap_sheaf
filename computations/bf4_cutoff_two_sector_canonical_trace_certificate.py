"""Emit a Lean-checkable sparse trace from canonical literal factors.

This is the cost gate for the shared elimination DAG.  It deliberately proves
only the canonical finite partition sum; the separate production-to-canonical
transport is not part of this pilot.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from computations.bf4_cutoff_two_sector_sparse_trace_certificate import (
    _tag,
    _write_if_changed,
    compute_trace,
    render_data,
)


ORDER = (
    38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50,
    13, 4, 41, 2, 11, 20, 65, 29, 59, 49, 68, 67,
)


def render_canonical_shard(trace: dict[str, object], shard: int) -> str:
    row = int(trace["row"])
    column = int(trace["column"])
    tag = _tag(row, column)
    start = 4 * shard
    end = start + 4
    namespace = (
        f"BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Shard{shard:02d}"
    )
    if shard == 0:
        imports = (
            "import YMGap.Continuum."
            f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data\n"
            "import YMGap.Continuum."
            "BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool"
        )
        previous_open = ""
        initial = f'''\ndef canonicalSparseTrace{tag}Factors0 : List ScopedQFactor :=
  cutoffTwoCanonicalSectorPairFactors {row} {column}
'''
    else:
        previous_module = (
            "YMGap.Continuum."
            f"BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}."
            f"Shard{shard - 1:02d}"
        )
        imports = f"import {previous_module}"
        previous_namespace = (
            "YMGap.Continuum."
            f"BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Shard"
            f"{shard - 1:02d}"
        )
        previous_open = f"open {previous_namespace}\n"
        initial = ""
    pieces = [f'''/- Generated canonical sparse trace {tag}, shard {shard}. -/
{imports}

namespace YMGap.Continuum.{namespace}

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
{previous_open}
local infix:50 " ≈ " => Q'.eqv
{initial}''']
    for index in range(start, end):
        pieces.append(f'''
def canonicalSparseTrace{tag}Step{index} : CheckedScopedEliminationStep 2
    {ORDER[index]}
    (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
    canonicalSparseTrace{tag}Factors{index} where
  bucketResult :=
    {{ result := (sparseTrace{tag}Datum {index}).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }}
  result_scope_remaining_checked := by decide

def canonicalSparseTrace{tag}Factors{index + 1} : List ScopedQFactor :=
  canonicalSparseTrace{tag}Step{index}.afterFactors
''')
    chain = "\n".join(
        f'''    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
        canonicalSparseTrace{tag}Factors{index + 1} := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTrace{tag}Step{index}.partitionSum_eqv_after'''
        for index in range(start, end)
    )
    pieces.append(f'''
theorem canonicalSparseTrace{tag}Shard{shard:02d}_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {start})
        canonicalSparseTrace{tag}Factors{start} ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {end})
        canonicalSparseTrace{tag}Factors{end} := by
  calc
{chain}

end YMGap.Continuum.{namespace}

#print axioms
  YMGap.Continuum.{namespace}.canonicalSparseTrace{tag}Shard{shard:02d}_partitionSum_eqv
''')
    return "".join(pieces)


def render_canonical_root(trace: dict[str, object]) -> str:
    row = int(trace["row"])
    column = int(trace["column"])
    tag = _tag(row, column)
    opens = "\n".join(
        "open YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Shard{shard:02d}"
        for shard in range(6)
    )
    chain = f"canonicalSparseTrace{tag}Shard05_partitionSum_eqv"
    for shard in reversed(range(5)):
        chain = (
            f"Q'.eqv_trans _ _ _ "
            f"canonicalSparseTrace{tag}Shard{shard:02d}_partitionSum_eqv "
            f"({chain})"
        )
    return f'''/- Complete canonical sparse certificate for sector ({row}, {column}). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
{opens}

local infix:50 " ≈ " => Q'.eqv

theorem canonicalSparseTrace{tag}Terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        canonicalSparseTrace{tag}Factors24 ≈
      sparseTrace{tag}ExpectedInterface := by
  decide

theorem canonicalSparseTrace{tag}InterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        canonicalSparseTrace{tag}Factors0 ≈
      sparseTrace{tag}ExpectedInterface := by
  exact Q'.eqv_trans _ _ _ ({chain})
    canonicalSparseTrace{tag}Terminal_partitionSum_eqv_expected

theorem canonicalSparseTrace{tag}InterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        canonicalSparseTrace{tag}Factors0 ≈
      sparseTrace{tag}ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct canonicalSparseTrace{tag}Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    canonicalSparseTrace{tag}InterfacePartitionSum_ordered_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Certificate.canonicalSparseTrace{tag}InterfacePartitionSum_eqv
'''


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
    _write_if_changed(
        output_dir / f"BF4PhysicalBoundaryCutoffTwoSectorSparseTrace{tag}Data.lean",
        render_data(trace),
    )
    shard_dir = (
        output_dir / f"BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}"
    )
    shard_dir.mkdir(parents=True, exist_ok=True)
    for shard in range(6):
        _write_if_changed(
            shard_dir / f"Shard{shard:02d}.lean",
            render_canonical_shard(trace, shard),
        )
    _write_if_changed(
        output_dir
        / f"BF4PhysicalBoundaryCutoffTwoCanonicalSparseTrace{tag}Certificate.lean",
        render_canonical_root(trace),
    )
    print(f"generated canonical sparse trace {tag}, six four-step shards")


if __name__ == "__main__":
    main()
