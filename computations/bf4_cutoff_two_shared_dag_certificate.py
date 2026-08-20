"""Hash-cons the exact cutoff-two nonzero elimination traces.

The producer builds the same 24-step ternary elimination used by the physical
kernel scout, but represents every factor by a stable integer ID.  Equal
literal tables and equal ordered buckets are interned.  Lean receives only
sparse table data and rechecks each selected bucket equation.

The initial version emits the complete shared factor pool plus a bounded pilot
of unique bucket certificates.  Scaling the certificate count is a generator
parameter, so compilation cost is measured before all buckets are emitted.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from textwrap import dedent

from computations.bf4_cutoff_two_65_sector_local_zero_certificate import (
    _raw_numerators,
)
from computations.bf4_cutoff_two_65_sector_spectrum_scout import (
    EXPECTED_FIXED_FACE_IDS,
    _common_factors,
    _elimination_order,
    _lower_heat_factor,
    _source_link_factors,
    sector_states,
)
from computations.bf4_cutoff_two_canonical_factor_pool import build_pool
from computations.bf4_cutoff_two_vacuum_column import Factor, _eliminate


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean" / "YMGap" / "Continuum"
RAW_DATA = LEAN / "BF4PhysicalBoundaryCutoffTwoSectorRawKernelData.lean"
SIZE = 65
INITIAL_FACTOR_COUNT = 81


@dataclass(frozen=True)
class SharedEdge:
    variable: int
    bucket_ids: tuple[int, ...]
    result_id: int


@dataclass(frozen=True)
class PairTrace:
    row: int
    column: int
    edge_ids: tuple[int, ...]
    node_ids: tuple[tuple[int, ...], ...]
    terminal_ids: tuple[int, ...]
    interface: Fraction
    lower_pair: Fraction
    raw: Fraction


@dataclass(frozen=True)
class SharedDAG:
    factors: tuple[Factor, ...]
    edges: tuple[SharedEdge, ...]
    edge_usage: tuple[int, ...]
    traces: tuple[PairTrace, ...]


def _factor_key(factor: Factor) -> tuple[tuple[int, ...], tuple[Fraction, ...]]:
    return factor.scope, factor.table


def build_shared_dag() -> SharedDAG:
    states = sector_states()
    coupling = Fraction(1, 2)
    order, width = _elimination_order(coupling)
    if width != 5:
        raise AssertionError("audited elimination width drifted")

    canonical = build_pool()
    common_ids = canonical["common_ids"]
    source_ids = canonical["source_ids"]
    assert isinstance(common_ids, tuple)
    assert isinstance(source_ids, tuple)

    initial_factors = _common_factors(coupling)
    all_source_factors = tuple(_source_link_factors(state) for state in states)
    factors: list[Factor | None] = [None] * INITIAL_FACTOR_COUNT
    for factor_id, factor in zip(common_ids, initial_factors, strict=True):
        factors[factor_id] = factor
    for ids, state_factors in zip(source_ids, all_source_factors, strict=True):
        for factor_id, factor in zip(ids, state_factors, strict=True):
            previous = factors[factor_id]
            if previous is not None and previous != factor:
                raise AssertionError("canonical initial factor ID collision")
            factors[factor_id] = factor
    if any(factor is None for factor in factors):
        raise AssertionError("canonical initial factor pool is incomplete")
    concrete_factors = [factor for factor in factors if factor is not None]
    factor_id_of = {
        _factor_key(factor): factor_id
        for factor_id, factor in enumerate(concrete_factors)
    }

    def intern_factor(factor: Factor) -> int:
        key = _factor_key(factor)
        old = factor_id_of.get(key)
        if old is not None:
            return old
        factor_id = len(concrete_factors)
        factor_id_of[key] = factor_id
        concrete_factors.append(factor)
        return factor_id

    raw_numerators = _raw_numerators(RAW_DATA)
    edge_id_of: dict[SharedEdge, int] = {}
    edges: list[SharedEdge] = []
    usage: Counter[int] = Counter()
    traces: list[PairTrace] = []
    for row in range(SIZE):
        for column in range(row, SIZE):
            if raw_numerators[row * SIZE + column] == 0:
                continue
            # A stable factor-ID order makes identical local buckets
            # definitionally equal across otherwise different traces.
            current_ids = tuple(sorted(
                common_ids + source_ids[row] + source_ids[column]
            ))
            trace_edges: list[int] = []
            trace_nodes = [current_ids]
            for variable in order:
                bucket_ids = tuple(
                    factor_id for factor_id in current_ids
                    if variable in concrete_factors[factor_id].scope
                )
                outside_ids = tuple(
                    factor_id for factor_id in current_ids
                    if variable not in concrete_factors[factor_id].scope
                )
                bucket = tuple(concrete_factors[factor_id] for factor_id in bucket_ids)
                _after, step, _pids = _eliminate(bucket, variable, None, 1)
                result_id = intern_factor(step.result)
                edge = SharedEdge(variable, bucket_ids, result_id)
                edge_id = edge_id_of.get(edge)
                if edge_id is None:
                    edge_id = len(edges)
                    edge_id_of[edge] = edge_id
                    edges.append(edge)
                usage[edge_id] += 1
                trace_edges.append(edge_id)
                current_ids = tuple(sorted((result_id,) + outside_ids))
                trace_nodes.append(current_ids)
            if any(concrete_factors[factor_id].scope for factor_id in current_ids):
                raise AssertionError("terminal shared trace retained a live scope")
            interface = Fraction(1)
            for factor_id in current_ids:
                interface *= concrete_factors[factor_id].table[0]
            raw = (
                _lower_heat_factor(coupling, states[row])
                * _lower_heat_factor(coupling, states[column])
                * interface
            )
            if raw == 0:
                raise AssertionError("raw table marked a zero entry as nonzero")
            traces.append(PairTrace(
                row, column, tuple(trace_edges), tuple(trace_nodes),
                current_ids, interface,
                _lower_heat_factor(coupling, states[row])
                * _lower_heat_factor(coupling, states[column]),
                raw,
            ))
    if len(traces) != 499:
        raise AssertionError(f"expected 499 unordered nonzero traces, got {len(traces)}")
    return SharedDAG(
        tuple(concrete_factors),
        tuple(edges),
        tuple(usage[index] for index in range(len(edges))),
        tuple(traces),
    )


def _lean_q(value: Fraction) -> str:
    if value < 0:
        raise ValueError("shared DAG factor is unexpectedly negative")
    if value.denominator == 1:
        return f"({value.numerator} : Q')"
    # `Q'` stores the predecessor of the positive denominator.
    return f"(⟨{value.numerator}, {value.denominator - 1}⟩ : Q')"


def _nat_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def _datum(factor: Factor) -> str:
    scope = tuple(EXPECTED_FIXED_FACE_IDS[index] for index in factor.scope)
    entries = [
        f"({index}, {_lean_q(value)})"
        for index, value in enumerate(factor.table) if value != 0
    ]
    return (
        "    { scope := " + _nat_list(scope)
        + ", nonzeroEntries := [" + ", ".join(entries) + "] }"
    )


def render_factor_pool(dag: SharedDAG) -> str:
    intermediate = dag.factors[INITIAL_FACTOR_COUNT:]
    data = ",\n".join(_datum(factor) for factor in intermediate)
    return f'''/-
# Shared literal-factor pool for cutoff-two nonzero sector traces

Generated by `computations/bf4_cutoff_two_shared_dag_certificate.py`.
The producer is untrusted; bucket equations are checked in separate modules.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoSharedDAGIntermediateFactorData : List SparseEliminationDatum :=
  [
{data}
  ]

def cutoffTwoSharedDAGFactor (index : Nat) : ScopedQFactor :=
  if index < {INITIAL_FACTOR_COUNT} then
    cutoffTwoCanonicalFactor index
  else
    (cutoffTwoSharedDAGIntermediateFactorData.getD
      (index - {INITIAL_FACTOR_COUNT})
      {{ scope := [], nonzeroEntries := [] }}).factor 2

def cutoffTwoSharedDAGFactorList (indices : List Nat) : List ScopedQFactor :=
  indices.map cutoffTwoSharedDAGFactor

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
'''


def render_bucket_pilot(dag: SharedDAG, count: int) -> str:
    selected = tuple(range(min(count, len(dag.edges))))
    pieces = ['''/- Pilot kernel checks for hash-consed elimination buckets. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBucketPilot

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate
''']
    for edge_id in selected:
        edge = dag.edges[edge_id]
        coordinate = EXPECTED_FIXED_FACE_IDS[edge.variable]
        pieces.append(f'''
def cutoffTwoSharedDAGBucket{edge_id:04d} : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList {_nat_list(edge.bucket_ids)}

def cutoffTwoSharedDAGBucket{edge_id:04d}Certificate : CheckedBucketResult 2
    {coordinate} cutoffTwoSharedDAGBucket{edge_id:04d} where
  result := cutoffTwoSharedDAGFactor {edge.result_id}
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide
''')
    if selected:
        last = selected[-1]
        pieces.append(f'''
theorem cutoffTwoSharedDAGBucketPilotLast_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket{last:04d}Certificate.result.scope
        cutoffTwoSharedDAGBucket{last:04d}Certificate.result.value
        (eliminatedBucketValue 2
          {EXPECTED_FIXED_FACE_IDS[dag.edges[last].variable]}
          cutoffTwoSharedDAGBucket{last:04d}) = true :=
  cutoffTwoSharedDAGBucket{last:04d}Certificate.table_checked
''')
    pieces.append('''
end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBucketPilot
''')
    if selected:
        pieces.append(f'''
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBucketPilot.cutoffTwoSharedDAGBucketPilotLast_checked
''')
    return "".join(pieces)


def render_bucket_shard(
    dag: SharedDAG, shard: int, start: int, end: int
) -> str:
    selected = tuple(range(start, end))
    pieces = [f'''/- Shared-DAG bucket certificates {start} through {end - 1}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate
''']
    for edge_id in selected:
        edge = dag.edges[edge_id]
        coordinate = EXPECTED_FIXED_FACE_IDS[edge.variable]
        pieces.append(f'''
def cutoffTwoSharedDAGBucket{edge_id:04d} : List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList {_nat_list(edge.bucket_ids)}

def cutoffTwoSharedDAGBucket{edge_id:04d}Certificate : CheckedBucketResult 2
    {coordinate} cutoffTwoSharedDAGBucket{edge_id:04d} where
  result := cutoffTwoSharedDAGFactor {edge.result_id}
  scope_nodup := by decide
  coordinate_not_scope := by decide
  scope_cover_checked := by decide
  table_checked := by decide
''')
    last = selected[-1]
    pieces.append(f'''
theorem cutoffTwoSharedDAGBucketShard{shard:03d}_checked :
    boundedLocalEquationCheck 2
        cutoffTwoSharedDAGBucket{last:04d}Certificate.result.scope
        cutoffTwoSharedDAGBucket{last:04d}Certificate.result.value
        (eliminatedBucketValue 2
          {EXPECTED_FIXED_FACE_IDS[dag.edges[last].variable]}
          cutoffTwoSharedDAGBucket{last:04d}) = true :=
  cutoffTwoSharedDAGBucket{last:04d}Certificate.table_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.cutoffTwoSharedDAGBucketShard{shard:03d}_checked
''')
    return "".join(pieces)


def render_bucket_root(shard_count: int) -> str:
    imports = "\n".join(
        "import YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.Shard{shard:03d}"
        for shard in range(shard_count)
    )
    return dedent(f'''\
        /- Import surface for every independently checked shared-DAG bucket. -/
        {imports}

        namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets

        def cutoffTwoSharedDAGBucketShardCount : Nat := {shard_count}

        end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
        ''')


def _trace_tag(trace: PairTrace) -> str:
    return f"R{trace.row:02d}C{trace.column:02d}"


def render_trace_data(trace: PairTrace) -> str:
    tag = _trace_tag(trace)
    definitions = "\n\n".join(
        f'''def cutoffTwoSharedDAGTrace{tag}Factors{index} :
    List ScopedQFactor :=
  cutoffTwoSharedDAGFactorList {_nat_list(ids)}'''
        for index, ids in enumerate(trace.node_ids)
    )
    return f'''/- Canonical factor nodes for shared-DAG trace {tag}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.FiniteScopedFactorTableCertificate

{definitions}

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data
'''


def render_trace_shard(
    dag: SharedDAG, trace: PairTrace, shard: int
) -> str:
    tag = _trace_tag(trace)
    start = 4 * shard
    end = min(start + 4, len(trace.edge_ids))
    namespace = f"BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Shard{shard:02d}"
    pieces = [f'''/- Structural shared-DAG trace {tag}, shard {shard}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data
import YMGap.Continuum.FiniteScopedFactorDAGCertificate

namespace YMGap.Continuum.{namespace}

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv
''']
    physical_order = tuple(EXPECTED_FIXED_FACE_IDS[index] for index in (
        12, 7, 5, 2, 10, 11, 18, 19, 8, 13, 15, 17,
        4, 1, 14, 0, 3, 6, 21, 9, 20, 16, 22, 23,
    ))
    # Guard against an accidental duplicated order constant in this renderer.
    expected_physical_order = (
        38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50,
        13, 4, 41, 2, 11, 20, 65, 29, 59, 49, 67, 68,
    )
    if physical_order != expected_physical_order:
        raise AssertionError("trace renderer elimination order drifted")
    for index in range(start, end):
        edge_id = trace.edge_ids[index]
        edge = dag.edges[edge_id]
        coordinate = EXPECTED_FIXED_FACE_IDS[edge.variable]
        before_ids = trace.node_ids[index]
        outside_ids = tuple(
            factor_id for factor_id in before_ids
            if edge.variable not in dag.factors[factor_id].scope
        )
        after_ids = (edge.result_id,) + outside_ids
        next_ids = trace.node_ids[index + 1]
        pieces.append(f'''
def cutoffTwoSharedDAGTrace{tag}Step{index} : CheckedScopedEliminationStep 2
    {coordinate}
    (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
    cutoffTwoSharedDAGTrace{tag}Factors{index} where
  bucketResult := cutoffTwoSharedDAGBucket{edge_id:04d}Certificate
  result_scope_remaining_checked := by decide

def cutoffTwoSharedDAGTrace{tag}Edge{index} :
    CheckedReorderedEliminationStep 2 {coordinate}
      (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
      cutoffTwoSharedDAGTrace{tag}Factors{index}
      cutoffTwoSharedDAGTrace{tag}Factors{index + 1} where
  step := cutoffTwoSharedDAGTrace{tag}Step{index}
  after_perm := by
    have houtside :
        factorOutside {coordinate}
            cutoffTwoSharedDAGTrace{tag}Factors{index} =
          cutoffTwoSharedDAGFactorList {_nat_list(outside_ids)} := by
      rfl
    have hids : ({_nat_list(after_ids)}).Perm {_nat_list(next_ids)} :=
      natListPerm_of_check _ _ (by decide)
    have hmapped := hids.map cutoffTwoSharedDAGFactor
    change
      (cutoffTwoSharedDAGTrace{tag}Step{index}.bucketResult.result ::
        factorOutside {coordinate}
          cutoffTwoSharedDAGTrace{tag}Factors{index}).Perm
        cutoffTwoSharedDAGTrace{tag}Factors{index + 1}
    rw [houtside]
    change
      (({_nat_list(after_ids)}).map cutoffTwoSharedDAGFactor).Perm
        (({_nat_list(next_ids)}).map cutoffTwoSharedDAGFactor)
    exact hmapped
''')
    chain = "\n".join(
        f'''    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
        cutoffTwoSharedDAGTrace{tag}Factors{index + 1} := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        cutoffTwoSharedDAGTrace{tag}Edge{index}.partitionSum_eqv_after'''
        for index in range(start, end)
    )
    pieces.append(f'''
theorem cutoffTwoSharedDAGTrace{tag}Shard{shard:02d}_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {start})
        cutoffTwoSharedDAGTrace{tag}Factors{start} ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {end})
        cutoffTwoSharedDAGTrace{tag}Factors{end} := by
  calc
{chain}

end YMGap.Continuum.{namespace}

#print axioms
  YMGap.Continuum.{namespace}.cutoffTwoSharedDAGTrace{tag}Shard{shard:02d}_partitionSum_eqv
''')
    return "".join(pieces)


def render_trace_root(trace: PairTrace) -> str:
    tag = _trace_tag(trace)
    imports = "\n".join(
        "import YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}.Shard{shard:02d}"
        for shard in range(6)
    )
    opens = "\n".join(
        "open YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Shard{shard:02d}"
        for shard in range(6)
    )
    chain = f"cutoffTwoSharedDAGTrace{tag}Shard05_partitionSum_eqv"
    for shard in reversed(range(5)):
        chain = (
            f"Q'.eqv_trans _ _ _ "
            f"cutoffTwoSharedDAGTrace{tag}Shard{shard:02d}_partitionSum_eqv "
            f"({chain})"
        )
    return f'''/- Complete compact shared-DAG trace {tag}. -/
{imports}

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
{opens}

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTrace{tag}ExpectedInterface : Q' :=
  {_lean_q(trace.interface)}

theorem cutoffTwoSharedDAGTrace{tag}Terminal_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTrace{tag}Factors24 ≈
      cutoffTwoSharedDAGTrace{tag}ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTrace{tag}Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTrace{tag}Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTrace{tag}Factors24 :=
  {chain}

theorem cutoffTwoSharedDAGTrace{tag}Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTrace{tag}Factors0 ≈
      cutoffTwoSharedDAGTrace{tag}ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTrace{tag}Segments_partitionSum_eqv
    cutoffTwoSharedDAGTrace{tag}Terminal_eqv_expected

theorem cutoffTwoSharedDAGTrace{tag}eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTrace{tag}Factors0 ≈
      cutoffTwoSharedDAGTrace{tag}ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTrace{tag}Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTrace{tag}Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Certificate.cutoffTwoSharedDAGTrace{tag}eqv_expected
'''


def emit_trace_pilot(dag: SharedDAG, row: int, column: int) -> None:
    trace = next(
        candidate for candidate in dag.traces
        if candidate.row == row and candidate.column == column
    )
    tag = _trace_tag(trace)
    _write_if_changed(
        LEAN / f"BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data.lean",
        render_trace_data(trace),
    )
    shard_dir = LEAN / f"BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}"
    shard_dir.mkdir(parents=True, exist_ok=True)
    for shard in range(6):
        _write_if_changed(
            shard_dir / f"Shard{shard:02d}.lean",
            render_trace_shard(dag, trace, shard),
        )
    _write_if_changed(
        LEAN / f"BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Certificate.lean",
        render_trace_root(trace),
    )
    if (row, column) == (1, 1):
        canonical = build_pool()
        common_ids = canonical["common_ids"]
        source_ids = canonical["source_ids"]
        assert isinstance(common_ids, tuple)
        assert isinstance(source_ids, tuple)
        unsorted_ids = common_ids + source_ids[row] + source_ids[column]
        _write_if_changed(
            LEAN / "BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate.lean",
            render_physical_r01c01_bridge(trace, unsorted_ids),
        )
    else:
        canonical = build_pool()
        common_ids = canonical["common_ids"]
        source_ids = canonical["source_ids"]
        assert isinstance(common_ids, tuple)
        assert isinstance(source_ids, tuple)
        unsorted_ids = common_ids + source_ids[row] + source_ids[column]
        _write_if_changed(
            LEAN / f"BF4PhysicalBoundaryCutoffTwoSharedDAGPhysical{tag}Certificate.lean",
            render_physical_pair_certificate(trace, unsorted_ids),
        )


def render_physical_pair_certificate(
    trace: PairTrace, unsorted_ids: tuple[int, ...]
) -> str:
    row = trace.row
    column = trace.column
    tag = _trace_tag(trace)
    sorted_ids = trace.node_ids[0]
    return f'''/- End-to-end shared-DAG physical certificate for sector {tag}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{row:02d}Sharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{column:02d}Sharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysical{tag}Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{row:02d}Sharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{column:02d}Sharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTrace{tag}Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoPhysical{tag}MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt {row}) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt {column}))

def cutoffTwoCanonical{tag}MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt {row} ++
      cutoffTwoCanonicalSourceFactorsAt {column})

def cutoffTwoCanonical{tag}IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList {_nat_list(unsorted_ids)}

def cutoffTwoCanonical{tag}SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList {_nat_list(sorted_ids)}

theorem cutoffTwoPhysical{tag}MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysical{tag}MatchedFactors
      cutoffTwoCanonical{tag}MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource{row:02d}Transport
      cutoffTwoCanonicalSource{column:02d}Transport)

theorem cutoffTwoCanonical{tag}Matched_eq_indexed :
    cutoffTwoCanonical{tag}MatchedFactors =
      cutoffTwoCanonical{tag}IndexedFactors := by
  rfl

theorem cutoffTwoCanonical{tag}Sorted_eq_trace :
    cutoffTwoCanonical{tag}SortedFactors =
      cutoffTwoSharedDAGTrace{tag}Factors0 := by
  rfl

theorem cutoffTwoCanonical{tag}Matched_perm_trace :
    cutoffTwoCanonical{tag}MatchedFactors.Perm
      cutoffTwoSharedDAGTrace{tag}Factors0 := by
  rw [cutoffTwoCanonical{tag}Matched_eq_indexed,
    ← cutoffTwoCanonical{tag}Sorted_eq_trace]
  unfold cutoffTwoCanonical{tag}IndexedFactors
    cutoffTwoCanonical{tag}SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    {_nat_list(unsorted_ids)} {_nat_list(sorted_ids)} (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysical{tag}MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysical{tag}MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonical{tag}MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0) cutoffTwoPhysical{tag}MatchedTransport

theorem cutoffTwoPhysical{tag}Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt {row})
        (cutoffTwoSectorLocalZeroStateAt {column}) =
      cutoffTwoPhysical{tag}MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysical{tag}MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysical{tag}Interface_eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt {row})
          (cutoffTwoSectorLocalZeroStateAt {column})) ≈
      cutoffTwoSharedDAGTrace{tag}ExpectedInterface := by
  rw [cutoffTwoPhysical{tag}Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysical{tag}MatchedPartitionSum_eqv
    (Q'.eqv_trans _ _ _
      (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
        cutoffTwoCanonical{tag}Matched_perm_trace)
      cutoffTwoSharedDAGTrace{tag}eqv_expected)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_{tag}_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt {row})
      (cutoffTwoSectorLocalZeroStateAt {column}) ≈
        cutoffTwoSectorRawKernel {row} {column} :=
  centralPhysicalReflectedKernel_cutoffTwo_eqv_of_interface
    (cutoffTwoSectorLocalZeroStateAt {row})
    (cutoffTwoSectorLocalZeroStateAt {column})
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
    cutoffTwoSharedDAGTrace{tag}ExpectedInterface
    {_lean_q(trace.lower_pair)} (cutoffTwoSectorRawKernel {row} {column})
    cutoffTwoPhysical{tag}Interface_eqv_expected
    (by decide) (by decide)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysical{tag}Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysical{tag}Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_{tag}_eqv_raw_sharedDAG
'''


def render_physical_r01c01_bridge(
    trace: PairTrace, unsorted_ids: tuple[int, ...]
) -> str:
    sorted_ids = trace.node_ids[0]
    return f'''/- End-to-end physical-to-shared-DAG certificate for sector (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoPhysicalR01C01MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1))

def cutoffTwoCanonicalR01C01MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 1 ++
      cutoffTwoCanonicalSourceFactorsAt 1)

def cutoffTwoCanonicalR01C01IndexedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList {_nat_list(unsorted_ids)}

def cutoffTwoCanonicalR01C01SortedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalFactorList {_nat_list(sorted_ids)}

theorem cutoffTwoPhysicalR01C01MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR01C01MatchedFactors
      cutoffTwoCanonicalR01C01MatchedFactors := by
  exact FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource01Transport
      cutoffTwoCanonicalSource01Transport)

theorem cutoffTwoCanonicalR01C01Matched_eq_indexed :
    cutoffTwoCanonicalR01C01MatchedFactors =
      cutoffTwoCanonicalR01C01IndexedFactors := by
  rfl

theorem cutoffTwoCanonicalR01C01Sorted_eq_trace :
    cutoffTwoCanonicalR01C01SortedFactors =
      cutoffTwoSharedDAGTraceR01C01Factors0 := by
  rfl

theorem cutoffTwoCanonicalR01C01Matched_perm_trace :
    cutoffTwoCanonicalR01C01MatchedFactors.Perm
      cutoffTwoSharedDAGTraceR01C01Factors0 := by
  rw [cutoffTwoCanonicalR01C01Matched_eq_indexed,
    ← cutoffTwoCanonicalR01C01Sorted_eq_trace]
  unfold cutoffTwoCanonicalR01C01IndexedFactors
    cutoffTwoCanonicalR01C01SortedFactors cutoffTwoCanonicalFactorList
  exact (natListPerm_of_check
    {_nat_list(unsorted_ids)} {_nat_list(sorted_ids)} (by decide)).map
      cutoffTwoCanonicalFactor

theorem cutoffTwoPhysicalR01C01Interface_eqv_canonical :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 1)
          (cutoffTwoSectorLocalZeroStateAt 1)) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR01C01Factors0 := by
  have htransport :
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          cutoffTwoPhysicalR01C01MatchedFactors ≈
        scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          cutoffTwoCanonicalR01C01MatchedFactors := by
    simpa [cutoffTwoCanonicalTransportIdentity] using
      scopedFactorPartitionSum_eqv_of_identity_listTransport 2
        (centralFixedFaceIds 0)
        cutoffTwoPhysicalR01C01MatchedTransport
  have hphysical :
      cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 1)
          (cutoffTwoSectorLocalZeroStateAt 1) =
        cutoffTwoPhysicalR01C01MatchedFactors := by
    simp [cutoffTwoSectorPairInterfaceFactors,
      cutoffTwoPhysicalR01C01MatchedFactors, List.append_assoc]
  rw [hphysical]
  exact Q'.eqv_trans _ _ _ htransport
    (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalR01C01Matched_perm_trace)

theorem cutoffTwoPhysicalR01C01Interface_eqv_one :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 1)
          (cutoffTwoSectorLocalZeroStateAt 1)) ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR01C01Interface_eqv_canonical
    cutoffTwoSharedDAGTraceR01C01Interface_eqv_one

private theorem q_mul_congr
    {{a a' b b' : Q'}} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw_sharedDAG :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt 1) ≈
        cutoffTwoSectorRawKernel 1 1 := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt 1)
      (cutoffTwoSectorLocalZeroStateAt_mem (by decide))
      (cutoffTwoSectorLocalZeroStateAt_mem (by decide))) ?_
  exact Q'.eqv_trans _ _ _
    (q_mul_congr
      (show cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt 1) *
          cutoffTwoLowerFaceScalar (cutoffTwoSectorLocalZeroStateAt 1) ≈
        (1 : Q') by decide)
      cutoffTwoPhysicalR01C01Interface_eqv_one)
    (show (1 : Q') * (1 : Q') ≈
        cutoffTwoSectorRawKernel 1 1 by decide)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate.centralPhysicalReflectedKernel_cutoffTwo_sector_R01C01_eqv_raw_sharedDAG
'''


def _write_if_changed(path: Path, source: str) -> None:
    if path.exists() and path.read_text() == source:
        return
    path.write_text(source)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pilot-buckets", type=int, default=24)
    parser.add_argument("--emit-all", action="store_true")
    parser.add_argument("--shard-size", type=int, default=24)
    parser.add_argument("--trace-row", type=int, default=1)
    parser.add_argument("--trace-column", type=int, default=1)
    arguments = parser.parse_args()
    dag = build_shared_dag()
    _write_if_changed(
        LEAN / "BF4PhysicalBoundaryCutoffTwoSharedDAGFactorPool.lean",
        render_factor_pool(dag),
    )
    _write_if_changed(
        LEAN / "BF4PhysicalBoundaryCutoffTwoSharedDAGBucketPilot.lean",
        render_bucket_pilot(dag, arguments.pilot_buckets),
    )
    if arguments.emit_all:
        if arguments.shard_size < 1:
            raise ValueError("shard size must be positive")
        shard_dir = LEAN / "BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets"
        shard_dir.mkdir(parents=True, exist_ok=True)
        ranges = tuple(
            (start, min(start + arguments.shard_size, len(dag.edges)))
            for start in range(0, len(dag.edges), arguments.shard_size)
        )
        for shard, (start, end) in enumerate(ranges):
            _write_if_changed(
                shard_dir / f"Shard{shard:03d}.lean",
                render_bucket_shard(dag, shard, start, end),
            )
        _write_if_changed(
            LEAN / "BF4PhysicalBoundaryCutoffTwoSharedDAGBuckets.lean",
            render_bucket_root(len(ranges)),
        )
    emit_trace_pilot(dag, arguments.trace_row, arguments.trace_column)
    scopes = Counter(len(factor.scope) for factor in dag.factors[INITIAL_FACTOR_COUNT:])
    reused = sum(count - 1 for count in dag.edge_usage)
    print(
        f"shared DAG: traces={len(dag.traces)}, edge-instances={sum(dag.edge_usage)}, "
        f"unique-canonical-buckets={len(dag.edges)}, reused={reused}, "
        f"factors={len(dag.factors)} ({len(dag.factors) - INITIAL_FACTOR_COUNT} intermediate), "
        f"intermediate-scopes={dict(sorted(scopes.items()))}, "
        f"pilot={min(arguments.pilot_buckets, len(dag.edges))}, "
        f"all-shards={'yes' if arguments.emit_all else 'no'}"
    )


if __name__ == "__main__":
    main()
