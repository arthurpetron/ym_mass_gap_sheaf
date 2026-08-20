"""Generate Lean local-table shards for all 64 doubled subset states.

The state action is derived from the exact cube-axis permutation producer.
Each emitted theorem asks Lean's constructive checker to recompute all 48
production lower-link factor transports.  This script only writes repetitive
proof plumbing; it is not trusted by any theorem.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from computations.bf4_cutoff_two_cube_automorphism_certificate import (
    _cube_position_action,
    _sector_state_action,
)


MODULE_STEM = "BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard"
NAMESPACE_STEM = "YMGap.Continuum." + MODULE_STEM


def theorem_text(source: int, target: int) -> str:
    return f"""theorem axisSwap01State{source:02d}LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors {source})
      (axisSwap01StateMatchedTargetFactors {target}) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State{source:02d}LinkTransportCheckedAt :
    axisSwap01StateLinkTransportCheckAt {source} = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename
    (axisSwap01StateSourceFactors {source})
    (axisSwap01StateMatchedTargetFactors {target}) = true
  exact axisSwap01State{source:02d}LinkTransportCheck
"""


def shard_text(shard: int, sources: tuple[int, ...], action: tuple[int, ...]) -> str:
    namespace = f"{NAMESPACE_STEM}{shard:02d}"
    theorems = "\n".join(theorem_text(source, action[source])
                           for source in sources)
    index_values = ", ".join(map(str, sources))
    local_rewrites = ", ".join(
        f"axisSwap01State{source:02d}LinkTransportCheckedAt"
        for source in sources
    )
    chunk = f"""def axisSwap01Shard{shard:02d}Indices : List (Fin 65) :=
  [{index_values}]

theorem axisSwap01Shard{shard:02d}AllChecked :
    axisSwap01Shard{shard:02d}Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard{shard:02d}Indices
  simp only [List.all_cons, List.all_nil, {local_rewrites},
    Bool.true_and]
"""
    prints = "\n".join(
        f"#print axioms {namespace}.axisSwap01State{source:02d}LinkTransportCheck\n"
        f"#print axioms {namespace}.axisSwap01State{source:02d}LinkTransportCheckedAt"
        for source in sources
    )
    return f"""/-
Generated local-table certificates for axis-swap sector states
{sources[0]} through {sources[-1]}.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

namespace {namespace}

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

{theorems}
{chunk}
end {namespace}

{prints}
"""


def generate(output_directory: Path, shard_size: int) -> tuple[Path, ...]:
    if shard_size <= 0:
        raise ValueError("shard size must be positive")
    action = _sector_state_action(
        _cube_position_action((1, 0, 2), (0, 0, 0))
    )
    if len(action) != 65 or action[0] != 0:
        raise AssertionError("axis-swap sector action drifted")
    sources = tuple(range(1, 65))
    written: list[Path] = []
    for shard, start in enumerate(range(0, len(sources), shard_size)):
        group = sources[start:start + shard_size]
        path = output_directory / f"{MODULE_STEM}{shard:02d}.lean"
        path.write_text(shard_text(shard, group, action), encoding="utf-8")
        written.append(path)
    return tuple(written)


def aggregate_text(shard_size: int, action: tuple[int, ...]) -> str:
    imports = "\n".join(
        f"import YMGap.Continuum.{MODULE_STEM}{shard:02d}"
        for shard in range((64 + shard_size - 1) // shard_size)
    )
    shard_count = (64 + shard_size - 1) // shard_size
    shard_namespaces = [f"{NAMESPACE_STEM}{shard:02d}"
                        for shard in range(shard_count)]
    shard_index_names = [f"{namespace}.axisSwap01Shard{shard:02d}Indices"
                         for shard, namespace in enumerate(shard_namespaces)]
    shard_checked_names = [
        f"{namespace}.axisSwap01Shard{shard:02d}AllChecked"
        for shard, namespace in enumerate(shard_namespaces)
    ]
    checks: list[str] = []
    check_names: list[str] = ["axisSwap01State00LinkTransportCheck"]
    for source in range(1, 65):
        shard = (source - 1) // shard_size
        check_name = (
            f"{NAMESPACE_STEM}{shard:02d}."
            f"axisSwap01State{source:02d}LinkTransportCheck"
        )
        check_names.append(check_name)
    for source in range(65):
        checks.append(f"""factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors {source})
        (axisSwap01StateMatchedTargetFactors {action[source]})""")
    check_expression = " &&\n      ".join(checks) + " && true"
    rewrites = ",\n      ".join(check_names)
    all_indices_expression = " ++\n    ".join(["[(0 : Fin 65)]"] + shard_index_names)
    unfold_indices = "\n    ".join(shard_index_names)
    chunk_rewrites = ",\n    ".join(
        ["axisSwap01State00LinkTransportCheck"] + shard_checked_names
    )
    return f"""/-
# Complete checked state-link transport for the first axis swap

All 65 state-dependent 48-factor certificates are assembled here.  The
fundamental cube uses its dedicated theorem; the 64 doubled subsets come from
the independently compiled shards.
-/

{imports}

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01State00LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 0)
      (axisSwap01StateMatchedTargetFactors 0) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

def axisSwap01AllStateIndices : List (Fin 65) :=
  {all_indices_expression}

theorem axisSwap01AllStateIndices_eq_finRange :
    axisSwap01AllStateIndices = List.finRange 65 := by
  unfold axisSwap01AllStateIndices
    {unfold_indices}
  decide

def axisSwap01AllStateLinkTransportCheck : Bool :=
  (List.finRange 65).all axisSwap01StateLinkTransportCheckAt

theorem axisSwap01AllStateLinkTransport_checked :
    axisSwap01AllStateLinkTransportCheck = true := by
  unfold axisSwap01AllStateLinkTransportCheck
  rw [← axisSwap01AllStateIndices_eq_finRange]
  unfold axisSwap01AllStateIndices
  simp only [List.all_append, List.all_cons, List.all_nil]
  rw [{chunk_rewrites}]

theorem axisSwap01AllStateLinkTransport : ∀ sourceIndex : Fin 65,
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors sourceIndex)
      (axisSwap01StateMatchedTargetFactors
        (axisSwap01SectorTargetIndex sourceIndex)) := by
  intro sourceIndex
  apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename
  exact List.all_eq_true.mp axisSwap01AllStateLinkTransport_checked
    sourceIndex (List.mem_finRange sourceIndex)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport.axisSwap01AllStateLinkTransport
"""


def audit_text(shard_size: int) -> str:
    imports = "\n".join(
        f"import YMGap.Continuum.{MODULE_STEM}{shard:02d}"
        for shard in range((64 + shard_size - 1) // shard_size)
    )
    prints: list[str] = []
    for source in range(1, 65):
        shard = (source - 1) // shard_size
        prints.append(
            f"#print axioms {NAMESPACE_STEM}{shard:02d}."
            f"axisSwap01State{source:02d}LinkTransportCheck"
        )
    return imports + "\n\n" + "\n".join(prints) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--shard-size", type=int, default=5)
    parser.add_argument(
        "--output-directory",
        type=Path,
        default=Path("lean/YMGap/Continuum"),
    )
    arguments = parser.parse_args()
    paths = generate(arguments.output_directory, arguments.shard_size)
    action = _sector_state_action(
        _cube_position_action((1, 0, 2), (0, 0, 0))
    )
    aggregate = arguments.output_directory / (
        "BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport.lean"
    )
    aggregate.write_text(
        aggregate_text(arguments.shard_size, action), encoding="utf-8"
    )
    audit = arguments.output_directory / (
        "BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportAxiomAudit.lean"
    )
    audit.write_text(audit_text(arguments.shard_size), encoding="utf-8")
    print(f"generated_shards={len(paths)}")
    print(f"generated_states={sum(path.read_text().count('LinkTransport :') for path in paths)}")
    print(f"generated_aggregate={aggregate}")
    print(f"generated_audit={audit}")


if __name__ == "__main__":
    main()
