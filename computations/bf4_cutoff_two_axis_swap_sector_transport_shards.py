"""Generate process-isolated Lean checks for the first cube-axis swap.

The state action is derived from the exact cube-axis permutation producer.
Each of the 64 non-cube states is normalized in its own Lean module; compact
five-state aggregates retain the historical shard API consumed by the
all-state and interface theorems.  This script writes repetitive proof
plumbing and is not trusted by any Lean theorem.
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
STATE_DIRECTORY_STEM = (
    "BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates"
)
AGGREGATE_SIZE = 5


def state_text(source: int, target: int, shard: int) -> str:
    namespace = f"{NAMESPACE_STEM}{shard:02d}"
    return f"""/- Process-isolated first-axis-swap state {source:02d}. -/
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

theorem axisSwap01State{source:02d}LinkTransportCheck :
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

end {namespace}

#print axioms {namespace}.axisSwap01State{source:02d}LinkTransportCheck
#print axioms {namespace}.axisSwap01State{source:02d}LinkTransportCheckedAt
"""


def shard_text(shard: int, sources: tuple[int, ...]) -> str:
    namespace = f"{NAMESPACE_STEM}{shard:02d}"
    imports = "\n".join(
        f"import YMGap.Continuum.{STATE_DIRECTORY_STEM}.State{source:02d}"
        for source in sources
    )
    values = ", ".join(map(str, sources))
    checks = ",\n    ".join(
        f"axisSwap01State{source:02d}LinkTransportCheckedAt"
        for source in sources
    )
    return f"""/- Compact aggregate for first-axis-swap states
{sources[0]} through {sources[-1]}. -/
{imports}

namespace {namespace}

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

def axisSwap01Shard{shard:02d}Indices : List (Fin 65) :=
  [{values}]

theorem axisSwap01Shard{shard:02d}AllChecked :
    axisSwap01Shard{shard:02d}Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard{shard:02d}Indices
  simp only [List.all_cons, List.all_nil,
    {checks},
    Bool.true_and]

end {namespace}

#print axioms {namespace}.axisSwap01Shard{shard:02d}AllChecked
"""


def audit_text() -> str:
    namespace = (
        "YMGap.Continuum."
        "BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport"
    )
    return f"""import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport

#print axioms {namespace}.axisSwap01AllStateLinkTransport
"""


def generate(output_directory: Path) -> tuple[Path, ...]:
    action = _sector_state_action(
        _cube_position_action((1, 0, 2), (0, 0, 0))
    )
    if len(action) != 65 or action[0] != 0:
        raise AssertionError("first axis-swap sector action drifted")

    written: list[Path] = []
    state_directory = output_directory / STATE_DIRECTORY_STEM
    state_directory.mkdir(parents=True, exist_ok=True)
    for source in range(1, 65):
        shard = (source - 1) // AGGREGATE_SIZE
        path = state_directory / f"State{source:02d}.lean"
        path.write_text(
            state_text(source, action[source], shard), encoding="utf-8"
        )
        written.append(path)

    for shard, start in enumerate(range(1, 65, AGGREGATE_SIZE)):
        sources = tuple(range(start, min(start + AGGREGATE_SIZE, 65)))
        path = output_directory / f"{MODULE_STEM}{shard:02d}.lean"
        path.write_text(shard_text(shard, sources), encoding="utf-8")
        written.append(path)

    audit = output_directory / (
        "BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportAxiomAudit.lean"
    )
    audit.write_text(audit_text(), encoding="utf-8")
    written.append(audit)
    return tuple(written)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-directory",
        type=Path,
        default=Path("lean/YMGap/Continuum"),
    )
    arguments = parser.parse_args()
    paths = generate(arguments.output_directory)
    print(f"generated_files={len(paths)}")
    for path in paths:
        print(path)


if __name__ == "__main__":
    main()
