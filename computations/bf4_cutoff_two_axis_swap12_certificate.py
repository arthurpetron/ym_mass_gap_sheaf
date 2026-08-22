"""Generate Lean certificates for the second adjacent cube-axis swap.

The first adjacent swap is already checked in Lean.  This untrusted producer
reuses that proof plumbing while deriving every finite permutation for the
swap of abstract cube axes 1 and 2 from the production factor-graph scout.
Lean independently rechecks the emitted coordinate, factor, and local-table
transports.
"""

from __future__ import annotations

import re
from pathlib import Path

from computations.bf4_cutoff_two_cube_automorphism_certificate import (
    action_data,
)
from computations.bf4_cutoff_two_cube_boundary_row import (
    EXPECTED_FIXED_FACE_IDS,
)


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean" / "YMGap" / "Continuum"
SOURCE_STEM = "BF4PhysicalBoundaryCutoffTwoAxisSwap"
TARGET_STEM = "BF4PhysicalBoundaryCutoffTwoAxisSwap12"
STATE_DIRECTORY_STEM = TARGET_STEM + "SectorTransportStates"
SHARD_STEM = TARGET_STEM + "SectorTransportShard"


def _lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def _replace_list(text: str, name: str, values: tuple[int, ...]) -> str:
    pattern = rf"(def {name} : List \(Fin \d+\) :=\n  )\[[^]]*\]"
    answer, count = re.subn(pattern, rf"\g<1>{_lean_list(values)}", text)
    if count != 1:
        raise AssertionError(f"could not replace {name}: count={count}")
    return answer


def _replace_boundary_rename(
    text: str,
    coordinate_action: tuple[int, ...],
) -> str:
    clauses = []
    for source, target_position in enumerate(coordinate_action):
        source_id = EXPECTED_FIXED_FACE_IDS[source]
        target_id = EXPECTED_FIXED_FACE_IDS[target_position]
        if source_id != target_id:
            clauses.append(f"  | {source_id} => {target_id}")
    body = (
        "def axisSwap12BoundaryRename : Nat → Nat\n"
        + "\n".join(clauses)
        + "\n  | id => id"
    )
    pattern = (
        r"def axisSwap12BoundaryRename : Nat → Nat\n"
        r"(?:  \| .*\n)*  \| id => id"
    )
    answer, count = re.subn(pattern, body, text)
    if count != 1:
        raise AssertionError(f"could not replace boundary rename: count={count}")
    return answer


def _replace_interface_support(
    text: str,
    coordinate_action: tuple[int, ...],
) -> str:
    open_anchor = (
        "open YMGap.Continuum.FiniteScopedFactorTableCertificate."
        "CheckedScopedEliminationStep\n"
    )
    explicit_opens = (
        open_anchor
        + "open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph\n"
        + "open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights\n"
    )
    if open_anchor not in text:
        raise AssertionError("interface open anchor drifted")
    text = text.replace(open_anchor, explicit_opens, 1)

    moved_ids = tuple(
        EXPECTED_FIXED_FACE_IDS[source]
        for source, target in enumerate(coordinate_action)
        if source != target
    )
    cases = []
    for moved_id in moved_ids:
        name = f"h{moved_id}"
        cases.extend([
            f"  by_cases {name} : id = {moved_id}",
            "  · subst id",
            "    rfl",
        ])
    cases.extend([
        "  · simp [axisSwap12BoundaryRename]",
    ])
    old = """theorem axisSwap12BoundaryRename_involutive (id : Nat) :
    axisSwap12BoundaryRename (axisSwap12BoundaryRename id) = id := by
  simp [axisSwap12BoundaryRename]"""
    new = """theorem axisSwap12BoundaryRename_involutive (id : Nat) :
    axisSwap12BoundaryRename (axisSwap12BoundaryRename id) = id := by
""" + "\n".join(cases)
    if old not in text:
        raise AssertionError("interface involution proof anchor drifted")
    return text.replace(old, new, 1)


def _replace_state_targets(
    text: str,
    sector_action: tuple[int, ...],
) -> str:
    """Replace target literals coupled to a concrete source-state literal."""

    for source, target in enumerate(sector_action):
        pattern = (
            rf"(\(axisSwap12StateSourceFactors {source}\)\s+"
            rf"\(axisSwap12StateMatchedTargetFactors )\d+(\))"
        )
        text = re.sub(pattern, rf"\g<1>{target}\g<2>", text)
    return text


def _state_text(source: int, target: int, shard: int) -> str:
    namespace = (
        "YMGap.Continuum."
        f"{TARGET_STEM}SectorTransportShard{shard:02d}"
    )
    return f"""/- Process-isolated second-axis-swap state {source:02d}. -/
import YMGap.Continuum.{TARGET_STEM}SectorTransportData

namespace {namespace}

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.{TARGET_STEM}CommonFactorTransport
open YMGap.Continuum.{TARGET_STEM}CubeSourceFactorTransport
open YMGap.Continuum.{TARGET_STEM}SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap12State{source:02d}LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors {source})
      (axisSwap12StateMatchedTargetFactors {target}) = true := by
  unfold axisSwap12StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap12StateSourceFactors cutoffTwoSectorStateAt
    axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12State{source:02d}LinkTransportCheckedAt :
    axisSwap12StateLinkTransportCheckAt {source} = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors {source})
    (axisSwap12StateMatchedTargetFactors {target}) = true
  exact axisSwap12State{source:02d}LinkTransportCheck

end {namespace}

#print axioms {namespace}.axisSwap12State{source:02d}LinkTransportCheck
#print axioms {namespace}.axisSwap12State{source:02d}LinkTransportCheckedAt
"""


def _shard_text(shard: int, sources: tuple[int, ...]) -> str:
    namespace = (
        "YMGap.Continuum."
        f"{TARGET_STEM}SectorTransportShard{shard:02d}"
    )
    imports = "\n".join(
        f"import YMGap.Continuum.{STATE_DIRECTORY_STEM}.State{source:02d}"
        for source in sources
    )
    values = ", ".join(map(str, sources))
    checks = ",\n    ".join(
        f"axisSwap12State{source:02d}LinkTransportCheckedAt"
        for source in sources
    )
    return f"""/- Compact aggregate for second-axis-swap states
{sources[0]} through {sources[-1]}. -/
{imports}

namespace {namespace}

open YMGap.Continuum.{TARGET_STEM}SectorTransportData

def axisSwap12Shard{shard:02d}Indices : List (Fin 65) :=
  [{values}]

theorem axisSwap12Shard{shard:02d}AllChecked :
    axisSwap12Shard{shard:02d}Indices.all
      axisSwap12StateLinkTransportCheckAt = true := by
  unfold axisSwap12Shard{shard:02d}Indices
  simp only [List.all_cons, List.all_nil,
    {checks},
    Bool.true_and]

end {namespace}

#print axioms {namespace}.axisSwap12Shard{shard:02d}AllChecked
"""


def _axiom_audit_text() -> str:
    namespace = f"YMGap.Continuum.{TARGET_STEM}AllStateTransport"
    return f"""import YMGap.Continuum.{TARGET_STEM}AllStateTransport

#print axioms {namespace}.axisSwap12AllStateLinkTransport
"""


def generate() -> tuple[Path, ...]:
    action = action_data((0, 2, 1), (0, 0, 0))
    coordinates = tuple(action["fixed_coordinate_permutation"])
    fixed_links = tuple(action["fixed_link_permutation"])
    lower_links = tuple(action["lower_link_permutation"])
    sectors = tuple(action["state_permutation"])
    common_order = coordinates + tuple(24 + index for index in fixed_links)

    sources = sorted(LEAN.glob(f"{SOURCE_STEM}*.lean"))
    sources = [path for path in sources if not path.name.startswith(TARGET_STEM)]
    if len(sources) != 19:
        raise AssertionError(f"expected 19 axis-swap templates, found {len(sources)}")

    written = []
    for source in sources:
        target = source.with_name(source.name.replace(SOURCE_STEM, TARGET_STEM, 1))
        text = source.read_text(encoding="utf-8")
        text = text.replace(SOURCE_STEM, TARGET_STEM)
        text = text.replace("axisSwap01", "axisSwap12")
        text = text.replace("first spatial-axis swap", "second spatial-axis swap")
        text = text.replace("first axis swap", "second adjacent axis swap")
        text = text.replace(
            "first nonidentity spatial-axis generator",
            "second adjacent spatial-axis generator",
        )
        text = text.replace(
            "first two abstract cube axes", "last two abstract cube axes"
        )
        text = _replace_state_targets(text, sectors)
        if source.name.endswith("CommonFactorTransport.lean"):
            text = _replace_boundary_rename(text, coordinates)
            text = _replace_list(text, "axisSwap12CommonTargetOrder", common_order)
        elif source.name.endswith("CubeSourceFactorTransport.lean"):
            text = _replace_list(
                text, "axisSwap12LowerLinkTargetOrder", lower_links
            )
        elif source.name.endswith("SectorTransportData.lean"):
            text = _replace_list(
                text, "axisSwap12SectorTargetOrder", sectors
            )
        elif source.name.endswith("SectorTransportAxiomAudit.lean"):
            text = _axiom_audit_text()
        elif source.name.endswith("InterfaceInvariance.lean"):
            text = _replace_interface_support(text, coordinates)
        if "axisSwap01" in text or re.search(
            rf"{SOURCE_STEM}(?!12)", text
        ):
            raise AssertionError(f"stale first-swap name in {target.name}")
        target.write_text(text, encoding="utf-8")
        written.append(target)

    state_directory = LEAN / STATE_DIRECTORY_STEM
    state_directory.mkdir(parents=True, exist_ok=True)
    for source in range(1, 65):
        shard = (source - 1) // 5
        path = state_directory / f"State{source:02d}.lean"
        path.write_text(
            _state_text(source, sectors[source], shard), encoding="utf-8"
        )
        written.append(path)
    for shard, start in enumerate(range(1, 65, 5)):
        sources_in_shard = tuple(range(start, min(start + 5, 65)))
        path = LEAN / f"{SHARD_STEM}{shard:02d}.lean"
        path.write_text(_shard_text(shard, sources_in_shard), encoding="utf-8")
    return tuple(written)


def main() -> None:
    paths = generate()
    print(f"generated_files={len(paths)}")
    for path in paths:
        print(path.relative_to(ROOT))


if __name__ == "__main__":
    main()
