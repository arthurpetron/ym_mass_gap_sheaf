"""Generate the cutoff-two spatial-S3 nonzero representative certificate.

The producer parses the stored raw table and independently mirrors the six
unsigned spatial actions to propose a 127-pair list.  Lean then checks the
literal list's size, uniqueness, upper-triangularity, nonzeroness, and complete
coverage of every nonzero upper source pair.  This script is not trusted by
any theorem.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from computations.bf4_cutoff_two_cube_automorphism_certificate import (
    _cube_position_action,
    _sector_state_action,
)


ROOT = Path(__file__).resolve().parents[1]
RAW_DATA = (
    ROOT
    / "lean"
    / "YMGap"
    / "Continuum"
    / "BF4PhysicalBoundaryCutoffTwoSectorRawKernelData.lean"
)
DATA_STEM = (
    "BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData"
)
CHECK_STEM = (
    "BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageCheck"
)
ROW_STEM = (
    "BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageRows"
)
DATA_NAMESPACE = "YMGap.Continuum." + DATA_STEM
CHECK_NAMESPACE = "YMGap.Continuum." + CHECK_STEM
ROW_NAMESPACE = "YMGap.Continuum." + ROW_STEM


def _raw_numerators() -> tuple[int, ...]:
    text = RAW_DATA.read_text(encoding="utf-8")
    marker = "def cutoffTwoSectorRawKernelData : Array Q' := #["
    body = text.split(marker, 1)[1].split(
        "\n]\n\ndef cutoffTwoSectorRawRowSumData", 1
    )[0]
    values: list[int] = []
    pattern = re.compile(
        r"\((?:0|1) : Q'\)|\(⟨(-?\d+),\s*(\d+)⟩ : Q'\)"
    )
    for match in pattern.finditer(body):
        literal = match.group(0)
        if literal.startswith("(0 "):
            values.append(0)
        elif literal.startswith("(1 "):
            values.append(1)
        else:
            values.append(int(match.group(1)))
    if len(values) != 65 * 65:
        raise AssertionError(f"raw table size drifted: {len(values)}")
    return tuple(values)


def _actions() -> tuple[tuple[int, ...], ...]:
    identity = tuple(range(65))
    swap01 = _sector_state_action(
        _cube_position_action((1, 0, 2), (0, 0, 0))
    )
    swap12 = _sector_state_action(
        _cube_position_action((0, 2, 1), (0, 0, 0))
    )
    swap12_swap01 = tuple(swap12[swap01[index]] for index in range(65))
    swap01_swap12 = tuple(swap01[swap12[index]] for index in range(65))
    swap01_swap12_swap01 = tuple(
        swap01[swap12[swap01[index]]] for index in range(65)
    )
    return (
        identity,
        swap01,
        swap12,
        swap12_swap01,
        swap01_swap12,
        swap01_swap12_swap01,
    )


def _canonical(
    pair: tuple[int, int], actions: tuple[tuple[int, ...], ...]
) -> tuple[int, int]:
    candidates = (
        tuple(sorted((action[pair[0]], action[pair[1]])))
        for action in actions
    )
    return min(candidates, key=lambda item: item[0] * 65 + item[1])


def representative_pairs() -> tuple[tuple[int, int], ...]:
    raw = _raw_numerators()
    actions = _actions()
    upper = tuple((row, column) for row in range(65) for column in range(row, 65))
    nonzero = tuple(
        pair for pair in upper if raw[pair[0] * 65 + pair[1]] != 0
    )
    representatives = tuple(sorted({_canonical(pair, actions) for pair in nonzero}))
    if len(nonzero) != 499:
        raise AssertionError(f"nonzero upper count drifted: {len(nonzero)}")
    if len(representatives) != 127:
        raise AssertionError(
            f"nonzero representative count drifted: {len(representatives)}"
        )
    for pair in upper:
        canonical = _canonical(pair, actions)
        if raw[pair[0] * 65 + pair[1]] != raw[canonical[0] * 65 + canonical[1]]:
            raise AssertionError(f"raw canonical transport failed: {pair}")
    return representatives


def _lean_pairs(pairs: tuple[tuple[int, int], ...]) -> str:
    lines = []
    for start in range(0, len(pairs), 6):
        chunk = pairs[start : start + 6]
        lines.append("  " + ", ".join(f"⟨{row}, {column}⟩" for row, column in chunk))
    return "[\n" + ",\n".join(lines) + "\n]"


def _lean_codes(pairs: tuple[tuple[int, int], ...]) -> str:
    codes = tuple(row * 65 + column for row, column in pairs)
    lines = []
    for start in range(0, len(codes), 12):
        lines.append("  " + ", ".join(map(str, codes[start : start + 12])))
    return "[\n" + ",\n".join(lines) + "\n]"


def _lean_code_check(pairs: tuple[tuple[int, int], ...]) -> str:
    codes = tuple(row * 65 + column for row, column in pairs)
    cases = "\n".join(f"  | {code} => true" for code in codes)
    return cases + "\n  | _ => false"


def data_text(pairs: tuple[tuple[int, int], ...]) -> str:
    return f"""/-
# The 127 nonzero cutoff-two unordered spatial-S3 representatives

This literal carrier is generated from the stored raw table, but its length,
uniqueness, upper-triangularity, and nonzeroness are checked below by Lean.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

namespace {DATA_NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSpatialS3NonzeroRepresentatives : List CutoffTwoSectorPair :=
{_lean_pairs(pairs)}

def cutoffTwoSpatialS3NonzeroRepresentativeCodes : List Nat :=
{_lean_codes(pairs)}

/-- A compact recognizer for the same 127 literal representative codes.
Unlike list membership, this stays compact in proofs with a variable code. -/
def cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck : Nat → Bool
{_lean_code_check(pairs)}

def cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes : List Nat :=
  (List.range 4225).filter
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck

theorem cutoffTwoSpatialS3NonzeroRepresentatives_length :
    cutoffTwoSpatialS3NonzeroRepresentatives.length = 127 := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentatives_nodup :
    cutoffTwoSpatialS3NonzeroRepresentatives.Nodup := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeCodes_length :
    cutoffTwoSpatialS3NonzeroRepresentativeCodes.length = 127 := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeCodes_nodup :
    cutoffTwoSpatialS3NonzeroRepresentativeCodes.Nodup := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq :
    cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes =
      cutoffTwoSpatialS3NonzeroRepresentativeCodes := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck_iff_mem_of_lt
    {{code : Nat}} (hcode : code < 4225) :
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck code = true ↔
      code ∈ cutoffTwoSpatialS3NonzeroRepresentativeCodes := by
  rw [← cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq]
  constructor
  · intro hcheck
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hcode, hcheck⟩
  · intro hmem
    exact (List.mem_filter.mp hmem).2

theorem cutoffTwoSectorPairCode_lt (pair : CutoffTwoSectorPair) :
    cutoffTwoSectorPairCode pair < 4225 := by
  unfold cutoffTwoSectorPairCode
  omega

theorem cutoffTwoSectorPairCode_injective :
    Function.Injective cutoffTwoSectorPairCode := by
  intro left right hcode
  rcases left with ⟨leftRow, leftColumn⟩
  rcases right with ⟨rightRow, rightColumn⟩
  change leftRow.val * 65 + leftColumn.val =
    rightRow.val * 65 + rightColumn.val at hcode
  have hrowVal : leftRow.val = rightRow.val := by
    omega
  have hcolumnVal : leftColumn.val = rightColumn.val := by
    omega
  have hrow : leftRow = rightRow := Fin.ext hrowVal
  have hcolumn : leftColumn = rightColumn := Fin.ext hcolumnVal
  cases hrow
  cases hcolumn
  rfl

theorem cutoffTwoSpatialS3NonzeroRepresentatives_map_code :
    cutoffTwoSpatialS3NonzeroRepresentatives.map cutoffTwoSectorPairCode =
      cutoffTwoSpatialS3NonzeroRepresentativeCodes := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentative_mem_of_codeCheck
    (pair : CutoffTwoSectorPair)
    (hcheck : cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck
      (cutoffTwoSectorPairCode pair) = true) :
    pair ∈ cutoffTwoSpatialS3NonzeroRepresentatives := by
  have hcode : cutoffTwoSectorPairCode pair ∈
      cutoffTwoSpatialS3NonzeroRepresentativeCodes :=
    (cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck_iff_mem_of_lt
      (cutoffTwoSectorPairCode_lt pair)).mp hcheck
  have hmapped : cutoffTwoSectorPairCode pair ∈
      cutoffTwoSpatialS3NonzeroRepresentatives.map cutoffTwoSectorPairCode := by
    rw [cutoffTwoSpatialS3NonzeroRepresentatives_map_code]
    exact hcode
  rcases List.mem_map.mp hmapped with
    ⟨representative, hrepresentative, hrepresentativeCode⟩
  have hpairs : representative = pair :=
    cutoffTwoSectorPairCode_injective hrepresentativeCode
  cases hpairs
  exact hrepresentative

def cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck : Bool :=
  cutoffTwoSpatialS3NonzeroRepresentatives.all fun pair =>
    decide (pair.row.val ≤ pair.column.val)

def cutoffTwoSpatialS3NonzeroRepresentativesRawCheck : Bool :=
  cutoffTwoSpatialS3NonzeroRepresentatives.all fun pair =>
    decide (¬ cutoffTwoSectorRawKernel pair.row.val pair.column.val ≈ 0)

theorem cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck_true :
    cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck = true := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentativesRawCheck_true :
    cutoffTwoSpatialS3NonzeroRepresentativesRawCheck = true := by
  decide

theorem cutoffTwoSpatialS3NonzeroRepresentative_upper
    {{pair : CutoffTwoSectorPair}}
    (hpair : pair ∈ cutoffTwoSpatialS3NonzeroRepresentatives) :
    pair.row.val ≤ pair.column.val := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      cutoffTwoSpatialS3NonzeroRepresentativesUpperCheck_true pair hpair)

theorem cutoffTwoSpatialS3NonzeroRepresentative_raw
    {{pair : CutoffTwoSectorPair}}
    (hpair : pair ∈ cutoffTwoSpatialS3NonzeroRepresentatives) :
    ¬ cutoffTwoSectorRawKernel pair.row.val pair.column.val ≈ 0 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      cutoffTwoSpatialS3NonzeroRepresentativesRawCheck_true pair hpair)

end {DATA_NAMESPACE}

#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentatives_length
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentatives_nodup
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentativeCodes_length
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentativeCodes_nodup
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck_iff_mem_of_lt
#print axioms {DATA_NAMESPACE}.cutoffTwoSectorPairCode_lt
#print axioms {DATA_NAMESPACE}.cutoffTwoSectorPairCode_injective
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentatives_map_code
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentative_mem_of_codeCheck
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentative_upper
#print axioms {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentative_raw
"""


def check_text() -> str:
    return f"""/- Row-wise completeness checker for the 127 representatives. -/
import YMGap.Continuum.{DATA_STEM}

namespace {CHECK_NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open {DATA_NAMESPACE}

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck
    (row : Fin 65) : Bool :=
  (List.finRange 65).all fun column =>
    if decide (row.val ≤ column.val) then
      if decide (cutoffTwoSectorRawKernel row.val column.val ≈ 0) then
        true
      else
        cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck
          (cutoffTwoSectorPairCode
            (cutoffTwoSectorPairCanonical ⟨row, column⟩))
    else true

theorem cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck_sound
    {{row column : Fin 65}}
    (hcheck :
      cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck row = true)
    (hupper : row.val ≤ column.val)
    (hnonzero : ¬ cutoffTwoSectorRawKernel row.val column.val ≈ 0) :
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck
        (cutoffTwoSectorPairCode
          (cutoffTwoSectorPairCanonical ⟨row, column⟩)) = true := by
  unfold cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck at hcheck
  have hcolumn := List.all_eq_true.mp hcheck column
    (List.mem_finRange column)
  rw [decide_eq_true hupper, decide_eq_false hnonzero] at hcolumn
  exact hcolumn

end {CHECK_NAMESPACE}
"""


def row_text(row: int) -> str:
    return f"""/- Process-isolated nonzero-representative coverage row {row:02d}. -/
import YMGap.Continuum.{CHECK_STEM}

namespace {ROW_NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open {CHECK_NAMESPACE}

theorem cutoffTwoSpatialS3NonzeroRepresentativeCoverageRow{row:02d}_checked :
    cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck
      ({row} : Fin 65) = true := by
  decide

end {ROW_NAMESPACE}

#print axioms
  {ROW_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentativeCoverageRow{row:02d}_checked
"""


def aggregate_text() -> str:
    imports = "\n".join(
        f"import YMGap.Continuum.{ROW_STEM}.Row{row:02d}"
        for row in range(65)
    )
    values = ", ".join(f"({row} : Fin 65)" for row in range(65))
    checks = ",\n    ".join(
        f"cutoffTwoSpatialS3NonzeroRepresentativeCoverageRow{row:02d}_checked"
        for row in range(65)
    )
    return f"""/- Compact aggregate of the 65 representative-coverage rows. -/
{imports}

namespace {ROW_NAMESPACE}

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open {DATA_NAMESPACE}
open {CHECK_NAMESPACE}

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSpatialS3NonzeroRepresentativeCoverageRows_checked :
    (List.finRange 65).all
      cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck = true := by
  rw [show List.finRange 65 = [{values}] by decide]
  simp only [List.all_cons, List.all_nil,
    {checks},
    Bool.true_and]

theorem cutoffTwoSectorPairCanonicalCodeCheck_nonzeroRepresentative
    {{row column : Fin 65}} (hupper : row.val ≤ column.val)
    (hnonzero : ¬ cutoffTwoSectorRawKernel row.val column.val ≈ 0) :
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck
        (cutoffTwoSectorPairCode
          (cutoffTwoSectorPairCanonical ⟨row, column⟩)) = true := by
  apply cutoffTwoSpatialS3NonzeroRepresentativeCoverageRowCheck_sound
  · exact List.all_eq_true.mp
      cutoffTwoSpatialS3NonzeroRepresentativeCoverageRows_checked row
      (List.mem_finRange row)
  · exact hupper
  · exact hnonzero

end {ROW_NAMESPACE}

#print axioms
  {ROW_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentativeCoverageRows_checked
#print axioms
  {ROW_NAMESPACE}.cutoffTwoSectorPairCanonicalCodeCheck_nonzeroRepresentative
"""


def audit_text() -> str:
    return f"""import YMGap.Continuum.{ROW_STEM}

#print axioms
  {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentatives_length
#print axioms
  {DATA_NAMESPACE}.cutoffTwoSpatialS3NonzeroRepresentative_raw
#print axioms
  {ROW_NAMESPACE}.cutoffTwoSectorPairCanonicalCodeCheck_nonzeroRepresentative
"""


def generate(output_directory: Path) -> tuple[Path, ...]:
    pairs = representative_pairs()
    written: list[Path] = []

    data = output_directory / f"{DATA_STEM}.lean"
    data.write_text(data_text(pairs), encoding="utf-8")
    written.append(data)

    check = output_directory / f"{CHECK_STEM}.lean"
    check.write_text(check_text(), encoding="utf-8")
    written.append(check)

    row_directory = output_directory / ROW_STEM
    row_directory.mkdir(parents=True, exist_ok=True)
    for row in range(65):
        path = row_directory / f"Row{row:02d}.lean"
        path.write_text(row_text(row), encoding="utf-8")
        written.append(path)

    aggregate = output_directory / f"{ROW_STEM}.lean"
    aggregate.write_text(aggregate_text(), encoding="utf-8")
    written.append(aggregate)

    audit = output_directory / (
        "BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativesAxiomAudit.lean"
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
