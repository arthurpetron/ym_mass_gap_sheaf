"""Generate process-isolated Lean checks for raw S3 canonical transport.

Only upper-triangle source pairs are checked, matching the already factored
physical-table residual.  The generator writes proof plumbing; Lean evaluates
and kernel-checks every closed raw equality.
"""

from __future__ import annotations

import argparse
from pathlib import Path


ROW_DIRECTORY_STEM = (
    "BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows"
)
CHECK_MODULE = (
    "YMGap.Continuum."
    "BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck"
)
ROW_NAMESPACE = (
    "YMGap.Continuum."
    "BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows"
)


def row_text(row: int) -> str:
    return f"""/- Process-isolated raw canonical upper row {row:02d}. -/
import {CHECK_MODULE}

namespace {ROW_NAMESPACE}

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

theorem cutoffTwoSectorRawCanonicalUpperRow{row:02d}_checked :
    cutoffTwoSectorRawCanonicalUpperRowCheck ({row} : Fin 65) = true := by
  decide

end {ROW_NAMESPACE}

#print axioms
  {ROW_NAMESPACE}.cutoffTwoSectorRawCanonicalUpperRow{row:02d}_checked
"""


def aggregate_text() -> str:
    imports = "\n".join(
        "import YMGap.Continuum."
        f"{ROW_DIRECTORY_STEM}.Row{row:02d}"
        for row in range(65)
    )
    values = ", ".join(f"({row} : Fin 65)" for row in range(65))
    checks = ",\n    ".join(
        f"cutoffTwoSectorRawCanonicalUpperRow{row:02d}_checked"
        for row in range(65)
    )
    return f"""/- Compact aggregate of the 65 raw canonical upper rows. -/
{imports}

namespace {ROW_NAMESPACE}

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSectorRawCanonicalUpperRows_checked :
    (List.finRange 65).all cutoffTwoSectorRawCanonicalUpperRowCheck = true := by
  rw [show List.finRange 65 = [{values}] by decide]
  simp only [List.all_cons, List.all_nil,
    {checks},
    Bool.true_and]

theorem cutoffTwoSectorRawKernel_pairCanonical_eqv_of_upper
    {{row column : Fin 65}} (hupper : row.val ≤ column.val) :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorRawKernel
        row.val column.val ≈
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorRawKernel
        (YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData.cutoffTwoSectorPairCanonical
          ⟨row, column⟩).row.val
        (YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData.cutoffTwoSectorPairCanonical
          ⟨row, column⟩).column.val := by
  apply cutoffTwoSectorRawCanonicalUpperRowCheck_sound
  · exact List.all_eq_true.mp cutoffTwoSectorRawCanonicalUpperRows_checked
      row (List.mem_finRange row)
  · exact hupper

end {ROW_NAMESPACE}

#print axioms
  {ROW_NAMESPACE}.cutoffTwoSectorRawCanonicalUpperRows_checked
#print axioms
  {ROW_NAMESPACE}.cutoffTwoSectorRawKernel_pairCanonical_eqv_of_upper
"""


def audit_text() -> str:
    return f"""import YMGap.Continuum.{ROW_DIRECTORY_STEM}

#print axioms
  {ROW_NAMESPACE}.cutoffTwoSectorRawKernel_pairCanonical_eqv_of_upper
"""


def generate(output_directory: Path) -> tuple[Path, ...]:
    written: list[Path] = []
    row_directory = output_directory / ROW_DIRECTORY_STEM
    row_directory.mkdir(parents=True, exist_ok=True)
    for row in range(65):
        path = row_directory / f"Row{row:02d}.lean"
        path.write_text(row_text(row), encoding="utf-8")
        written.append(path)

    aggregate = output_directory / f"{ROW_DIRECTORY_STEM}.lean"
    aggregate.write_text(aggregate_text(), encoding="utf-8")
    written.append(aggregate)

    audit = output_directory / (
        "BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRowsAxiomAudit.lean"
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
