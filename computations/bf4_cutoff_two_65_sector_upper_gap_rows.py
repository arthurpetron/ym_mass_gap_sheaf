"""Emit process-isolated Lean checks for the cutoff-two upper-gap bridge.

The script performs no trusted arithmetic.  It only writes the 64 identical
row wrappers; Lean's kernel evaluates every historical-to-canonical rational
comparison in the generated theorem bodies.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def row_source(row: int) -> str:
    return f'''/- Kernel comparison of historical row {row} with all canonical sparse entries. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGapData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorCanonicalUpperBridgeRow{row:02d}_checked :
    cutoffTwoSectorCanonicalUpperBridgeRowCheck {row} = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorCanonicalUpperBridgeRow{row:02d}_checked
'''


def root_source() -> str:
    imports = "\n".join(
        "import YMGap.Continuum."
        "BF4PhysicalBoundaryCutoffTwoSectorUpperGapRows."
        f"Row{row:02d}"
        for row in range(64)
    )
    rows = ", ".join(str(row) for row in range(64))
    checks = ",\n    ".join(
        f"cutoffTwoSectorCanonicalUpperBridgeRow{row:02d}_checked"
        for row in range(64)
    )
    return f'''/- Compose the 64 process-isolated cutoff-two upper-gap row checks. -/
{imports}

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

theorem cutoffTwoSectorCanonicalUpperBridgeRows_checked :
    (List.range 64).all cutoffTwoSectorCanonicalUpperBridgeRowCheck = true := by
  rw [show List.range 64 = [{rows}] by decide]
  simp only [List.all_cons, List.all_nil,
    {checks}]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorCanonicalUpperBridgeRows_checked
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(
            "lean/YMGap/Continuum/"
            "BF4PhysicalBoundaryCutoffTwoSectorUpperGapRows"
        ),
    )
    arguments = parser.parse_args()
    arguments.output_dir.mkdir(parents=True, exist_ok=True)
    changed = 0
    for row in range(64):
        path = arguments.output_dir / f"Row{row:02d}.lean"
        source = row_source(row)
        if not path.exists() or path.read_text() != source:
            path.write_text(source)
            changed += 1
    root_path = arguments.output_dir.parent / (
        "BF4PhysicalBoundaryCutoffTwoSectorUpperGapRows.lean"
    )
    source = root_source()
    if not root_path.exists() or root_path.read_text() != source:
        root_path.write_text(source)
        changed += 1
    print(
        f"wrote {changed} changed row sources in {arguments.output_dir} "
        f"and {root_path}"
    )


if __name__ == "__main__":
    main()
