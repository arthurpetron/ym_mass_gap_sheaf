"""Assemble the 127 shared-DAG representative proofs into the residual record."""

from __future__ import annotations

from pathlib import Path

from computations.bf4_cutoff_two_spatial_s3_nonzero_representatives import (
    representative_pairs,
)


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean" / "YMGap" / "Continuum"
TARGET = LEAN / "BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.lean"


def _tag(row: int, column: int) -> str:
    return f"R{row:02d}C{column:02d}"


def _module(row: int, column: int) -> str:
    tag = _tag(row, column)
    if (row, column) == (1, 1):
        return f"BF4PhysicalBoundaryCutoffTwoSharedDAGPhysical{tag}KernelCertificate"
    return f"BF4PhysicalBoundaryCutoffTwoSharedDAGPhysical{tag}Certificate"


def _namespace(row: int, column: int) -> str:
    return f"YMGap.Continuum.{_module(row, column)}"


def render() -> str:
    pairs = representative_pairs()
    imports = "\n".join(
        f"import YMGap.Continuum.{_module(row, column)}"
        for row, column in pairs
    )
    wrappers = "\n\n".join(
        f'''theorem cutoffTwoSharedDAGRepresentative{_tag(row, column)}_checked :
    cutoffTwoSectorRepresentativePhysicalStatement ⟨{row}, {column}⟩ :=
  {_namespace(row, column)}.centralPhysicalReflectedKernel_cutoffTwo_sector_{_tag(row, column)}_rawStateAt_eqv_raw_sharedDAG'''
        for row, column in pairs
    )
    alternatives = " |\n    ".join("hpair" for _ in pairs)
    branches = "\n".join(
        f'''  · exact cutoffTwoSectorRepresentativePhysicalStatement_of_eq hpair
      cutoffTwoSharedDAGRepresentative{_tag(row, column)}_checked'''
        for row, column in pairs
    )
    return f'''/-
# Complete shared-DAG certificate for the 127 spatial-S3 representatives

Each imported theorem checks one genuine production physical/raw kernel
equality.  Pair membership is dispatched only through the literal,
kernel-checked representative carrier; the abstract statement wrapper avoids
reducing the concrete 65-state list during equality transport.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive
{imports}

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

{wrappers}

theorem cutoffTwoSharedDAGRepresentatives_checked
    (pair : CutoffTwoSectorPair)
    (hpair : pair ∈ cutoffTwoSpatialS3NonzeroRepresentatives) :
    cutoffTwoSectorRepresentativePhysicalStatement pair := by
  simp only [cutoffTwoSpatialS3NonzeroRepresentatives,
    List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with
    {alternatives}
{branches}

def cutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate :
    CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate where
  representativeChecked := by
    intro pair hcheck
    exact cutoffTwoSharedDAGRepresentatives_checked pair
      (cutoffTwoSpatialS3NonzeroRepresentative_mem_of_codeCheck pair hcheck)

def cutoffTwoSectorPhysicalTableCertificate :
    BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge.CutoffTwoSectorPhysicalTableCertificate :=
  cutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate.toPhysicalTableCertificate

/-- Opaque presentation boundary for downstream consumers.  This is the same
checked certificate, sealed so elaboration does not unfold its 127-way
representative dispatch during ordinary theorem application. -/
opaque cutoffTwoSectorPhysicalTableCertificateSealed :
    BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge.CutoffTwoSectorPhysicalTableCertificate :=
  cutoffTwoSectorPhysicalTableCertificate

/-- Specialized opaque row-zero bridge.  Downstream graph proofs consume this
theorem without comparing the full representative-dispatch proof term. -/
opaque cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_eqv_raw
    {{column : Nat}} (hcolumn : column < 65) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt 0) (cutoffTwoSectorStateAt column) ≈
      cutoffTwoSectorRawKernel 0 column :=
  centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw
    cutoffTwoSectorPhysicalTableCertificateSealed
    (row := 0) (column := column) (by decide) hcolumn

/-- Specialized positive row-zero bridge.  This is the compact fact needed by
the vacuum-component graph; it prevents later files from replaying the
table-to-production positivity transport. -/
opaque cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_pos
    {{column : Nat}} (hcolumn : column < 65) :
    (0 : Q') < centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorStateAt 0) (cutoffTwoSectorStateAt column) :=
  Q'.pos_of_lt_of_le
    (cutoffTwoSectorRawKernel_rowZero_pos hcolumn)
    (Q'.ge_of_eqv
      (cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_eqv_raw hcolumn))

/-- Opaque identification of the first table state with the named fundamental
cube.  The equality is definitional, but sealing it prevents later graph files
from normalizing the full literal labelling. -/
opaque cutoffTwoSectorStateAt_zero_eq_cube_sealed :
    cutoffTwoSectorStateAt 0 = centralLowerCubeState :=
  rfl

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSharedDAGRepresentatives_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSectorPhysicalTableCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSectorPhysicalTableCertificateSealed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_eqv_raw
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.cutoffTwoSectorStateAt_zero_eq_cube_sealed
'''


def main() -> None:
    source = render()
    if not TARGET.exists() or TARGET.read_text() != source:
        TARGET.write_text(source)
    print(f"generated {TARGET.relative_to(ROOT)} with 127 representative imports")


if __name__ == "__main__":
    main()
