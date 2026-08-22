/- Row-wise completeness checker for the 127 representatives. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData

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
    {row column : Fin 65}
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

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageCheck
