/-
# Row checker for raw transport to cutoff-two spatial S3 representatives

The existing physical-table residual is upper triangular.  This module checks
only the raw-table equality from such an entry to its deterministic spatial-S3
canonical pair.  Expensive closed rows are isolated in generated modules.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSectorRawCanonicalUpperRowCheck (row : Fin 65) : Bool :=
  (List.finRange 65).all fun column =>
    if decide (row.val ≤ column.val) then
      let canonical := cutoffTwoSectorPairCanonical ⟨row, column⟩
      decide
        (cutoffTwoSectorRawKernel row.val column.val ≈
          cutoffTwoSectorRawKernel canonical.row.val canonical.column.val)
    else true

theorem cutoffTwoSectorRawCanonicalUpperRowCheck_sound
    {row column : Fin 65}
    (hcheck : cutoffTwoSectorRawCanonicalUpperRowCheck row = true)
    (hupper : row.val ≤ column.val) :
    cutoffTwoSectorRawKernel row.val column.val ≈
      cutoffTwoSectorRawKernel
        (cutoffTwoSectorPairCanonical ⟨row, column⟩).row.val
        (cutoffTwoSectorPairCanonical ⟨row, column⟩).column.val := by
  unfold cutoffTwoSectorRawCanonicalUpperRowCheck at hcheck
  have hcolumn := List.all_eq_true.mp hcheck column
    (List.mem_finRange column)
  rw [if_pos (decide_eq_true hupper)] at hcolumn
  exact of_decide_eq_true hcolumn

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck

