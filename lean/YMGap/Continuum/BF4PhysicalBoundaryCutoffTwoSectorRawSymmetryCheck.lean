/- Row-wise symmetry checker for the stored cutoff-two sector table. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSectorRawSymmetryRowCheck (row : Nat) : Bool :=
  (List.range 65).all fun column =>
    decide (cutoffTwoSectorRawKernel row column ≈
      cutoffTwoSectorRawKernel column row)

theorem cutoffTwoSectorRawSymmetryRowCheck_sound
    {row column : Nat}
    (hcheck : cutoffTwoSectorRawSymmetryRowCheck row = true)
    (hcolumn : column < 65) :
    cutoffTwoSectorRawKernel row column ≈
      cutoffTwoSectorRawKernel column row := by
  unfold cutoffTwoSectorRawSymmetryRowCheck at hcheck
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck column (List.mem_range.mpr hcolumn))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck

