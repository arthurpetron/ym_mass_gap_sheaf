/-
# Positive row zero in the cutoff-two raw sector table

This process-isolated finite certificate checks that every one of the 65
stored entries in raw row zero is strictly positive.  Keeping the Boolean
normalization in its own module prevents the downstream canonical-component
proof from retaining the full decision term during elaboration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate

def cutoffTwoSectorRawRowZeroPositiveCheck : Bool :=
  (List.range 65).all fun column =>
    decide ((0 : Q') < cutoffTwoSectorRawKernel 0 column)

theorem cutoffTwoSectorRawRowZeroPositive_checked :
    cutoffTwoSectorRawRowZeroPositiveCheck = true := by
  decide

theorem cutoffTwoSectorRawKernel_rowZero_pos
    {column : Nat} (hcolumn : column < 65) :
    (0 : Q') < cutoffTwoSectorRawKernel 0 column := by
  have hchecked := cutoffTwoSectorRawRowZeroPositive_checked
  unfold cutoffTwoSectorRawRowZeroPositiveCheck at hchecked
  exact of_decide_eq_true
    (List.all_eq_true.mp hchecked
      column (List.mem_range.mpr hcolumn))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive.cutoffTwoSectorRawKernel_rowZero_pos
