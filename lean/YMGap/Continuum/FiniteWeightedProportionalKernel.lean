/-
# Normalized proportional kernel for a positive finite weight family

The normalized target weights form a nonnegative rational probability row.
Applying the same row to every source gives exact weighted column load equal
to the source/target total ratio times the target weight.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.FiniteWeightedFractionalKernelCapacity

namespace YMGap.Continuum.FiniteWeightedProportionalKernel

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- One normalized target weight. -/
def normalizedTargetWeight
    {Target : Type} (targetWeight : Target → Q') (targets : List Target)
    (htotal : (0 : Q') < listQSum targetWeight targets)
    (target : Target) : Q' :=
  Q'.recipPos (listQSum targetWeight targets) htotal *
    targetWeight target

theorem normalizedTargetWeight_nonnegative
    {Target : Type} (targetWeight : Target → Q') (targets : List Target)
    (htotal : (0 : Q') < listQSum targetWeight targets)
    (hweight : ∀ target, (0 : Q') ≤ targetWeight target)
    (target : Target) :
    (0 : Q') ≤
      normalizedTargetWeight targetWeight targets htotal target := by
  unfold normalizedTargetWeight
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
    (hweight target)

/-- The normalized target weights sum exactly to one. -/
theorem normalizedTargetWeight_total_one
    {Target : Type} (targetWeight : Target → Q') (targets : List Target)
    (htotal : (0 : Q') < listQSum targetWeight targets) :
    listQSum
        (normalizedTargetWeight targetWeight targets htotal)
        targets ≈
      1 := by
  unfold normalizedTargetWeight
  let targetTotal := listQSum targetWeight targets
  let reciprocal := Q'.recipPos targetTotal htotal
  exact Q'.eqv_trans _ _ _
    (listQSum_mul_left reciprocal targetWeight targets)
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv reciprocal targetTotal)
      (Q'.mul_recipPos_eqv targetTotal htotal))

/-- Reusing the normalized target row at every source gives exact column
load `(source total / target total) * targetWeight target`. -/
theorem proportionalWeightedColumn_eqv
    {Source Target : Type}
    (sources : List Source) (sourceWeight : Source → Q')
    (targets : List Target) (targetWeight : Target → Q')
    (htotal : (0 : Q') < listQSum targetWeight targets)
    (target : Target) :
    listQSum
        (fun source => sourceWeight source *
          normalizedTargetWeight targetWeight targets htotal target)
        sources ≈
      Q'.divPos (listQSum sourceWeight sources)
          (listQSum targetWeight targets) htotal *
        targetWeight target := by
  let sourceTotal := listQSum sourceWeight sources
  let targetTotal := listQSum targetWeight targets
  let reciprocal := Q'.recipPos targetTotal htotal
  change
    listQSum
        (fun source => sourceWeight source *
          (reciprocal * targetWeight target))
        sources ≈
      (sourceTotal * reciprocal) * targetWeight target
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun source =>
        Q'.mul_comm_eqv (sourceWeight source)
          (reciprocal * targetWeight target))
      sources)
    (Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (reciprocal * targetWeight target) sourceWeight sources)
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (reciprocal * targetWeight target) sourceTotal)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv sourceTotal reciprocal
            (targetWeight target)))))

end YMGap.Continuum.FiniteWeightedProportionalKernel

#print axioms
  YMGap.Continuum.FiniteWeightedProportionalKernel.normalizedTargetWeight_nonnegative
#print axioms
  YMGap.Continuum.FiniteWeightedProportionalKernel.normalizedTargetWeight_total_one
#print axioms
  YMGap.Continuum.FiniteWeightedProportionalKernel.proportionalWeightedColumn_eqv
