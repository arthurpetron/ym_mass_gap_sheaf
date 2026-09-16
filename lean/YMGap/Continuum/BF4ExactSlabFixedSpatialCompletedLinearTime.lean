/-
# Rational linearity of the actual completed physical-time map

Literal distance advance preserves append and rational scaling of the
original physical probe spans. These subtype equalities supply pointwise
pairing equality, hence zero-modulus closeness on the existing Cauchy
carrier. The actual completed time map therefore preserves the SAME
completed addition, rational scaling, zero and negation.
Subtraction compatibility then gives constant-one contraction of the actual
completed squared distance, using the SAME completed diagonal form bound.

This concerns physical time on the already constructed reflected carrier,
not a new operator or a changed normalization. Nome, spatial width and
retained heat stage remain fixed. No one-step positivity, strict gap,
metric-completeness theorem or continuum assertion is supplied here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
  (advanceSpan_append advanceSpan_scale)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef (completedZero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry (completedSub completedDist)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm (completedInner_time_contraction)

private theorem physicalTime_addSpan {width : Nat} (n : Nat) (x y : PhysicalSpan width) :
    physicalTime n (addSpan x y) = addSpan (physicalTime n x) (physicalTime n y) :=
  Subtype.ext (advanceSpan_append n x.val y.val)

private theorem physicalTime_smulSpan {width : Nat} (n : Nat) (c : Q') (x : PhysicalSpan width) :
    physicalTime n (smulSpan c x) = smulSpan c (physicalTime n x) :=
  Subtype.ext (advanceSpan_scale n c x.val)

private theorem physicalTime_zeroSpan (width n : Nat) :
    physicalTime n (zero width) = zero width :=
  Subtype.ext rfl

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

/-- Physical time preserves the actual completed addition. This is distinct
from the existing addition-of-times semigroup law completedTime_add. -/
theorem completedTime_additive (n : Nat) (x y : Completion hw0 hw1 width stage) :
    completedTime hw0 hw1 width stage n (completedAdd hw0 hw1 width stage x y) =
      completedAdd hw0 hw1 width stage
        (completedTime hw0 hw1 width stage n x) (completedTime hw0 hw1 width stage n y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply completion_eq_of_pointwise hw0 hw1 width stage
  intro k
  change PairingEq hw0 hw1 width stage (physicalTime n (addSpan (X.seq k) (Y.seq k)))
    (addSpan (physicalTime n (X.seq k)) (physicalTime n (Y.seq k)))
  rw [physicalTime_addSpan]
  intro z
  exact Equiv.refl _

/-- Rational scaling commutes with the SAME physical time on the completion. -/
theorem completedTime_smul (n : Nat) (c : Q') (x : Completion hw0 hw1 width stage) :
    completedTime hw0 hw1 width stage n (completedSmul hw0 hw1 width stage c x) =
      completedSmul hw0 hw1 width stage c (completedTime hw0 hw1 width stage n x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1 width stage
  intro k
  change PairingEq hw0 hw1 width stage (physicalTime n (smulSpan c (X.seq k)))
    (smulSpan c (physicalTime n (X.seq k)))
  rw [physicalTime_smulSpan]
  intro z
  exact Equiv.refl _

theorem completedTime_zero_element (n : Nat) :
    completedTime hw0 hw1 width stage n (completedZero hw0 hw1 width stage) =
      completedZero hw0 hw1 width stage := by
  unfold completedZero
  rw [completedTime_embedSpan, physicalTime_zeroSpan]

theorem completedTime_neg (n : Nat) (x : Completion hw0 hw1 width stage) :
    completedTime hw0 hw1 width stage n (completedNeg hw0 hw1 width stage x) =
      completedNeg hw0 hw1 width stage (completedTime hw0 hw1 width stage n x) :=
  completedTime_smul hw0 hw1 width stage n (-1) x

/-- The literal completed difference is preserved by the actual time map. -/
theorem completedTime_sub (n : Nat) (x y : Completion hw0 hw1 width stage) :
    completedTime hw0 hw1 width stage n (completedSub hw0 hw1 width stage x y) =
      completedSub hw0 hw1 width stage
        (completedTime hw0 hw1 width stage n x) (completedTime hw0 hw1 width stage n y) := by
  unfold completedSub
  rw [completedTime_additive, completedTime_neg]

/-- Non-strict contraction of the SAME completed squared distance. The
constant is one; this gives no strict rate or vacuum-complement gap. -/
theorem completedDist_time_contraction (n : Nat) (x y : Completion hw0 hw1 width stage) :
    RCle (completedDist hw0 hw1 width stage
        (completedTime hw0 hw1 width stage n x) (completedTime hw0 hw1 width stage n y))
      (completedDist hw0 hw1 width stage x y) := by
  simpa only [completedDist, completedTime_sub] using
    (completedInner_time_contraction hw0 hw1 width stage n
      (completedSub hw0 hw1 width stage x y))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime.completedTime_additive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime.completedTime_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime.completedTime_zero_element
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime.completedTime_neg
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime.completedTime_sub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedLinearTime.completedDist_time_contraction
