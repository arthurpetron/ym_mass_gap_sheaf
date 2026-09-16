/-
# Bilinearity of the SAME completed intrinsic reflected pairing

The actual intrinsic addition and rational-scaling identities pass through
the previously constructed representative pairing limits. Quotient
elimination then gives both-slot bilinearity for the existing completed
operations on the physical Cauchy carrier. Zero pairing follows from the
proved actual zero-scalar operation. No representative is selected and no
old plaquette-model pairing or linearity theorem is substituted.

Nome, spatial width and retained heat stage remain fixed. These are laws of
the original completed scalar form, not a claim of metric completeness,
a completed Hilbert-space package, one-step positivity or a strict gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
  (pairing_add_left pairing_smul_left)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (seminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (Completion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef (completedZero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

/-- The actual append operation is additive under the constructed pairing
limit, without synchronizing the limits' different approximation indices. -/
theorem representativeInner_add_left (X Y Z : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 width stage
        ((addition hw0 hw1 width stage).mapCauchy X Y) Z)
      (CReal.add (representativeInner hw0 hw1 width stage X Z)
        (representativeInner hw0 hw1 width stage Y Z)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_add_left hw0 hw1 width (X.seq n).val (Y.seq n).val (Z.seq n).val stage)
    (pairSequence_converges hw0 hw1 width stage
      ((addition hw0 hw1 width stage).mapCauchy X Y) Z)
    (TrigAddCReal.convergesTo_add
      (pairSequence_converges hw0 hw1 width stage X Z)
      (pairSequence_converges hw0 hw1 width stage Y Z))

/-- Literal rational scaling passes through the SAME representative limit. -/
theorem representativeInner_smul_left (c : Q') (X Y : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 width stage
        ((scalarContinuous hw0 hw1 width stage c).mapCauchy X) Y)
      (CReal.mul (ofQ' c) (representativeInner hw0 hw1 width stage X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_smul_left hw0 hw1 width c (X.seq n).val (Y.seq n).val stage)
    (pairSequence_converges hw0 hw1 width stage
      ((scalarContinuous hw0 hw1 width stage c).mapCauchy X) Y)
    (convergesTo_const_mul (ofQ' c) (pairSequence_converges hw0 hw1 width stage X Y))

theorem completedInner_add_left (x y z : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage (completedAdd hw0 hw1 width stage x y) z =
      RCadd (completedInner hw0 hw1 width stage x z) (completedInner hw0 hw1 width stage y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact fun X Y Z => Quotient.sound (representativeInner_add_left hw0 hw1 width stage X Y Z)

theorem completedInner_add_right (x y z : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage x (completedAdd hw0 hw1 width stage y z) =
      RCadd (completedInner hw0 hw1 width stage x y) (completedInner hw0 hw1 width stage x z) := by
  rw [completedInner_symm hw0 hw1 width stage x, completedInner_add_left,
    completedInner_symm hw0 hw1 width stage y x, completedInner_symm hw0 hw1 width stage z x]

theorem completedInner_smul_left (c : Q') (x y : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage (completedSmul hw0 hw1 width stage c x) y =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedInner hw0 hw1 width stage x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_smul_left hw0 hw1 width stage c X Y)

theorem completedInner_smul_right (c : Q') (x y : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage x (completedSmul hw0 hw1 width stage c y) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedInner hw0 hw1 width stage x y) := by
  rw [completedInner_symm hw0 hw1 width stage x, completedInner_smul_left,
    completedInner_symm hw0 hw1 width stage y x]

theorem completedInner_zero_left (x : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage (completedZero hw0 hw1 width stage) x = RCzero := by
  rw [← completedSmul_zero hw0 hw1 width stage x, completedInner_smul_left]
  refine Quotient.inductionOn (completedInner hw0 hw1 width stage x x) ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

theorem completedInner_zero_right (x : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage x (completedZero hw0 hw1 width stage) = RCzero := by
  rw [completedInner_symm, completedInner_zero_left]

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.representativeInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.representativeInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.completedInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.completedInner_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.completedInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.completedInner_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.completedInner_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear.completedInner_zero_right
