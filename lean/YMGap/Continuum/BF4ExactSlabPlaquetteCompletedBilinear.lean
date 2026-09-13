/-
# Bilinearity of the ORIGINAL completed plaquette pairing

The pointwise original form laws pass through the constructed mixed-pairing
limits. Their descent proves rational bilinearity for the actual completed
operations and pairing, with exact compatibility at the original null
quotient. No form law is assumed as a field of a new carrier.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

theorem representativeInner_add_left (X Y Z : (D).Cauchy) :
    Equiv (representativeInner w hw0 hw1 ((addition w hw0 hw1).mapCauchy X Y) Z)
      (CReal.add (representativeInner w hw0 hw1 X Z) (representativeInner w hw0 hw1 Y Z)) :=
  Equiv_of_limit_of_equal (fun n => form_add_left w hw0 hw1 (X.seq n) (Y.seq n) (Z.seq n))
    (pairSequence_converges w hw0 hw1 ((addition w hw0 hw1).mapCauchy X Y) Z)
    (TrigAddCReal.convergesTo_add (pairSequence_converges w hw0 hw1 X Z) (pairSequence_converges w hw0 hw1 Y Z))

theorem representativeInner_smul_left (c : Q') (X Y : (D).Cauchy) :
    Equiv (representativeInner w hw0 hw1 ((scalarContinuous w hw0 hw1 c).mapCauchy X) Y)
      (CReal.mul (ofQ' c) (representativeInner w hw0 hw1 X Y)) :=
  Equiv_of_limit_of_equal (fun n => form_smul_left w hw0 hw1 c (X.seq n) (Y.seq n))
    (pairSequence_converges w hw0 hw1 ((scalarContinuous w hw0 hw1 c).mapCauchy X) Y)
    (convergesTo_const_mul (ofQ' c) (pairSequence_converges w hw0 hw1 X Y))

theorem completedInner_add_left (x y z : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 (completedAdd w hw0 hw1 x y) z =
      RCadd (completedInner w hw0 hw1 x z) (completedInner w hw0 hw1 y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact fun X Y Z => Quotient.sound (representativeInner_add_left w hw0 hw1 X Y Z)

theorem completedInner_add_right (x y z : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 x (completedAdd w hw0 hw1 y z) =
      RCadd (completedInner w hw0 hw1 x y) (completedInner w hw0 hw1 x z) := by
  rw [completedInner_symm w hw0 hw1 x, completedInner_add_left,
    completedInner_symm w hw0 hw1 y x, completedInner_symm w hw0 hw1 z x]

theorem completedInner_smul_left (c : Q') (x y : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 (completedSmul w hw0 hw1 c x) y =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedInner w hw0 hw1 x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_smul_left w hw0 hw1 c X Y)

theorem completedInner_smul_right (c : Q') (x y : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 x (completedSmul w hw0 hw1 c y) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedInner w hw0 hw1 x y) := by
  rw [completedInner_symm w hw0 hw1 x, completedInner_smul_left, completedInner_symm w hw0 hw1 y x]

theorem completedInner_zero_left (x : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 (completedZero w hw0 hw1 half) x = RCzero := by
  rw [← completedSmul_zero w hw0 hw1 x, completedInner_smul_left]
  refine Quotient.inductionOn (completedInner w hw0 hw1 x x) ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

theorem completedInner_zero_right (x : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 x (completedZero w hw0 hw1 half) = RCzero := by
  rw [completedInner_symm, completedInner_zero_left]

theorem completedAdd_embedQuotient (x y : Carrier w hw0 hw1 half) :
    completedAdd w hw0 hw1 (embedQuotient w hw0 hw1 x) (embedQuotient w hw0 hw1 y) =
      embedQuotient w hw0 hw1 (BF4ExactSlabPlaquetteNullQuotient.add w hw0 hw1 x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact completedAdd_embedExpression w hw0 hw1

theorem completedSmul_embedQuotient (c : Q') (x : Carrier w hw0 hw1 half) :
    completedSmul w hw0 hw1 c (embedQuotient w hw0 hw1 x) =
      embedQuotient w hw0 hw1 (smul w hw0 hw1 c x) := by
  refine Quotient.inductionOn x ?_
  exact completedSmul_embedExpression w hw0 hw1 c

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.representativeInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.representativeInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedInner_add_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedInner_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedInner_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedInner_zero_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedAdd_embedQuotient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear.completedSmul_embedQuotient
