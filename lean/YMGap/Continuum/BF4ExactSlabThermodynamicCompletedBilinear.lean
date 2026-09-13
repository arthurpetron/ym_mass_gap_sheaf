/-
# Bilinearity of the ORIGINAL thermodynamic completed pairing

The actual semantic form laws pass through the constructed pairing limits.
They prove rational bilinearity for the completed operations on the SAME
carrier; no bilinear law is assumed in a newly packaged state space.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear

local notation "D" => seminorm

theorem representativeInner_add_left (X Y Z : (D).Cauchy) :
    Equiv (representativeInner ((addition).mapCauchy X Y) Z)
      (CReal.add (representativeInner X Z) (representativeInner Y Z)) :=
  Equiv_of_limit_of_equal (fun n => presentedForm_add_left (X.seq n) (Y.seq n) (Z.seq n))
    (pairSequence_converges ((addition).mapCauchy X Y) Z)
    (TrigAddCReal.convergesTo_add (pairSequence_converges X Z) (pairSequence_converges Y Z))

theorem representativeInner_smul_left (c : Q') (X Y : (D).Cauchy) :
    Equiv (representativeInner ((scalarContinuous c).mapCauchy X) Y)
      (CReal.mul (ofQ' c) (representativeInner X Y)) :=
  Equiv_of_limit_of_equal (fun n => presentedForm_smul_left c (X.seq n) (Y.seq n))
    (pairSequence_converges ((scalarContinuous c).mapCauchy X) Y)
    (convergesTo_const_mul (ofQ' c) (pairSequence_converges X Y))

theorem completedInner_add_left (x y z : Completion) :
    completedInner (completedAdd x y) z =
      RCadd (completedInner x z) (completedInner y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact fun X Y Z => Quotient.sound (representativeInner_add_left X Y Z)

theorem completedInner_add_right (x y z : Completion) :
    completedInner x (completedAdd y z) =
      RCadd (completedInner x y) (completedInner x z) := by
  rw [completedInner_symm x, completedInner_add_left,
    completedInner_symm y x, completedInner_symm z x]

theorem completedInner_smul_left (c : Q') (x y : Completion) :
    completedInner (completedSmul c x) y =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedInner x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_smul_left c X Y)

theorem completedInner_smul_right (c : Q') (x y : Completion) :
    completedInner x (completedSmul c y) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedInner x y) := by
  rw [completedInner_symm x, completedInner_smul_left, completedInner_symm y x]

theorem completedInner_zero_left (x : Completion) :
    completedInner (completedZero) x = RCzero := by
  rw [← completedSmul_zero x, completedInner_smul_left]
  refine Quotient.inductionOn (completedInner x x) ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

theorem completedInner_zero_right (x : Completion) :
    completedInner x (completedZero) = RCzero := by
  rw [completedInner_symm, completedInner_zero_left]


end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.representativeInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.representativeInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.completedInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.completedInner_add_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.completedInner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.completedInner_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.completedInner_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear.completedInner_zero_right
