/-
# Form laws for the actual cutoff-removed reflected pairing

The same fixed-stage intrinsic pairings converge to jointPairing with the
explicit jointPairingCauchy data already retained. Their unconditional
symmetry, normalization, linearity, positivity and sharp Cauchy--Schwarz
inequality therefore pass to this particular limit.

The limiting radical law is proved from limiting Cauchy--Schwarz by a
constructive epsilon-squared argument. A presentation that is null only
in the limit is never asserted to be null at any finite heat stage.
The physical signed difference stays on the same guarded presentation
carrier. These are limiting scalar form laws, not a new completion or a
spatial-width/spacing-uniform estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (pairing_unit_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits

/-- Literal signed subtraction, retaining both physical-face guards. -/
def differenceSpan {width : Nat} (x y : PhysicalSpan width) : PhysicalSpan width :=
  ⟨difference x.val y.val, physical_difference x.property y.property⟩

-- Subsequent proofs use the already proved scalar convergence and form laws.
attribute [local irreducible] pairing jointPairing

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

/-- Symmetry of the actual cutoff-removed intrinsic reflected form. -/
theorem jointPairing_symm (x y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width y x) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_symm hw0 hw1 width x.val y.val x.property y.property stage)
    (pairing_converges_jointPairing hw0 hw1 width x y)
    (pairing_converges_jointPairing hw0 hw1 width y x)

/-- The original signed-span reflection positivity survives cutoff removal. -/
theorem jointPairing_nonnegative (x : PhysicalSpan width) :
    leEv czero (jointPairing hw0 hw1 width x x) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairing_converges_jointPairing hw0 hw1 width x x)
    (fun stage => pairing_self_nonnegative hw0 hw1 width x.val x.property stage)

/-- Normalization is inherited from the same original partition function. -/
theorem jointPairing_unit_unit :
    Equiv (jointPairing hw0 hw1 width (unit width) (unit width)) cone :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_unit_unit hw0 hw1 width stage)
    (pairing_converges_jointPairing hw0 hw1 width (unit width) (unit width))
    (convergesTo_const cone)

/-- Sharp Cauchy--Schwarz, rather than a presentation-dependent absolute cap. -/
theorem jointPairing_cauchySchwarz (x y : PhysicalSpan width) :
    leEv
      (mul (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x y))
      (mul (jointPairing hw0 hw1 width x x) (jointPairing hw0 hw1 width y y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairing_converges_jointPairing hw0 hw1 width x y)
      (pairing_converges_jointPairing hw0 hw1 width x y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairing_converges_jointPairing hw0 hw1 width x x)
      (pairing_converges_jointPairing hw0 hw1 width y y))
    (fun stage => pairing_cauchySchwarz hw0 hw1 width x.val y.val
      x.property y.property stage)

private theorem zero_of_square_le_zero (A : CReal)
    (h : leEv (mul A A) czero) : Equiv A czero := by
  intro epsilon he
  obtain ⟨index, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

/-- Limit-null vectors annihilate the limiting form. The hypothesis is
not strengthened to nullity at any fixed heat cutoff. -/
theorem jointPairing_radical_zero (x y : PhysicalSpan width)
    (hnull : Equiv (jointPairing hw0 hw1 width x x) czero) :
    Equiv (jointPairing hw0 hw1 width x y) czero := by
  have hzero : Equiv
      (mul (jointPairing hw0 hw1 width x x) (jointPairing hw0 hw1 width y y)) czero :=
    Equiv.trans (CReal.mul_congr_left hnull)
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.zero_mul_eqv ((jointPairing hw0 hw1 width y y).approx n)))
  exact zero_of_square_le_zero _ (leEv_trans
    (jointPairing_cauchySchwarz hw0 hw1 width x y) (leEv_of_equiv hzero))

/-- Rational addition on the same physical presentation carrier, left slot. -/
theorem jointPairing_add_left (x y z : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (addSpan x y) z)
      (add (jointPairing hw0 hw1 width x z) (jointPairing hw0 hw1 width y z)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_add_left hw0 hw1 width x.val y.val z.val stage)
    (pairing_converges_jointPairing hw0 hw1 width (addSpan x y) z)
    (TrigAddCReal.convergesTo_add
      (pairing_converges_jointPairing hw0 hw1 width x z)
      (pairing_converges_jointPairing hw0 hw1 width y z))

theorem jointPairing_add_right (x y z : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width x (addSpan y z))
      (add (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x z)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_add_right hw0 hw1 width x.val y.val z.val stage)
    (pairing_converges_jointPairing hw0 hw1 width x (addSpan y z))
    (TrigAddCReal.convergesTo_add
      (pairing_converges_jointPairing hw0 hw1 width x y)
      (pairing_converges_jointPairing hw0 hw1 width x z))

theorem jointPairing_smul_left (c : Q') (x y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (smulSpan c x) y)
      (mul (ofQ' c) (jointPairing hw0 hw1 width x y)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_smul_left hw0 hw1 width c x.val y.val stage)
    (pairing_converges_jointPairing hw0 hw1 width (smulSpan c x) y)
    (convergesTo_const_mul (ofQ' c) (pairing_converges_jointPairing hw0 hw1 width x y))

theorem jointPairing_smul_right (c : Q') (x y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width x (smulSpan c y))
      (mul (ofQ' c) (jointPairing hw0 hw1 width x y)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_smul_right hw0 hw1 width c x.val y.val stage)
    (pairing_converges_jointPairing hw0 hw1 width x (smulSpan c y))
    (convergesTo_const_mul (ofQ' c) (pairing_converges_jointPairing hw0 hw1 width x y))

/-- The physical signed difference acts as subtraction in the limiting form. -/
theorem jointPairing_difference_left (x y z : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (differenceSpan x y) z)
      (sub (jointPairing hw0 hw1 width x z) (jointPairing hw0 hw1 width y z)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_difference_left hw0 hw1 width x.val y.val z.val stage)
    (pairing_converges_jointPairing hw0 hw1 width (differenceSpan x y) z)
    (TrigAddCReal.convergesTo_add
      (pairing_converges_jointPairing hw0 hw1 width x z)
      (TrigAddCReal.convergesTo_neg (pairing_converges_jointPairing hw0 hw1 width y z)))

theorem jointPairing_difference_right (x y z : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width x (differenceSpan y z))
      (sub (jointPairing hw0 hw1 width x y) (jointPairing hw0 hw1 width x z)) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_difference_right hw0 hw1 width x.val y.val z.val stage)
    (pairing_converges_jointPairing hw0 hw1 width x (differenceSpan y z))
    (TrigAddCReal.convergesTo_add
      (pairing_converges_jointPairing hw0 hw1 width x y)
      (TrigAddCReal.convergesTo_neg (pairing_converges_jointPairing hw0 hw1 width x z)))

/-- Exact four-term squared-difference expansion, retaining both cross terms. -/
theorem jointPairing_difference_diagonal (x y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (differenceSpan x y) (differenceSpan x y))
      (sub
        (sub (jointPairing hw0 hw1 width x x) (jointPairing hw0 hw1 width x y))
        (sub (jointPairing hw0 hw1 width y x) (jointPairing hw0 hw1 width y y))) :=
  Equiv_of_limit_of_equal
    (fun stage => pairing_difference_diagonal hw0 hw1 width x.val y.val stage)
    (pairing_converges_jointPairing hw0 hw1 width (differenceSpan x y) (differenceSpan x y))
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add
        (pairing_converges_jointPairing hw0 hw1 width x x)
        (TrigAddCReal.convergesTo_neg (pairing_converges_jointPairing hw0 hw1 width x y)))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (pairing_converges_jointPairing hw0 hw1 width y x)
          (TrigAddCReal.convergesTo_neg (pairing_converges_jointPairing hw0 hw1 width y y)))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.differenceSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_unit_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_radical_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_difference_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_difference_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws.jointPairing_difference_diagonal
