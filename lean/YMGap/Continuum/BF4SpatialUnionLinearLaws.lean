/-
# Rational linear laws on the actual spatial union completion

Test the existing completed operations against an arbitrary vector in the
SAME union pairing. Its proved bilinearity reduces the module identities
to exact rational algebra, and pairing separation proves vector equality.
Time balance likewise gives commutation with every signed rational scalar.

No scalar representative is chosen, and no full RC-module, metric
completeness, observable-coverage or continuum assertion is made here.
-/

import YMGap.Continuum.BF4SpatialUnionBilinear

namespace YMGap.Continuum.BF4SpatialUnionLinearLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4SpatialUnionGeometry
  (completedZero completedInner_time_balance)
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "S" => completedSmul hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

theorem completedAdd_assoc (x y z : V) : A (A x y) z = A x (A y z) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_add_left]
  refine Quotient.inductionOn₃ (B x test) (B y test) (B z test) ?_
  exact fun X Y W => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (X.approx n) (Y.approx n) (W.approx n)))

theorem completedNeg_add (x : V) :
    A (completedNeg hw0 hw1 hsmall hd hs x) x = Z := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_add_left, completedInner_neg_left, completedInner_zero_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.neg_add_self_eqv (X.approx n)))

theorem completedSmul_one (x : V) : S 1 x = x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_smul_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.one_mul_eqv (X.approx n)))

theorem completedSmul_zero (x : V) : S 0 x = Z := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_smul_left, completedInner_zero_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (X.approx n)))

theorem completedSmul_mul (a b : Q') (x : V) : S a (S b x) = S (a*b) x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_smul_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.mul_assoc_eqv a b (X.approx n))))

theorem completedSmul_add (c : Q') (x y : V) : S c (A x y) = A (S c x) (S c y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_add_left, completedInner_smul_left]
  refine Quotient.inductionOn₂ (B x test) (B y test) ?_
  exact fun X Y => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv c (X.approx n) (Y.approx n)))

theorem completedAdd_smul (a b : Q') (x : V) : A (S a x) (S b x) = S (a+b) x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [completedInner_add_left, completedInner_smul_left]
  refine Quotient.inductionOn (B x test) ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.add_mul_eqv a b (X.approx n))))

/-- Rational setoid equality, not literal numerator/denominator equality. -/
theorem completedSmul_congr {a b : Q'} (h : a.eqv b) (x : V) : S a x = S b x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_smul_left, completedInner_smul_left]
  exact congrArg (fun q : RC => RCmul q (B x test))
    (Quotient.sound (ofQ'_equiv_of_eqv h))

/-- The SAME discrete physical time commutes with arbitrary signed rational scaling. -/
theorem completedTime_smul (n : Nat) (c : Q') (x : V) : T n (S c x) = S c (T n x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_time_balance, completedInner_smul_left,
    completedInner_smul_left, completedInner_time_balance]

end YMGap.Continuum.BF4SpatialUnionLinearLaws

#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedAdd_assoc
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedNeg_add
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedSmul_one
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedSmul_zero
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedSmul_mul
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedSmul_add
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedAdd_smul
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedSmul_congr
#print axioms YMGap.Continuum.BF4SpatialUnionLinearLaws.completedTime_smul
