/-
# Bounded original channel functionals on the actual null quotient

Each intrinsic packet leaf gives a linear coefficient of the ORIGINAL
lower action. The original normalized OS bound applies to differences,
so coefficients descend through exactly the original null relation.
The positive squared-distance tolerance F*epsilon^2/2 is explicit and
independent of both observables. No completed extension or time-translation
identification is assumed here; no volume/beta/spacing-uniform gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "actualTree" N => BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.tree
  (interfaceExpansion (Q'.le_of_lt hw0) N half)

def coefficient (N : Nat) (l : Leaf (actualTree N)) (e : PlaquetteExpression half) : CReal :=
  coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)

theorem coefficient_add (N : Nat) (l : Leaf (actualTree N)) (e f : PlaquetteExpression half) :
    Equiv (coefficient w hw0 hw1 N l (.add e f))
      (CReal.add (coefficient w hw0 hw1 N l e) (coefficient w hw0 hw1 N l f)) := by
  unfold coefficient coefficientLimit
  change Equiv (numeratorLimit w hw0 hw1 _ _ _ (polyMul (polyAdd (lower e) (lower f)) l.channel)) _
  rw [polyMul_add_left_exact]
  exact numeratorLimit_add w hw0 hw1 _ _ _ _ _

theorem coefficient_smul (N : Nat) (l : Leaf (actualTree N)) (c : Q') (e : PlaquetteExpression half) :
    Equiv (coefficient w hw0 hw1 N l (.smul c e))
      (CReal.mul (ofQ' c) (coefficient w hw0 hw1 N l e)) :=
  (numeratorLimit_congr w hw0 hw1 _ _ _ (RatPolyCoeffEqv.polyMul_smul_left c (lower e) l.channel)).trans
    (numeratorLimit_smul w hw0 hw1 _ _ _ c _)

theorem coefficient_neg (N : Nat) (l : Leaf (actualTree N)) (e : PlaquetteExpression half) :
    Equiv (coefficient w hw0 hw1 N l (.smul (-1) e)) (CReal.neg (coefficient w hw0 hw1 N l e)) :=
  (coefficient_smul w hw0 hw1 N l (-1) e).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_trans _ _ _
      (Q'.neg_mul_eqv 1 ((coefficient w hw0 hw1 N l e).approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

theorem coefficient_sub (N : Nat) (l : Leaf (actualTree N)) (e f : PlaquetteExpression half) :
    Equiv (coefficient w hw0 hw1 N l (subtract e f))
      (CReal.sub (coefficient w hw0 hw1 N l e) (coefficient w hw0 hw1 N l f)) :=
  (coefficient_add w hw0 hw1 N l e (.smul (-1) f)).trans
    (Pivot2.add_congr (Equiv.refl _) (coefficient_neg w hw0 hw1 N l f))

theorem coefficient_zero (N : Nat) (l : Leaf (actualTree N)) :
    Equiv (coefficient w hw0 hw1 N l (zeroExpression half)) czero :=
  (coefficient_smul w hw0 hw1 N l 0 .unit).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_zero_mul _))

theorem coefficient_null_congr (N : Nat) (l : Leaf (actualTree N))
    {e f : PlaquetteExpression half} (h : Null w hw0 hw1 e f) :
    Equiv (coefficient w hw0 hw1 N l e) (coefficient w hw0 hw1 N l f) :=
  Equiv_of_sub_eqv_zero ((coefficient_sub w hw0 hw1 N l e f).symm.trans
    ((form_null_iff_channel_coefficients_zero w hw0 hw1 (subtract e f)).mp (Quotient.exact h) N l))

/-- The target is the actual real quotient, not a chosen numerical representative. -/
def quotientCoefficient (N : Nat) (l : Leaf (actualTree N)) : Carrier w hw0 hw1 half → RC :=
  Quotient.lift (fun e => Quotient.mk crealSetoid (coefficient w hw0 hw1 N l e))
    (fun _ _ h => Quotient.sound (coefficient_null_congr w hw0 hw1 N l h))

theorem quotientCoefficient_embed (N : Nat) (l : Leaf (actualTree N)) (e : PlaquetteExpression half) :
    quotientCoefficient w hw0 hw1 N l (embed w hw0 hw1 e) =
      Quotient.mk crealSetoid (coefficient w hw0 hw1 N l e) := rfl

theorem quotientCoefficient_add (N : Nat) (l : Leaf (actualTree N)) (x y : Carrier w hw0 hw1 half) :
    quotientCoefficient w hw0 hw1 N l (BF4ExactSlabPlaquetteNullQuotient.add w hw0 hw1 x y) =
      RCadd (quotientCoefficient w hw0 hw1 N l x) (quotientCoefficient w hw0 hw1 N l y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro e f
  exact Quotient.sound (coefficient_add w hw0 hw1 N l e f)

theorem quotientCoefficient_smul (N : Nat) (l : Leaf (actualTree N)) (c : Q') (x : Carrier w hw0 hw1 half) :
    quotientCoefficient w hw0 hw1 N l (smul w hw0 hw1 c x) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (quotientCoefficient w hw0 hw1 N l x) := by
  refine Quotient.inductionOn x ?_
  intro e
  exact Quotient.sound (coefficient_smul w hw0 hw1 N l c e)

theorem coefficient_difference_bound (N : Nat) (l : Leaf (actualTree N)) (e f : PlaquetteExpression half) :
    leEv (CReal.mul (ofQ' (intrinsicNormFloor w hw0 N l))
      (CReal.mul (CReal.sub (coefficient w hw0 hw1 N l e) (coefficient w hw0 hw1 N l f))
        (CReal.sub (coefficient w hw0 hw1 N l e) (coefficient w hw0 hw1 N l f))))
      (distSq w hw0 hw1 e f) :=
  leEv_trans (leEv_of_equiv (Pivot2.mul_congr_right
    (Pivot2.mul_congr (coefficient_sub w hw0 hw1 N l e f).symm
      (coefficient_sub w hw0 hw1 N l e f).symm)))
    (intrinsic_normalized_energy_bound w hw0 hw1 (subtract e f) N l)

/-- Squared-distance tolerance: no observable is a parameter. -/
def coefficientTolerance (N : Nat) (l : Leaf (actualTree N)) (epsilon : Q') : Q' :=
  intrinsicNormFloor w hw0 N l * (HalfPow.half * (epsilon * epsilon))

theorem coefficientTolerance_positive (N : Nat) (l : Leaf (actualTree N))
    {epsilon : Q'} (he : (0 : Q') < epsilon) : (0 : Q') < coefficientTolerance w hw0 N l epsilon :=
  Q'.mul_pos (intrinsicNormFloor_positive w hw0 N l) (ExpNeg.half_mul_pos _ (Q'.mul_pos he he))

/-- Pure scalar estimate reused on dense and completed original coefficients. -/
theorem weighted_square_small (F : Q') (hF : (0 : Q') < F) (A : CReal)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (h : leEv (CReal.mul (ofQ' F) (CReal.mul A A)) (ofQ' (F * (HalfPow.half * (epsilon * epsilon))))) :
    leRat A epsilon ∧ leRat (CReal.neg A) epsilon := by
  obtain ⟨M, hM⟩ := h (F * (HalfPow.half * (epsilon * epsilon)))
    (Q'.mul_pos hF (ExpNeg.half_mul_pos _ (Q'.mul_pos he he)))
  have hb : ∀ n, M ≤ n → A.approx n ≤ epsilon ∧ -A.approx n ≤ epsilon := by
    intro n hn
    apply Q'.abs_le_two_sided
    apply Q'.abs_le_of_sq_le_sq he
    apply Q'.le_of_mul_le_mul_left (c := F) _ hF
    exact Q'.le_trans' _ _ _ (hM n hn) (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
      (Q'.mul_eqv_congr_left _ _ _ (ExpNeg.two_halves (epsilon * epsilon)))))
  exact ⟨leRat_of_eventually ⟨M, fun n hn => (hb n hn).1⟩,
    leRat_of_eventually ⟨M, fun n hn => (hb n hn).2⟩⟩

theorem coefficient_close (N : Nat) (l : Leaf (actualTree N)) (e f : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (h : leEv (distSq w hw0 hw1 e f) (ofQ' (coefficientTolerance w hw0 N l epsilon))) :
    leRat (CReal.sub (coefficient w hw0 hw1 N l e) (coefficient w hw0 hw1 N l f)) epsilon ∧
    leRat (CReal.sub (coefficient w hw0 hw1 N l f) (coefficient w hw0 hw1 N l e)) epsilon := by
  have hs := weighted_square_small _ (intrinsicNormFloor_positive w hw0 N l) _ epsilon he
    (leEv_trans (coefficient_difference_bound w hw0 hw1 N l e f) h)
  exact ⟨hs.1, leRat_of_equiv
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _))) hs.2⟩

end YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient

#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_add
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_smul
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_neg
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_sub
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_zero
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.quotientCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.quotientCoefficient_embed
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.quotientCoefficient_add
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.quotientCoefficient_smul
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficientTolerance
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficientTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.weighted_square_small
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelQuotient.coefficient_close
