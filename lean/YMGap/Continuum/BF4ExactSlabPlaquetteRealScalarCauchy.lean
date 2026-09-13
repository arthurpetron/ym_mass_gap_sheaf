/-
# Explicit real-scalar streams on the ORIGINAL plaquette completion

For a real s with supplied Type-level rational Cauchy data and an original
plaquette Cauchy representative X, the stream s_n * X_n is Cauchy in the
SAME reflected squared distance. Both tail ceilings and every tolerance
are computed. No modulus is extracted from the legacy CReal.cauchy field.

The estimate splits a*x-b*y through a*y, spending epsilon/4 on each of
the two squared distances before the sqrt-free triangle doubles them.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

private theorem polynomial_scalar_difference (a b : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul a p) (polySmul (-1) (polySmul b p)))
      (polySmul (a + -b) p) := by
  have hb : Q'.eqv ((-1) * b) (-b) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 b) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv b))
  exact ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.smul_assoc (-1) b p).trans (RatPolyCoeffEqv.smul_coefficient hb p))).trans
      (RatPolyCoeffEqv.add_smul_same a (-b) p)

theorem expression_scalar_difference {half : Nat} (a b : Q') (e : PlaquetteExpression half) :
    expressionEqv (subtract (.smul a e) (.smul b e)) (.smul (a + -b) e) :=
  ⟨polynomial_scalar_difference a b (lower e), polynomial_scalar_difference a b (upper e)⟩

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A) (ha : Q'.abs a ≤ A) :
    a * a ≤ A * A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

/-- A computed tail ceiling, valid from the supplied one-tolerance stage. -/
def scalarCeiling (s : CReal) (cs : QCauchy s.approx) : Q' := Q'.abs (s.approx (cs.M 1)) + 1

theorem scalarCeiling_nonnegative (s : CReal) (cs : QCauchy s.approx) :
    (0 : Q') ≤ scalarCeiling s cs := Q'.zero_le_add _ _ (Q'.abs_nonneg _) Q'.zero_le_one

theorem scalar_approx_le_ceiling (s : CReal) (cs : QCauchy s.approx) (n : Nat) (hn : cs.M 1 ≤ n) :
    Q'.abs (s.approx n) ≤ scalarCeiling s cs := by
  have h := cs.bound 1 (by decide) n (cs.M 1) hn (Nat.le_refl _)
  exact Q'.abs_le_abs_add_one_of_bounds h.1 h.2

private theorem ceilingBudget_pos (B : Q') (hB : (0 : Q') ≤ B) : (0 : Q') < B + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 B hB) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Clipping at one lets a linear error budget control the squared error. -/
def coefficientTolerance (B : Q') (hB : (0 : Q') ≤ B) (epsilon : Q') : Q' :=
  Q'.min' (Q'.divPos (quarter epsilon) (B + 1) (ceilingBudget_pos B hB)) 1

theorem coefficientTolerance_pos (B : Q') (hB : (0 : Q') ≤ B) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < coefficientTolerance B hB epsilon := by
  unfold coefficientTolerance Q'.min'
  split
  · exact Q'.divPos_pos _ _ _ (quarter_pos he)
  · decide

theorem coefficientTolerance_budget (B : Q') (hB : (0 : Q') ≤ B) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    coefficientTolerance B hB epsilon * coefficientTolerance B hB epsilon * B ≤ quarter epsilon := by
  let delta := coefficientTolerance B hB epsilon
  have hd : (0 : Q') ≤ delta := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have h1 : delta ≤ 1 := Q'.min_le_right' _ _
  have hs : delta * delta ≤ delta :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 hd) (Q'.le_of_eqv (Q'.mul_one_eqv delta))
  have hlinear : delta * B ≤ quarter epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg B 1 Q'.zero_le_one) hd)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.min_le_left' _ _)
        (Q'.le_of_lt (ceilingBudget_pos B hB))) (Q'.le_of_eqv (Q'.divPos_mul_eqv _ _ _)))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hs hB) hlinear

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

theorem distSq_scalar_difference (a b : Q') (e : PlaquetteExpression half) :
    Equiv (distSq w hw0 hw1 (.smul a e) (.smul b e))
      (CReal.mul (ofQ' ((a + -b) * (a + -b))) (form w hw0 hw1 e e)) :=
  (form_congr w hw0 hw1 (expression_scalar_difference a b e) (expression_scalar_difference a b e)).trans
    (form_smul_diagonal w hw0 hw1 (a + -b) e)

theorem scalar_change_bound (a b B epsilon : Q') (hB : (0 : Q') ≤ B) (he : (0 : Q') < epsilon)
    (e : PlaquetteExpression half) (hnorm : leEv (form w hw0 hw1 e e) (ofQ' B))
    (hab : a ≤ b + coefficientTolerance B hB epsilon ∧ b ≤ a + coefficientTolerance B hB epsilon) :
    leEv (distSq w hw0 hw1 (.smul a e) (.smul b e)) (ofQ' (quarter epsilon)) := by
  let delta := coefficientTolerance B hB epsilon
  have hd := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have habs : Q'.abs (a + -b) ≤ delta := Q'.abs_le (Q'.neg_le_sub_of_le_add hab.2) (Q'.sub_le_of_le_add hab.1)
  have hs := square_le_of_abs_le hd habs
  have hfactor : leEv czero (ofQ' ((a + -b) * (a + -b))) :=
    leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (a + -b))
  have hscaled := leEv_mul_nonneg_left hfactor hnorm
  exact leEv_trans (leEv_of_equiv (distSq_scalar_difference w hw0 hw1 a b e))
    (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hs hB) (coefficientTolerance_budget B hB he))))

def realScalarRate (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (cs.M 1) (normBase w hw0 hw1 X))
    (max (X.modulus (scalarTolerance (scalarCeiling s cs) (quarter epsilon)))
      (cs.M (coefficientTolerance (normCeiling w hw0 hw1 X) (normCeiling_nonnegative w hw0 hw1 X) epsilon)))

theorem realScalar_bound (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : realScalarRate w hw0 hw1 s cs X epsilon ≤ m) (hn : realScalarRate w hw0 hw1 s cs X epsilon ≤ n) :
    leEv (distSq w hw0 hw1 (.smul (s.approx m) (X.seq m)) (.smul (s.approx n) (X.seq n))) (ofQ' epsilon) := by
  let A := scalarCeiling s cs
  let B := normCeiling w hw0 hw1 X
  let hB := normCeiling_nonnegative w hw0 hw1 X
  let delta := scalarTolerance A (quarter epsilon)
  have hd := scalarTolerance_pos A (quarter_pos he)
  have hXm : X.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have ham : cs.M 1 ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm
  have hnormn : normBase w hw0 hw1 X ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hsm : cs.M (coefficientTolerance B hB epsilon) ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hsn : cs.M (coefficientTolerance B hB epsilon) ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hsquare := square_le_of_abs_le (scalarCeiling_nonnegative s cs) (scalar_approx_le_ceiling s cs m ham)
  have hfirst : leEv (distSq w hw0 hw1 (.smul (s.approx m) (X.seq m)) (.smul (s.approx m) (X.seq n)))
      (ofQ' (quarter epsilon)) := by
    have hfactor : leEv czero (ofQ' (s.approx m * s.approx m)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (s.approx m))
    have hscaled := leEv_mul_nonneg_left hfactor (X.isCauchy delta hd m n hXm hXn)
    exact leEv_trans (leEv_of_equiv (distSq_smul w hw0 hw1 (s.approx m) (X.seq m) (X.seq n)))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
        Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (Q'.le_of_lt hd))
          (scalarTolerance_bound A (quarter_pos he)))))
  have hsecond := scalar_change_bound w hw0 hw1 (s.approx m) (s.approx n) B epsilon hB he (X.seq n)
    (diagonal_le_normCeiling w hw0 hw1 X n hnormn)
    (cs.bound _ (coefficientTolerance_pos B hB he) m n hsm hsn)
  have hsum := leEv_add (leEv_add hfirst hfirst) (leEv_add hsecond hsecond)
  rw [ofQ'_add, ofQ'_add] at hsum
  have hbudget : Q'.eqv ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon)) epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon)) (ExpNeg.two_halves (HalfPow.half * epsilon)))
      (ExpNeg.two_halves epsilon)
  exact leEv_trans (distSq_triangle w hw0 hw1 _ (.smul (s.approx m) (X.seq n)) _)
    (leEv_trans hsum (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hbudget)))

/-- The actual original-expression stream, together with its computed modulus. -/
def realScalarCauchy (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) : (D).Cauchy where
  seq n := .smul (s.approx n) (X.seq n)
  modulus := realScalarRate w hw0 hw1 s cs X
  isCauchy := realScalar_bound w hw0 hw1 s cs X

end YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.expression_scalar_difference
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.scalarCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.scalarCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.scalar_approx_le_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.coefficientTolerance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.coefficientTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.coefficientTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.distSq_scalar_difference
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.scalar_change_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.realScalarRate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.realScalar_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy.realScalarCauchy
