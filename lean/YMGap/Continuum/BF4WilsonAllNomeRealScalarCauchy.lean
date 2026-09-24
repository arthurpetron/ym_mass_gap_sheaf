/-
# Constructive real-scalar streams on the literal all-nome Wilson completion

A real scalar is used only together with explicit rational Cauchy data.  The
varying stream `s.approx n • X.seq n` is proved Cauchy in the SAME fixed-width
Wilson seminorm, with a computed modulus.  No representative is selected from
the propositional `CReal.cauchy` field.
-/

import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm distSq distSq_triangle)
open YMGap.Continuum.BF4WilsonAllNomeLinear (distSq_smul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (pairingData)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling
    coefficientTolerance coefficientTolerance_pos coefficientTolerance_budget)

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A)
    (ha : Q'.abs a ≤ A) : a*a ≤ A*A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => intrinsicForm hw0 hw1
local notation "d" => distSq hw0 hw1
local notation "PD" => pairingData hw0 hw1 (width := width)

private theorem sub_congr {a b c e : CReal} (hab : Equiv a b) (hce : Equiv c e) :
    Equiv (sub a c) (sub b e) := Equiv_add hab (neg_congr hce)

private theorem scalar_difference_pairing (a b : Q')
    (x y : IntrinsicExpression width) :
    Equiv (P (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference
      (smul a x) (smul b x)) y) (mul (ofQ' (a + -b)) (P x y)) := by
  have h := intrinsicForm_difference_left hw0 hw1 (smul a x) (smul b x) y
  have hs := sub_congr (intrinsicForm_smul_left hw0 hw1 a x y)
    (intrinsicForm_smul_left hw0 hw1 b x y)
  exact h.trans (hs.trans (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (by decide) (fun | 0 => a | 1 => b | _ => (P x y).approx n))))

/-- Exact coefficient-square factor when only the rational coefficient changes. -/
theorem distSq_scalar_difference (a b : Q') (x : IntrinsicExpression width) :
    Equiv (d (smul a x) (smul b x))
      (mul (ofQ' ((a + -b)*(a + -b))) (P x x)) := by
  let v := YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference
    (smul a x) (smul b x)
  change Equiv (P v v) (mul (ofQ' ((a + -b)*(a + -b))) (P x x))
  have hl := scalar_difference_pairing hw0 hw1 a b x v
  have hr := (YMGap.Continuum.BF4WilsonAllNomeReflectedForm.intrinsicForm_symm hw0 hw1 x v).trans
    (scalar_difference_pairing hw0 hw1 a b x x)
  exact hl.trans ((Pivot2.mul_congr_right hr).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_symm (Q'.mul_assoc_eqv (a + -b) (a + -b) ((P x x).approx n)))))

/-- A common coefficient tolerance controls a scalar change at a dense vector. -/
theorem scalar_change_bound (a b B epsilon : Q') (hB : (0 : Q') ≤ B)
    (he : (0 : Q') < epsilon) (x : IntrinsicExpression width)
    (hnorm : leEv (P x x) (ofQ' B))
    (hab : a ≤ b + coefficientTolerance B hB epsilon ∧
      b ≤ a + coefficientTolerance B hB epsilon) :
    leEv (d (smul a x) (smul b x)) (ofQ' (quarter epsilon)) := by
  let delta := coefficientTolerance B hB epsilon
  have hdelta := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have habs : Q'.abs (a + -b) ≤ delta :=
    Q'.abs_le (Q'.neg_le_sub_of_le_add hab.2) (Q'.sub_le_of_le_add hab.1)
  have hsquare := square_le_of_abs_le hdelta habs
  have hfactor : leEv czero (ofQ' ((a + -b)*(a + -b))) :=
    leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (a + -b))
  exact leEv_trans (leEv_of_equiv (distSq_scalar_difference hw0 hw1 a b x))
    (leEv_trans (leEv_mul_nonneg_left hfactor hnorm)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare hB)
        (coefficientTolerance_budget B hB he))))

def realScalarRate (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') : Nat :=
  max (max (cs.M 1) (CRealSeminormPairingCompletion.normBase PD X))
    (max (X.modulus (scalarTolerance (scalarCeiling s cs) (quarter epsilon)))
      (cs.M (coefficientTolerance (CRealSeminormPairingCompletion.normCeiling PD X)
        (CRealSeminormPairingCompletion.normCeiling_nonnegative PD X) epsilon)))

theorem realScalar_bound (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : realScalarRate hw0 hw1 s cs X epsilon ≤ m)
    (hn : realScalarRate hw0 hw1 s cs X epsilon ≤ n) :
    leEv (d (smul (s.approx m) (X.seq m)) (smul (s.approx n) (X.seq n)))
      (ofQ' epsilon) := by
  let A := scalarCeiling s cs
  let B := CRealSeminormPairingCompletion.normCeiling PD X
  let hB := CRealSeminormPairingCompletion.normCeiling_nonnegative PD X
  let delta := scalarTolerance A (quarter epsilon)
  have hdlt : (0 : Q') < delta := scalarTolerance_pos A (quarter_pos he)
  have hXm : X.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have ham : cs.M 1 ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm
  have hnormn : CRealSeminormPairingCompletion.normBase PD X ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hsm : cs.M (coefficientTolerance B hB epsilon) ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hsn : cs.M (coefficientTolerance B hB epsilon) ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hsquare : s.approx m * s.approx m ≤ A*A := square_le_of_abs_le
    (scalarCeiling_nonnegative s cs) (scalar_approx_le_ceiling s cs m ham)
  have hfirst : leEv (d (smul (s.approx m) (X.seq m)) (smul (s.approx m) (X.seq n)))
      (ofQ' (quarter epsilon)) := by
    have hfactor : leEv czero (ofQ' (s.approx m * s.approx m)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (s.approx m))
    exact leEv_trans (leEv_of_equiv (distSq_smul hw0 hw1 (s.approx m) (X.seq m) (X.seq n)))
      (leEv_trans (leEv_mul_nonneg_left hfactor (X.isCauchy delta hdlt m n hXm hXn))
        (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (Q'.le_of_lt hdlt))
          (scalarTolerance_bound A (quarter_pos he)))))
  have hsecond : leEv (d (smul (s.approx m) (X.seq n)) (smul (s.approx n) (X.seq n)))
      (ofQ' (quarter epsilon)) := scalar_change_bound hw0 hw1 (s.approx m) (s.approx n)
        B epsilon hB he (X.seq n)
        (CRealSeminormPairingCompletion.diagonal_le_normCeiling PD X n hnormn)
        (cs.bound _ (coefficientTolerance_pos B hB he) m n hsm hsn)
  have hsum := leEv_add (leEv_add hfirst hfirst) (leEv_add hsecond hsecond)
  rw [ofQ'_add, ofQ'_add] at hsum
  have hbudget : Q'.eqv ((quarter epsilon + quarter epsilon) +
      (quarter epsilon + quarter epsilon)) epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*epsilon))
        (ExpNeg.two_halves (HalfPow.half*epsilon))) (ExpNeg.two_halves epsilon)
  exact leEv_trans (distSq_triangle hw0 hw1 (smul (s.approx m) (X.seq m))
      (smul (s.approx m) (X.seq n)) (smul (s.approx n) (X.seq n)))
    (leEv_trans hsum (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hbudget)))

def realScalarCauchy (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) : (D).Cauchy where
  seq n := smul (s.approx n) (X.seq n)
  modulus := realScalarRate hw0 hw1 s cs X
  isCauchy := realScalar_bound hw0 hw1 s cs X

theorem realScalarCauchy_seq (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) (n : Nat) :
    (realScalarCauchy hw0 hw1 s cs X).seq n = smul (s.approx n) (X.seq n) := rfl

theorem realScalarCauchy_modulus (s : CReal) (cs : QCauchy s.approx)
    (X : (D).Cauchy) (epsilon : Q') :
    (realScalarCauchy hw0 hw1 s cs X).modulus epsilon =
      realScalarRate hw0 hw1 s cs X epsilon := rfl

end YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy

#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.distSq_scalar_difference
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.scalar_change_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.realScalarRate
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.realScalar_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.realScalarCauchy
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.realScalarCauchy_seq
#print axioms YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy.realScalarCauchy_modulus
