/-
# Modulus-bearing real-scalar streams for the ORIGINAL thermodynamic carrier

Given actual scalar QCauchy data and an original presentation Cauchy stream,
the pointwise stream s_n*X_n is Cauchy in the SAME thermodynamic squared
distance. Scalar and vector tail ceilings, coefficient tolerances and the
output modulus are computed. No legacy real or quotient modulus is selected.

Only generic rational bounds and scalar-stream estimates are reused from
the finite module. The vector norm and scalar action below are original
thermodynamic constructions, not finite-slab replacements.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling
    coefficientTolerance coefficientTolerance_pos coefficientTolerance_budget)

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A) (ha : Q'.abs a ≤ A) :
    a * a ≤ A * A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

local notation "D" => seminorm

theorem observable_scalar_difference (a b : Q') (x : Observable) :
    subtract (qsmul a x) (qsmul b x) = qsmul (a + -b) x := by
  have hb : Q'.eqv ((-1) * b) (-b) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 b) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv b))
  unfold subtract
  rw [qsmul_assoc, qsmul_coefficient hb x]
  exact (add_smul a (-b) x).symm

theorem distSq_scalar_difference (a b : Q') (p : Presentation) :
    Equiv (distSq (smul a p) (smul b p))
      (CReal.mul (ofQ' ((a + -b) * (a + -b))) (presentedForm p p)) := by
  have h : Equiv (distSq (smul a p) (smul b p))
      (presentedForm (smul (a + -b) p) (smul (a + -b) p)) := by
    apply Quotient.exact (s := crealSetoid)
    change pairing (subtract (qsmul a (embed p)) (qsmul b (embed p)))
        (subtract (qsmul a (embed p)) (qsmul b (embed p))) =
      pairing (qsmul (a + -b) (embed p)) (qsmul (a + -b) (embed p))
    rw [observable_scalar_difference]
  exact h.trans (presentedForm_smul_diagonal (a + -b) p)

theorem scalar_change_bound (a b B epsilon : Q') (hB : (0 : Q') ≤ B) (he : (0 : Q') < epsilon)
    (e : Presentation) (hnorm : leEv (presentedForm e e) (ofQ' B))
    (hab : a ≤ b + coefficientTolerance B hB epsilon ∧ b ≤ a + coefficientTolerance B hB epsilon) :
    leEv (distSq (smul a e) (smul b e)) (ofQ' (quarter epsilon)) := by
  let delta := coefficientTolerance B hB epsilon
  have hd := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have habs : Q'.abs (a + -b) ≤ delta := Q'.abs_le (Q'.neg_le_sub_of_le_add hab.2) (Q'.sub_le_of_le_add hab.1)
  have hs := square_le_of_abs_le hd habs
  have hfactor : leEv czero (ofQ' ((a + -b) * (a + -b))) :=
    leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (a + -b))
  have hscaled := leEv_mul_nonneg_left hfactor hnorm
  exact leEv_trans (leEv_of_equiv (distSq_scalar_difference a b e))
    (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hs hB) (coefficientTolerance_budget B hB he))))

def realScalarRate (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (cs.M 1) (normBase X))
    (max (X.modulus (scalarTolerance (scalarCeiling s cs) (quarter epsilon)))
      (cs.M (coefficientTolerance (normCeiling X) (normCeiling_nonnegative X) epsilon)))

theorem realScalar_bound (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : realScalarRate s cs X epsilon ≤ m) (hn : realScalarRate s cs X epsilon ≤ n) :
    leEv (distSq (smul (s.approx m) (X.seq m)) (smul (s.approx n) (X.seq n))) (ofQ' epsilon) := by
  let A := scalarCeiling s cs
  let B := normCeiling X
  let hB := normCeiling_nonnegative X
  let delta := scalarTolerance A (quarter epsilon)
  have hd := scalarTolerance_pos A (quarter_pos he)
  have hXm : X.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have ham : cs.M 1 ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm
  have hnormn : normBase X ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hsm : cs.M (coefficientTolerance B hB epsilon) ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hsn : cs.M (coefficientTolerance B hB epsilon) ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hsquare := square_le_of_abs_le (scalarCeiling_nonnegative s cs) (scalar_approx_le_ceiling s cs m ham)
  have hfirst : leEv (distSq (smul (s.approx m) (X.seq m)) (smul (s.approx m) (X.seq n)))
      (ofQ' (quarter epsilon)) := by
    have hfactor : leEv czero (ofQ' (s.approx m * s.approx m)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (s.approx m))
    have hscaled := leEv_mul_nonneg_left hfactor (X.isCauchy delta hd m n hXm hXn)
    exact leEv_trans (leEv_of_equiv (distSq_smul (s.approx m) (X.seq m) (X.seq n)))
      (leEv_trans hscaled (leEv_le_ofQ'_of_approx_le (fun _ =>
        Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (Q'.le_of_lt hd))
          (scalarTolerance_bound A (quarter_pos he)))))
  have hsecond := scalar_change_bound (s.approx m) (s.approx n) B epsilon hB he (X.seq n)
    (diagonal_le_normCeiling X n hnormn)
    (cs.bound _ (coefficientTolerance_pos B hB he) m n hsm hsn)
  have hsum := leEv_add (leEv_add hfirst hfirst) (leEv_add hsecond hsecond)
  rw [ofQ'_add, ofQ'_add] at hsum
  have hbudget : Q'.eqv ((quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon)) epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon)) (ExpNeg.two_halves (HalfPow.half * epsilon)))
      (ExpNeg.two_halves epsilon)
  exact leEv_trans (distSq_triangle _ (smul (s.approx m) (X.seq n)) _)
    (leEv_trans hsum (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hbudget)))

/-- The actual original-expression stream, together with its computed modulus. -/
def realScalarCauchy (s : CReal) (cs : QCauchy s.approx) (X : (D).Cauchy) : (D).Cauchy where
  seq n := smul (s.approx n) (X.seq n)
  modulus := realScalarRate s cs X
  isCauchy := realScalar_bound s cs X

end YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy.observable_scalar_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy.distSq_scalar_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy.scalar_change_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy.realScalarRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy.realScalar_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarCauchy.realScalarCauchy
