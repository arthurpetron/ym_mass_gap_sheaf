/-
# Uniform coefficient bound for the positive artanh/Euler companion

The finite positive companion has nonnegative coefficients.  This module
proves that it is coefficientwise monotone in both finite cutoffs, enlarges
those cutoffs beyond any requested coefficient, and compares the stabilized
coefficient with the closed target `1,2,2,...`.

Everything is finite and constructive: no infinite power series, normalized
rational representative, or classical choice is used.
-/

import YMGap.Constructive.CRealArtanhEulerPositiveCompanion

namespace YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion

/-! ## 1. Coefficientwise order on finite rational polynomials -/

/-- Pointwise order on padded finite-polynomial coefficients. -/
def CoeffLe (p q : Poly) : Prop :=
  forall index : Nat, coeff p index <= coeff q index

theorem coeffLe_refl (p : Poly) : CoeffLe p p :=
  fun index => Q'.le_refl' (coeff p index)

theorem coeffLe_trans {p q r : Poly}
    (hpq : CoeffLe p q) (hqr : CoeffLe q r) : CoeffLe p r :=
  fun index => Q'.le_trans' _ _ _ (hpq index) (hqr index)

theorem coeffLe_padd {p q r s : Poly}
    (hpr : CoeffLe p r) (hqs : CoeffLe q s) :
    CoeffLe (padd p q) (padd r s) := by
  intro index
  exact Q'.le_trans' _ (coeff p index + coeff q index) _
    (Q'.le_of_eqv (coeff_padd index p q))
    (Q'.le_trans' _ (coeff r index + coeff s index) _
      (Q'.add_le_add (hpr index) (hqs index))
      (Q'.ge_of_eqv (coeff_padd index r s)))

theorem coeffLe_padd_left_of_nonnegative (p q : Poly)
    (hq : CoeffNonnegative q) : CoeffLe p (padd p q) := by
  intro index
  exact Q'.le_trans' _ (coeff p index + coeff q index) _
    (Q'.add_le_self_of_nonneg _ _ (hq index))
    (Q'.ge_of_eqv (coeff_padd index p q))

theorem coeffLe_pscale {p q : Poly} (scalar : Q')
    (hscalar : (0 : Q') <= scalar) (hpq : CoeffLe p q) :
    CoeffLe (pscale scalar p) (pscale scalar q) := by
  intro index
  exact Q'.le_trans' _ (scalar * coeff p index) _
    (Q'.le_of_eqv (coeff_pscale scalar p index))
    (Q'.le_trans' _ (scalar * coeff q index) _
      (Q'.mul_le_mul_of_nonneg_left _ _ scalar (hpq index) hscalar)
      (Q'.ge_of_eqv (coeff_pscale scalar q index)))

/-- Cauchy multiplication is monotone for nonnegative coefficient lists. -/
theorem coeffLe_pmul {p q r s : Poly}
    (hpq : CoeffLe p q) (hrs : CoeffLe r s)
    (hr : CoeffNonnegative r) (hq : CoeffNonnegative q) :
    CoeffLe (pmul p r) (pmul q s) := by
  intro degree
  have hterm : forall index : Nat,
      coeff p index * coeff r (degree - index) <=
        coeff q index * coeff s (degree - index) := by
    intro index
    exact Q'.le_trans' _
      (coeff q index * coeff r (degree - index)) _
      (Q'.mul_le_mul_of_nonneg_right
        (coeff p index) (coeff q index)
        (coeff r (degree - index))
        (hpq index) (hr (degree - index)))
      (Q'.mul_le_mul_of_nonneg_left
        (coeff r (degree - index)) (coeff s (degree - index))
        (coeff q index)
        (hrs (degree - index)) (hq index))
  exact Q'.le_trans' _ (cauchyCoeff p r degree) _
    (Q'.le_of_eqv (coeff_pmul_eqv_cauchyCoeff p r degree))
    (Q'.le_trans' _ (cauchyCoeff q s degree) _
      (ExpNeg.finSum_le_finSum_of_termwise _ _ hterm (degree + 1))
      (Q'.ge_of_eqv (coeff_pmul_eqv_cauchyCoeff q s degree)))

/-! ## 2. Monotonicity in the artanh stage -/

theorem coeffLe_artanhPartialPoly_succ (stage : Nat) :
    CoeffLe (artanhPartialPoly stage) (artanhPartialPoly (stage + 1)) := by
  change CoeffLe (artanhPartialPoly stage)
    (padd (artanhPartialPoly stage) (artanhTermPoly stage))
  exact coeffLe_padd_left_of_nonnegative _ _
    (coeffNonnegative_artanhTermPoly stage)

theorem coeffLe_positiveArtanhExponentPoly_succ (stage : Nat) :
    CoeffLe (positiveArtanhExponentPoly stage)
      (positiveArtanhExponentPoly (stage + 1)) := by
  unfold positiveArtanhExponentPoly
  exact coeffLe_padd
    (coeffLe_artanhPartialPoly_succ stage)
    (coeffLe_artanhPartialPoly_succ stage)

theorem coeffLe_positiveExpStepPoly_stage_succ (stage k : Nat) :
    CoeffLe
      (positiveExpStepPoly (positiveArtanhExponentPoly stage) k)
      (positiveExpStepPoly (positiveArtanhExponentPoly (stage + 1)) k) := by
  unfold positiveExpStepPoly
  exact coeffLe_pscale (Q'.invSucc k) (Q'.invSucc_nonneg k)
    (coeffLe_positiveArtanhExponentPoly_succ stage)

theorem coeffLe_positiveExpTermPoly_stage_succ (stage : Nat) :
    forall k : Nat,
    CoeffLe
      (positiveExpTermPoly (positiveArtanhExponentPoly stage) k)
      (positiveExpTermPoly (positiveArtanhExponentPoly (stage + 1)) k)
  | 0 => coeffLe_refl (pconst 1)
  | k + 1 =>
      coeffLe_pmul
        (coeffLe_positiveExpTermPoly_stage_succ stage k)
        (coeffLe_positiveExpStepPoly_stage_succ stage k)
        (coeffNonnegative_positiveExpStepPoly stage k)
        (coeffNonnegative_positiveExpTermPoly (stage + 1) k)

theorem coeffLe_positiveExpPartialPoly_stage_succ (stage : Nat) :
    forall inner : Nat,
    CoeffLe
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      (positiveExpPartialPoly
        (positiveArtanhExponentPoly (stage + 1)) inner)
  | 0 => coeffLe_refl []
  | inner + 1 =>
      coeffLe_padd
        (coeffLe_positiveExpPartialPoly_stage_succ stage inner)
        (coeffLe_positiveExpTermPoly_stage_succ stage inner)

theorem coeffLe_positiveExpPartialPoly_stage_add
    (stage inner : Nat) : forall extra : Nat,
    CoeffLe
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      (positiveExpPartialPoly
        (positiveArtanhExponentPoly (stage + extra)) inner)
  | 0 => coeffLe_refl _
  | extra + 1 => by
      exact coeffLe_trans
        (coeffLe_positiveExpPartialPoly_stage_add stage inner extra)
        (by
          rw [Nat.add_succ]
          exact coeffLe_positiveExpPartialPoly_stage_succ
            (stage + extra) inner)

/-! ## 3. Monotonicity in the Euler depth -/

theorem coeffLe_positiveExpPartialPoly_inner_succ (stage inner : Nat) :
    CoeffLe
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      (positiveExpPartialPoly
        (positiveArtanhExponentPoly stage) (inner + 1)) := by
  change CoeffLe
    (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
    (padd
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      (positiveExpTermPoly (positiveArtanhExponentPoly stage) inner))
  exact coeffLe_padd_left_of_nonnegative _ _
    (coeffNonnegative_positiveExpTermPoly stage inner)

theorem coeffLe_positiveExpPartialPoly_inner_add
    (stage inner : Nat) : forall extra : Nat,
    CoeffLe
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      (positiveExpPartialPoly
        (positiveArtanhExponentPoly stage) (inner + extra))
  | 0 => coeffLe_refl _
  | extra + 1 => by
      exact coeffLe_trans
        (coeffLe_positiveExpPartialPoly_inner_add stage inner extra)
        (by
          rw [Nat.add_succ]
          exact coeffLe_positiveExpPartialPoly_inner_succ
            stage (inner + extra))

/-! ## 4. Stable target comparison and the bound of two -/

/-- The closed target has magnitude at most two at every coefficient. -/
theorem abs_positiveArtanhFormalTargetCoeff_le_two : forall index : Nat,
    Q'.abs (positiveArtanhFormalTargetCoeff index) <= Q'.ofNat 2
  | 0 => by decide
  | index + 1 => by
      unfold positiveArtanhFormalTargetCoeff
      let sign : Q' := (-1 : Q') ^ (index + 1)
      exact Q'.le_trans' _ (Q'.abs sign + Q'.abs sign) _
        (ExpNeg.abs_add_le sign sign)
        (Q'.le_of_eqv
          (Q'.eqv_trans _ ((1 : Q') + 1) _
            (q_add_congr
              (abs_negOne_pow_eqv_one (index + 1))
              (abs_negOne_pow_eqv_one (index + 1)))
            (by decide)))

/-- Every finite positive companion coefficient is at most two.  The proof
enlarges both cutoffs beyond the requested index, uses nonnegative
coefficientwise monotonicity, and then invokes the already proved stabilized
reflected coefficient identity. -/
theorem coeff_positiveExpPartialPoly_le_two
    (stage inner index : Nat) :
    coeff
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      index <= Q'.ofNat 2 := by
  let stableStage := stage + (index + 1)
  let stableInner := inner + (index + 1)
  let initialCompanion :=
    positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner
  let stageCompanion :=
    positiveExpPartialPoly (positiveArtanhExponentPoly stableStage) inner
  let stableCompanion :=
    positiveExpPartialPoly
      (positiveArtanhExponentPoly stableStage) stableInner
  have hstage : CoeffLe initialCompanion stageCompanion := by
    exact coeffLe_positiveExpPartialPoly_stage_add
      stage inner (index + 1)
  have hinner : CoeffLe stageCompanion stableCompanion := by
    exact coeffLe_positiveExpPartialPoly_inner_add
      stableStage inner (index + 1)
  have hstableInner : index < stableInner := by
    dsimp [stableInner]
    omega
  have hstableStage : index < 2 * stableStage + 1 := by
    dsimp [stableStage]
    omega
  let reflected :=
    expPartialPoly (positiveArtanhExponentPoly stableStage) stableInner
  have hreflectedStable :
      (coeff reflected index).eqv
        (positiveArtanhEulerStableCoeff stableStage index) := by
    exact coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
      stableStage stableInner index hstableInner
  have hstableTarget :
      (positiveArtanhEulerStableCoeff stableStage index).eqv
        (positiveArtanhFormalTargetCoeff index) :=
    positiveArtanhEulerStableCoeff_eq_target_of_lt
      stableStage index hstableStage
  have hcompanionTarget :
      (coeff stableCompanion index).eqv
        (Q'.abs (positiveArtanhFormalTargetCoeff index)) := by
    exact Q'.eqv_trans _ (Q'.abs (coeff reflected index)) _
      (Q'.eqv_symm
        (abs_coeff_expPartialPoly_eqv_positiveCompanionCoeff
          stableStage stableInner index))
      (Q'.abs_eqv_congr
        (Q'.eqv_trans _ _ _ hreflectedStable hstableTarget))
  exact Q'.le_trans' _ (coeff stageCompanion index) _
    (hstage index)
    (Q'.le_trans' _ (coeff stableCompanion index) _
      (hinner index)
      (Q'.le_trans' _
        (Q'.abs (positiveArtanhFormalTargetCoeff index)) _
        (Q'.le_of_eqv hcompanionTarget)
        (abs_positiveArtanhFormalTargetCoeff_le_two index)))

/-- Canonical inhabitant of the former positive-companion scalar frontier. -/
def canonicalPositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler :
    PositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler where
  coefficientBound := coeff_positiveExpPartialPoly_le_two

end YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound.coeffLe_pmul
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound.coeffLe_positiveExpPartialPoly_stage_add
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound.coeffLe_positiveExpPartialPoly_inner_add
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound.abs_positiveArtanhFormalTargetCoeff_le_two
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound.coeff_positiveExpPartialPoly_le_two
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound.canonicalPositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler
