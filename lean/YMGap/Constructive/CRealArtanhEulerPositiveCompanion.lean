/-
# Nonnegative companion for the finite reflected artanh/Euler polynomial

The scalar frontier asks for a uniform magnitude bound on coefficients of the
finite polynomial representing `exp (-2 * artanh z)`.  Substitution `z -> -z`
turns that reflected polynomial into the finite positive exponential of the
same odd artanh exponent.  This module constructs that companion on the same
finite coefficient-list carrier, proves the exact recoding, and proves every
companion coefficient nonnegative.

No infinite series, coefficient normalization, or classical choice is used.
-/

import YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
import YMGap.Constructive.QPolyAlternate

namespace YMGap.Constructive.CRealArtanhEulerPositiveCompanion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyAlternate
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor

/-! ## 1. Alternating recoding of the odd artanh exponent -/

/-- Even powers of the rational sign `-1` are rationally equivalent to one. -/
theorem negOne_pow_two_mul_eqv_one : forall k : Nat,
    (((-1 : Q') ^ (2 * k))).eqv 1
  | 0 => Q'.eqv_refl 1
  | k + 1 => by
      have hindex : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [hindex, Q'.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _
        ((-1 : Q') * ((-1 : Q') * (1 : Q'))) _ ?_ ?_
      exact Q'.mul_eqv_congr_left (-1) _ _
        (Q'.mul_eqv_congr_left (-1) _ _
          (negOne_pow_two_mul_eqv_one k))
      decide

/-- Odd powers of the rational sign `-1` are rationally equivalent to `-1`. -/
theorem negOne_pow_two_mul_add_one_eqv_negOne (k : Nat) :
    (((-1 : Q') ^ (2 * k + 1))).eqv (-1 : Q') := by
  rw [Q'.pow_succ]
  exact Q'.eqv_trans _ ((-1 : Q') * 1) _
    (Q'.mul_eqv_congr_left (-1) _ _
      (negOne_pow_two_mul_eqv_one k))
    (Q'.mul_one_eqv (-1))

/-- Alternating substitution negates every positive odd monomial. -/
theorem alternate_ppow_pvar_odd (k : Nat) :
    CoeffEqv
      (alternate (ppow pvar (2 * k + 1)))
      (pneg (ppow pvar (2 * k + 1))) := by
  intro index
  let monomial := ppow pvar (2 * k + 1)
  refine Q'.eqv_trans _
    (((-1 : Q') ^ index) * coeff monomial index) _
    (coeff_alternate monomial index) ?_
  by_cases heq : index = 2 * k + 1
  · subst index
    exact Q'.eqv_trans _
      ((-1 : Q') * coeff monomial (2 * k + 1)) _
      (Q'.mul_eqv_congr_right _ _ _
        (negOne_pow_two_mul_add_one_eqv_negOne k))
      (Q'.eqv_symm (coeff_pneg monomial (2 * k + 1)))
  · have hzero : (coeff monomial index).eqv 0 :=
      Q'.eqv_trans _
        (if index = 2 * k + 1 then (1 : Q') else 0) _
        (coeff_ppow_pvar (2 * k + 1) index)
        (by rw [if_neg heq]; exact Q'.eqv_refl 0)
    have hleft :
        (((-1 : Q') ^ index) * coeff monomial index).eqv 0 :=
      Q'.eqv_trans _ (((-1 : Q') ^ index) * 0) _
        (Q'.mul_eqv_congr_left ((-1 : Q') ^ index) _ 0 hzero)
        (q_mul_zero ((-1 : Q') ^ index))
    have hright : (coeff (pneg monomial) index).eqv 0 :=
      Q'.eqv_trans _ ((-1 : Q') * coeff monomial index) _
        (coeff_pneg monomial index)
        (Q'.eqv_trans _ ((-1 : Q') * 0) _
          (Q'.mul_eqv_congr_left (-1) _ 0 hzero)
          (q_mul_zero (-1)))
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

/-- Nested coefficient scalings commute up to padded rational equivalence. -/
theorem coeffEqv_pscale_comm (a b : Q') (p : Poly) :
    CoeffEqv (pscale a (pscale b p)) (pscale b (pscale a p)) :=
  CoeffEqv.trans
    (coeffEqv_pscale_comp a b p)
    (CoeffEqv.trans
      (coeffEqv_pscale_scalar (Q'.mul_comm_eqv a b) p)
      (CoeffEqv.symm (coeffEqv_pscale_comp b a p)))

/-- Alternating substitution negates one finite artanh summand. -/
theorem alternate_artanhTermPoly (k : Nat) :
    CoeffEqv (alternate (artanhTermPoly k))
      (pneg (artanhTermPoly k)) := by
  unfold artanhTermPoly pneg
  exact CoeffEqv.trans
    (alternate_pscale (CRealLog.recipOdd k)
      (ppow pvar (2 * k + 1)))
    (CoeffEqv.trans
      (CoeffEqv.pscale (CRealLog.recipOdd k)
        (alternate_ppow_pvar_odd k))
      (coeffEqv_pscale_comm (CRealLog.recipOdd k) (-1)
        (ppow pvar (2 * k + 1))))

/-- Alternating substitution negates the complete finite artanh sum. -/
theorem alternate_artanhPartialPoly : forall stage : Nat,
    CoeffEqv (alternate (artanhPartialPoly stage))
      (pneg (artanhPartialPoly stage))
  | 0 => CoeffEqv.refl []
  | stage + 1 => by
      exact CoeffEqv.trans
        (alternate_padd (artanhPartialPoly stage) (artanhTermPoly stage))
        (CoeffEqv.trans
          (CoeffEqv.padd
            (alternate_artanhPartialPoly stage)
            (alternate_artanhTermPoly stage))
          (CoeffEqv.symm
            (coeffEqv_pneg_padd
              (artanhPartialPoly stage) (artanhTermPoly stage))))

/-- The doubled finite artanh exponent is odd coefficientwise. -/
theorem alternate_positiveArtanhExponentPoly (stage : Nat) :
    CoeffEqv (alternate (positiveArtanhExponentPoly stage))
      (pneg (positiveArtanhExponentPoly stage)) := by
  unfold positiveArtanhExponentPoly
  exact CoeffEqv.trans
    (alternate_padd (artanhPartialPoly stage) (artanhPartialPoly stage))
    (CoeffEqv.trans
      (CoeffEqv.padd
        (alternate_artanhPartialPoly stage)
        (alternate_artanhPartialPoly stage))
      (CoeffEqv.symm
        (coeffEqv_pneg_padd
          (artanhPartialPoly stage) (artanhPartialPoly stage))))

/-- Alternating substitution of the negated odd exponent restores it. -/
theorem alternate_pneg_positiveArtanhExponentPoly (stage : Nat) :
    CoeffEqv
      (alternate (pneg (positiveArtanhExponentPoly stage)))
      (positiveArtanhExponentPoly stage) := by
  exact CoeffEqv.trans
    (alternate_pscale (-1) (positiveArtanhExponentPoly stage))
    (CoeffEqv.trans
      (CoeffEqv.pneg (alternate_positiveArtanhExponentPoly stage))
      (coeffEqv_pneg_pneg (positiveArtanhExponentPoly stage)))

/-! ## 2. The finite positive Euler companion -/

/-- Positive exponential recursion step `exponent/(k+1)`. -/
def positiveExpStepPoly (exponent : Poly) (k : Nat) : Poly :=
  pscale (Q'.invSucc k) exponent

/-- One term of the finite positive exponential polynomial. -/
def positiveExpTermPoly (exponent : Poly) : Nat -> Poly
  | 0 => pconst 1
  | k + 1 =>
      pmul (positiveExpTermPoly exponent k) (positiveExpStepPoly exponent k)

/-- Partial sum of the finite positive exponential polynomial. -/
def positiveExpPartialPoly (exponent : Poly) : Nat -> Poly
  | 0 => []
  | inner + 1 => padd (positiveExpPartialPoly exponent inner)
      (positiveExpTermPoly exponent inner)

/-- Alternating substitution sends each reflected step to the positive step. -/
theorem alternate_expStepPoly_positiveArtanh (stage k : Nat) :
    CoeffEqv
      (alternate (expStepPoly (positiveArtanhExponentPoly stage) k))
      (positiveExpStepPoly (positiveArtanhExponentPoly stage) k) := by
  unfold expStepPoly positiveExpStepPoly
  exact CoeffEqv.trans
    (alternate_pscale (Q'.invSucc k)
      (pneg (positiveArtanhExponentPoly stage)))
    (CoeffEqv.pscale (Q'.invSucc k)
      (alternate_pneg_positiveArtanhExponentPoly stage))

/-- Alternating substitution sends a reflected Euler term to its positive
companion term. -/
theorem alternate_expTermPoly_positiveArtanh (stage : Nat) : forall k : Nat,
    CoeffEqv
      (alternate (expTermPoly (positiveArtanhExponentPoly stage) k))
      (positiveExpTermPoly (positiveArtanhExponentPoly stage) k)
  | 0 => by
      intro index
      cases index with
      | zero => exact Q'.eqv_refl 1
      | succ index => exact Q'.eqv_refl 0
  | k + 1 =>
      CoeffEqv.trans
        (alternate_pmul
          (expTermPoly (positiveArtanhExponentPoly stage) k)
          (expStepPoly (positiveArtanhExponentPoly stage) k))
        (CoeffEqv.pmul
          (alternate_expTermPoly_positiveArtanh stage k)
          (alternate_expStepPoly_positiveArtanh stage k))

/-- Exact finite recoding of the reflected Euler partial sum. -/
theorem alternate_expPartialPoly_positiveArtanh (stage : Nat) :
    forall inner : Nat,
    CoeffEqv
      (alternate
        (expPartialPoly (positiveArtanhExponentPoly stage) inner))
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
  | 0 => CoeffEqv.refl []
  | inner + 1 =>
      CoeffEqv.trans
        (alternate_padd
          (expPartialPoly (positiveArtanhExponentPoly stage) inner)
          (expTermPoly (positiveArtanhExponentPoly stage) inner))
        (CoeffEqv.padd
          (alternate_expPartialPoly_positiveArtanh stage inner)
          (alternate_expTermPoly_positiveArtanh stage inner))

/-! ## 3. Coefficientwise nonnegativity -/

/-- Every padded coefficient of a finite polynomial is nonnegative. -/
def CoeffNonnegative (p : Poly) : Prop :=
  forall index : Nat, (0 : Q') <= coeff p index

theorem coeffNonnegative_empty : CoeffNonnegative [] :=
  fun index => by
    change (0 : Q') <= 0
    exact Q'.le_refl' 0

theorem coeffNonnegative_pconst {c : Q'} (hc : (0 : Q') <= c) :
    CoeffNonnegative (pconst c) := by
  intro index
  cases index with
  | zero => exact hc
  | succ index =>
      change (0 : Q') <= 0
      exact Q'.le_refl' 0

theorem coeffNonnegative_padd {p q : Poly}
    (hp : CoeffNonnegative p) (hq : CoeffNonnegative q) :
    CoeffNonnegative (padd p q) := by
  intro index
  exact Q'.le_trans' _ (coeff p index + coeff q index) _
    (Q'.zero_le_add _ _ (hp index) (hq index))
    (Q'.le_of_eqv (Q'.eqv_symm (coeff_padd index p q)))

theorem coeffNonnegative_pscale {k : Q'} {p : Poly}
    (hk : (0 : Q') <= k) (hp : CoeffNonnegative p) :
    CoeffNonnegative (pscale k p) := by
  intro index
  exact Q'.le_trans' _ (k * coeff p index) _
    (Q'.mul_nonneg _ _ hk (hp index))
    (Q'.le_of_eqv (Q'.eqv_symm (coeff_pscale k p index)))

theorem finSum_nonnegative (f : Nat -> Q')
    (hf : forall index : Nat, (0 : Q') <= f index) :
    forall count : Nat, (0 : Q') <= finSum f count
  | 0 => Q'.le_refl' 0
  | count + 1 =>
      Q'.zero_le_add _ _
        (finSum_nonnegative f hf count) (hf count)

theorem coeffNonnegative_pmul {p q : Poly}
    (hp : CoeffNonnegative p) (hq : CoeffNonnegative q) :
    CoeffNonnegative (pmul p q) := by
  intro degree
  have hsum : (0 : Q') <= cauchyCoeff p q degree :=
    finSum_nonnegative
      (fun index => coeff p index * coeff q (degree - index))
      (fun index => Q'.mul_nonneg _ _
        (hp index) (hq (degree - index)))
      (degree + 1)
  exact Q'.le_trans' _ (cauchyCoeff p q degree) _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm (coeff_pmul_eqv_cauchyCoeff p q degree)))

theorem coeffNonnegative_ppow_pvar (power : Nat) :
    CoeffNonnegative (ppow pvar power) := by
  intro index
  by_cases heq : index = power
  · exact Q'.le_trans' _ 1 _ Q'.zero_le_one
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.eqv_trans _
            (if index = power then (1 : Q') else 0) _
            (coeff_ppow_pvar power index)
            (by rw [if_pos heq]; exact Q'.eqv_refl 1))))
  · exact Q'.le_trans' _ 0 _ (by decide)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.eqv_trans _
            (if index = power then (1 : Q') else 0) _
            (coeff_ppow_pvar power index)
            (by rw [if_neg heq]; exact Q'.eqv_refl 0))))

theorem coeffNonnegative_artanhTermPoly (k : Nat) :
    CoeffNonnegative (artanhTermPoly k) := by
  unfold artanhTermPoly
  exact coeffNonnegative_pscale
    (CRealLog.recipOdd_nonneg k)
    (coeffNonnegative_ppow_pvar (2 * k + 1))

theorem coeffNonnegative_artanhPartialPoly : forall stage : Nat,
    CoeffNonnegative (artanhPartialPoly stage)
  | 0 => coeffNonnegative_empty
  | stage + 1 => coeffNonnegative_padd
      (coeffNonnegative_artanhPartialPoly stage)
      (coeffNonnegative_artanhTermPoly stage)

theorem coeffNonnegative_positiveArtanhExponentPoly (stage : Nat) :
    CoeffNonnegative (positiveArtanhExponentPoly stage) := by
  unfold positiveArtanhExponentPoly
  exact coeffNonnegative_padd
    (coeffNonnegative_artanhPartialPoly stage)
    (coeffNonnegative_artanhPartialPoly stage)

theorem coeffNonnegative_positiveExpStepPoly (stage k : Nat) :
    CoeffNonnegative
      (positiveExpStepPoly (positiveArtanhExponentPoly stage) k) := by
  unfold positiveExpStepPoly
  exact coeffNonnegative_pscale (Q'.invSucc_nonneg k)
    (coeffNonnegative_positiveArtanhExponentPoly stage)

theorem coeffNonnegative_positiveExpTermPoly (stage : Nat) : forall k : Nat,
    CoeffNonnegative
      (positiveExpTermPoly (positiveArtanhExponentPoly stage) k)
  | 0 => coeffNonnegative_pconst Q'.zero_le_one
  | k + 1 => coeffNonnegative_pmul
      (coeffNonnegative_positiveExpTermPoly stage k)
      (coeffNonnegative_positiveExpStepPoly stage k)

/-- Every coefficient of the finite positive Euler companion is nonnegative. -/
theorem coeffNonnegative_positiveExpPartialPoly (stage : Nat) :
    forall inner : Nat,
    CoeffNonnegative
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
  | 0 => coeffNonnegative_empty
  | inner + 1 => coeffNonnegative_padd
      (coeffNonnegative_positiveExpPartialPoly stage inner)
      (coeffNonnegative_positiveExpTermPoly stage inner)

/-! ## 4. Magnitudes of reflected coefficients are companion coefficients -/

/-- Multiplication by any power of the sign `-1` preserves rational absolute
value. -/
theorem abs_negOne_pow_mul_eqv_abs (a : Q') : forall index : Nat,
    (Q'.abs (((-1 : Q') ^ index) * a)).eqv (Q'.abs a)
  | 0 => Q'.abs_eqv_congr (Q'.one_mul_eqv a)
  | index + 1 => by
      rw [Q'.pow_succ]
      exact Q'.eqv_trans _
        (Q'.abs ((-1 : Q') * (((-1 : Q') ^ index) * a))) _
        (Q'.abs_eqv_congr
          (Q'.mul_assoc_eqv (-1) ((-1 : Q') ^ index) a))
        (Q'.eqv_trans _
          (Q'.abs (- (((-1 : Q') ^ index) * a))) _
          (Q'.abs_eqv_congr
            (negOne_mul_eqv_neg (((-1 : Q') ^ index) * a)))
          (Q'.eqv_trans _
            (Q'.abs (((-1 : Q') ^ index) * a)) _
            (Q'.abs_neg' (((-1 : Q') ^ index) * a))
            (abs_negOne_pow_mul_eqv_abs a index)))

/-- The absolute value of each reflected finite-Euler coefficient is exactly
the corresponding nonnegative companion coefficient. -/
theorem abs_coeff_expPartialPoly_eqv_positiveCompanionCoeff
    (stage inner index : Nat) :
    (Q'.abs
      (coeff (expPartialPoly (positiveArtanhExponentPoly stage) inner)
        index)).eqv
      (coeff
        (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
        index) := by
  let reflected :=
    expPartialPoly (positiveArtanhExponentPoly stage) inner
  let companion :=
    positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner
  have hrecoded :
      (coeff (alternate reflected) index).eqv
        (coeff companion index) :=
    alternate_expPartialPoly_positiveArtanh stage inner index
  have hsign :
      (coeff (alternate reflected) index).eqv
        (((-1 : Q') ^ index) * coeff reflected index) :=
    coeff_alternate reflected index
  have hreflectedToAlternate :
      (Q'.abs (coeff reflected index)).eqv
        (Q'.abs (coeff (alternate reflected) index)) :=
    Q'.eqv_trans _
      (Q'.abs (((-1 : Q') ^ index) * coeff reflected index)) _
      (Q'.eqv_symm
        (abs_negOne_pow_mul_eqv_abs (coeff reflected index) index))
      (Q'.abs_eqv_congr (Q'.eqv_symm hsign))
  have hcompanionNonnegative :
      (0 : Q') <= coeff companion index :=
    coeffNonnegative_positiveExpPartialPoly stage inner index
  exact Q'.eqv_trans _
    (Q'.abs (coeff (alternate reflected) index)) _
    hreflectedToAlternate
    (Q'.eqv_trans _
      (Q'.abs (coeff companion index)) _
      (Q'.abs_eqv_congr hrecoded)
      (Q'.eqv_of_eq
        (ExpNeg.abs_of_nonneg hcompanionNonnegative)))

/-! ## 5. Contracted public scalar frontier -/

/-- The remaining scalar obligation after alternating recoding: every
coefficient of every finite positive companion is at most two. -/
structure PositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler :
    Type 1 where
  coefficientBound : forall (stage inner index : Nat),
    coeff
      (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
      index <= Q'.ofNat 2

/-- A uniform positive-companion upper bound supplies the former reflected
coefficient-magnitude compiler at every direct-window input. -/
def positiveWindowArtanhEulerPolynomialCoefficientMagnitudeCompilerOfPositiveCompanion
    (compiler :
      PositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientMagnitudeCompiler where
  evaluate z hz hzb := {
    coefficientBound := fun epsilon hepsilon index => by
      let stage :=
        CRealArtanhEulerRatio.positiveArtanhEulerAnchorStage epsilon
      let inner :=
        CRealArtanhEulerRatio.positiveArtanhEulerAnchorPivot z epsilon
      exact Q'.le_trans' _
        (coeff
          (positiveExpPartialPoly (positiveArtanhExponentPoly stage) inner)
          index) _
        (Q'.le_of_eqv
          (abs_coeff_expPartialPoly_eqv_positiveCompanionCoeff
            stage inner index))
        (compiler.coefficientBound stage inner index)
  }

end YMGap.Constructive.CRealArtanhEulerPositiveCompanion

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanion.alternate_positiveArtanhExponentPoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanion.alternate_expPartialPoly_positiveArtanh
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanion.coeffNonnegative_pmul
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanion.coeffNonnegative_positiveExpPartialPoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanion.abs_coeff_expPartialPoly_eqv_positiveCompanionCoeff
#print axioms
  YMGap.Constructive.CRealArtanhEulerPositiveCompanion.positiveWindowArtanhEulerPolynomialCoefficientMagnitudeCompilerOfPositiveCompanion
