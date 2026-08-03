/-
# Rational-coefficient canonicalization under quaternion Haar

The reflective ring normalizer uses integer coefficients.  Conditional Haar
integration, however, introduces rational sphere moments before like terms
are combined.  This file supplies the corresponding finite canonicalizer
directly on `RatPoly`: it sorts monomials, combines equal monomials, and
deletes coefficients whose numerator is zero.

The proof is deliberately stated for an arbitrary monomial weight.  Exact
quaternion Haar, including an arbitrary polynomial multiplier, is then just
one specialization.  Thus a checked empty rational normal form is a genuine
coefficient-retaining zero certificate; no evaluation point or truncation of
the remaining quaternion blocks is used.
-/

import YMGap.Continuum.SU2QuaternionHaarRingNormalizer

namespace YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer

local infix:50 " ≈ " => Q'.eqv

/-- Insert one rational term into a monomial-sorted polynomial, combining an
equal key and deleting a coefficient exactly when its numerator vanishes. -/
def insertRatTerm
    (monomial : List Nat) (coefficient : Q') : RatPoly → RatPoly
  | [] =>
      if coefficient.num = 0 then [] else [(monomial, coefficient)]
  | (otherMonomial, otherCoefficient) :: rest =>
      if coefficient.num = 0 then
        (otherMonomial, otherCoefficient) :: rest
      else
        match monoCmp monomial otherMonomial with
        | .lt =>
            (monomial, coefficient) ::
              (otherMonomial, otherCoefficient) :: rest
        | .eq =>
            let combined := coefficient + otherCoefficient
            if combined.num = 0 then rest
            else (monomial, combined) :: rest
        | .gt =>
            (otherMonomial, otherCoefficient) ::
              insertRatTerm monomial coefficient rest

/-- Canonical rational polynomial: sorted, like terms combined, rational
zero representatives removed. -/
def canonRat (polynomial : RatPoly) : RatPoly :=
  polynomial.foldr
    (fun term accumulated =>
      insertRatTerm term.1 term.2 accumulated) []

/-- Evaluate a rational polynomial against an arbitrary monomial weight. -/
def ratWeightedSum
    (weight : List Nat → Q') : RatPoly → Q'
  | [] => 0
  | (monomial, coefficient) :: rest =>
      coefficient * weight monomial + ratWeightedSum weight rest

private theorem eqv_zero_of_num_eq_zero
    (coefficient : Q') (hzero : coefficient.num = 0) :
    coefficient ≈ 0 := by
  show coefficient.num * ((0 : Q').den : Int) =
    (0 : Q').num * (coefficient.den : Int)
  rw [hzero]
  change (0 : Int) * 1 = 0 * (coefficient.den : Int)
  simp

private theorem weighted_term_zero
    (weight : List Nat → Q')
    (monomial : List Nat) (coefficient : Q')
    (hzero : coefficient.num = 0) :
    coefficient * weight monomial ≈ 0 :=
  Q'.eqv_trans _ (0 * weight monomial) _
    (Q'.mul_eqv_congr_right _ _ _
      (eqv_zero_of_num_eq_zero coefficient hzero))
    (Q'.zero_mul_eqv _)

/-- Rational insertion preserves every monomial-weighted finite sum. -/
theorem ratWeightedSum_insertRatTerm
    (weight : List Nat → Q')
    (monomial : List Nat) (coefficient : Q') :
    ∀ polynomial : RatPoly,
      ratWeightedSum weight
          (insertRatTerm monomial coefficient polynomial) ≈
        coefficient * weight monomial +
          ratWeightedSum weight polynomial
  | [] => by
      unfold insertRatTerm
      by_cases hzero : coefficient.num = 0
      · rw [if_pos hzero]
        exact Q'.eqv_symm
          (Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr'
              (weighted_term_zero weight monomial coefficient hzero)
              (Q'.eqv_refl 0))
            (QPoly.q_zero_add_eqv 0))
      · rw [if_neg hzero]
        exact Q'.eqv_refl _
  | (otherMonomial, otherCoefficient) :: rest => by
      unfold insertRatTerm
      by_cases hzero : coefficient.num = 0
      · rw [if_pos hzero]
        change
          otherCoefficient * weight otherMonomial +
                ratWeightedSum weight rest ≈
            coefficient * weight monomial +
              (otherCoefficient * weight otherMonomial +
                ratWeightedSum weight rest)
        exact Q'.eqv_symm
          (Q'.eqv_trans _
            (0 +
              (otherCoefficient * weight otherMonomial +
                ratWeightedSum weight rest)) _
            (Q'.add_eqv_congr_right _ _ _
              (weighted_term_zero weight monomial coefficient hzero))
            (QPoly.q_zero_add_eqv _))
      · rw [if_neg hzero]
        cases hcompare : monoCmp monomial otherMonomial with
        | lt => exact Q'.eqv_refl _
        | eq =>
            have hmonomial : monomial = otherMonomial :=
              monoCmp_eq hcompare
            subst otherMonomial
            let combined := coefficient + otherCoefficient
            by_cases hcombined : combined.num = 0
            · rw [if_pos hcombined]
              change
                ratWeightedSum weight rest ≈
                  coefficient * weight monomial +
                    (otherCoefficient * weight monomial +
                      ratWeightedSum weight rest)
              refine Q'.eqv_trans _
                (0 + ratWeightedSum weight rest) _
                (Q'.eqv_symm (QPoly.q_zero_add_eqv _)) ?_
              refine Q'.eqv_trans _
                ((coefficient * weight monomial +
                    otherCoefficient * weight monomial) +
                  ratWeightedSum weight rest) _ ?_ ?_
              · refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
                exact Q'.eqv_symm
                  (Q'.eqv_trans _
                    ((coefficient + otherCoefficient) *
                      weight monomial) _
                    (Q'.eqv_symm
                      (Q'.add_mul_eqv coefficient otherCoefficient
                        (weight monomial)))
                    (weighted_term_zero weight monomial combined hcombined))
              · exact Q'.add_assoc_eqv _ _ _
            · rw [if_neg hcombined]
              change
                combined * weight monomial +
                    ratWeightedSum weight rest ≈
                  coefficient * weight monomial +
                    (otherCoefficient * weight monomial +
                      ratWeightedSum weight rest)
              exact Q'.eqv_trans _
                ((coefficient * weight monomial +
                    otherCoefficient * weight monomial) +
                  ratWeightedSum weight rest) _
                (Q'.add_eqv_congr_right _ _ _
                  (Q'.add_mul_eqv coefficient otherCoefficient
                    (weight monomial)))
                (Q'.add_assoc_eqv _ _ _)
        | gt =>
            change
              otherCoefficient * weight otherMonomial +
                    ratWeightedSum weight
                      (insertRatTerm monomial coefficient rest) ≈
                coefficient * weight monomial +
                  (otherCoefficient * weight otherMonomial +
                    ratWeightedSum weight rest)
            refine Q'.eqv_trans _
              (otherCoefficient * weight otherMonomial +
                (coefficient * weight monomial +
                  ratWeightedSum weight rest)) _
              (Q'.add_eqv_congr_left _ _ _
                (ratWeightedSum_insertRatTerm
                  weight monomial coefficient rest)) ?_
            refine Q'.eqv_trans _
              ((otherCoefficient * weight otherMonomial +
                  coefficient * weight monomial) +
                ratWeightedSum weight rest) _
              (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
            refine Q'.eqv_trans _
              ((coefficient * weight monomial +
                  otherCoefficient * weight otherMonomial) +
                ratWeightedSum weight rest) _
              (Q'.add_eqv_congr_right _ _ _
                (Q'.add_comm_eqv _ _)) ?_
            exact Q'.add_assoc_eqv _ _ _

/-- Canonicalization preserves every rational monomial-weighted sum. -/
theorem ratWeightedSum_canon
    (weight : List Nat → Q') :
    ∀ polynomial : RatPoly,
      ratWeightedSum weight (canonRat polynomial) ≈
        ratWeightedSum weight polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        ratWeightedSum weight
            (insertRatTerm term.1 term.2 (canonRat rest)) ≈
          term.2 * weight term.1 + ratWeightedSum weight rest
      exact Q'.eqv_trans _
        (term.2 * weight term.1 +
          ratWeightedSum weight (canonRat rest)) _
        (ratWeightedSum_insertRatTerm
          weight term.1 term.2 (canonRat rest))
        (Q'.add_eqv_congr_left _ _ _
          (ratWeightedSum_canon weight rest))

private theorem quaternionHaarRow_scale
    (blocks : Nat) (monomial : List Nat) (coefficient : Q') :
    ∀ right : RatPoly,
      quaternionHaarRow blocks (monomial, coefficient) right ≈
        coefficient *
          quaternionHaarRow blocks (monomial, 1) right
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | other :: remaining => by
      change
        (coefficient * other.2) *
              quaternionHaarMono blocks
                (monoMul monomial other.1) +
            quaternionHaarRow blocks
              (monomial, coefficient) remaining ≈
          coefficient *
            ((1 * other.2) *
                quaternionHaarMono blocks
                  (monoMul monomial other.1) +
              quaternionHaarRow blocks
                (monomial, 1) remaining)
      refine Q'.eqv_trans _
        (coefficient *
              ((1 * other.2) *
                quaternionHaarMono blocks
                  (monoMul monomial other.1)) +
            coefficient *
              quaternionHaarRow blocks
                (monomial, 1) remaining) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _
            (coefficient *
              (other.2 *
                quaternionHaarMono blocks
                  (monoMul monomial other.1))) _
            (Q'.mul_assoc_eqv _ _ _)
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.eqv_symm
                  (Q'.one_mul_eqv other.2)))))
          (quaternionHaarRow_scale
            blocks monomial coefficient remaining)
      · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

private theorem quaternionHaarBilinear_eq_ratWeightedSum
    (blocks : Nat) (right : RatPoly) :
    ∀ polynomial : RatPoly,
      quaternionHaarBilinear blocks polynomial right ≈
        ratWeightedSum
          (fun monomial =>
            quaternionHaarRow blocks (monomial, 1) right)
          polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        quaternionHaarRow blocks term right +
              quaternionHaarBilinear blocks rest right ≈
          term.2 *
                quaternionHaarRow blocks (term.1, 1) right +
              ratWeightedSum
                (fun monomial =>
                  quaternionHaarRow blocks (monomial, 1) right)
                rest
      exact Q'.add_eqv_congr'
        (quaternionHaarRow_scale
          blocks term.1 term.2 right)
        (quaternionHaarBilinear_eq_ratWeightedSum
          blocks right rest)

/-- Rational canonicalization is invisible to exact product Haar after an
arbitrary polynomial multiplier. -/
theorem quaternionHaar_canonRat_mul
    (blocks : Nat) (polynomial right : RatPoly) :
    quaternionHaar blocks
        (polyMul (canonRat polynomial) right) ≈
      quaternionHaar blocks (polyMul polynomial right) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks (canonRat polynomial) right) _
    (quaternionHaar_polyMul blocks (canonRat polynomial) right) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum
      (fun monomial =>
        quaternionHaarRow blocks (monomial, 1) right)
      (canonRat polynomial)) _
    (quaternionHaarBilinear_eq_ratWeightedSum
      blocks right (canonRat polynomial)) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum
      (fun monomial =>
        quaternionHaarRow blocks (monomial, 1) right)
      polynomial) _
    (ratWeightedSum_canon _ polynomial) ?_
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks polynomial right) _
    (Q'.eqv_symm
      (quaternionHaarBilinear_eq_ratWeightedSum
        blocks right polynomial)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul blocks polynomial right)

/-- An empty checked rational normal form annihilates the polynomial under
Haar even in the presence of an arbitrary multiplier. -/
theorem quaternionHaar_mul_eq_zero_of_canonRat_eq_nil
    (blocks : Nat) (polynomial multiplier : RatPoly)
    (hzero : canonRat polynomial = []) :
    quaternionHaar blocks (polyMul polynomial multiplier) ≈ 0 := by
  have hcanon := quaternionHaar_canonRat_mul
    blocks polynomial multiplier
  rw [hzero] at hcanon
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcanon) (Q'.eqv_refl 0)

end YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

#print axioms YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer.ratWeightedSum_canon
#print axioms YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer.quaternionHaar_canonRat_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer.quaternionHaar_mul_eq_zero_of_canonRat_eq_nil
