/-
# Ring-normalized certificates under arbitrary-product quaternion Haar

`RingNormaliser.normalize` combines equal monomials, whereas the geometric
BF4 carrier deliberately keeps the raw expansion of a polynomial.  This file
proves that exact product Haar, even after multiplication by an arbitrary
polynomial, is insensitive to that canonicalization.

The key argument is deliberately more general than Haar.  Insertion into a
canonical raw polynomial preserves every rational linear functional of its
monomials.  Taking the monomial weight to be the exact Haar row against a
fixed right factor gives the desired bridge.  Consequently a checked
reflective ring identity can be transported directly into an integrated
polynomial identity.

No choice, excluded middle beyond decidable data, or external algebra system
is used.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

namespace YMGap.Continuum.SU2QuaternionHaarRingNormalizer

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical insertion preserves arbitrary monomial weights -/

/-- A finite integer polynomial evaluated by an arbitrary rational monomial
weight.  No multiplicativity is assumed of `weight`. -/
def rawWeightedSum
    (weight : List Nat → Q') : RawPoly → Q'
  | [] => 0
  | (monomial, coefficient) :: rest =>
      Q'.ofInt coefficient * weight monomial +
        rawWeightedSum weight rest

private theorem rawWeightedSum_insertTerm
    (weight : List Nat → Q') (monomial : List Nat)
    (coefficient : Int) :
    ∀ polynomial : RawPoly,
      rawWeightedSum weight
          (insertTerm monomial coefficient polynomial) ≈
        Q'.ofInt coefficient * weight monomial +
          rawWeightedSum weight polynomial
  | [] => by
      by_cases hzero : coefficient = 0
      · subst hzero
        simp only [insertTerm, rawWeightedSum]
        exact Q'.eqv_symm
          (Q'.eqv_trans _ _ _
            (QPoly.q_add_zero_eqv _)
            (by
              exact
                (Q'.zero_mul_eqv
                  (weight monomial))))
      · simp only [insertTerm, if_neg hzero, rawWeightedSum]
        exact Q'.eqv_refl _
  | (otherMonomial, otherCoefficient) :: rest => by
      by_cases hzero : coefficient = 0
      · subst hzero
        simp only [insertTerm, rawWeightedSum]
        refine Q'.eqv_symm ?_
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.zero_mul_eqv
              (weight monomial)))
          (QPoly.q_zero_add_eqv _)
      · simp only [insertTerm, if_neg hzero]
        cases hcompare :
            monoCmp monomial otherMonomial with
        | lt =>
            simp only [rawWeightedSum]
            exact Q'.eqv_refl _
        | eq =>
            have hmonomial :
                monomial = otherMonomial :=
              monoCmp_eq hcompare
            subst hmonomial
            by_cases hcancel :
                coefficient + otherCoefficient = 0
            · simp only [hcancel,
                rawWeightedSum]
              refine Q'.eqv_symm ?_
              refine Q'.eqv_trans _
                ((Q'.ofInt coefficient *
                      weight monomial +
                    Q'.ofInt otherCoefficient *
                      weight monomial) +
                  rawWeightedSum weight rest) _ ?_ ?_
              · exact Q'.eqv_symm
                  (Q'.add_assoc_eqv _ _ _)
              · refine Q'.eqv_trans _
                  (Q'.ofInt
                        (coefficient + otherCoefficient) *
                      weight monomial +
                    rawWeightedSum weight rest) _ ?_ ?_
                · exact Q'.add_eqv_congr_right _ _ _
                    (Q'.eqv_symm
                      (Q'.eqv_trans _ _ _
                        (Q'.mul_eqv_congr_right _ _ _
                          (ofInt_add coefficient
                            otherCoefficient))
                        (Q'.add_mul_eqv
                          (Q'.ofInt coefficient)
                          (Q'.ofInt otherCoefficient)
                          (weight monomial))))
                · rw [hcancel]
                  exact Q'.eqv_trans _ _ _
                    (Q'.add_eqv_congr_right _ _ _
                      (Q'.zero_mul_eqv
                        (weight monomial)))
                    (QPoly.q_zero_add_eqv _)
            · simp only [hcancel, rawWeightedSum]
              refine Q'.eqv_trans _
                ((Q'.ofInt coefficient +
                    Q'.ofInt otherCoefficient) *
                      weight monomial +
                  rawWeightedSum weight rest) _ ?_ ?_
              · exact Q'.add_eqv_congr_right _ _ _
                  (Q'.mul_eqv_congr_right _ _ _
                    (ofInt_add coefficient
                      otherCoefficient))
              · refine Q'.eqv_trans _
                  ((Q'.ofInt coefficient *
                        weight monomial +
                      Q'.ofInt otherCoefficient *
                        weight monomial) +
                    rawWeightedSum weight rest) _
                  (Q'.add_eqv_congr_right _ _ _
                    (Q'.add_mul_eqv
                      (Q'.ofInt coefficient)
                      (Q'.ofInt otherCoefficient)
                      (weight monomial)))
                  ?_
                exact Q'.add_assoc_eqv _ _ _
        | gt =>
            simp only [rawWeightedSum]
            refine Q'.eqv_trans _
              (Q'.ofInt otherCoefficient *
                    weight otherMonomial +
                (Q'.ofInt coefficient *
                      weight monomial +
                  rawWeightedSum weight rest)) _ ?_ ?_
            · exact Q'.add_eqv_congr_left _ _ _
                (rawWeightedSum_insertTerm
                  weight monomial coefficient rest)
            · refine Q'.eqv_trans _
                ((Q'.ofInt otherCoefficient *
                        weight otherMonomial +
                      Q'.ofInt coefficient *
                        weight monomial) +
                    rawWeightedSum weight rest) _ ?_ ?_
              · exact Q'.eqv_symm
                  (Q'.add_assoc_eqv _ _ _)
              · refine Q'.eqv_trans _
                  ((Q'.ofInt coefficient *
                          weight monomial +
                        Q'.ofInt otherCoefficient *
                          weight otherMonomial) +
                    rawWeightedSum weight rest) _ ?_ ?_
                · exact Q'.add_eqv_congr_right _ _ _
                    (Q'.add_comm_eqv _ _)
                · exact Q'.add_assoc_eqv _ _ _

/-- Canonicalization preserves every finite rational monomial-weighted sum. -/
theorem rawWeightedSum_canon
    (weight : List Nat → Q') :
    ∀ polynomial : RawPoly,
      rawWeightedSum weight (canon polynomial) ≈
        rawWeightedSum weight polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        rawWeightedSum weight
            (insertTerm term.1 term.2
              (canon rest)) ≈
          Q'.ofInt term.2 * weight term.1 +
            rawWeightedSum weight rest
      exact Q'.eqv_trans _ _ _
        (rawWeightedSum_insertTerm
          weight term.1 term.2 (canon rest))
        (Q'.add_eqv_congr_left _ _ _
          (rawWeightedSum_canon weight rest))

/-! ## 2. Exact Haar realization of the arbitrary weight -/

theorem quaternionHaarRow_ofInt_scale
    (blocks : Nat) (monomial : List Nat)
    (coefficient : Int) :
    ∀ right : RatPoly,
      quaternionHaarRow blocks
          (monomial, Q'.ofInt coefficient) right ≈
        Q'.ofInt coefficient *
          quaternionHaarRow blocks
            (monomial, 1) right
  | [] =>
      Q'.eqv_symm
        (Q'.mul_zero_eqv
          (Q'.ofInt coefficient))
  | term :: rest => by
      change
        (Q'.ofInt coefficient * term.2) *
              quaternionHaarMono blocks
                (monoMul monomial term.1) +
            quaternionHaarRow blocks
              (monomial, Q'.ofInt coefficient)
              rest ≈
          Q'.ofInt coefficient *
            ((1 * term.2) *
                quaternionHaarMono blocks
                  (monoMul monomial term.1) +
              quaternionHaarRow blocks
                (monomial, 1) rest)
      refine Q'.eqv_trans _
        (Q'.ofInt coefficient *
              ((1 * term.2) *
                quaternionHaarMono blocks
                  (monoMul monomial term.1)) +
            Q'.ofInt coefficient *
              quaternionHaarRow blocks
                (monomial, 1) rest) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv _ _ _)
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.eqv_symm
                  (Q'.one_mul_eqv term.2)))))
          (quaternionHaarRow_ofInt_scale
            blocks monomial coefficient rest)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv _ _ _)

private theorem quaternionHaarBilinear_rawToRatPoly
    (blocks : Nat) (right : RatPoly) :
    ∀ polynomial : RawPoly,
      quaternionHaarBilinear blocks
          (rawToRatPoly polynomial) right ≈
        rawWeightedSum
          (fun monomial =>
            quaternionHaarRow blocks
              (monomial, 1) right)
          polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        quaternionHaarRow blocks
              (term.1, Q'.ofInt term.2) right +
            quaternionHaarBilinear blocks
              (rawToRatPoly rest) right ≈
          Q'.ofInt term.2 *
              quaternionHaarRow blocks
                (term.1, 1) right +
            rawWeightedSum
              (fun monomial =>
                quaternionHaarRow blocks
                  (monomial, 1) right)
              rest
      exact QPoly.q_add_congr
        (quaternionHaarRow_ofInt_scale
          blocks term.1 term.2 right)
        (quaternionHaarBilinear_rawToRatPoly
          blocks right rest)

/-- Canonicalizing an integer raw polynomial is invisible to exact Haar
after multiplication by an arbitrary rational polynomial. -/
theorem quaternionHaar_raw_canon_mul
    (blocks : Nat) (polynomial : RawPoly)
    (right : RatPoly) :
    quaternionHaar blocks
        (polyMul
          (rawToRatPoly (canon polynomial)) right) ≈
      quaternionHaar blocks
        (polyMul
          (rawToRatPoly polynomial) right) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks
      (rawToRatPoly (canon polynomial)) right) _
    (quaternionHaar_polyMul
      blocks (rawToRatPoly (canon polynomial))
      right) ?_
  refine Q'.eqv_trans _
    (rawWeightedSum
      (fun monomial =>
        quaternionHaarRow blocks
          (monomial, 1) right)
      (canon polynomial)) _
    (quaternionHaarBilinear_rawToRatPoly
      blocks right (canon polynomial)) ?_
  refine Q'.eqv_trans _
    (rawWeightedSum
      (fun monomial =>
        quaternionHaarRow blocks
          (monomial, 1) right)
      polynomial) _
    (rawWeightedSum_canon _ polynomial) ?_
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks
      (rawToRatPoly polynomial) right) _
    (Q'.eqv_symm
      (quaternionHaarBilinear_rawToRatPoly
        blocks right polynomial)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul
      blocks (rawToRatPoly polynomial) right)

/-! ## 3. Canonicalization after an arbitrary monomial embedding -/

/-- Interpret the monomial key of a raw integer polynomial through an
arbitrary dense-monomial embedding.  This permits small sparse keys to drive
the normalizer while the resulting polynomial still lives on the literal
quaternion-coordinate carrier. -/
def mappedRawToRatPoly
    (embed : List Nat → List Nat) (polynomial : RawPoly) : RatPoly :=
  polynomial.map fun term => (embed term.1, Q'.ofInt term.2)

private theorem quaternionHaarBilinear_mappedRawToRatPoly
    (blocks : Nat) (embed : List Nat → List Nat)
    (right : RatPoly) :
    ∀ polynomial : RawPoly,
      quaternionHaarBilinear blocks
          (mappedRawToRatPoly embed polynomial) right ≈
        rawWeightedSum
          (fun key =>
            quaternionHaarRow blocks
              (embed key, 1) right)
          polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        quaternionHaarRow blocks
              (embed term.1, Q'.ofInt term.2) right +
            quaternionHaarBilinear blocks
              (mappedRawToRatPoly embed rest) right ≈
          Q'.ofInt term.2 *
              quaternionHaarRow blocks
                (embed term.1, 1) right +
            rawWeightedSum
              (fun key =>
                quaternionHaarRow blocks
                  (embed key, 1) right)
              rest
      exact QPoly.q_add_congr
        (quaternionHaarRow_ofInt_scale
          blocks (embed term.1) term.2 right)
        (quaternionHaarBilinear_mappedRawToRatPoly
          blocks embed right rest)

/-- Canonicalization of arbitrary compact monomial keys is invisible to
exact product Haar after those keys are mapped back to dense monomials and
multiplied by an arbitrary rational polynomial. -/
theorem quaternionHaar_mapped_raw_canon_mul
    (blocks : Nat) (embed : List Nat → List Nat)
    (polynomial : RawPoly) (right : RatPoly) :
    quaternionHaar blocks
        (polyMul
          (mappedRawToRatPoly embed (canon polynomial)) right) ≈
      quaternionHaar blocks
        (polyMul
          (mappedRawToRatPoly embed polynomial) right) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks
      (mappedRawToRatPoly embed (canon polynomial)) right) _
    (quaternionHaar_polyMul
      blocks (mappedRawToRatPoly embed (canon polynomial))
      right) ?_
  refine Q'.eqv_trans _
    (rawWeightedSum
      (fun key =>
        quaternionHaarRow blocks
          (embed key, 1) right)
      (canon polynomial)) _
    (quaternionHaarBilinear_mappedRawToRatPoly
      blocks embed right (canon polynomial)) ?_
  refine Q'.eqv_trans _
    (rawWeightedSum
      (fun key =>
        quaternionHaarRow blocks
          (embed key, 1) right)
      polynomial) _
    (rawWeightedSum_canon _ polynomial) ?_
  refine Q'.eqv_trans _
    (quaternionHaarBilinear blocks
      (mappedRawToRatPoly embed polynomial) right) _
    (Q'.eqv_symm
      (quaternionHaarBilinear_mappedRawToRatPoly
        blocks embed right polynomial)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul
      blocks (mappedRawToRatPoly embed polynomial) right)

/-- A checked equality of reflective normal forms may be consumed under
Haar, with an arbitrary polynomial multiplier. -/
theorem quaternionHaar_expr_mul_congr_of_normal_eq
    (blocks : Nat) (left right : PolyExpr)
    (h : normalize left = normalize right)
    (multiplier : RatPoly) :
    quaternionHaar blocks
        (polyMul (exprToRatPoly left) multiplier) ≈
      quaternionHaar blocks
        (polyMul (exprToRatPoly right) multiplier) := by
  unfold exprToRatPoly
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (rawToRatPoly
          (canon (rawNormalize left)))
        multiplier)) _
    (Q'.eqv_symm
      (quaternionHaar_raw_canon_mul
        blocks (rawNormalize left) multiplier)) ?_
  rw [show
      canon (rawNormalize left) =
        canon (rawNormalize right) by
      exact h]
  exact quaternionHaar_raw_canon_mul
    blocks (rawNormalize right) multiplier

/-- Right-multiplier orientation of the same normalized identity. -/
theorem quaternionHaar_mul_expr_congr_of_normal_eq
    (blocks : Nat) (left right : PolyExpr)
    (h : normalize left = normalize right)
    (multiplier : RatPoly) :
    quaternionHaar blocks
        (polyMul multiplier (exprToRatPoly left)) ≈
      quaternionHaar blocks
        (polyMul multiplier (exprToRatPoly right)) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (exprToRatPoly left) multiplier)) _
    (quaternionHaar_polyMul_comm
      blocks multiplier (exprToRatPoly left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (exprToRatPoly right) multiplier)) _
    (quaternionHaar_expr_mul_congr_of_normal_eq
      blocks left right h multiplier) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_comm
      blocks multiplier (exprToRatPoly right))

end YMGap.Continuum.SU2QuaternionHaarRingNormalizer

#print axioms YMGap.Continuum.SU2QuaternionHaarRingNormalizer.rawWeightedSum_canon
#print axioms YMGap.Continuum.SU2QuaternionHaarRingNormalizer.quaternionHaar_raw_canon_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarRingNormalizer.quaternionHaar_mapped_raw_canon_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarRingNormalizer.quaternionHaar_expr_mul_congr_of_normal_eq
