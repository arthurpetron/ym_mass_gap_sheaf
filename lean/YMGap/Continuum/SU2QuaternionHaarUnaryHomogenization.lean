/-
# Unary radius homogenization for arbitrary quaternion product Haar

The existing homogenization layer proves Haar preservation for a product of
two homogenized polynomials, as needed for square positivity.  The exposed
BF4 vacuum link instead needs the corresponding unary statement: inserting
enough block-radius factors to make every monomial bihomogeneous does not
change its normalized product-Haar value.

This is a finite polynomial theorem.  It uses the already-proved sphere-ideal
identity `quaternionHaar_radiusIter` and introduces no measure or positivity
assumption.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

namespace YMGap.Continuum.SU2QuaternionHaarUnaryHomogenization

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem quaternionHaar_append_local
    (blocks : Nat) : ∀ left right : RatPoly,
    quaternionHaar blocks (left ++ right) ≈
      quaternionHaar blocks left + quaternionHaar blocks right
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | term :: rest, right => by
      change
        term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks (rest ++ right) ≈
          (term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest) +
            quaternionHaar blocks right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaar_append_local blocks rest right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem quaternionHaar_homogenizeTerm
    (totalBlocks : Nat) (targetDegrees : Nat → Nat)
    (term : RatTerm) : ∀ processedBlocks,
    processedBlocks ≤ totalBlocks →
      quaternionHaar totalBlocks
          (homogenizeQuaternionTerm
            targetDegrees processedBlocks term) ≈
        quaternionHaar totalBlocks [term]
  | 0, _ => Q'.eqv_refl _
  | processedBlocks + 1, hprocessed => by
      unfold homogenizeQuaternionTerm
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_radiusIter
          totalBlocks processedBlocks (by omega)
          (homogenizeQuaternionTerm
            targetDegrees processedBlocks term)
          (quaternionRaiseCount targetDegrees processedBlocks term))
        (quaternionHaar_homogenizeTerm
          totalBlocks targetDegrees term processedBlocks (by omega))

private theorem quaternionHaar_polyMul_append_left_local
    (blocks : Nat) (left right multiplier : RatPoly) :
    quaternionHaar blocks
        (polyMul (left ++ right) multiplier) ≈
      quaternionHaar blocks (polyMul left multiplier) +
        quaternionHaar blocks (polyMul right multiplier) := by
  simp only [polyMul, List.flatMap_append]
  exact quaternionHaar_append_local blocks _ _

/-- Homogenizing only an initial segment of the quaternion blocks preserves
the Haar functional on the full carrier.  This form avoids traversing all 116
BF4 blocks when the exposed plaquette is supported in just four of them. -/
theorem quaternionHaar_homogenizePolynomial_upTo
    (totalBlocks processedBlocks : Nat)
    (hprocessed : processedBlocks ≤ totalBlocks)
    (targetDegrees : Nat → Nat) :
    ∀ polynomial : RatPoly,
      quaternionHaar totalBlocks
          (homogenizeQuaternionPolynomial
            targetDegrees processedBlocks polynomial) ≈
        quaternionHaar totalBlocks polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      unfold homogenizeQuaternionPolynomial
      refine Q'.eqv_trans _
        (quaternionHaar totalBlocks
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks term) +
          quaternionHaar totalBlocks
            (homogenizeQuaternionPolynomial
              targetDegrees processedBlocks rest)) _
        (quaternionHaar_append_local totalBlocks _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar totalBlocks [term] +
          quaternionHaar totalBlocks rest) _
        (Q'.add_eqv_congr'
          (quaternionHaar_homogenizeTerm
            totalBlocks targetDegrees term processedBlocks hprocessed)
          (quaternionHaar_homogenizePolynomial_upTo
            totalBlocks processedBlocks hprocessed targetDegrees rest)) ?_
      change
        (term.2 * quaternionHaarMono totalBlocks term.1 + 0) +
              quaternionHaar totalBlocks rest ≈
          term.2 * quaternionHaarMono totalBlocks term.1 +
            quaternionHaar totalBlocks rest
      rw [Q'.add_zero']
      exact Q'.eqv_refl _

private theorem quaternionHaar_homogenizeTerm_mul
    (totalBlocks : Nat) (targetDegrees : Nat → Nat)
    (term : RatTerm) (multiplier : RatPoly) : ∀ processedBlocks,
    processedBlocks ≤ totalBlocks →
      quaternionHaar totalBlocks
          (polyMul
            (homogenizeQuaternionTerm
              targetDegrees processedBlocks term)
            multiplier) ≈
        quaternionHaar totalBlocks
          (polyMul [term] multiplier)
  | 0, _ => Q'.eqv_refl _
  | processedBlocks + 1, hprocessed => by
      unfold homogenizeQuaternionTerm
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_radiusIter_pair_left
          totalBlocks processedBlocks (by omega)
          (homogenizeQuaternionTerm
            targetDegrees processedBlocks term)
          multiplier
          (quaternionRaiseCount targetDegrees processedBlocks term))
        (quaternionHaar_homogenizeTerm_mul
          totalBlocks targetDegrees term multiplier
          processedBlocks (by omega))

/-- Initial-segment homogenization is also invisible with an arbitrary
polynomial multiplier.  In the BF4 application `processedBlocks = 4` and
`totalBlocks = 116`, so the other 112 blocks are retained verbatim. -/
theorem quaternionHaar_homogenizePolynomial_mul_upTo
    (totalBlocks processedBlocks : Nat)
    (hprocessed : processedBlocks ≤ totalBlocks)
    (targetDegrees : Nat → Nat) :
    ∀ (polynomial multiplier : RatPoly),
      quaternionHaar totalBlocks
          (polyMul
            (homogenizeQuaternionPolynomial
              targetDegrees processedBlocks polynomial)
            multiplier) ≈
        quaternionHaar totalBlocks (polyMul polynomial multiplier)
  | [], multiplier => Q'.eqv_refl 0
  | term :: rest, multiplier => by
      unfold homogenizeQuaternionPolynomial
      refine Q'.eqv_trans _
        (quaternionHaar totalBlocks
              (polyMul
                (homogenizeQuaternionTerm
                  targetDegrees processedBlocks term)
                multiplier) +
          quaternionHaar totalBlocks
              (polyMul
                (homogenizeQuaternionPolynomial
                  targetDegrees processedBlocks rest)
                multiplier)) _
        (quaternionHaar_polyMul_append_left_local totalBlocks _ _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar totalBlocks (polyMul [term] multiplier) +
          quaternionHaar totalBlocks (polyMul rest multiplier)) _
        (Q'.add_eqv_congr'
          (quaternionHaar_homogenizeTerm_mul
            totalBlocks targetDegrees term multiplier
            processedBlocks hprocessed)
          (quaternionHaar_homogenizePolynomial_mul_upTo
            totalBlocks processedBlocks hprocessed targetDegrees
            rest multiplier)) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_append_left_local
          totalBlocks [term] rest multiplier)

/-- **Unary Haar homogenization.**  Multiplying each monomial by computed
block-radius powers up to `targetDegrees` preserves its exact normalized
product-Haar value.  No degree upper-bound premise is needed for preservation;
such premises are required only by the separate theorem asserting that the
output actually reaches the requested degrees. -/
theorem quaternionHaar_homogenizePolynomial
    (blocks : Nat) (targetDegrees : Nat → Nat) :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (homogenizeQuaternionPolynomial
            targetDegrees blocks polynomial) ≈
        quaternionHaar blocks polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      unfold homogenizeQuaternionPolynomial
      refine Q'.eqv_trans _
        (quaternionHaar blocks
            (homogenizeQuaternionTerm targetDegrees blocks term) +
          quaternionHaar blocks
            (homogenizeQuaternionPolynomial targetDegrees blocks rest)) _
        (quaternionHaar_append_local blocks _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks [term] +
          quaternionHaar blocks rest) _
        (Q'.add_eqv_congr'
          (quaternionHaar_homogenizeTerm
            blocks targetDegrees term blocks (Nat.le_refl _))
          (quaternionHaar_homogenizePolynomial
            blocks targetDegrees rest)) ?_
      change
        (term.2 * quaternionHaarMono blocks term.1 + 0) +
              quaternionHaar blocks rest ≈
          term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks rest
      rw [Q'.add_zero']
      exact Q'.eqv_refl _

/-- Unary homogenization remains Haar-invisible in the presence of an
arbitrary polynomial multiplier.  This is the form needed to solidify one
exposed plaquette character while leaving the other 23 fixed-face factors
untouched. -/
theorem quaternionHaar_homogenizePolynomial_mul
    (blocks : Nat) (targetDegrees : Nat → Nat) :
    ∀ (polynomial multiplier : RatPoly),
      quaternionHaar blocks
          (polyMul
            (homogenizeQuaternionPolynomial
              targetDegrees blocks polynomial)
            multiplier) ≈
        quaternionHaar blocks (polyMul polynomial multiplier)
  | [], multiplier => Q'.eqv_refl 0
  | term :: rest, multiplier => by
      unfold homogenizeQuaternionPolynomial
      refine Q'.eqv_trans _
        (quaternionHaar blocks
              (polyMul
                (homogenizeQuaternionTerm targetDegrees blocks term)
                multiplier) +
          quaternionHaar blocks
              (polyMul
                (homogenizeQuaternionPolynomial
                  targetDegrees blocks rest)
                multiplier)) _
        (quaternionHaar_polyMul_append_left_local blocks _ _ _) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks (polyMul [term] multiplier) +
          quaternionHaar blocks (polyMul rest multiplier)) _
        (Q'.add_eqv_congr'
          (quaternionHaar_homogenizeTerm_mul
            blocks targetDegrees term multiplier blocks (Nat.le_refl _))
          (quaternionHaar_homogenizePolynomial_mul
            blocks targetDegrees rest multiplier)) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_append_left_local
          blocks [term] rest multiplier)

end YMGap.Continuum.SU2QuaternionHaarUnaryHomogenization

#print axioms YMGap.Continuum.SU2QuaternionHaarUnaryHomogenization.quaternionHaar_homogenizePolynomial
#print axioms YMGap.Continuum.SU2QuaternionHaarUnaryHomogenization.quaternionHaar_homogenizePolynomial_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarUnaryHomogenization.quaternionHaar_homogenizePolynomial_upTo
#print axioms YMGap.Continuum.SU2QuaternionHaarUnaryHomogenization.quaternionHaar_homogenizePolynomial_mul_upTo
