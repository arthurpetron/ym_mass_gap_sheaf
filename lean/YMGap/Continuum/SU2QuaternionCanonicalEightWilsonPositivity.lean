/-
# Wilson-weighted positivity on the strict canonical carrier

This file transports the exact supported Wilson sum-of-squares theorem to the
`Fin 8 -> Nat` monomial representation.  The only representation issue is
trailing zeroes in the earlier dense-list carrier.  It is resolved directly at
the exact linear moment fold, then lifted over every finite polynomial.

The result is a nonconstant, normalized `ReferenceWeight` on the strict
boundary-exchange algebra.  No positivity field is assumed.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight
import YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

namespace YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization
open YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

local infix:50 " ≈ " => Q'.eqv

private theorem retained_weight_single_linear_sum (t : Term8) :
    productHaarLinearSum
        (polyMul [embedTerm8 t] (embedPoly8 retainedRelativeWeight8)) ≈
      productHaarLinearSum
        (polyMul [embedTerm8 t] retainedRelativeWeight) := by
  simp [embedPoly8, retainedRelativeWeight8,
    relativeFundamentalCharacter8, relativeDot8, crossCoordinate8,
    crossMono8, gIndex8, hIndex8,
    retainedRelativeWeight, relativeFundamentalCharacter, relativeDot,
    gCoordinate, hCoordinate, polyAdd8, polySmul8, polyOne8,
    polyAdd, polySmul, polyOne, polyVar, polyMul, productHaarLinearSum,
    productHaarMono, exponentAt]
  constructor <;> omega

private theorem retained_weight_single_pair (t : Term8) :
    productHaar
        (polyMul [embedTerm8 t] (embedPoly8 retainedRelativeWeight8)) ≈
      productHaar
        (polyMul [embedTerm8 t] retainedRelativeWeight) := by
  refine Q'.eqv_trans _
    (productHaarLinearSum
      (polyMul [embedTerm8 t] (embedPoly8 retainedRelativeWeight8))) _
    (productHaar_eqv_linearSum _) ?_
  refine Q'.eqv_trans _
    (productHaarLinearSum
      (polyMul [embedTerm8 t] retainedRelativeWeight)) _
    (retained_weight_single_linear_sum t) ?_
  exact Q'.eqv_symm (productHaar_eqv_linearSum _)

private theorem embedded_retained_weight_pair_right : ∀ p : Poly8,
    productHaar
        (polyMul (embedPoly8 p) (embedPoly8 retainedRelativeWeight8)) ≈
      productHaar (polyMul (embedPoly8 p) retainedRelativeWeight)
  | [] => Q'.eqv_refl 0
  | t :: p => by
      change
        productHaar
            (polyMul [embedTerm8 t] (embedPoly8 retainedRelativeWeight8) ++
              polyMul (embedPoly8 p) (embedPoly8 retainedRelativeWeight8)) ≈
          productHaar
            (polyMul [embedTerm8 t] retainedRelativeWeight ++
              polyMul (embedPoly8 p) retainedRelativeWeight)
      refine Q'.eqv_trans _
        (productHaar
            (polyMul [embedTerm8 t] (embedPoly8 retainedRelativeWeight8)) +
          productHaar
            (polyMul (embedPoly8 p) (embedPoly8 retainedRelativeWeight8))) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _
        (productHaar (polyMul [embedTerm8 t] retainedRelativeWeight) +
          productHaar (polyMul (embedPoly8 p) retainedRelativeWeight)) _
        (QPoly.q_add_congr (retained_weight_single_pair t)
          (embedded_retained_weight_pair_right p)) ?_
      exact Q'.eqv_symm (productHaar_append_eqv _ _)

/-- Padding the five retained-weight monomials to the canonical length-eight
representation does not change any exact Haar pairing. -/
theorem embedded_retained_weight_pair (p : Poly8) :
    productHaar
        (polyMul (embedPoly8 retainedRelativeWeight8) (embedPoly8 p)) ≈
      productHaar (polyMul retainedRelativeWeight (embedPoly8 p)) := by
  refine Q'.eqv_trans _
    (productHaar
      (polyMul (embedPoly8 p) (embedPoly8 retainedRelativeWeight8))) _
    (productHaar_polyMul_comm _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (embedPoly8 p) retainedRelativeWeight)) _
    (embedded_retained_weight_pair_right p) ?_
  exact productHaar_polyMul_comm _ _

/-- Exact identification of the canonical weighted square with the supported
dense-list Wilson square already proved by the finite SOS calculation. -/
theorem canonical_retained_square_eq_dense (p : Poly8) :
    canonicalProductHaar
        (polyMul8 retainedRelativeWeight8 (polyMul8 p p)) ≈
      productHaar
        (polyMul retainedRelativeWeight
          (polyMul (embedPoly8 p) (embedPoly8 p))) := by
  unfold canonicalProductHaar
  rw [embedPoly8_mul]
  refine Q'.eqv_trans _
    (productHaar
      (polyMul retainedRelativeWeight (embedPoly8 (polyMul8 p p)))) _
    (embedded_retained_weight_pair (polyMul8 p p)) ?_
  rw [embedPoly8_mul]
  exact Q'.eqv_refl _

/-- Wilson-weighted all-degree positivity on every canonical polynomial. -/
theorem canonical_retained_square_nonneg (p : Poly8) :
    (0 : Q') ≤ canonicalProductHaar
      (polyMul8 retainedRelativeWeight8 (polyMul8 p p)) := by
  have hdense : (0 : Q') ≤
      productHaar
        (polyMul retainedRelativeWeight
          (polyMul (embedPoly8 p) (embedPoly8 p))) :=
    retainedRelativeWeight_square_nonneg
      (embedPoly8 p) (embedPoly8_supported p)
  exact Q'.le_trans' _ _ _ hdense
    (Q'.le_of_eqv (Q'.eqv_symm (canonical_retained_square_eq_dense p)))

theorem canonical_retained_partition_strict :
    canonicalProductHaar (polyMul8 retainedRelativeWeight8 polyOne8) = 1 := by
  decide

/-- A concrete nontrivially Wilson-weighted reference datum on the strict
canonical observable algebra. -/
def canonicalRetainedReferenceWeight :
    ReferenceWeight canonicalQuaternionPairAlg where
  I₀ := canonicalProductHaarFunctional
  w := retainedRelativeWeight8
  Z := 1
  Z_eq := canonical_retained_partition_strict
  Z_pos := by decide
  weighted_pos := canonical_retained_square_nonneg

end YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity.embedded_retained_weight_pair
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity.canonical_retained_square_nonneg
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity.canonicalRetainedReferenceWeight
