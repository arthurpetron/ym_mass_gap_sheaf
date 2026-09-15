/-
# The scalar vertex-gauge average on the ORIGINAL translated slab probe

The general three-vertex calculation is instantiated with the four actual
corrected-slab links of `probeFace half`. The resulting polynomial is exactly
1/128 of `lower (bulkProbe half)`, with arbitrary original-link insertions
retained. The old bare-Haar mixed moment is not used to infer this identity.

OPEN: realizing this local vertex image by a common Haar-preserving change
of variables on every affected original link, retaining the FULL action and
original observable insertion. Until that bridge and its limit consequences
are proved, this is not an identification of the existing `completedTest`
with a plaquette pairing, a new separating test, or a transfer preimage.
-/

import YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
import YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference

namespace YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage

private abbrev link (half : Nat) (edge : Z4Plaq → Z4Link) : PolyQuaternion :=
  correctedSlabLinkPolynomial (centralExtent half) (edge (probeFace half))

private theorem four_product (a b c d : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul d (polyMul c (polyMul b polyOne))))
      (polyMul (polyMul (polyMul a b) c) d) :=
  ((RatPolyCoeffEqv.refl a).mul ((RatPolyCoeffEqv.refl d).mul
    ((RatPolyCoeffEqv.refl c).mul (RatPolyCoeffEqv.mul_one b)))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 3) (.mul (.var 2) (.var 1))))
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (by decide) (fun i => match i with | 0 => a | 1 => b | 2 => c | _ => d))

/-- `edgesOf` lists A,D,C,B. Only their scalar factors are reordered;
the noncommutative plaquette word is not permuted. -/
theorem bulkScalar_product_pin (half : Nat) :
    RatPolyCoeffEqv (bulkScalar half)
      (polyMul (polyMul (polyMul (link half faceLinkA).scalar
        (link half faceLinkB).scalar) (link half faceLinkC).scalar) (link half faceLinkD).scalar) :=
  four_product (link half faceLinkA).scalar (link half faceLinkB).scalar
    (link half faceLinkC).scalar (link half faceLinkD).scalar

/-- Same ordered holonomy and same original plaquette expression. -/
theorem bulkProbe_word_pin (half : Nat) :
    RatPolyCoeffEqv
      (characterPolynomial (plaquetteWord (link half faceLinkA) (link half faceLinkB)
        (link half faceLinkC) (link half faceLinkD)).scalar 1)
      (lower (bulkProbe half)) := by
  rw [bulkProbe_pin]
  apply characterPolynomial_coeffEqv
  exact ((((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)).scalar.symm

/-- Three auxiliary gauge blocks, followed by the original slab coordinates.
This is a literal local image, not yet a global substitution theorem. -/
def bulkScalarVertexImage (half : Nat) : RatPoly :=
  gaugedScalarProduct (link half faceLinkA) (link half faceLinkB)
    (link half faceLinkC) (link half faceLinkD)

theorem bulkScalar_vertex_average (half : Nat) :
    RatPolyCoeffEqv (averageThree (bulkScalarVertexImage half))
      (polySmul characterFraction (lower (bulkProbe half))) :=
  (gaugedScalarProduct_average _ _ _ _).trans ((bulkProbe_word_pin half).smul characterFraction)

/-- No disjointness from the four ORIGINAL probe links is demanded of the
tail. It is independent only of the three added gauge variables. -/
theorem bulkScalar_vertex_average_with_tail (half : Nat) (tail : RatPoly) :
    RatPolyCoeffEqv
      (averageThree (polyMul (bulkScalarVertexImage half) (liftBoundary 3 tail)))
      (polySmul characterFraction (polyMul (lower (bulkProbe half)) tail)) :=
  (gaugedScalarProduct_average_with_tail _ _ _ _ tail).trans
    (((bulkProbe_word_pin half).mul_right tail).smul characterFraction)

end YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage.bulkScalar_product_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage.bulkProbe_word_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage.bulkScalarVertexImage
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage.bulkScalar_vertex_average
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage.bulkScalar_vertex_average_with_tail
