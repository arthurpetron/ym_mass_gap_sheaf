/-
# Literal translated finite plaquette expressions on the ORIGINAL carrier

Use the existing lower plaquette-expression syntax, including arbitrary
finite products, sums and signed rational scales. Evaluation translates
every actual face together. Support, square caps, finite-box link locality
and the original Haar embedding pin are proved by structural recursion.
The cap depends only on the original expression, not the translation.
-/

import YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier
import YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay
import YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound

namespace YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def shiftedExpression {base : Nat} (margin : Nat) (e : PlaquetteExpression base) : RatPoly :=
  evaluate (fun id spin => shiftedCharacter base margin (slabPlaquetteAt (centralExtent base) id) spin) e

theorem shiftedExpression_supported {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (base+margin))).length
      (shiftedExpression margin e) :=
  evaluate_supported _ (fun _ _ spin => original_character_support _ _ spin) e

def shiftedExpressionBound {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    SquareBound (boundaryCompleteSlabLinks (centralExtent (base+margin))).length
      (shiftedExpression margin e) (bound e)
  | .unit => .one _
  | .character _ hi spin => character_squareBound
      (.scalar (supported_slabPlaquette _ _)
        (haarNorm_slabPlaquette (shiftedFace_physical (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) margin))) spin
  | .add e f => (shiftedExpressionBound margin e).add (shiftedExpressionBound margin f)
  | .mul e f => (shiftedExpressionBound margin e).mul (shiftedExpressionBound margin f)
  | .smul c e => (shiftedExpressionBound margin e).smul c

theorem shifted_face_links {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin : Nat)
    (link : Z4Link) (hl : link ∈ edgesOf (shiftFace margin margin face)) :
    link ∈ (boxLinks (centralExtent base+1)).map (shiftLink margin margin) := by
  rw [edgesOf_shiftFace] at hl
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
  exact List.mem_map.mpr ⟨source,
    boundary_mem_boxLinks ((mem_boundaryCompleteSlabPlaquettes _ _).mp hf).1 hs, rfl⟩

theorem shiftedExpression_local {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    LinkLocal (centralExtent (base+margin))
      ((boxLinks (centralExtent base+1)).map (shiftLink margin margin)) (shiftedExpression margin e)
  | .unit => BlockLocal.one _ _
  | .character _ hi spin =>
      LinkLocal.mono ((face_scalar_local _ _).character spin)
        (shifted_face_links (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) margin)
  | .add e f => (shiftedExpression_local margin e).add (shiftedExpression_local margin f)
  | .mul e f => (shiftedExpression_local margin e).mul (shiftedExpression_local margin f)
  | .smul c e => (shiftedExpression_local margin e).smul c

/-- Every factor is pinned to the SAME literal inter-slab polynomial map. -/
theorem shiftedExpression_image {base : Nat} (margin padding : Nat) : ∀ e : PlaquetteExpression base,
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length
      ((slabEmbedding (base+margin) padding).polynomial (shiftedExpression margin e))
      (shiftedExpression (margin+padding) e)
  | .unit => (slabEmbedding (base+margin) padding).polynomial_one_prefix
  | .character id hi spin => by
      simpa only [shiftedExpression, evaluate, shiftedCharacter, Nat.add_assoc] using
        characterImage_prefix (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) margin padding spin
  | .add e f => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding (base+margin) padding).polynomial
        (polyAdd (shiftedExpression margin e) (shiftedExpression margin f))) _
      rw [BlockEmbedding.polynomial_add]
      exact (shiftedExpression_image margin padding e).append (shiftedExpression_image margin padding f)
  | .mul e f => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding (base+margin) padding).polynomial
        (polyMul (shiftedExpression margin e) (shiftedExpression margin f))) _
      rw [BlockEmbedding.polynomial_mul]
      exact (shiftedExpression_image margin padding e).mul (shiftedExpression_image margin padding f)
  | .smul c e => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding (base+margin) padding).polynomial
        (polySmul c (shiftedExpression margin e))) _
      rw [BlockEmbedding.polynomial_smul]
      exact (shiftedExpression_image margin padding e).smul c

end YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression

#print axioms YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression.shiftedExpression
#print axioms YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression.shiftedExpression_supported
#print axioms YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression.shiftedExpressionBound
#print axioms YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression.shifted_face_links
#print axioms YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression.shiftedExpression_local
#print axioms YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression.shiftedExpression_image
