/-
# Finite plaquette expressions on BOTH sides of the original reflection plane

The generators are actual physical faces of a fixed original slab, not just
lower-half face IDs. Unit, character, sum, product and signed rational scale
are evaluated on literal translated SU(2) holonomies. Square bounds, link
locality and the original inter-slab embedding pin are constructed.

The existing lower algebra embeds explicitly. Its reflected upper image is
pinned to the existing upper polynomial after the same zero-lag bulk shift.
This includes reflected mixed products without identifying square positivity
with OS positivity. It is the plaquette-generated spacetime algebra, not all
Wilson-loop or gauge observables.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility

namespace YMGap.Continuum.BF4ExactSlabSpacetimeExpression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression lower upper)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility
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

inductive SpacetimeExpression (base : Nat) : Type where
  | unit : SpacetimeExpression base
  | character (face : Z4Plaq) (physical : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base))
      (spin : Nat) : SpacetimeExpression base
  | add : SpacetimeExpression base → SpacetimeExpression base → SpacetimeExpression base
  | mul : SpacetimeExpression base → SpacetimeExpression base → SpacetimeExpression base
  | smul : Q' → SpacetimeExpression base → SpacetimeExpression base

def evaluate {base : Nat} (margin : Nat) : SpacetimeExpression base → RatPoly
  | .unit => polyOne
  | .character face _ spin => shiftedCharacter base margin face spin
  | .add e f => polyAdd (evaluate margin e) (evaluate margin f)
  | .mul e f => polyMul (evaluate margin e) (evaluate margin f)
  | .smul c e => polySmul c (evaluate margin e)

def bound {base : Nat} : SpacetimeExpression base → Q'
  | .unit => 1
  | .character _ _ spin => characterBound spin
  | .add e f => sumBound (bound e) (bound f)
  | .mul e f => bound e * bound f
  | .smul c e => (c*c)*bound e

def squareBound {base : Nat} (margin : Nat) : ∀ e : SpacetimeExpression base,
    SquareBound (boundaryCompleteSlabLinks (centralExtent (base+margin))).length (evaluate margin e) (bound e)
  | .unit => .one _
  | .character _ hf spin => character_squareBound
      (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (shiftedFace_physical hf margin))) spin
  | .add e f => (squareBound margin e).add (squareBound margin f)
  | .mul e f => (squareBound margin e).mul (squareBound margin f)
  | .smul c e => (squareBound margin e).smul c

theorem supported {base : Nat} (margin : Nat) (e : SpacetimeExpression base) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (base+margin))).length (evaluate margin e) :=
  (squareBound margin e).support

theorem bound_nonnegative {base : Nat} (e : SpacetimeExpression base) : (0 : Q') ≤ bound e :=
  (squareBound 0 e).nonnegative

theorem linkLocal {base : Nat} (margin : Nat) : ∀ e : SpacetimeExpression base,
    LinkLocal (centralExtent (base+margin)) ((boxLinks (centralExtent base+1)).map (shiftLink margin margin)) (evaluate margin e)
  | .unit => BlockLocal.one _ _
  | .character _ hf spin => LinkLocal.mono ((face_scalar_local _ _).character spin) (shifted_face_links hf margin)
  | .add e f => (linkLocal margin e).add (linkLocal margin f)
  | .mul e f => (linkLocal margin e).mul (linkLocal margin f)
  | .smul c e => (linkLocal margin e).smul c

theorem image_prefix {base : Nat} (margin padding : Nat) : ∀ e : SpacetimeExpression base,
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length
      ((slabEmbedding (base+margin) padding).polynomial (evaluate margin e)) (evaluate (margin+padding) e)
  | .unit => (slabEmbedding (base+margin) padding).polynomial_one_prefix
  | .character _ hf spin => by
      simpa only [evaluate, shiftedCharacter, Nat.add_assoc] using characterImage_prefix hf margin padding spin
  | .add e f => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding (base+margin) padding).polynomial
        (polyAdd (evaluate margin e) (evaluate margin f))) _
      rw [BlockEmbedding.polynomial_add]
      exact (image_prefix margin padding e).append (image_prefix margin padding f)
  | .mul e f => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding (base+margin) padding).polynomial
        (polyMul (evaluate margin e) (evaluate margin f))) _
      rw [BlockEmbedding.polynomial_mul]
      exact (image_prefix margin padding e).mul (image_prefix margin padding f)
  | .smul c e => by
      change QuaternionPrefixPolynomialEqv _ ((slabEmbedding (base+margin) padding).polynomial (polySmul c (evaluate margin e))) _
      rw [BlockEmbedding.polynomial_smul]
      exact (image_prefix margin padding e).smul c

def fromLower {base : Nat} : PlaquetteExpression base → SpacetimeExpression base
  | .unit => .unit
  | .character id hi spin => .character (slabPlaquetteAt (centralExtent base) id)
      (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) spin
  | .add e f => .add (fromLower e) (fromLower f)
  | .mul e f => .mul (fromLower e) (fromLower f)
  | .smul c e => .smul c (fromLower e)

def reflect {base : Nat} : SpacetimeExpression base → SpacetimeExpression base
  | .unit => .unit
  | .character face hf spin => .character (timeReflectPlaquette (centralExtent base) face)
      (timeReflectPlaquette_mem_boundaryCompleteSlab hf) spin
  | .add e f => .add (reflect e) (reflect f)
  | .mul e f => .mul (reflect e) (reflect f)
  | .smul c e => .smul c (reflect e)

def fromUpper {base : Nat} (e : PlaquetteExpression base) : SpacetimeExpression base := reflect (fromLower e)

private theorem congrTwo {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a=a') (hb : b=b') : f a b = f a' b' := by cases ha; cases hb; rfl

theorem evaluate_fromLower {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    evaluate margin (fromLower e) = shiftedExpression margin e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e f => congrTwo polyAdd (evaluate_fromLower margin e) (evaluate_fromLower margin f)
  | .mul e f => congrTwo polyMul (evaluate_fromLower margin e) (evaluate_fromLower margin f)
  | .smul c e => congrArg (polySmul c) (evaluate_fromLower margin e)

/-- The reflected image is the existing original upper polynomial in each enlarged slab. -/
theorem evaluate_fromUpper {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    evaluate margin (fromUpper e) = upper (enlarge margin e)
  | .unit => rfl
  | .character id hi spin => by
      change characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (base+margin))
        (shiftFace margin margin (timeReflectPlaquette (centralExtent base) (slabPlaquetteAt (centralExtent base) id)))).scalar spin =
        characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (base+margin))
          (slabPlaquetteAt (centralExtent (base+margin))
            (slabFaceReflectId (centralExtent (base+margin)) (bulkFaceId base margin 0 id)))).scalar spin
      have hp := (mem_centralLowerFaceIds.mp hi).1
      rw [slabPlaquetteAt_slabFaceReflectId (bulkFaceId_physical hp), bulkFaceId_pin hp, Nat.sub_zero,
        shiftFace_reflection (show margin ≤ margin+margin by omega)
          ((mem_boundaryCompleteSlabPlaquettes _ _).mp (slabPlaquetteAt_mem hp)).2, Nat.add_sub_cancel]
  | .add e f => congrTwo polyAdd (evaluate_fromUpper margin e) (evaluate_fromUpper margin f)
  | .mul e f => congrTwo polyMul (evaluate_fromUpper margin e) (evaluate_fromUpper margin f)
  | .smul c e => congrArg (polySmul c) (evaluate_fromUpper margin e)

theorem evaluate_lower_enlarge {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    evaluate margin (fromLower e) = lower (enlarge margin e) := by
  rw [evaluate_fromLower]
  unfold enlarge
  rw [bulkLower_pin]
  rfl

def reflectedProduct {base : Nat} (e f : PlaquetteExpression base) : SpacetimeExpression base :=
  .mul (fromUpper e) (fromLower f)

theorem reflectedProduct_pin {base : Nat} (margin : Nat) (e f : PlaquetteExpression base) :
    evaluate margin (reflectedProduct e f) = polyMul (upper (enlarge margin e)) (lower (enlarge margin f)) :=
  congrTwo polyMul (evaluate_fromUpper margin e) (evaluate_lower_enlarge margin f)

end YMGap.Continuum.BF4ExactSlabSpacetimeExpression

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.SpacetimeExpression
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.evaluate
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.bound
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.squareBound
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.supported
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.bound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.linkLocal
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.image_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.fromLower
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.reflect
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.fromUpper
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.evaluate_fromLower
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.evaluate_fromUpper
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.evaluate_lower_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.reflectedProduct
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpression.reflectedProduct_pin
