/-
# The growing original channel is its literal physical polynomial image

The actual slab link embedding sends every original selected all-spin
channel to the existing same-branch channel at the translated crossing
face. Both polynomials are supported on their respective Haar carriers.
The same statement holds after multiplication by the actual translated
lower observable. Haar pairings of any two such insertions are preserved.

This removes the geometric polynomial-pullback obligation for this bulk
enlargement. Haar preservation alone does not compare differently dressed
actions, normalized OS coefficients, or growing-volume packet floors.
-/

import YMGap.Continuum.BF4ExactSlabGramChannelEmbedding
import YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel
import YMGap.Continuum.BF4ExactSlabBulkExpectationComparison

namespace YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabGramChannelEmbedding
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

private theorem leaf_support {blocks : Nat} : {t : SquareTree} → (l : Leaf t) →
    SquareTreeSupported blocks t → SupportedQuaternionBlocks blocks l.channel
  | _, .here _ _, h => h
  | _, .left l, h => leaf_support l h.1
  | _, .right l, h => leaf_support l h.2

theorem facePolynomial_supported {half id : Nat} (c : SpinChannel half id) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (facePolynomial c) :=
  leaf_support c.leaf (spatialGramSquares_support _ _ c.spin)

private theorem faceLink_shift (padding : Nat) (face : ClusterCount4DProgress.Z4Plaq) :
    faceLinkA (shiftFace padding padding face) = shiftLink padding padding (faceLinkA face) := rfl

/-- Source and target are the ACTUAL original link polynomials, not new coordinates. -/
theorem shiftedChannel_polynomial {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (padding : Nat) (c : SpinChannel half id) :
    PolynomialImage (slabEmbedding half padding) (facePolynomial c) (facePolynomial (shiftedChannel padding c)) := by
  apply channel_image
  have hp := (mem_centralFixedFaceIds.mp hi).1
  rw [bulkFaceId_pin hp, Nat.sub_zero, faceLink_shift]
  exact link_pin (faceLinkA_physical (slabPlaquetteAt_mem hp))

def insertion {half id : Nat} (e : PlaquetteExpression half) (c : SpinChannel half id) : RatPoly :=
  polyMul (lower e) (facePolynomial c)

theorem insertion_supported {half id : Nat} (e : PlaquetteExpression half) (c : SpinChannel half id) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (insertion e c) :=
  supported_polyMul (lower_supported e) (facePolynomial_supported c)

/-- The original observable and channel move together on the same link map. -/
theorem insertion_image {half id : Nat} (hi : id ∈ centralFixedFaceIds half) (padding : Nat)
    (e : PlaquetteExpression half) (c : SpinChannel half id) :
    PolynomialImage (slabEmbedding half padding) (insertion e c)
      (insertion (bulkAtTime padding ⟨0, Nat.zero_lt_succ padding⟩ e) (shiftedChannel padding c)) :=
  image_mul _ (lower_bulk_image padding e) (shiftedChannel_polynomial hi padding c)

/-- Use prefix equality only when BOTH actual insertions have carrier support. -/
theorem haar_image (half padding : Nat) {p q : RatPoly}
    (h : PolynomialImage (slabEmbedding half padding) p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length q) :
    Q'.eqv (quaternionHaar (boundaryCompleteSlabLinks (centralExtent (half+padding))).length q)
      (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _ h
    ((slabEmbedding half padding).polynomial_supported p) hq)) (haar_embedding half padding p hp)

theorem insertion_haar {half id : Nat} (hi : id ∈ centralFixedFaceIds half) (padding : Nat)
    (e : PlaquetteExpression half) (c : SpinChannel half id) :
    Q'.eqv (quaternionHaar (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      (insertion (bulkAtTime padding ⟨0, Nat.zero_lt_succ padding⟩ e) (shiftedChannel padding c)))
      (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (insertion e c)) :=
  haar_image half padding (insertion_image hi padding e c) (insertion_supported e c) (insertion_supported _ _)

/-- Mixed Haar pairings retain all shared links; no independence is used. -/
theorem insertion_pair_haar {half i j : Nat}
    (hi : i ∈ centralFixedFaceIds half) (hj : j ∈ centralFixedFaceIds half) (padding : Nat)
    (e f : PlaquetteExpression half) (c : SpinChannel half i) (d : SpinChannel half j) :
    Q'.eqv (quaternionHaar (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      (polyMul (insertion (bulkAtTime padding ⟨0, Nat.zero_lt_succ padding⟩ e) (shiftedChannel padding c))
        (insertion (bulkAtTime padding ⟨0, Nat.zero_lt_succ padding⟩ f) (shiftedChannel padding d))))
      (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (polyMul (insertion e c) (insertion f d))) :=
  haar_image half padding (image_mul _ (insertion_image hi padding e c) (insertion_image hj padding f d))
    (supported_polyMul (insertion_supported e c) (insertion_supported f d))
    (supported_polyMul (insertion_supported _ _) (insertion_supported _ _))

end YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial

#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.facePolynomial_supported
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.shiftedChannel_polynomial
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.insertion
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.insertion_supported
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.insertion_image
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.haar_image
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.insertion_haar
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial.insertion_pair_haar
