/-
# The same original channel amplitude under embedded LOWER action

The actual source lower-face action, observable and all-spin channel move
together through the literal slab embedding. Their target-carrier integral
is exactly the original smaller-slab lower amplitude at every cutoff.
The target interior limit is therefore the original coefficient limit.
A computed SOURCE cutoff controls both the bulk and numerical errors at
EVERY padding. No target-volume ceiling is paid for unused Haar variables.

The target action here consists of the embedded source LOWER faces only.
It is not the full enlarged lower action: added interactions and original
partition normalization still require control. This is no uniform bound
for full thermodynamic coefficients, no transfer-kernel or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabGrowingChannelInterior

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabGramChannelEmbedding
open YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def embeddedLowerIds (half padding : Nat) : List Nat :=
  (centralLowerFaceIds half).map (bulkFaceId half padding 0)

theorem embeddedLowerIds_lower {half padding id : Nat} (hi : id ∈ embeddedLowerIds half padding) :
    id ∈ centralLowerFaceIds (half+padding) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact bulkFaceId_lower hj

private theorem heat_image (w : Q') (K : Nat) {half padding id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    PolynomialImage (slabEmbedding half padding) (faceHeatPolynomial w K (centralExtent half) id)
      (faceHeatPolynomial w K (centralExtent (half+padding)) (bulkFaceId half padding 0 id)) := by
  have h := heatFactor_pin w K (padding := padding) hi
  change PolynomialImage _ _ (BF4ExactSlabBulkActionDressing.geometricHeat w K _ _)
  rw [bulkFaceId_pin hi, Nat.sub_zero]
  exact h

private theorem product_image (w : Q') (K half padding : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (centralExtent half)) →
    PolynomialImage (slabEmbedding half padding)
      (polynomialProduct (faceHeatPolynomial w K (centralExtent half)) ids)
      (polynomialProduct (fun id => faceHeatPolynomial w K (centralExtent (half+padding))
        (bulkFaceId half padding 0 id)) ids)
  | [], _ => image_one _
  | id :: ids, h => image_mul _ (heat_image w K (h id List.mem_cons_self))
      (product_image w K half padding ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

theorem lowerHeat_image (w : Q') (K half padding : Nat) :
    PolynomialImage (slabEmbedding half padding) (lowerHeatProduct w K half)
      (polynomialProduct (faceHeatPolynomial w K (centralExtent (half+padding))) (embeddedLowerIds half padding)) := by
  simpa only [embeddedLowerIds, polynomialProduct, List.foldr_map] using
    product_image w K half padding (centralLowerFaceIds half) (fun _ hi => (mem_centralLowerFaceIds.mp hi).1)

/-- An actual arbitrary-face-list numerator, not a replacement definition of the full action. -/
def interiorSequence (w : Q') (half padding : Nat) (p : RatPoly) (K : Nat) : Q' :=
  numerator w (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (centralExtent (half+padding)) (embeddedLowerIds half padding) p K

theorem interiorSequence_image (w : Q') (K half padding : Nat) {p q : RatPoly}
    (h : PolynomialImage (slabEmbedding half padding) p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length q) :
    Q'.eqv (interiorSequence w half padding q K) (lowerMoment w K half p) :=
  haar_image half padding (image_mul _ h (lowerHeat_image w K half padding))
    (supported_polyMul hp (heatProduct_supported w K _ _))
    (supported_polyMul hq (heatProduct_supported w K _ _))

variable (w : Q') {half id : Nat} (hi : id ∈ centralFixedFaceIds half) (padding : Nat)
    (e : PlaquetteExpression half) (c : SpinChannel half id)

local notation "shiftedInsertion" => insertion (bulkAtTime padding (Fin.mk 0 (Nat.zero_lt_succ padding)) e) (shiftedChannel padding c)

include hi in
theorem interiorSequence_selected (K : Nat) :
    Q'.eqv (interiorSequence w half padding shiftedInsertion K) (lowerMoment w K half (insertion e c)) :=
  interiorSequence_image w K half padding (insertion_image hi padding e c)
    (insertion_supported e c) (insertion_supported _ _)

variable (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

def interiorLimit : CReal := numeratorLimit w hw0 hw1
  (boundaryCompleteSlabLinks (centralExtent (half+padding))).length (centralExtent (half+padding))
  (embeddedLowerIds half padding) shiftedInsertion

def interiorLimitCauchy : QCauchy (interiorLimit w padding e c hw0 hw1).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (numeratorCauchy w hw0 hw1 _ _ _ shiftedInsertion)

include hi in
theorem interiorLimit_selected :
    Equiv (interiorLimit w padding e c hw0 hw1) (coefficientLimit w hw0 hw1 half (insertion e c)) :=
  Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ shiftedInsertion)
    (numerator_converges w hw0 hw1 _ _ _ (insertion e c))
    (fun epsilon he => ⟨0, fun K _ => eqv_close (interiorSequence_selected w hi padding e c K) epsilon he⟩)

/-- Depends on the source insertion and heat parameter, NOT on padding. -/
def selectedApproxCutoff (epsilon : Q') : Nat :=
  numeratorCutoff w (centralExtent half) (centralLowerFaceIds half) (insertion e c) epsilon

include hi in
/-- One source cutoff controls the enlarged INTERIOR amplitude at every padding. -/
theorem selected_approx_close (epsilon : Q') (he : (0 : Q') < epsilon) (K n : Nat)
    (hK : selectedApproxCutoff w e c epsilon ≤ K) (hn : selectedApproxCutoff w e c epsilon ≤ n) :
    interiorSequence w half padding shiftedInsertion K ≤ (coefficientLimit w hw0 hw1 half (insertion e c)).approx n + epsilon ∧
    (coefficientLimit w hw0 hw1 half (insertion e c)).approx n ≤ interiorSequence w half padding shiftedInsertion K + epsilon := by
  have h := numerator_approx_close w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (centralLowerFaceIds half) (insertion e c) epsilon he K n hK hn
  have hp := interiorSequence_selected w hi padding e c K
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.1,
    Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ epsilon (Q'.ge_of_eqv hp))⟩

end YMGap.Continuum.BF4ExactSlabGrowingChannelInterior

#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.embeddedLowerIds
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.embeddedLowerIds_lower
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.lowerHeat_image
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.interiorSequence
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.interiorSequence_image
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.interiorSequence_selected
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.interiorLimit
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.interiorLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.interiorLimit_selected
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.selectedApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabGrowingChannelInterior.selected_approx_close
