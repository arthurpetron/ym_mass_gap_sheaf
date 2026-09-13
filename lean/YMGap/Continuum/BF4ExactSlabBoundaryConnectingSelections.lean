/-
# The EXISTING bulk boundary response, filtered by selected separating cuts

Each original exterior-selection response is the ordinary connected
numerator of the probe and that selected remainder under the ORIGINAL
interior action. Inclusion-exclusion in the interior faces and the proved
separator search then remove every coefficient with a separating cut.

This improves whole-interior detachment: the full interior may interact;
only a selected interior set needs to split for its coefficient to vanish.
All cutoff, carrier, interior and exterior action factors are pinned to the
existing boundaryNumerator. Quantitative coefficient bounds, path-length
control and NORMALIZED summability/decay remain open.
-/

import YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
import YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion

namespace YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem selectionResponse_connected (w : Q') (K half padding : Nat) (p : RatPoly) (ids : List Nat) :
    selectionResponse w K half padding p ids ≈
      connectedNumerator w K (centralExtent (half+padding)) (interiorIds half padding)
        p (remainderProduct w K (centralExtent (half+padding)) ids) := by
  let extent := centralExtent (half+padding)
  let I := polynomialProduct (faceHeatPolynomial w K extent) (interiorIds half padding)
  let r := remainderProduct w K extent ids
  have hone : interiorSequence w half padding polyOne K ≈
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (interiorIds half padding) K :=
    haar_of_coeff (RatPolyCoeffEqv.one_mul I)
  have hr : selectionMoment w K half padding polyOne ids ≈ interiorSequence w half padding r K :=
    haar_of_coeff ((RatPolyCoeffEqv.one_mul r).mul (RatPolyCoeffEqv.refl I))
  exact Q'.add_eqv_congr' (qmul (Q'.eqv_refl _) hone)
    (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _) hr))

def connectingResponse (w : Q') (K half padding : Nat) (p : RatPoly) (links : List Z4Link) (ids : List Nat) : Q' :=
  listQSum (connectedCoefficient w K (centralExtent (half+padding))
    p (remainderProduct w K (centralExtent (half+padding)) ids))
    (connectedSelections (centralExtent (half+padding)) links
      (faceLinks (centralExtent (half+padding)) ids) (interiorIds half padding))

theorem selectionResponse_connecting_expansion (w : Q') (K half padding : Nat)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (ids : List Nat) :
    selectionResponse w K half padding p ids ≈ connectingResponse w K half padding p links ids :=
  Q'.eqv_trans _ _ _ (selectionResponse_connected w K half padding p ids)
    (connectedNumerator_filtered w K (centralExtent (half+padding)) p
      (remainderProduct w K (centralExtent (half+padding)) ids) links
      (faceLinks (centralExtent (half+padding)) ids) hp (remainderProduct_supported w K _ ids)
      hl (remainderProduct_local w K _ ids) (interiorIds half padding))

/-- Exact SAME boundary numerator: exterior selections, then interior coefficients
filtered by the computed absence of a separating cut. No reciprocal bound. -/
theorem boundaryNumerator_connecting_expansion (w : Q') (K half padding : Nat)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) :
    boundaryNumerator w half padding p K ≈
      listQSum (connectingResponse w K half padding p links) (selections (exteriorIds half padding)) :=
  Q'.eqv_trans _ _ _ (boundaryNumerator_expansion w K half padding p)
    (listQSum_congr_on _ _ _ (fun ids _ => selectionResponse_connecting_expansion w K half padding p links hp hl ids))

end YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections.selectionResponse_connected
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections.connectingResponse
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections.selectionResponse_connecting_expansion
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections.boundaryNumerator_connecting_expansion
