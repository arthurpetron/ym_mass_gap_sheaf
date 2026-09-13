/-
# Canonical rooted-family expansion of the EXISTING original boundary D

For each exterior selection, the common root carries the actual probe links
and the literal links of its exterior remainder. The original interior
connected numerator is grouped by the computed ordered core. Its signed
spectator fiber weight remains inside each family. The exact double sum is
pinned to the existing bulk boundary numerator, at the SAME cutoff/carrier.

This does not yet replace each actual fiber weight by the full detached
partition square, or bound the boundary response after mixed normalization.
-/

import YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
import YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections

namespace YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion
open YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem interiorIds_nodup (half padding : Nat) : (interiorIds half padding).Nodup :=
  (interiorIds_perm half padding).symm.nodup (embeddedIds_nodup half padding)

def boundaryRootedResponse (w : Q') (K half padding : Nat) (p : RatPoly) (links : List Z4Link)
    (exterior : List Nat) : Q' :=
  let extent := centralExtent (half+padding)
  rootedResponse w K extent p (remainderProduct w K extent exterior)
    (links++faceLinks extent exterior) (interiorIds half padding)

theorem selectionResponse_rooted_expansion (w : Q') (K half padding : Nat)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (exterior : List Nat) :
    selectionResponse w K half padding p exterior ≈ boundaryRootedResponse w K half padding p links exterior :=
  Q'.eqv_trans _ _ _ (selectionResponse_connected w K half padding p exterior)
    (connectedNumerator_rooted_expansion w K (centralExtent (half+padding)) p
      (remainderProduct w K (centralExtent (half+padding)) exterior)
      (links++faceLinks (centralExtent (half+padding)) exterior) (interiorIds half padding)
      (interiorIds_nodup half padding) hp (remainderProduct_supported w K _ exterior)
      (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      ((remainderProduct_local w K _ exterior).mono (fun _ h => List.mem_append.mpr (Or.inr h))))

/-- Full ORIGINAL boundary numerator, with no presumed family saturation,
partition positivity, small-nome hypothesis, or change of normalization. -/
theorem boundaryNumerator_rooted_expansion (w : Q') (K half padding : Nat)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) :
    boundaryNumerator w half padding p K ≈
      listQSum (boundaryRootedResponse w K half padding p links) (selections (exteriorIds half padding)) :=
  Q'.eqv_trans _ _ _ (boundaryNumerator_expansion w K half padding p)
    (listQSum_congr_on _ _ _ (fun exterior _ => selectionResponse_rooted_expansion w K half padding p links hp hl exterior))

end YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies.interiorIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies.boundaryRootedResponse
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies.selectionResponse_rooted_expansion
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies.boundaryNumerator_rooted_expansion
