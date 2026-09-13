/-
# The full ORIGINAL boundary D is exhausted by the previously bounded families

The actual fixed-core fiber is identified with `spectatorSum` on the full
detached region. For each original exterior selection this reaches the
EXISTING `boundarySpectatorFamily`, so the exact full boundary expansion
and the previous removed-face estimate now refer to the same families.

The identities need no small-nome restriction. The transferred estimate
retains all previous heat guards and its INTERIOR partition square. Collar/
path counting, summability and mixed boundary normalization remain open.
-/

import YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
import YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies
import YMGap.Continuum.BF4ExactSlabResummedCoefficientBound

namespace YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion
open YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections
open YMGap.Continuum.BF4ExactSlabBoundaryRootedFamilies
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound
open YMGap.Continuum.BF4ExactSlabResummedCoefficientBound
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem rootedFamily_spectatorSum_pin (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q)
    (ambient anchor : List Nat) (hn : ambient.Nodup) (ha : anchor ∈ selections ambient)
    (hf : core extent links anchor = anchor) :
    rootedFamily w K extent p q links ambient anchor ≈
      spectatorSum w K extent p q anchor (detachedIds extent links anchor ambient) :=
  Q'.eqv_trans _ _ _ (rootedFamily_resummed w K extent p q links hp hq hlp hlq ambient anchor hn ha hf)
    (Q'.eqv_symm (spectatorSum_pin w K extent p q links hp hq hlp hlq anchor _
      (detached_disjoint extent links anchor ambient)))

/-- This is the actual filtered fiber of original coefficients, not a new law. -/
def boundaryRootedFamily (w : Q') (K half padding : Nat) (p : RatPoly) (links : List Z4Link)
    (exterior anchor : List Nat) : Q' :=
  let extent := centralExtent (half+padding)
  rootedFamily w K extent p (remainderProduct w K extent exterior)
    (links++faceLinks extent exterior) (interiorIds half padding) anchor

theorem boundaryRootedFamily_pin (w : Q') (K half padding : Nat) (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (exterior anchor : List Nat)
    (ha : anchor ∈ rootedAnchors (centralExtent (half+padding))
      (links++faceLinks (centralExtent (half+padding)) exterior) (interiorIds half padding)) :
    boundaryRootedFamily w K half padding p links exterior anchor ≈
      boundarySpectatorFamily w K half padding p links exterior anchor :=
  rootedFamily_spectatorSum_pin w K (centralExtent (half+padding)) p
    (remainderProduct w K (centralExtent (half+padding)) exterior)
    (links++faceLinks (centralExtent (half+padding)) exterior) hp (remainderProduct_supported w K _ exterior)
    (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
    ((remainderProduct_local w K _ exterior).mono (fun _ h => List.mem_append.mpr (Or.inr h)))
    (interiorIds half padding) anchor (interiorIds_nodup half padding)
    (List.mem_filter.mp ha).1 (of_decide_eq_true (List.mem_filter.mp ha).2)

theorem selectionResponse_resummed_expansion (w : Q') (K half padding : Nat)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (exterior : List Nat) :
    selectionResponse w K half padding p exterior ≈
      listQSum (boundarySpectatorFamily w K half padding p links exterior)
        (rootedAnchors (centralExtent (half+padding))
          (links++faceLinks (centralExtent (half+padding)) exterior) (interiorIds half padding)) := by
  let extent := centralExtent (half+padding)
  have hlp := hl.mono (fun _ h => List.mem_append.mpr (Or.inl h) :
    ∀ link, link ∈ links → link ∈ links++faceLinks extent exterior)
  have hlq := (remainderProduct_local w K extent exterior).mono
    (fun _ h => List.mem_append.mpr (Or.inr h) :
      ∀ link, link ∈ faceLinks extent exterior → link ∈ links++faceLinks extent exterior)
  refine Q'.eqv_trans _ _ _ (selectionResponse_connected w K half padding p exterior)
    (Q'.eqv_trans _ _ _ (connectedNumerator_resummed_expansion w K extent p
      (remainderProduct w K extent exterior) (links++faceLinks extent exterior) hp
      (remainderProduct_supported w K extent exterior) hlp hlq _ (interiorIds_nodup half padding)) ?_)
  exact listQSum_congr_on _ _ _ (fun anchor _ => Q'.eqv_symm
    (spectatorSum_pin w K extent p (remainderProduct w K extent exterior)
      (links++faceLinks extent exterior) hp (remainderProduct_supported w K extent exterior)
      hlp hlq anchor _ (detached_disjoint extent _ anchor (interiorIds half padding))))

/-- The previously bounded anchored families now exhaust the SAME full D. -/
theorem boundaryNumerator_resummed_expansion (w : Q') (K half padding : Nat)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) :
    boundaryNumerator w half padding p K ≈
      listQSum (fun exterior => listQSum (boundarySpectatorFamily w K half padding p links exterior)
        (rootedAnchors (centralExtent (half+padding))
          (links++faceLinks (centralExtent (half+padding)) exterior) (interiorIds half padding)))
        (selections (exteriorIds half padding)) :=
  Q'.eqv_trans _ _ _ (boundaryNumerator_expansion w K half padding p)
    (listQSum_congr_on _ _ _ (fun exterior _ => selectionResponse_resummed_expansion w K half padding p links hp hl exterior))

/-- Transfer the existing removed-face estimate to the ACTUAL fiber. The
right-hand side remains Z_INTERIOR^2, not the mixed boundary denominator. -/
theorem boundaryRootedFamily_cleared_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
    (hdelta : heatRemainderBound w ≤ 1) (K half padding : Nat) (p : RatPoly) (c : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (exterior anchor : List Nat)
    (he : exterior ∈ selections (exteriorIds half padding))
    (ha : anchor ∈ rootedAnchors (centralExtent (half+padding))
      (links++faceLinks (centralExtent (half+padding)) exterior) (interiorIds half padding)) :
    let extent := centralExtent (half+padding)
    let F := removalFloor w (collarIds extent (links++faceLinks extent exterior) anchor (interiorIds half padding)).length
    (F*F)*Q'.abs (boundaryRootedFamily w K half padding p links exterior anchor) ≤
      anchorCap w c ((heatRemainderBound w)^exterior.length) anchor.length * partitionSquare w K extent (interiorIds half padding) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.abs_eqv_congr
    (boundaryRootedFamily_pin w K half padding p links P.support hl exterior anchor ha))))
    (boundarySpectatorFamily_cleared_bound hw0 hw1 hsmall hdelta K half padding p c links P hl exterior anchor
      he (List.mem_filter.mp ha).1)

end YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies.rootedFamily_spectatorSum_pin
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies.boundaryRootedFamily
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies.boundaryRootedFamily_pin
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies.selectionResponse_resummed_expansion
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies.boundaryNumerator_resummed_expansion
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryResummedFamilies.boundaryRootedFamily_cleared_bound
