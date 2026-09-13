/-
# Small-factor bounds for the ACTUAL probe-rooted mixed boundary families

The new mixed coefficient estimate is consumed by the existing matched
partition comparison. Both original unit moments remain visible. The
collar-removal cost is retained on the left; no summation over cores or
uniform decay is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabMixedCoefficientBound
import YMGap.Continuum.BF4ExactSlabMixedRelativePartition

namespace YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRootedResummation
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedCoefficientBound
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)
include hw0 hw1 hsmall hdelta

theorem mixedFamily_weight_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (links : List Z4Link)
    (hl : LinkLocal extent links p) (ambient anchor : List Nat) (hn : ambient.Nodup)
    (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    mixedRemovalFloor w keep (collarIds extent links anchor ambient) *
      Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤
        ((c+c)*mixedHeatWeight w keep anchor) * mixedPartition w K extent keep ambient :=
  Q'.le_trans' _ _ _
    (mixedFamily_cleared_bound hw0 hw1 hsmall hdelta K extent keep p links P.support hl ambient anchor hn ha hf hphys)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (mixedCoefficient_bound hw0 hw1 hsmall K extent keep p c P anchor (fun id hi => hphys id (selected_mem ha id hi)))
      (mixedPartition_nonnegative hw0 hw1 hsmall hdelta K extent keep ambient hphys))

theorem mixedFamily_geometric_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (links : List Z4Link)
    (hl : LinkLocal extent links p) (ambient anchor : List Nat) (hn : ambient.Nodup)
    (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    mixedRemovalFloor w keep (collarIds extent links anchor ambient) *
      Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤
        ((c+c)*(pairedHeatRate w)^anchor.length) * mixedPartition w K extent keep ambient :=
  Q'.le_trans' _ _ _
    (mixedFamily_weight_bound hw0 hw1 hsmall hdelta K extent keep p c P links hl ambient anchor hn ha hf hphys)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (mixedHeatWeight_le_pairedPow hw0 keep anchor)
        (Q'.zero_le_add _ _ P.nonnegative P.nonnegative))
      (mixedPartition_nonnegative hw0 hw1 hsmall hdelta K extent keep ambient hphys))

/-- The concrete original boundary family has the two matching unit moments. -/
theorem boundary_mixedFamily_weight_bound (K half padding : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (links : List Z4Link) (hl : LinkLocal (centralExtent (half+padding)) links p) (anchor : List Nat)
    (ha : anchor ∈ activeAnchors (centralExtent (half+padding)) links (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding)))) :
    let extent := centralExtent (half+padding)
    let keep := boundaryKeep half padding
    let ambient := slabPhysicalFaceEdges extent
    mixedRemovalFloor w keep (collarIds extent links anchor ambient) * Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤
      ((c+c)*mixedHeatWeight w keep anchor) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  Q'.le_trans' _ _ _ (mixedFamily_weight_bound hw0 hw1 hsmall hdelta K (centralExtent (half+padding))
    (boundaryKeep half padding) p c P links hl _ anchor (YMGap.Continuum.CayleyParentInj.range_nodup _)
    (List.mem_filter.mp (List.mem_filter.mp ha).1).1
    (of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2) (fun _ h => h))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (boundary_mixedPartition w K half padding)))

end SmallNome
end YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies

#print axioms YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies.mixedFamily_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies.mixedFamily_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedBoundedFamilies.boundary_mixedFamily_weight_bound
