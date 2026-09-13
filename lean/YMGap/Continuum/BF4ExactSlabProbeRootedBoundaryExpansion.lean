/-
# Only probe-rooted cores reaching exterior faces survive in the ORIGINAL D

The mixed determinant cancels on every all-interior selection. A computable
test removes those cores from the full resummed expansion. Every retained
core carries a Type-valued witness of an exterior face AND a literal graph
path from the probe root to it, staying in that core. Exterior spectators
remain in the mixed original partition product, not in the root support.

This is an exact expansion and path witness, not a geometric length bound,
coefficient smallness estimate, normalized decay or continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabMixedRootedResummation
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRootedResummation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def touchesOutside (keep : Nat → Bool) (ids : List Nat) : Bool := ids.any (fun id => !(keep id))

def activeAnchors (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient : List Nat) : List (List Nat) :=
  (rootedAnchors extent links ambient).filter (touchesOutside keep)

/-- Direct finite search returns the exterior index as data. -/
def outsideWitness (keep : Nat → Bool) : ∀ ids : List Nat, touchesOutside keep ids = true →
    Σ' id : Nat, (id ∈ ids) ×' (keep id = false)
  | [], h => by cases h
  | id :: ids, h => by
      cases hk : keep id with
      | false => exact ⟨id, List.mem_cons_self, hk⟩
      | true =>
          have ht : touchesOutside keep ids = true := by simpa only [touchesOutside, List.any_cons, hk, Bool.not_true, Bool.false_or] using h
          obtain ⟨j, hj, ho⟩ := outsideWitness keep ids ht
          exact ⟨j, List.mem_cons_of_mem id hj, ho⟩

theorem inside_of_not_touch (keep : Nat → Bool) : ∀ ids : List Nat, touchesOutside keep ids = false →
    ∀ id, id ∈ ids → keep id = true
  | [], _, _, hi => False.elim (List.not_mem_nil hi)
  | a :: ids, h, id, hi => by
      have ha : keep a = true := by cases hk : keep a <;> simp [touchesOutside, hk] at h ⊢
      rcases List.mem_cons.mp hi with he | hi
      · exact he ▸ ha
      · exact inside_of_not_touch keep ids
          (by simpa only [touchesOutside, List.any_cons, ha, Bool.not_true, Bool.false_or] using h) id hi

def active_anchor_path {extent : Nat} {links : List Z4Link} {keep : Nat → Bool} {ambient anchor : List Nat}
    (ha : anchor ∈ activeAnchors extent links keep ambient) :
    Σ' id : Nat, (id ∈ anchor) ×' (keep id = false) ×'
      ChainIn (adjacent extent links) (vertices anchor) none (some id) := by
  obtain ⟨id, hi, ho⟩ := outsideWitness keep anchor (List.mem_filter.mp ha).2
  have hf : core extent links anchor = anchor := of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2
  have path := core_path extent links anchor id (hf.symm ▸ hi)
  rw [hf] at path
  exact ⟨id, hi, ho, path⟩

theorem mixedNumerator_active_expansion (w : Q') (K extent : Nat) (keep : Nat → Bool)
    (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hl : LinkLocal extent links p) (ambient : List Nat) (hn : ambient.Nodup) :
    mixedNumerator w K extent keep p ambient ≈
      listQSum (fun anchor => mixedCoefficient w K extent keep p anchor *
        mixedPartition w K extent keep (detachedIds extent links anchor ambient)) (activeAnchors extent links keep ambient) :=
  Q'.eqv_trans _ _ _ (mixedNumerator_rooted_expansion w K extent keep p links hp hl ambient hn)
    (sum_filter_zero _ (touchesOutside keep) _ (fun anchor _ hn =>
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (mixedCoefficient_inside_zero w K extent keep p anchor (inside_of_not_touch keep anchor hn))) (Q'.zero_mul_eqv _)))

/-- Exact SAME D, now a SINGLE probe-rooted sum over all physical faces. -/
theorem boundary_probe_rooted_expansion (w : Q') (K half padding : Nat) (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) :
    let extent := centralExtent (half+padding)
    let keep := boundaryKeep half padding
    let ambient := slabPhysicalFaceEdges extent
    boundaryNumerator w half padding p K ≈
      listQSum (fun anchor => mixedCoefficient w K extent keep p anchor *
        mixedPartition w K extent keep (detachedIds extent links anchor ambient)) (activeAnchors extent links keep ambient) :=
  Q'.eqv_trans _ _ _ (boundary_mixedNumerator w K half padding p)
    (mixedNumerator_active_expansion w K (centralExtent (half+padding)) (boundaryKeep half padding)
      p links hp hl _ (YMGap.Continuum.CayleyParentInj.range_nodup _))

/-- The returned path ends at an ACTUAL exterior face of the original bulk split. -/
def boundary_anchor_path {half padding : Nat} {links : List Z4Link} {anchor : List Nat}
    (ha : anchor ∈ activeAnchors (centralExtent (half+padding)) links (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding)))) :
    Σ' id : Nat, (id ∈ exteriorIds half padding) ×'
      ChainIn (adjacent (centralExtent (half+padding)) links) (vertices anchor) none (some id) := by
  obtain ⟨id, hi, ho, path⟩ := active_anchor_path ha
  have hp := selected_mem (List.mem_filter.mp (List.mem_filter.mp ha).1).1 id hi
  refine ⟨id, List.mem_filter.mpr ⟨hp, ?_⟩, path⟩
  change Bool.not (boundaryKeep half padding id) = true
  rw [ho]
  rfl

end YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion

#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.touchesOutside
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.activeAnchors
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.outsideWitness
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.inside_of_not_touch
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.active_anchor_path
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.mixedNumerator_active_expansion
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.boundary_probe_rooted_expansion
#print axioms YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion.boundary_anchor_path
