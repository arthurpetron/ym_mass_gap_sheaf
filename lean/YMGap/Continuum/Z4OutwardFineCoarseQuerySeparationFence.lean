/-
# Fine/coarse outward face queries are not nested label sets

A distinguished dyadic child is geometrically contained in its parent square,
but the finite physical encoding assigns the child and parent distinct
plaquette labels.  Their singleton decoded query supports are therefore
disjoint, not nested.  This rules out a tempting direct event-monotonicity
argument based solely on list inclusion.
-/

import YMGap.Continuum.Z4OutwardThreeCubeFineCarrier
import YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns

namespace YMGap.Continuum.Z4OutwardFineCoarseQuerySeparationFence

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

/-! ## 1. Generic decoded-singleton separation -/

theorem geometricSupportIds_singletons_disjoint_of_ne
    (volume : Nat) {fine coarse : Z4Plaq}
    (hne : fine ≠ coarse) :
    ∀ id, id ∈ geometricSupportIds volume [fine] →
      id ∉ geometricSupportIds volume [coarse] := by
  intro id hfine hcoarse
  have hfineParts :=
    (mem_geometricSupportIds_iff volume [fine] id).1 hfine
  have hcoarseParts :=
    (mem_geometricSupportIds_iff volume [coarse] id).1 hcoarse
  have hfineEq : boxPlaquetteAt volume id = fine := by
    simpa only [List.mem_singleton] using hfineParts.2
  have hcoarseEq : boxPlaquetteAt volume id = coarse := by
    simpa only [List.mem_singleton] using hcoarseParts.2
  exact hne (hfineEq.symm.trans hcoarseEq)

/-! ## 2. The three parent/child plaquette pairs are literally distinct -/

theorem outwardOriginFinePlaquettes_ne_coarseParents :
    dyadicCell
        (axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)) .origin ≠
      axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ) ∧
    dyadicCell
        (axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ)) .origin ≠
      axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ) ∧
    dyadicCell
        (axisShiftPlaquette zeroAxisOffset (cubeFace .topXY)) .origin ≠
      axisShiftPlaquette zeroAxisOffset (cubeFace .topXY) := by
  decide

/-! ## 3. Exact support separation and failed inclusions -/

theorem outwardXFineCoarseQuery_disjoint :
    ∀ id,
      id ∈ axisFineFaceQuerySupport
          zeroAxisOffset .rightYZ .origin →
        id ∉ axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ := by
  exact geometricSupportIds_singletons_disjoint_of_ne 6
    outwardOriginFinePlaquettes_ne_coarseParents.1

theorem outwardYFineCoarseQuery_disjoint :
    ∀ id,
      id ∈ axisFineFaceQuerySupport
          zeroAxisOffset .backXZ .origin →
        id ∉ axisCoarseFaceQuerySupport zeroAxisOffset .backXZ := by
  exact geometricSupportIds_singletons_disjoint_of_ne 6
    outwardOriginFinePlaquettes_ne_coarseParents.2.1

theorem outwardZFineCoarseQuery_disjoint :
    ∀ id,
      id ∈ axisFineFaceQuerySupport
          zeroAxisOffset .topXY .origin →
        id ∉ axisCoarseFaceQuerySupport zeroAxisOffset .topXY := by
  exact geometricSupportIds_singletons_disjoint_of_ne 6
    outwardOriginFinePlaquettes_ne_coarseParents.2.2

theorem outwardFineQueries_not_subset_coarseParents :
    ¬ (∀ id,
        id ∈ axisFineFaceQuerySupport
            zeroAxisOffset .rightYZ .origin →
          id ∈ axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ) ∧
    ¬ (∀ id,
        id ∈ axisFineFaceQuerySupport
            zeroAxisOffset .backXZ .origin →
          id ∈ axisCoarseFaceQuerySupport zeroAxisOffset .backXZ) ∧
    ¬ (∀ id,
        id ∈ axisFineFaceQuerySupport
            zeroAxisOffset .topXY .origin →
          id ∈ axisCoarseFaceQuerySupport zeroAxisOffset .topXY) := by
  constructor
  · intro hsubset
    obtain ⟨id, hid⟩ := axisFineFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .rightYZ .origin
    exact outwardXFineCoarseQuery_disjoint id hid (hsubset id hid)
  constructor
  · intro hsubset
    obtain ⟨id, hid⟩ := axisFineFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .backXZ .origin
    exact outwardYFineCoarseQuery_disjoint id hid (hsubset id hid)
  · intro hsubset
    obtain ⟨id, hid⟩ := axisFineFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .topXY .origin
    exact outwardZFineCoarseQuery_disjoint id hid (hsubset id hid)

theorem outwardCoarseParents_not_subset_fineQueries :
    ¬ (∀ id,
        id ∈ axisCoarseFaceQuerySupport zeroAxisOffset .rightYZ →
          id ∈ axisFineFaceQuerySupport
            zeroAxisOffset .rightYZ .origin) ∧
    ¬ (∀ id,
        id ∈ axisCoarseFaceQuerySupport zeroAxisOffset .backXZ →
          id ∈ axisFineFaceQuerySupport
            zeroAxisOffset .backXZ .origin) ∧
    ¬ (∀ id,
        id ∈ axisCoarseFaceQuerySupport zeroAxisOffset .topXY →
          id ∈ axisFineFaceQuerySupport
            zeroAxisOffset .topXY .origin) := by
  constructor
  · intro hsubset
    obtain ⟨id, hid⟩ := axisCoarseFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .rightYZ
    exact outwardXFineCoarseQuery_disjoint id (hsubset id hid) hid
  constructor
  · intro hsubset
    obtain ⟨id, hid⟩ := axisCoarseFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .backXZ
    exact outwardYFineCoarseQuery_disjoint id (hsubset id hid) hid
  · intro hsubset
    obtain ⟨id, hid⟩ := axisCoarseFaceQuerySupport_nonempty
      zeroAxisOffset (Or.inl rfl) .topXY
    exact outwardZFineCoarseQuery_disjoint id (hsubset id hid) hid

#print axioms geometricSupportIds_singletons_disjoint_of_ne
#print axioms outwardOriginFinePlaquettes_ne_coarseParents
#print axioms outwardXFineCoarseQuery_disjoint
#print axioms outwardYFineCoarseQuery_disjoint
#print axioms outwardZFineCoarseQuery_disjoint
#print axioms outwardFineQueries_not_subset_coarseParents
#print axioms outwardCoarseParents_not_subset_fineQueries

end YMGap.Continuum.Z4OutwardFineCoarseQuerySeparationFence
