/-
# The active-link incident mass is four times the component mass at most

At an active paired-support link, every positive incident source face lies in
the same target component.  Therefore replacing the source pair weight by its
restriction to that component changes no active-link row.  The exact
complete-slab incidence permutation then counts the restricted face weight
four times, once for each plaquette boundary link.

This proves the volume-independent budget needed by the aggregate auxiliary
compiler: the sum of the two replicas' incident physical masses over all
active links is at most four times their physical mass on the component.

Constructive contract: duplicate-free weighted subset accounting, an exact
finite incidence permutation, and natural arithmetic only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
import YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinkMass

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ResidualListMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Constructive weighted restriction identities -/

/-- Zero a natural-valued field off a displayed finite support. -/
def restrictNatWeightTo (support : List Nat) (weight : Nat → Nat)
    (item : Nat) : Nat :=
  if item ∈ support then weight item else 0

private theorem restrictedNatListSum_eq_filter
    (support : List Nat) (weight : Nat → Nat) :
    ∀ items : List Nat,
      natListSum (items.map (restrictNatWeightTo support weight)) =
        natListSum
          ((items.filter fun item => decide (item ∈ support)).map weight)
  | [] => rfl
  | head :: tail => by
      by_cases hhead : head ∈ support
      · simp [restrictNatWeightTo, hhead, natListSum,
          restrictedNatListSum_eq_filter support weight tail]
      · simp [restrictNatWeightTo, hhead, natListSum,
          restrictedNatListSum_eq_filter support weight tail]

private theorem natListSum_map_eq_listNatWeight
    {A : Type} (weight : A → Nat) : ∀ items : List A,
    natListSum (items.map weight) = listNatWeight weight items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map_cons, natListSum, listNatWeight]
      rw [natListSum_map_eq_listNatWeight weight tail]

/-- If a duplicate-free support lies in a duplicate-free ambient list, then
summing the ambient field after zeroing off the support gives exactly the
support sum. -/
theorem natListSum_restrictNatWeightTo_eq_support
    (support ambient : List Nat) (weight : Nat → Nat)
    (hsupport : support.Nodup) (hambient : ambient.Nodup)
    (hsubset : ∀ item, item ∈ support → item ∈ ambient) :
    natListSum (ambient.map (restrictNatWeightTo support weight)) =
      natListSum (support.map weight) := by
  let selected := ambient.filter fun item => decide (item ∈ support)
  have hselectedNodup : selected.Nodup := by
    exact List.filter_sublist.nodup hambient
  have hselectedMem : ∀ item, item ∈ selected ↔ item ∈ support := by
    intro item
    constructor
    · intro hitem
      exact of_decide_eq_true (List.mem_filter.mp hitem).2
    · intro hitem
      exact List.mem_filter.mpr ⟨hsubset item hitem, decide_eq_true hitem⟩
  have hperm : selected.Perm support :=
    perm_of_nodup_mem_iff selected support
      hselectedNodup hsupport hselectedMem
  have hsum := natListSum_perm (hperm.map weight)
  rw [restrictedNatListSum_eq_filter support weight ambient]
  exact hsum

private theorem natListSum_map_le_of_nodup_mem
    (weight : SlabLink → Nat) (source target : List SlabLink)
    (hsource : source.Nodup)
    (hsubset : ∀ link, link ∈ source → link ∈ target) :
    natListSum (source.map weight) ≤ natListSum (target.map weight) := by
  rw [natListSum_map_eq_listNatWeight weight source,
    natListSum_map_eq_listNatWeight weight target]
  exact listNatWeight_le_of_nodup_mem
    weight source target hsource hsubset

private theorem rangeNodupLocal : ∀ count : Nat,
    (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal count,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro item hitem member hmember heq
      have hmemberEq : member = count := List.mem_singleton.mp hmember
      subst member
      subst item
      exact Nat.lt_irrefl count (List.mem_range.mp hitem)

/-! ## 2. Active local rows see only component mass -/

/-- At an active link, zeroing the paired physical field outside the target
component does not alter its incident l1 mass. -/
theorem activeLink_incidentPairMass_eq_restricted
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    {link : SlabLink}
    (hlink : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId) :
    natListSum
        ((slabIncidentPlaqIds D.extent link).map fun faceId =>
          pair.1.1.1 faceId + pair.2.1.1 faceId) =
      natListSum
        ((slabIncidentPlaqIds D.extent link).map
          (restrictNatWeightTo
            (slabTwoReplicaTargetSupportComponent D.extent
              pair.1.1.1 pair.2.1.1 targetFaceId)
            (fun faceId => pair.1.1.1 faceId + pair.2.1.1 faceId))) := by
  apply natListSum_map_congr
  intro faceId hface
  by_cases hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId
  · simp [restrictNatWeightTo, hcomponent]
  · have hzero : pair.1.1.1 faceId + pair.2.1.1 faceId = 0 := by
      by_cases hsum : pair.1.1.1 faceId + pair.2.1.1 faceId = 0
      · exact hsum
      · have hpositive :
            0 < pair.1.1.1 faceId ∨ 0 < pair.2.1.1 faceId := by
          omega
        exact False.elim (hcomponent
          (slabObservableTwoReplicaPairTargetSupportActiveLink_positiveIncident_mem_component
            D rootFaceId targetFaceId htarget pair hpair
            hlink hface hpositive))
    simp [restrictNatWeightTo, hcomponent, hzero]

/-! ## 3. Exact global factor four -/

/-- The two source replicas' total incident mass over active component links
is at most four times their paired physical mass on the component. -/
theorem activeLinks_incidentPairMass_le_four_mul_componentMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    natListSum
        ((slabObservableTwoReplicaPairTargetSupportActiveLinks
            D pair targetFaceId).map fun link =>
          natListSum
            ((slabIncidentPlaqIds D.extent link).map fun faceId =>
              pair.1.1.1 faceId + pair.2.1.1 faceId)) ≤
      4 * slabObservableTwoReplicaPairTargetSupportMass
        D pair targetFaceId := by
  let component := slabTwoReplicaTargetSupportComponent D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId
  let pairWeight : Nat → Nat := fun faceId =>
    pair.1.1.1 faceId + pair.2.1.1 faceId
  let restrictedWeight := restrictNatWeightTo component pairWeight
  let activeLinks :=
    slabObservableTwoReplicaPairTargetSupportActiveLinks
      D pair targetFaceId
  have hactiveEq :
      natListSum
          (activeLinks.map fun link =>
            natListSum
              ((slabIncidentPlaqIds D.extent link).map pairWeight)) =
        natListSum
          (activeLinks.map fun link =>
            natListSum
              ((slabIncidentPlaqIds D.extent link).map restrictedWeight)) := by
    apply natListSum_map_congr
    intro link hlink
    exact activeLink_incidentPairMass_eq_restricted
      D rootFaceId targetFaceId htarget pair hpair hlink
  have hactiveLe :
      natListSum
          (activeLinks.map fun link =>
            natListSum
              ((slabIncidentPlaqIds D.extent link).map restrictedWeight)) ≤
        natListSum
          ((boundaryCompleteSlabLinks D.extent).map fun link =>
            natListSum
              ((slabIncidentPlaqIds D.extent link).map restrictedWeight)) := by
    apply natListSum_map_le_of_nodup_mem
    · exact
        slabObservableTwoReplicaPairTargetSupportActiveLinks_nodup
          D pair targetFaceId
    · intro link hlink
      exact
        slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
          D pair hlink
  have hrestrictedComponent :
      natListSum
          ((slabPhysicalFaceEdges D.extent).map restrictedWeight) =
        natListSum (component.map pairWeight) := by
    apply natListSum_restrictNatWeightTo_eq_support
    · exact rootComponent_nodup
        (slabSupportFaceAdjacentB D.extent)
        (slabTwoReplicaSupportFaceVertices D.extent
          pair.1.1.1 pair.2.1.1)
        targetFaceId
    · unfold slabPhysicalFaceEdges
      exact rangeNodupLocal _
    · intro faceId hface
      exact
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface
  have hincidence :=
    slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum
      D.extent restrictedWeight
  rw [hactiveEq]
  calc
    natListSum
          (activeLinks.map fun link =>
            natListSum
              ((slabIncidentPlaqIds D.extent link).map restrictedWeight)) ≤
        natListSum
          ((boundaryCompleteSlabLinks D.extent).map fun link =>
            natListSum
              ((slabIncidentPlaqIds D.extent link).map restrictedWeight)) :=
      hactiveLe
    _ = 4 * natListSum
          ((slabPhysicalFaceEdges D.extent).map restrictedWeight) :=
      hincidence
    _ = 4 * natListSum (component.map pairWeight) := by
      rw [hrestrictedComponent]
    _ = 4 * slabObservableTwoReplicaPairTargetSupportMass
          D pair targetFaceId := by
      unfold slabObservableTwoReplicaPairTargetSupportMass
      rw [natListSum_map_eq_listNatWeight pairWeight component]

#print axioms restrictNatWeightTo
#print axioms natListSum_restrictNatWeightTo_eq_support
#print axioms activeLink_incidentPairMass_eq_restricted
#print axioms activeLinks_incidentPairMass_le_four_mul_componentMass

end YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinkMass
