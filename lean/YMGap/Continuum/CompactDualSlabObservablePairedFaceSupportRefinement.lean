/-
# The paired strand graph refines the physical union-support graph

The paired-face switch graph remembers the literal SU(2) strand pairings of
both accepted replicas.  The paired-support graph forgets those pairings and
joins every two positive faces incident on one physical slab link.  Hence
every paired-face edge is a paired-support edge, and every paired-face vertex
is a union-support vertex.

This module packages those facts as a rooted finite-graph homomorphism.  Its
load-bearing consequence is exact: if the target and root are disconnected
in the coarser physical-support graph, then they remain disconnected in the
paired strand graph for every accepted auxiliary assignment.  Conversely,
recoupling may disconnect the finer strand graph even when physical support
is connected.  That strict asymmetry is the mathematical opening for a
positive SU(2) posterior fraction.

Constructive contract: finite graph witnesses and literal slab incidence
only; no `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
import YMGap.Continuum.FiniteBoolGraphRootComponentMap

namespace YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteBoolGraphRootComponentMap
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Decode the finite projected-face carriers -/

/-- A true projected-face adjacency returns its first literal edge and one
of the two possible orientations. -/
def slabProjectedFaceAdjacentEdgeWitness
    (left right : Nat) :
    forall edges : List SlabProjectedFaceEdge,
      slabProjectedFaceAdjacentB edges left right = true ->
      Sigma fun edge : SlabProjectedFaceEdge =>
        (edge ∈ edges) ×'
          (((edge.source = left) ×' (edge.target = right)) ⊕'
            ((edge.source = right) ×' (edge.target = left)))
  | [], hadj => by cases hadj
  | edge :: edges, hadj => by
      by_cases hforward : edge.source = left ∧ edge.target = right
      · exact ⟨edge, List.mem_cons_self,
          PSum.inl ⟨hforward.1, hforward.2⟩⟩
      · by_cases hreverse : edge.source = right ∧ edge.target = left
        · exact ⟨edge, List.mem_cons_self,
            PSum.inr ⟨hreverse.1, hreverse.2⟩⟩
        · have htail :
              slabProjectedFaceAdjacentB edges left right = true := by
            simpa [slabProjectedFaceAdjacentB,
              slabProjectedFaceEdgeConnectsB,
              hforward, hreverse] using hadj
          obtain ⟨found, hfound, horientation⟩ :=
            slabProjectedFaceAdjacentEdgeWitness left right edges htail
          exact ⟨found, List.mem_cons_of_mem edge hfound, horientation⟩

private theorem copyFace_mem_support
    {extent : Nat} {left right : SlabLabelling}
    {current : SlabLabelling}
    (hcurrent : current = left ∨ current = right)
    (copy : SlabFaceStrandCopy current)
    (hphysical : copy.faceId ∈ slabPhysicalFaceEdges extent) :
    copy.faceId ∈
      slabTwoReplicaSupportFaceVertices extent left right := by
  have hpositive : 0 < current copy.faceId :=
    Nat.zero_lt_of_lt copy.slot.isLt
  apply mem_slabTwoReplicaSupportFaceVertices hphysical
  rcases hcurrent with rfl | rfl
  · exact Or.inl hpositive
  · exact Or.inr hpositive

private theorem strandVertexFace_mem_support
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      slabObservableTwoReplicaPairPairedFaceVertices D pair) :
    faceId ∈ slabTwoReplicaSupportFaceVertices D.extent
      pair.1.1.1 pair.2.1.1 := by
  unfold slabObservableTwoReplicaPairPairedFaceVertices at hface
  rcases List.mem_append.mp hface with hleft | hright
  · unfold slabFaceStrandFaceVertices at hleft
    obtain ⟨copy, hcopy, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨edge, hedge, hendpoint⟩ := List.mem_flatMap.mp hcopy
    have hphysical :=
      slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
        D.cutoff D.extent pair.1.1.1
        (boundaryCompleteSlabLinks D.extent)
        pair.1.1.2 pair.1.assignment_mem hedge
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
    rcases hendpoint with rfl | rfl
    · exact copyFace_mem_support (Or.inl rfl) edge.source hphysical.1
    · exact copyFace_mem_support (Or.inl rfl) edge.target hphysical.2
  · unfold slabFaceStrandFaceVertices at hright
    obtain ⟨copy, hcopy, rfl⟩ := List.mem_map.mp hright
    obtain ⟨edge, hedge, hendpoint⟩ := List.mem_flatMap.mp hcopy
    have hphysical :=
      slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
        D.cutoff D.extent pair.2.1.1
        (boundaryCompleteSlabLinks D.extent)
        pair.2.1.2
        (slabExpandedFineSourceEntryAssignment_mem pair.2) hedge
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
    rcases hendpoint with rfl | rfl
    · exact copyFace_mem_support (Or.inr rfl) edge.source hphysical.1
    · exact copyFace_mem_support (Or.inr rfl) edge.target hphysical.2

/-! ## 2. Every projected strand edge is a support edge -/

private theorem supportAdjacent_of_physicalPlaquetteAdjacent
    {extent left right : Nat}
    (hleft : left ∈ slabPhysicalFaceEdges extent)
    (hright : right ∈ slabPhysicalFaceEdges extent)
    (hadj : z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left)
      (slabPlaquetteAt extent right)) :
    slabSupportFaceAdjacentB extent left right = true := by
  have hleftEdge : hadj.link ∈
      edgesOf (slabPlaquetteAt extent left) :=
    of_decide_eq_true hadj.on_p
  have hrightEdge : hadj.link ∈
      edgesOf (slabPlaquetteAt extent right) :=
    of_decide_eq_true hadj.on_q
  have hlink : hadj.link ∈ boundaryCompleteSlabLinks extent := by
    apply (mem_boundaryCompleteSlabLinks_iff extent hadj.link).mpr
    exact ⟨slabPlaquetteAt extent left,
      slabPlaquetteAt_mem hleft, hleftEdge⟩
  have hleftIncident : left ∈
      slabIncidentPlaqIds extent hadj.link := by
    apply mem_slabIncidentPlaqIds.mpr
    exact ⟨slabPlaquetteAt extent left,
      slabPlaquetteAt_mem_enumerate hleft, hleftEdge⟩
  have hrightIncident : right ∈
      slabIncidentPlaqIds extent hadj.link := by
    apply mem_slabIncidentPlaqIds.mpr
    exact ⟨slabPlaquetteAt extent right,
      slabPlaquetteAt_mem_enumerate hright, hrightEdge⟩
  exact slabSupportFaceAdjacentB_true_of_link
    hlink hleftIncident hrightIncident

private theorem leftStrandEdge_supportAdjacent
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    {edge : SlabFaceStrandEdge pair.1.1.1}
    (hedge : edge ∈
      slabObservableTwoReplicaPairLeftStrandEdges D pair) :
    slabSupportFaceAdjacentB D.extent
      edge.source.faceId edge.target.faceId = true := by
  have hphysical :=
    slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
      D.cutoff D.extent pair.1.1.1
      (boundaryCompleteSlabLinks D.extent)
      pair.1.1.2 pair.1.assignment_mem hedge
  have hadjacent :=
    slabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
      D.cutoff D.extent pair.1.1.1
      (boundaryCompleteSlabLinks D.extent)
      pair.1.1.2 pair.1.assignment_mem
      edge.source edge.target
      (slabFaceStrandAdjacentB_true_of_mem hedge)
  exact supportAdjacent_of_physicalPlaquetteAdjacent
    hphysical.1 hphysical.2 hadjacent

private theorem rightStrandEdge_supportAdjacent
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    {edge : SlabFaceStrandEdge pair.2.1.1}
    (hedge : edge ∈
      slabObservableTwoReplicaPairRightStrandEdges D pair) :
    slabSupportFaceAdjacentB D.extent
      edge.source.faceId edge.target.faceId = true := by
  have hphysical :=
    slabFusionWitnessAssignmentFaceStrandEdge_endpoints_physical
      D.cutoff D.extent pair.2.1.1
      (boundaryCompleteSlabLinks D.extent)
      pair.2.1.2
      (slabExpandedFineSourceEntryAssignment_mem pair.2) hedge
  have hadjacent :=
    slabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
      D.cutoff D.extent pair.2.1.1
      (boundaryCompleteSlabLinks D.extent)
      pair.2.1.2
      (slabExpandedFineSourceEntryAssignment_mem pair.2)
      edge.source edge.target
      (slabFaceStrandAdjacentB_true_of_mem hedge)
  exact supportAdjacent_of_physicalPlaquetteAdjacent
    hphysical.1 hphysical.2 hadjacent

private theorem projectedStrandEdge_supportAdjacent
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    {edge : SlabProjectedFaceEdge}
    (hedge : edge ∈
      slabObservableTwoReplicaPairPairedFaceEdges D pair) :
    slabSupportFaceAdjacentB D.extent edge.source edge.target = true := by
  unfold slabObservableTwoReplicaPairPairedFaceEdges at hedge
  rcases List.mem_append.mp hedge with hleft | hright
  · obtain ⟨strandEdge, hstrand, hedgeEq⟩ := List.mem_map.mp hleft
    rw [← hedgeEq]
    exact leftStrandEdge_supportAdjacent D pair hstrand
  · obtain ⟨strandEdge, hstrand, hedgeEq⟩ := List.mem_map.mp hright
    rw [← hedgeEq]
    exact rightStrandEdge_supportAdjacent D pair hstrand

theorem slabObservableTwoReplicaPairPairedFaceAdjacent_imp_supportAdjacent
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (left right : Nat)
    (hadjacent : slabObservableTwoReplicaPairPairedFaceAdjacentB
      D pair left right = true) :
    slabSupportFaceAdjacentB D.extent left right = true := by
  obtain ⟨edge, hedge, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      (slabObservableTwoReplicaPairPairedFaceEdges D pair) hadjacent
  have hedgeAdjacent := projectedStrandEdge_supportAdjacent D pair hedge
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hedgeAdjacent
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      rw [slabSupportFaceAdjacentB_symmetric D.extent]
      exact hedgeAdjacent

/-! ## 3. Rooted component refinement -/

def slabObservablePairedFaceToSupportGraphHom
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    RootedFiniteBoolGraphHom
      (slabObservableTwoReplicaPairPairedFaceAdjacentB D pair)
      (slabObservableTwoReplicaPairPairedFaceVertices D pair)
      targetFaceId
      (slabSupportFaceAdjacentB D.extent)
      (slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1)
      targetFaceId where
  toFun := fun faceId => faceId
  map_root := rfl
  map_vertex := strandVertexFace_mem_support D pair
  map_edge := fun left right _ _ hadjacent =>
    slabObservableTwoReplicaPairPairedFaceAdjacent_imp_supportAdjacent
      D pair left right hadjacent

/-- Every face in the target-rooted paired strand component belongs to the
target-rooted physical union-support component. -/
theorem slabObservableTwoReplicaPairTargetFaceComponent_subset_support
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    {faceId : Nat}
    (hface : faceId ∈
      slabObservableTwoReplicaPairTargetFaceComponent
        D pair targetFaceId) :
    faceId ∈ slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId := by
  let hom := slabObservablePairedFaceToSupportGraphHom
    D pair targetFaceId
  have hsourceRoot :=
    slabObservableTwoReplicaPairTarget_mem_pairedFaceVertices
      D rootFaceId targetFaceId htarget pair hpair
  have htargetPositive :=
    slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
      D rootFaceId targetFaceId pair hpair
  have htargetRoot : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1 :=
    mem_slabTwoReplicaSupportFaceVertices htarget
      (Or.inl htargetPositive)
  exact hom.map_mem_targetRootComponent
    (slabObservableTwoReplicaPairPairedFaceAdjacentB_symmetric D pair)
    (slabSupportFaceAdjacentB_symmetric D.extent)
    hsourceRoot htargetRoot hface

/-- Fine paired-strand connectivity implies coarse union-support
connectivity. -/
theorem slabObservableTwoReplicaPairPairedFaceConnected_imp_supportConnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = true) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId pair = true := by
  have hrootFace : rootFaceId ∈
      slabObservableTwoReplicaPairTargetFaceComponent
        D pair targetFaceId := by
    unfold slabObservableTwoReplicaPairPairedFaceConnectedB
      slabObservableTwoReplicaPairPairedFaceSwapMask at hconnected
    exact of_decide_eq_true hconnected
  have hrootSupport :=
    slabObservableTwoReplicaPairTargetFaceComponent_subset_support
      D rootFaceId targetFaceId htarget pair hpair hrootFace
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
  exact decide_eq_true hrootSupport

/-- **Support disconnection is stable under every accepted strand
resolution.**  This is the exact full-row law needed by the posterior
recoupling construction. -/
theorem slabObservableTwoReplicaPairPairedFaceDisconnected_of_supportDisconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hdisconnected : slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId pair = false) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = false := by
  cases hface : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair with
  | false => rfl
  | true =>
      have hsupport :=
        slabObservableTwoReplicaPairPairedFaceConnected_imp_supportConnected
          D rootFaceId targetFaceId htarget pair hpair hface
      rw [hdisconnected] at hsupport
      cases hsupport

end YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement.slabObservableTwoReplicaPairPairedFaceAdjacent_imp_supportAdjacent
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement.slabObservablePairedFaceToSupportGraphHom
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement.slabObservableTwoReplicaPairTargetFaceComponent_subset_support
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement.slabObservableTwoReplicaPairPairedFaceConnected_imp_supportConnected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement.slabObservableTwoReplicaPairPairedFaceDisconnected_of_supportDisconnected
