/-
# Canonical paired peeling is local to the initial support component

The global physical code records only the target-rooted union-support
component.  To use that code for reconstruction, canonical peeling must not
alter physical labels outside this initial component.

The proof is geometric.  A rooted strand component projects to a path of
genuinely adjacent slab plaquettes.  Every copy on that path is positive in
the current state and current labels are pointwise below the initial pair, so
all projected faces lie in the initial union-support carrier.  Component
closure then keeps the entire peel inside the initial target component.

This module first proves that statement for one accepted paired choice.  It
then propagates it through the well-founded canonical iteration.

Constructive contract: Type-valued strand paths, finite root-component
closure, and pointwise natural subtraction only; no choice, `Classical`,
`sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Genuine plaquette adjacency induces support-graph adjacency -/

/-- Two physical slab face ids whose decoded plaquettes share a lattice link
are adjacent in the fixed complete-slab support graph. -/
theorem slabSupportFaceAdjacentB_true_of_physicalPlaquetteAdjacent
    {extent left right : Nat}
    (hleft : left ∈ slabPhysicalFaceEdges extent)
    (hright : right ∈ slabPhysicalFaceEdges extent)
    (hadj : z4Chain.toLattice.Adjacent
      (slabPlaquetteAt extent left)
      (slabPlaquetteAt extent right)) :
    slabSupportFaceAdjacentB extent left right = true := by
  have hleftEdge : hadj.link ∈
      edgesOf (slabPlaquetteAt extent left) := by
    exact of_decide_eq_true hadj.on_p
  have hrightEdge : hadj.link ∈
      edgesOf (slabPlaquetteAt extent right) := by
    exact of_decide_eq_true hadj.on_q
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

/-! ## 2. A current strand component stays in the initial face component -/

private theorem componentChain_faceId_mem_initialTargetComponent
    {K extent targetFaceId : Nat}
    {initialLeft initialRight current : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent current links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent current links assignment hassignment)
    (htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices extent initialLeft initialRight)
    (hcurrentSupport : ∀ faceId, 0 < current faceId →
      0 < initialLeft faceId ∨ 0 < initialRight faceId) :
    {left right : SlabFaceStrandCopy current} →
      ChainIn
        (slabFaceStrandAdjacentB
          (slabFusionWitnessAssignmentFaceStrandEdges
            K extent current links assignment hassignment))
        seed.component left right →
      left.faceId ∈ slabTwoReplicaTargetSupportComponent
        extent initialLeft initialRight targetFaceId →
      left.faceId ∈ slabPhysicalFaceEdges extent →
      right.faceId ∈ slabTwoReplicaTargetSupportComponent
        extent initialLeft initialRight targetFaceId
  | _, _, FiniteBoolGraphComponents.ChainIn.refl _, hleftComponent, _ =>
      hleftComponent
  | left, _right,
      FiniteBoolGraphComponents.ChainIn.step (b := next)
        hadj hnext rest,
      hleftComponent, hleftPhysical => by
      have hnextPhysical :=
        SlabFusionWitnessFaceStrandSeed.component_faceId_physical
          seed next hnext
      have hnextPositive : 0 < current next.faceId := by
        exact Nat.zero_lt_of_lt next.slot.isLt
      have hnextVertex : next.faceId ∈
          slabTwoReplicaSupportFaceVertices
            extent initialLeft initialRight :=
        mem_slabTwoReplicaSupportFaceVertices hnextPhysical
          (hcurrentSupport next.faceId hnextPositive)
      have hplaquette :=
        slabFusionWitnessAssignmentFaceStrandAdjacentToPlaquetteAdjacent
          K extent current links assignment hassignment left next hadj
      have hsupportAdj :=
        slabSupportFaceAdjacentB_true_of_physicalPlaquetteAdjacent
          hleftPhysical hnextPhysical hplaquette
      have hnextComponent : next.faceId ∈
          slabTwoReplicaTargetSupportComponent
            extent initialLeft initialRight targetFaceId := by
        exact rootComponent_closed_under_edge
          (slabSupportFaceAdjacentB extent)
          (slabSupportFaceAdjacentB_symmetric extent)
          htargetVertex hleftComponent hnextVertex hsupportAdj
      exact componentChain_faceId_mem_initialTargetComponent
        seed htargetVertex hcurrentSupport rest hnextComponent hnextPhysical

/-- Every physical face-copy in a current rooted strand component belongs to
the initial target-rooted union-support component whenever the current
one-replica labelling is pointwise below the chosen initial replica. -/
theorem SlabFusionWitnessFaceStrandSeed.component_faceId_mem_initialTargetComponent
    {K extent targetFaceId : Nat}
    {initialLeft initialRight current : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent current links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent current links assignment hassignment)
    (htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices extent initialLeft initialRight)
    (hcurrentSupport : ∀ faceId, 0 < current faceId →
      0 < initialLeft faceId ∨ 0 < initialRight faceId)
    (hroot : seed.root.faceId ∈
      slabTwoReplicaTargetSupportComponent
        extent initialLeft initialRight targetFaceId)
    (copy : SlabFaceStrandCopy current) (hcopy : copy ∈ seed.component) :
    copy.faceId ∈ slabTwoReplicaTargetSupportComponent
      extent initialLeft initialRight targetFaceId := by
  have hrootMem : seed.root ∈ seed.component := by
    unfold SlabFaceStrandSeed.component
    exact root_mem_rootComponent
      (slabFaceStrandAdjacentB
        (slabFusionWitnessAssignmentFaceStrandEdges
          K extent current links assignment hassignment))
      seed.root_mem
  have hchain := rootComponent_connected
    (slabFaceStrandAdjacentB
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent current links assignment hassignment))
    (slabFaceStrandAdjacentB_symmetric
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent current links assignment hassignment))
    seed.root_mem seed.root copy hrootMem hcopy
  have hrootPhysical :=
    SlabFusionWitnessFaceStrandSeed.component_faceId_physical
      seed seed.root hrootMem
  exact componentChain_faceId_mem_initialTargetComponent
    seed htargetVertex hcurrentSupport hchain hroot hrootPhysical

/-- Consequently a rooted strand selection removes zero copies at every face
outside the initial target-rooted support component. -/
theorem SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_mem_initialTargetComponent
    {K extent targetFaceId : Nat}
    {initialLeft initialRight current : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent current links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent current links assignment hassignment)
    (htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices extent initialLeft initialRight)
    (hcurrentSupport : ∀ faceId, 0 < current faceId →
      0 < initialLeft faceId ∨ 0 < initialRight faceId)
    (hroot : seed.root.faceId ∈
      slabTwoReplicaTargetSupportComponent
        extent initialLeft initialRight targetFaceId)
    (faceId : Nat)
    (houtside : faceId ∉ slabTwoReplicaTargetSupportComponent
      extent initialLeft initialRight targetFaceId) :
    slabFaceStrandSelectionCount seed.selected faceId = 0 := by
  by_cases hfacePhysical : faceId ∈ slabPhysicalFaceEdges extent
  · apply selectionCount_eq_zero_of_not_mem_decodedSupport seed faceId
    intro hdecoded
    have hgeometric :=
      (componentDecodedPlaquetteSupport_sameSupport seed).2
        (slabPlaquetteAt extent faceId) hdecoded
    obtain ⟨copy, hcopy, hprojection⟩ :=
      (mem_componentPlaquetteSupport_iff
        seed (slabPlaquetteAt extent faceId)).mp hgeometric
    have hcopyComponent :=
      SlabFusionWitnessFaceStrandSeed.component_faceId_mem_initialTargetComponent
        seed htargetVertex hcurrentSupport hroot copy hcopy
    have hcopyPhysical :=
      SlabFusionWitnessFaceStrandSeed.component_faceId_physical
        seed copy hcopy
    have hfaceEq : copy.faceId = faceId :=
      slabPlaquetteAt_injective_on_physical
        hcopyPhysical hfacePhysical hprojection
    apply houtside
    rw [← hfaceEq]
    exact hcopyComponent
  · exact
      SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_physical
        seed faceId hfacePhysical

/-! ## 3. One paired peel is pointwise identical outside the component -/

/-- Pointwise physical domination of one accepted pair by another. -/
def SlabAcceptedPairPhysicalLE
    {D : SlabPhysicalData}
    (current initial : SlabAcceptedTwoReplicaState D) : Prop :=
  ∀ faceId,
    current.1.1.1 faceId ≤ initial.1.1.1 faceId ∧
      current.2.1.1 faceId ≤ initial.2.1.1 faceId

theorem SlabAcceptedPairedPeelChoice.lowerState_physical_eq_of_not_mem_initialTargetComponent
    {D : SlabPhysicalData} {targetFaceId : Nat}
    {initial state : SlabAcceptedTwoReplicaState D}
    (htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices D.extent
        initial.1.1.1 initial.2.1.1)
    (hstate : SlabAcceptedPairPhysicalLE state initial)
    (choice : SlabAcceptedPairedPeelChoice D state)
    (hroot : choice.faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        initial.1.1.1 initial.2.1.1 targetFaceId)
    (queryFaceId : Nat)
    (houtside : queryFaceId ∉
      slabTwoReplicaTargetSupportComponent D.extent
        initial.1.1.1 initial.2.1.1 targetFaceId) :
    choice.lowerState.1.1.1 queryFaceId = state.1.1.1 queryFaceId ∧
      choice.lowerState.2.1.1 queryFaceId = state.2.1.1 queryFaceId := by
  cases choice with
  | left faceId hface hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        D faceId hface state.1 hpositive
      have hzero :=
        SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_mem_initialTargetComponent
          seed htargetVertex (fun query hpositive =>
            Or.inl (by
              have hle := (hstate query).1
              omega))
          hroot queryFaceId houtside
      constructor
      · change
          state.1.1.1 queryFaceId -
              slabFaceStrandSelectionCount seed.selected queryFaceId =
            state.1.1.1 queryFaceId
        rw [hzero, Nat.sub_zero]
      · rfl
  | right faceId hface hleftZero hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        D faceId hface state.2 hpositive
      have hzero :=
        SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_mem_initialTargetComponent
          seed htargetVertex (fun query hpositive =>
            Or.inr (by
              have hle := (hstate query).2
              omega))
          hroot queryFaceId houtside
      constructor
      · rfl
      · change
          state.2.1.1 queryFaceId -
              slabFaceStrandSelectionCount seed.selected queryFaceId =
            state.2.1.1 queryFaceId
        rw [hzero, Nat.sub_zero]

/-! ## 4. Locality persists through the complete canonical iteration -/

theorem SlabAcceptedPairedPeelChoice.lowerState_physicalLE
    {D : SlabPhysicalData}
    {initial state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state)
    (hstate : SlabAcceptedPairPhysicalLE state initial) :
    SlabAcceptedPairPhysicalLE choice.lowerState initial := by
  intro faceId
  have hstep :=
    YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass.SlabAcceptedPairedPeelChoice.lowerState_physical_le
      choice faceId
  have hinitial := hstate faceId
  exact ⟨Nat.le_trans hstep.1 hinitial.1,
    Nat.le_trans hstep.2 hinitial.2⟩

/-- For any current state dominated by a fixed initial pair, canonical
peeling of the initial target component leaves every outside physical value
literally unchanged. -/
theorem slabAcceptedPairCanonicalPeeling_final_physical_eq_of_not_mem_initialTargetComponent
    (D : SlabPhysicalData) (targetFaceId : Nat)
    (initial : SlabAcceptedTwoReplicaState D)
    (htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices D.extent
        initial.1.1.1 initial.2.1.1)
    (hphysical : ∀ faceId,
      faceId ∈ slabTwoReplicaTargetSupportComponent D.extent
        initial.1.1.1 initial.2.1.1 targetFaceId →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D)
    (hstate : SlabAcceptedPairPhysicalLE state initial) :
    ∀ queryFaceId,
      queryFaceId ∉ slabTwoReplicaTargetSupportComponent D.extent
        initial.1.1.1 initial.2.1.1 targetFaceId →
      let finalState :=
        (slabAcceptedPairCanonicalPeeling D
          (slabTwoReplicaTargetSupportComponent D.extent
            initial.1.1.1 initial.2.1.1 targetFaceId)
          hphysical state).1
      finalState.1.1.1 queryFaceId = state.1.1.1 queryFaceId ∧
        finalState.2.1.1 queryFaceId = state.2.1.1 queryFaceId := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro queryFaceId houtside
    exact ⟨rfl, rfl⟩
  · rename_i choice hchoice
    intro queryFaceId houtside
    have hroot : choice.faceId ∈
        slabTwoReplicaTargetSupportComponent D.extent
          initial.1.1.1 initial.2.1.1 targetFaceId :=
      slabAcceptedPairCanonicalChoice?_some_face_mem
        D state
        (slabTwoReplicaTargetSupportComponent D.extent
          initial.1.1.1 initial.2.1.1 targetFaceId)
        hphysical choice hchoice
    have hstep :=
      YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.SlabAcceptedPairedPeelChoice.lowerState_physical_eq_of_not_mem_initialTargetComponent
        htargetVertex hstate choice hroot queryFaceId houtside
    have htail :=
      slabAcceptedPairCanonicalPeeling_final_physical_eq_of_not_mem_initialTargetComponent
        D targetFaceId initial htargetVertex hphysical choice.lowerState
        (YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.SlabAcceptedPairedPeelChoice.lowerState_physicalLE
          choice hstate) queryFaceId houtside
    exact ⟨htail.1.trans hstep.1, htail.2.trans hstep.2⟩
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 5. Observable specialization -/

/-- The complete observable target-support peel is physically identical to
its source pair at every face outside the original target component. -/
theorem slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (queryFaceId : Nat)
    (houtside : queryFaceId ∉
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) :
    let finalState :=
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget pair hpair).1
    finalState.1.1.1 queryFaceId = pair.1.1.1 queryFaceId ∧
      finalState.2.1.1 queryFaceId = pair.2.1.1 queryFaceId := by
  have htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices D.extent
        pair.1.1.1 pair.2.1.1 := by
    apply mem_slabTwoReplicaSupportFaceVertices htarget
    exact Or.inl
      (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
        D rootFaceId targetFaceId pair hpair)
  have hlocal :=
    slabAcceptedPairCanonicalPeeling_final_physical_eq_of_not_mem_initialTargetComponent
      D targetFaceId
      (slabObservableTwoReplicaPairToAcceptedState pair)
      htargetVertex
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)
      (fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩)
      queryFaceId houtside
  simpa only [slabObservablePairTargetSupportCanonicalPeeling,
    slabObservableTwoReplicaPairToAcceptedState,
    slabObservablePositiveSourceEntryToAccepted] using hlocal

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.slabSupportFaceAdjacentB_true_of_physicalPlaquetteAdjacent
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.SlabFusionWitnessFaceStrandSeed.component_faceId_mem_initialTargetComponent
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_mem_initialTargetComponent
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.SlabAcceptedPairedPeelChoice.lowerState_physical_eq_of_not_mem_initialTargetComponent
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.slabAcceptedPairCanonicalPeeling_final_physical_eq_of_not_mem_initialTargetComponent
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality.slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
