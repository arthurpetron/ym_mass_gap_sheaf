/-
# Transport the separated pivot cylinder to the observable recoupling row

The quarter-mass cylinder is stated on the parametric written-link product.
The observable row uses the propositionally equal whole-slab package list.
This module transports every cylinder target across that equality while
retaining full-row membership and exact product weights.

Constructive contract: equality transport, finite list recursion, and exact
rational weights only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The cylinder is a sublist of the complete target row -/

theorem reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)),
      target ∈ reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
          D hcutoff hextent state linkedList →
        target ∈ finiteBistochasticTargetAssignments
          (linkedList.map fun linked =>
            slabPhysicalPairRecouplingPackageAtLink 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              linked)
  | [], target, htarget => False.elim (List.not_mem_nil htarget)
  | linked :: rest, target, htarget => by
      by_cases hpivot : linked.1 = reflectedBentSwitchPivot
      · simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_true] at htarget
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp htarget
        cases heq
        simp only [List.map_cons, finiteBistochasticTargetAssignments]
        apply List.mem_flatMap.mpr
        refine ⟨
          reflectedBentGuardGraftLocalTargetAtCutoff
            D hcutoff hextent state linked,
          ?_,
          ?_⟩
        · unfold slabPhysicalPairRecouplingPackageAtLink
          exact slabPhysicalPairRecouplingTarget_mem
            (slabIncidentPlaqIds 5 linked.1).length
            (reflectedBentGuardGraftLocalData D hextent state linked)
            (reflectedBentGuardGraftLocalTargetAtCutoff
              D hcutoff hextent state linked)
        exact List.mem_map.mpr ⟨tail, htail, rfl⟩
      · simp only [reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff,
          hpivot, dite_false] at htarget
        obtain ⟨headTarget, hhead, hmapped⟩ :=
          List.mem_flatMap.mp htarget
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hmapped
        cases heq
        have htailFull :=
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
            D hcutoff hextent state rest tail htail
        simp only [List.map_cons, finiteBistochasticTargetAssignments]
        apply List.mem_flatMap.mpr
        refine ⟨headTarget, hhead, ?_⟩
        exact List.mem_map.mpr ⟨tail, htailFull, rfl⟩

/-! ## 2. Exact product entries survive package-list transport -/

theorem finiteBistochasticProductWeight_transport_eqv
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (source : FiniteBistochasticSourceAssignment left)
    (target : FiniteBistochasticTargetAssignment right) :
    finiteBistochasticProductWeight source
        (transportFiniteBistochasticTargetAssignment hpackages target) ≈
      finiteBistochasticProductWeight
        (transportFiniteBistochasticSourceAssignment hpackages source)
        target := by
  cases hpackages
  exact Q'.eqv_refl _

/-! ## 3. A normalization-free observable-row presentation -/

/-- A row written on any propositionally equal package list.  The source-row
field is transported back to the explicit guarded production source once,
preventing downstream target transport from expanding a concrete dependent
product. -/
structure ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) : Type 2 where
  packages : List FiniteBistochasticQKernelPackage
  packages_eq : packages =
    linkedList.map fun linked =>
      slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked
  source : FiniteBistochasticSourceAssignment packages
  source_eq : transportFiniteBistochasticSourceAssignment packages_eq source =
    slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      (reflectedBentGuardGraftLeftAssignment D hextent state)
      (reflectedBentGuardGraftRightAssignment D hextent state)
      (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
        D hcutoff hextent state)
      linkedList

/-- One transported observable target retains its reference target, event
membership, exact transport package, and the reference disconnection witness.
-/
structure ReflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList) : Type where
  sourceTarget : FiniteBistochasticTargetAssignment
    (linkedList.map fun linked =>
      slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked)
  sourceTarget_mem : sourceTarget ∈ event.targets
  targetPackage : TransportedTargetPackage row.packages
    (linkedList.map fun linked =>
      slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked)
    row.packages_eq
  targetPackage_source : targetPackage.sourceTarget = sourceTarget
  disconnected :
    ReflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff
      D hcutoff hextent state linkedList sourceTarget

def reflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList)
    (target : {target // target ∈ event.targets}) :
    ReflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
      D hcutoff hextent state linkedList row event where
  sourceTarget := target.1
  sourceTarget_mem := target.2
  targetPackage := transportedTargetPackage row.packages_eq
    { target := target.1
      target_mem :=
        reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
          D hcutoff hextent state linkedList target.1
            (event.targets_eq ▸ target.2) }
  targetPackage_source := by
    exact transportedTargetPackage_sourceTarget row.packages_eq
      { target := target.1
        target_mem :=
          reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
            D hcutoff hextent state linkedList target.1
              (event.targets_eq ▸ target.2) }
  disconnected := event.every_target_disconnected target.1 target.2

def reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList) :
    List (ReflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
      D hcutoff hextent state linkedList row event) :=
  event.targets.attach.map fun target =>
    reflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
      D hcutoff hextent state linkedList row event target

def reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList)
    (choice : ReflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
      D hcutoff hextent state linkedList row event) : Q' :=
  finiteBistochasticProductWeight row.source choice.targetPackage.target

theorem reflectedBentGuardGraftPivotCylinderTransportedChoiceWeight_eqv
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList)
    (choice : ReflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
      D hcutoff hextent state linkedList row event) :
    reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
        D hcutoff hextent state linkedList row event choice ≈
      reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
        D hcutoff hextent state linkedList choice.sourceTarget := by
  unfold reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
    reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
  rw [choice.targetPackage.target_eq, choice.targetPackage_source]
  have htransport := finiteBistochasticProductWeight_transport_eqv
    row.packages_eq row.source choice.sourceTarget
  rw [row.source_eq] at htransport
  exact htransport

theorem reflectedBentGuardGraftPivotCylinderTransportedChoices_weight_sum_eqv
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList) :
    listQSum
        (reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
          D hcutoff hextent state linkedList row event)
        (reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
          D hcutoff hextent state linkedList row event) ≈
      listQSum
        (reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList)
        event.targets := by
  unfold reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun target : {target // target ∈ event.targets} =>
        reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList target.1)
      event.targets.attach) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact reflectedBentGuardGraftPivotCylinderTransportedChoiceWeight_eqv
      D hcutoff hextent state linkedList row event
        (reflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
          D hcutoff hextent state linkedList row event target)
  · exact Q'.eqv_of_eq
      (listQSum_attach
        (reflectedBentGuardGraftPivotCylinderRowWeightFromAtCutoff
          D hcutoff hextent state linkedList)
        event.targets)

/-- The transported row contains a literal target list of total weight at
least `1/4`, and every listed target retains its disconnection witness. -/
theorem reflectedBentGuardGraftPivotCylinderTransportedChoices_weight_floor
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state linkedList)
    (event : ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state linkedList) :
    oneQuarter ≤
      listQSum
        (reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
          D hcutoff hextent state linkedList row event)
        (reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
          D hcutoff hextent state linkedList row event) := by
  exact Q'.le_trans' _ _ _ event.weight_floor
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (reflectedBentGuardGraftPivotCylinderTransportedChoices_weight_sum_eqv
          D hcutoff hextent state linkedList row event)))

#print axioms reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff_mem_full
#print axioms finiteBistochasticProductWeight_transport_eqv
#print axioms reflectedBentGuardGraftPivotCylinderTransportedChoiceAtCutoff
#print axioms reflectedBentGuardGraftPivotCylinderTransportedChoiceWeight_eqv
#print axioms reflectedBentGuardGraftPivotCylinderTransportedChoices_weight_sum_eqv
#print axioms reflectedBentGuardGraftPivotCylinderTransportedChoices_weight_floor

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
