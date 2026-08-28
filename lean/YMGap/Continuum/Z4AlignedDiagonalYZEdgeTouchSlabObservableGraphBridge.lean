/-
# Identify the aligned target graph with the standard assignment graph

The component-preserving target edges were first assembled directly from the
structural local selector.  The observable layer instead looks up each local
auxiliary in a global assignment.  Prove constructively that lookup in the
structural assignment returns the original selector, then identify the two
whole-slab edge lists exactly.  Marked-face disconnection therefore holds for
the repository's standard global assignment graph, not merely a parallel
presentation.

Constructive contract: list recursion, proof irrelevance, and exact graph
equality only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableGraphBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetDisconnection
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Structural lookup recovers the chosen local auxiliary -/

theorem alignedDiagonalSwitchRealizedAssignmentAt_eq :
    forall
      (linkedList :
        List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (alignedDiagonalSwitchRealizedLeftAssignmentFrom linkedList) =
        alignedDiagonalSwitchRealizedLeftAuxiliary linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          alignedDiagonalSwitchRealizedLeftAssignmentFrom]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [alignedDiagonalSwitchRealizedLeftAssignmentFrom,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact alignedDiagonalSwitchRealizedAssignmentAt_eq
          rest linked hrest

/-! ## 2. Exact equality with the standard global edge compiler -/

theorem alignedDiagonalTargetMeasureIndexAssignment_mem_full :
    alignedDiagonalTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5
        alignedDiagonalSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  simpa only [alignedDiagonalTargetMeasureIndexAssignment,
    alignedDiagonalSwitchLinkedList,
    List.attach_map_subtype_val] using
      alignedDiagonalTargetMeasureIndexAssignment_mem

theorem slabLinkFaceStrandEdges_eq_of_auxiliary_eq
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {first second : SlabLabelling}
    (hfirst : first ∈
      slabLinkFusionWitnesses K extent physical link)
    (hsecond : second ∈
      slabLinkFusionWitnesses K extent physical link)
    (heq : first = second) :
    slabLinkFaceStrandEdges K extent physical link first hfirst =
      slabLinkFaceStrandEdges K extent physical link second hsecond := by
  cases heq
  rfl

def alignedDiagonalMeasureFaceStrandEdges :
    List (SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical) :=
  slabFusionWitnessAssignmentFaceStrandEdges 1 5
    alignedDiagonalSwitchLeftPhysical
    (boundaryCompleteSlabLinks 5)
    alignedDiagonalTargetMeasureIndexAssignment
    alignedDiagonalTargetMeasureIndexAssignment_mem_full

theorem alignedDiagonalMeasureFaceStrandEdges_eq_target :
    alignedDiagonalMeasureFaceStrandEdges =
      alignedDiagonalTargetFaceStrandEdges := by
  unfold alignedDiagonalMeasureFaceStrandEdges
    slabFusionWitnessAssignmentFaceStrandEdges
    alignedDiagonalTargetFaceStrandEdges
  change alignedDiagonalSwitchLinkedList.flatMap
      (slabFusionWitnessAssignmentFaceStrandEdgesAt 1 5
        alignedDiagonalSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5)
        alignedDiagonalTargetMeasureIndexAssignment
        alignedDiagonalTargetMeasureIndexAssignment_mem_full) =
    alignedDiagonalSwitchLinkedList.flatMap
      alignedDiagonalTargetFaceStrandEdgesAt
  apply congrArg (fun compiler =>
    alignedDiagonalSwitchLinkedList.flatMap compiler)
  funext linked
  unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
    alignedDiagonalTargetFaceStrandEdgesAt
    alignedDiagonalTargetMeasureIndexAssignment
  have hlookup := alignedDiagonalSwitchRealizedAssignmentAt_eq
    alignedDiagonalSwitchLinkedList linked
    (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
  exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup

theorem alignedDiagonalMeasureFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical)
    (hedge : edge ∈ alignedDiagonalMeasureFaceStrandEdges) :
    AlignedDiagonalFaceStrandEdgeSameSide edge := by
  rw [alignedDiagonalMeasureFaceStrandEdges_eq_target] at hedge
  exact alignedDiagonalTargetFaceStrandEdge_same_side edge hedge

/-! ## 3. Standard-graph marked disconnection -/

def alignedDiagonalMeasureProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges alignedDiagonalMeasureFaceStrandEdges

def alignedDiagonalMeasureFaceVertices : List Nat :=
  slabFaceStrandFaceVertices alignedDiagonalMeasureFaceStrandEdges

def alignedDiagonalMeasureFaceAdjacentB (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB alignedDiagonalMeasureProjectedFaceEdges
    left right

theorem alignedDiagonalMeasureProjectedFaceEdges_eq_target :
    alignedDiagonalMeasureProjectedFaceEdges =
      alignedDiagonalTargetProjectedFaceEdges :=
  congrArg slabProjectedFaceEdges
    alignedDiagonalMeasureFaceStrandEdges_eq_target

theorem alignedDiagonalMeasureFaceVertices_eq_target :
    alignedDiagonalMeasureFaceVertices =
      alignedDiagonalTargetFaceVertices :=
  congrArg slabFaceStrandFaceVertices
    alignedDiagonalMeasureFaceStrandEdges_eq_target

theorem alignedDiagonalMeasureFaceAdjacentB_eq_target :
    alignedDiagonalMeasureFaceAdjacentB =
      alignedDiagonalTargetFaceAdjacentB := by
  funext left right
  unfold alignedDiagonalMeasureFaceAdjacentB
    alignedDiagonalTargetFaceAdjacentB
  rw [alignedDiagonalMeasureProjectedFaceEdges_eq_target]

def transportChainIn
    {adjacent₁ adjacent₂ : Nat → Nat → Bool}
    {vertices₁ vertices₂ : List Nat}
    (hadjacent : adjacent₁ = adjacent₂)
    (hvertices : vertices₁ = vertices₂)
    {first last : Nat} :
    ChainIn adjacent₁ vertices₁ first last →
      ChainIn adjacent₂ vertices₂ first last := by
  cases hadjacent
  cases hvertices
  exact fun path => path

def alignedDiagonalMeasure_noMarkedFaceChain :
    ChainIn alignedDiagonalMeasureFaceAdjacentB
      alignedDiagonalMeasureFaceVertices
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId → False :=
  fun path => by
    apply alignedDiagonalTarget_noMarkedFaceChain
    exact transportChainIn
      alignedDiagonalMeasureFaceAdjacentB_eq_target
      alignedDiagonalMeasureFaceVertices_eq_target path

structure AlignedDiagonalMeasureGraphBridgeCertificate : Type where
  exactEdges : alignedDiagonalMeasureFaceStrandEdges =
    alignedDiagonalTargetFaceStrandEdges
  everyEdgeSameSide : forall edge,
    edge ∈ alignedDiagonalMeasureFaceStrandEdges ->
      AlignedDiagonalFaceStrandEdgeSameSide edge
  markedDisconnected : ChainIn alignedDiagonalMeasureFaceAdjacentB
    alignedDiagonalMeasureFaceVertices
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId → False

def alignedDiagonalMeasureGraphBridgeCertificate :
    AlignedDiagonalMeasureGraphBridgeCertificate :=
  { exactEdges := alignedDiagonalMeasureFaceStrandEdges_eq_target
    everyEdgeSameSide := alignedDiagonalMeasureFaceStrandEdge_same_side
    markedDisconnected := alignedDiagonalMeasure_noMarkedFaceChain }

#print axioms alignedDiagonalSwitchRealizedAssignmentAt_eq
#print axioms slabLinkFaceStrandEdges_eq_of_auxiliary_eq
#print axioms alignedDiagonalMeasureFaceStrandEdges_eq_target
#print axioms alignedDiagonalMeasureFaceStrandEdge_same_side
#print axioms alignedDiagonalMeasureFaceAdjacentB_eq_target
#print axioms alignedDiagonalMeasure_noMarkedFaceChain
#print axioms alignedDiagonalMeasureGraphBridgeCertificate

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableGraphBridge
