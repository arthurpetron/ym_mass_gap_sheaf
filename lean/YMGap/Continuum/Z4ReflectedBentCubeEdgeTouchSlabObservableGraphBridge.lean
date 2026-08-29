/-
# Identify the reflected target graph with the standard assignment graph

Lookup in the structurally assembled assignment returns the original local
selector.  Hence the standard global assignment graph is exactly the already
proved disconnected target graph, not a parallel presentation.

Constructive contract: list recursion, proof irrelevance, and exact graph
equality only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

theorem reflectedBentSwitchRealizedAssignmentAt_eq :
    forall
      (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (reflectedBentSwitchRealizedLeftAssignmentFrom linkedList) =
        reflectedBentSwitchRealizedLeftAuxiliary linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          reflectedBentSwitchRealizedLeftAssignmentFrom]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [reflectedBentSwitchRealizedLeftAssignmentFrom,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact reflectedBentSwitchRealizedAssignmentAt_eq rest linked hrest

theorem reflectedBentTargetMeasureIndexAssignment_mem_full :
    reflectedBentTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5
        reflectedBentSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
  simpa only [reflectedBentTargetMeasureIndexAssignment,
    reflectedBentSwitchLinkedList,
    List.attach_map_subtype_val] using
      reflectedBentTargetMeasureIndexAssignment_mem

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

def reflectedBentMeasureFaceStrandEdges :
    List (SlabFaceStrandEdge reflectedBentSwitchLeftPhysical) :=
  slabFusionWitnessAssignmentFaceStrandEdges 1 5
    reflectedBentSwitchLeftPhysical
    (boundaryCompleteSlabLinks 5)
    reflectedBentTargetMeasureIndexAssignment
    reflectedBentTargetMeasureIndexAssignment_mem_full

theorem reflectedBentMeasureFaceStrandEdges_eq_target :
    reflectedBentMeasureFaceStrandEdges =
      reflectedBentTargetFaceStrandEdges := by
  unfold reflectedBentMeasureFaceStrandEdges
    slabFusionWitnessAssignmentFaceStrandEdges
    reflectedBentTargetFaceStrandEdges
  change reflectedBentSwitchLinkedList.flatMap
      (slabFusionWitnessAssignmentFaceStrandEdgesAt 1 5
        reflectedBentSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5)
        reflectedBentTargetMeasureIndexAssignment
        reflectedBentTargetMeasureIndexAssignment_mem_full) =
    reflectedBentSwitchLinkedList.flatMap
      reflectedBentTargetFaceStrandEdgesAt
  apply congrArg (fun compiler =>
    reflectedBentSwitchLinkedList.flatMap compiler)
  funext linked
  unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
    reflectedBentTargetFaceStrandEdgesAt
    reflectedBentTargetMeasureIndexAssignment
  have hlookup := reflectedBentSwitchRealizedAssignmentAt_eq
    reflectedBentSwitchLinkedList linked
    (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
  exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup

theorem reflectedBentMeasureFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge reflectedBentSwitchLeftPhysical)
    (hedge : edge ∈ reflectedBentMeasureFaceStrandEdges) :
    ReflectedBentFaceStrandEdgeSameSide edge := by
  rw [reflectedBentMeasureFaceStrandEdges_eq_target] at hedge
  exact reflectedBentTargetFaceStrandEdge_same_side edge hedge

def reflectedBentMeasureProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges reflectedBentMeasureFaceStrandEdges

def reflectedBentMeasureFaceVertices : List Nat :=
  slabFaceStrandFaceVertices reflectedBentMeasureFaceStrandEdges

def reflectedBentMeasureFaceAdjacentB (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB reflectedBentMeasureProjectedFaceEdges
    left right

theorem reflectedBentMeasureProjectedFaceEdges_eq_target :
    reflectedBentMeasureProjectedFaceEdges =
      reflectedBentTargetProjectedFaceEdges :=
  congrArg slabProjectedFaceEdges
    reflectedBentMeasureFaceStrandEdges_eq_target

theorem reflectedBentMeasureFaceVertices_eq_target :
    reflectedBentMeasureFaceVertices =
      reflectedBentTargetFaceVertices :=
  congrArg slabFaceStrandFaceVertices
    reflectedBentMeasureFaceStrandEdges_eq_target

theorem reflectedBentMeasureFaceAdjacentB_eq_target :
    reflectedBentMeasureFaceAdjacentB =
      reflectedBentTargetFaceAdjacentB := by
  funext left right
  unfold reflectedBentMeasureFaceAdjacentB
    reflectedBentTargetFaceAdjacentB
  rw [reflectedBentMeasureProjectedFaceEdges_eq_target]

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

def reflectedBentMeasure_noMarkedFaceChain :
    ChainIn reflectedBentMeasureFaceAdjacentB
      reflectedBentMeasureFaceVertices
      reflectedBentRootFaceId reflectedBentTargetFaceId → False :=
  fun path => by
    apply reflectedBentTarget_noMarkedFaceChain
    exact transportChainIn
      reflectedBentMeasureFaceAdjacentB_eq_target
      reflectedBentMeasureFaceVertices_eq_target path

structure ReflectedBentMeasureGraphBridgeCertificate : Type where
  exactEdges : reflectedBentMeasureFaceStrandEdges =
    reflectedBentTargetFaceStrandEdges
  everyEdgeSameSide : forall edge,
    edge ∈ reflectedBentMeasureFaceStrandEdges ->
      ReflectedBentFaceStrandEdgeSameSide edge
  markedDisconnected : ChainIn reflectedBentMeasureFaceAdjacentB
    reflectedBentMeasureFaceVertices
    reflectedBentRootFaceId reflectedBentTargetFaceId → False

def reflectedBentMeasureGraphBridgeCertificate :
    ReflectedBentMeasureGraphBridgeCertificate :=
  { exactEdges := reflectedBentMeasureFaceStrandEdges_eq_target
    everyEdgeSameSide := reflectedBentMeasureFaceStrandEdge_same_side
    markedDisconnected := reflectedBentMeasure_noMarkedFaceChain }

#print axioms reflectedBentSwitchRealizedAssignmentAt_eq
#print axioms slabLinkFaceStrandEdges_eq_of_auxiliary_eq
#print axioms reflectedBentMeasureFaceStrandEdges_eq_target
#print axioms reflectedBentMeasureFaceStrandEdge_same_side
#print axioms reflectedBentMeasureFaceAdjacentB_eq_target
#print axioms reflectedBentMeasure_noMarkedFaceChain
#print axioms reflectedBentMeasureGraphBridgeCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge
