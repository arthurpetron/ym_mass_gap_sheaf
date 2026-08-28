/-
# Global strand edges of the reflected bent-cube target

At the pivot, the selected `(1,0)` carrier preserves both lobes; away from
the pivot, the unique-shared-link theorem gives the same conclusion for every
accepted carrier.  Assemble the literal local terminal-pair lists over all
corrected-slab links and retain the accepted global measure index.

Constructive contract: explicit finite edge data and structural assembly
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

def ReflectedBentFaceStrandEdgeSameSide
    (edge : SlabFaceStrandEdge reflectedBentSwitchLeftPhysical) : Prop :=
  (slabPlaquetteAt 5 edge.source.faceId ∈ reflectedBentNearSurface ∧
    slabPlaquetteAt 5 edge.target.faceId ∈ reflectedBentNearSurface) ∨
  (slabPlaquetteAt 5 edge.source.faceId ∈ reflectedBentFarSurface ∧
    slabPlaquetteAt 5 edge.target.faceId ∈ reflectedBentFarSurface)

def reflectedBentTargetFaceStrandEdgesAt
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List (SlabFaceStrandEdge reflectedBentSwitchLeftPhysical) :=
  slabLinkFaceStrandEdges 1 5 reflectedBentSwitchLeftPhysical linked.1
    (reflectedBentSwitchRealizedLeftAuxiliary linked)
    (reflectedBentSwitchRealizedLeftAuxiliary_mem linked)

theorem reflectedBentTargetTerminal_pair_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      reflectedBentSwitchLeftPhysical linked.1
      (reflectedBentSwitchRealizedLeftAuxiliary linked)
      (reflectedBentSwitchRealizedLeftAuxiliary_mem linked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      reflectedBentSwitchLeftPhysical linked.1
      (reflectedBentSwitchRealizedLeftAuxiliary linked)
      (reflectedBentSwitchRealizedLeftAuxiliary_mem linked) terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical linked.1
        (reflectedBentSwitchRealizedLeftAuxiliary linked)
        (reflectedBentSwitchRealizedLeftAuxiliary_mem linked)
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical linked.1
        (reflectedBentSwitchRealizedLeftAuxiliary linked)
        (reflectedBentSwitchRealizedLeftAuxiliary_mem linked)
        partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
        targetFace ∈ reflectedBentNearSurface) ∨
      (sourceFace ∈ reflectedBentFarSurface ∧
        targetFace ∈ reflectedBentFarSurface) := by
  by_cases hpivot : linked.1 = reflectedBentSwitchPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        simpa only [reflectedBentSwitchRealizedLeftAuxiliary,
          if_pos rfl] using
          reflectedBentPivotTerminal_pair_same_side
            reflectedBentPivotLeftAuxiliary_mem terminal
  · exact reflectedBentNonpivotTerminal_pair_same_side hpivot
      (reflectedBentSwitchRealizedLeftAuxiliary_mem linked) terminal

theorem reflectedBentTargetFaceStrandEdgeAt_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (edge : SlabFaceStrandEdge reflectedBentSwitchLeftPhysical)
    (hedge : edge ∈ reflectedBentTargetFaceStrandEdgesAt linked) :
    ReflectedBentFaceStrandEdgeSameSide edge := by
  unfold reflectedBentTargetFaceStrandEdgesAt
    slabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  have hside := reflectedBentTargetTerminal_pair_same_side linked terminal
  simpa only [ReflectedBentFaceStrandEdgeSameSide,
    slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using hside

def reflectedBentSwitchLinkedList :
    List {link // link ∈ boundaryCompleteSlabLinks 5} :=
  (boundaryCompleteSlabLinks 5).attach

def reflectedBentTargetFaceStrandEdges :
    List (SlabFaceStrandEdge reflectedBentSwitchLeftPhysical) :=
  reflectedBentSwitchLinkedList.flatMap
    reflectedBentTargetFaceStrandEdgesAt

theorem reflectedBentTargetFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge reflectedBentSwitchLeftPhysical)
    (hedge : edge ∈ reflectedBentTargetFaceStrandEdges) :
    ReflectedBentFaceStrandEdgeSameSide edge := by
  unfold reflectedBentTargetFaceStrandEdges at hedge
  obtain ⟨linked, _, hedgeLocal⟩ := List.mem_flatMap.mp hedge
  exact reflectedBentTargetFaceStrandEdgeAt_same_side
    linked edge hedgeLocal

def reflectedBentTargetMeasureIndexAssignment :
    SlabFusionWitnessAssignment :=
  reflectedBentSwitchRealizedLeftAssignmentFrom
    reflectedBentSwitchLinkedList

theorem reflectedBentTargetMeasureIndexAssignment_mem :
    reflectedBentTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5
        reflectedBentSwitchLeftPhysical
        (reflectedBentSwitchLinkedList.map Subtype.val) :=
  reflectedBentSwitchRealizedLeftAssignmentFrom_mem
    reflectedBentSwitchLinkedList

structure ReflectedBentTargetEdgeCertificate : Type where
  measureIndexAssignment : SlabFusionWitnessAssignment
  measureIndexAccepted : measureIndexAssignment ∈
    slabFusionWitnessAssignmentsOn 1 5 reflectedBentSwitchLeftPhysical
      (reflectedBentSwitchLinkedList.map Subtype.val)
  targetEdges : List (SlabFaceStrandEdge reflectedBentSwitchLeftPhysical)
  targetEdges_eq : targetEdges = reflectedBentTargetFaceStrandEdges
  everyTargetEdgeSameSide : forall edge, edge ∈ targetEdges ->
    ReflectedBentFaceStrandEdgeSameSide edge

def reflectedBentTargetEdgeCertificate :
    ReflectedBentTargetEdgeCertificate :=
  { measureIndexAssignment := reflectedBentTargetMeasureIndexAssignment
    measureIndexAccepted := reflectedBentTargetMeasureIndexAssignment_mem
    targetEdges := reflectedBentTargetFaceStrandEdges
    targetEdges_eq := rfl
    everyTargetEdgeSameSide :=
      reflectedBentTargetFaceStrandEdge_same_side }

#print axioms reflectedBentTargetTerminal_pair_same_side
#print axioms reflectedBentTargetFaceStrandEdgeAt_same_side
#print axioms reflectedBentTargetFaceStrandEdge_same_side
#print axioms reflectedBentTargetMeasureIndexAssignment_mem
#print axioms reflectedBentTargetEdgeCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
