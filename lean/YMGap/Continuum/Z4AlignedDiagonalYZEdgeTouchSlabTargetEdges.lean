/-
# Global strand edges of the aligned-diagonal target

The selected target is realized in the ordinary equal-rank production basis.
At the pivot its `(0,1)` carrier stays within the two cut components; away
from the pivot the unique-cross-link theorem gives the same conclusion for
every accepted carrier.  Assemble the literal local terminal-pair lists over
all corrected-slab links and retain the accepted global measure index.

Constructive contract: explicit finite edge data and structural list
assembly only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabNonpivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

def AlignedDiagonalFaceStrandEdgeSameSide
    (edge : SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical) : Prop :=
  (slabPlaquetteAt 5 edge.source.faceId ∈ alignedDiagonalNearSurface ∧
    slabPlaquetteAt 5 edge.target.faceId ∈ alignedDiagonalNearSurface) ∨
  (slabPlaquetteAt 5 edge.source.faceId ∈ alignedDiagonalFarSurface ∧
    slabPlaquetteAt 5 edge.target.faceId ∈ alignedDiagonalFarSurface)

/-! ## 1. One selected local target -/

def alignedDiagonalTargetFaceStrandEdgesAt
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List (SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical) :=
  slabLinkFaceStrandEdges 1 5 alignedDiagonalSwitchLeftPhysical linked.1
    (alignedDiagonalSwitchRealizedLeftAuxiliary linked)
    (alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked)

theorem alignedDiagonalTargetTerminal_pair_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      alignedDiagonalSwitchLeftPhysical linked.1
      (alignedDiagonalSwitchRealizedLeftAuxiliary linked)
      (alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      alignedDiagonalSwitchLeftPhysical linked.1
      (alignedDiagonalSwitchRealizedLeftAuxiliary linked)
      (alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked) terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical linked.1
        (alignedDiagonalSwitchRealizedLeftAuxiliary linked)
        (alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked)
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical linked.1
        (alignedDiagonalSwitchRealizedLeftAuxiliary linked)
        (alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked)
        partner).faceId
    (sourceFace ∈ alignedDiagonalNearSurface ∧
        targetFace ∈ alignedDiagonalNearSurface) ∨
      (sourceFace ∈ alignedDiagonalFarSurface ∧
        targetFace ∈ alignedDiagonalFarSurface) := by
  by_cases hpivot : linked.1 = alignedDiagonalSwitchPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        simpa only [alignedDiagonalSwitchRealizedLeftAuxiliary,
          if_pos rfl] using
          alignedDiagonalPivotTerminal_pair_same_side
            alignedDiagonalPivotLeftAuxiliary_mem terminal
  · exact alignedDiagonalNonpivotTerminal_pair_same_side hpivot
      (alignedDiagonalSwitchRealizedLeftAuxiliary_mem linked) terminal

theorem alignedDiagonalTargetFaceStrandEdgeAt_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (edge : SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical)
    (hedge : edge ∈ alignedDiagonalTargetFaceStrandEdgesAt linked) :
    AlignedDiagonalFaceStrandEdgeSameSide edge := by
  unfold alignedDiagonalTargetFaceStrandEdgesAt
    slabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  have hside := alignedDiagonalTargetTerminal_pair_same_side linked terminal
  simpa only [AlignedDiagonalFaceStrandEdgeSameSide,
    slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using hside

/-! ## 2. Whole-link assembly and global side invariant -/

def alignedDiagonalSwitchLinkedList :
    List {link // link ∈ boundaryCompleteSlabLinks 5} :=
  (boundaryCompleteSlabLinks 5).attach

def alignedDiagonalTargetFaceStrandEdges :
    List (SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical) :=
  alignedDiagonalSwitchLinkedList.flatMap
    alignedDiagonalTargetFaceStrandEdgesAt

theorem alignedDiagonalTargetFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical)
    (hedge : edge ∈ alignedDiagonalTargetFaceStrandEdges) :
    AlignedDiagonalFaceStrandEdgeSameSide edge := by
  unfold alignedDiagonalTargetFaceStrandEdges at hedge
  obtain ⟨linked, _, hedgeLocal⟩ := List.mem_flatMap.mp hedge
  exact alignedDiagonalTargetFaceStrandEdgeAt_same_side
    linked edge hedgeLocal

def alignedDiagonalTargetMeasureIndexAssignment :
    SlabFusionWitnessAssignment :=
  alignedDiagonalSwitchRealizedLeftAssignmentFrom
    alignedDiagonalSwitchLinkedList

theorem alignedDiagonalTargetMeasureIndexAssignment_mem :
    alignedDiagonalTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5
        alignedDiagonalSwitchLeftPhysical
        (alignedDiagonalSwitchLinkedList.map Subtype.val) :=
  alignedDiagonalSwitchRealizedLeftAssignmentFrom_mem
    alignedDiagonalSwitchLinkedList

structure AlignedDiagonalTargetEdgeCertificate : Type where
  measureIndexAssignment : SlabFusionWitnessAssignment
  measureIndexAccepted : measureIndexAssignment ∈
    slabFusionWitnessAssignmentsOn 1 5 alignedDiagonalSwitchLeftPhysical
      (alignedDiagonalSwitchLinkedList.map Subtype.val)
  targetEdges : List
    (SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical)
  targetEdges_eq : targetEdges = alignedDiagonalTargetFaceStrandEdges
  everyTargetEdgeSameSide : forall edge, edge ∈ targetEdges ->
    AlignedDiagonalFaceStrandEdgeSameSide edge

def alignedDiagonalTargetEdgeCertificate :
    AlignedDiagonalTargetEdgeCertificate :=
  { measureIndexAssignment := alignedDiagonalTargetMeasureIndexAssignment
    measureIndexAccepted := alignedDiagonalTargetMeasureIndexAssignment_mem
    targetEdges := alignedDiagonalTargetFaceStrandEdges
    targetEdges_eq := rfl
    everyTargetEdgeSameSide :=
      alignedDiagonalTargetFaceStrandEdge_same_side }

#print axioms alignedDiagonalTargetTerminal_pair_same_side
#print axioms alignedDiagonalTargetFaceStrandEdgeAt_same_side
#print axioms alignedDiagonalTargetFaceStrandEdge_same_side
#print axioms alignedDiagonalTargetMeasureIndexAssignment_mem
#print axioms alignedDiagonalTargetEdgeCertificate

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
