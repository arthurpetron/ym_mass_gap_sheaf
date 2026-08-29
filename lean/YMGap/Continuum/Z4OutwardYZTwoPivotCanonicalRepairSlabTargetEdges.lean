/-
# Global strand edges of the two-pivot outward repair target

At the spatial and temporal pivots, the two selected carriers preserve both
repair lobes.  At every other link, the two-link intersection theorem forces
the same conclusion for every accepted sparse carrier.  Assemble the literal
local terminal-pair lists over all corrected-slab links and retain the
accepted global production assignment.

Constructive contract: explicit finite edge data and structural assembly
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabNonpivotPairing
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotFacePairing
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetRealization

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetEdges

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabNonpivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotFacePairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetRealization

def OutwardYZCanonicalRepairFaceStrandEdgeSameSide
    (edge : SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical) : Prop :=
  (slabPlaquetteAt 5 edge.source.faceId ∈
      outwardYZCanonicalRepairTargetLobe ∧
    slabPlaquetteAt 5 edge.target.faceId ∈
      outwardYZCanonicalRepairTargetLobe) ∨
  (slabPlaquetteAt 5 edge.source.faceId ∈
      outwardYZCanonicalRepairRootLobe ∧
    slabPlaquetteAt 5 edge.target.faceId ∈
      outwardYZCanonicalRepairRootLobe)

def outwardYZCanonicalRepairTargetFaceStrandEdgesAt
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List (SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical) :=
  slabLinkFaceStrandEdges 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical linked.1
    (outwardYZCanonicalRepairRealizedLeftAuxiliary linked)
    (outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked)

theorem outwardYZCanonicalRepairTargetTerminal_pair_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical linked.1
      (outwardYZCanonicalRepairRealizedLeftAuxiliary linked)
      (outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical linked.1
      (outwardYZCanonicalRepairRealizedLeftAuxiliary linked)
      (outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked) terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical linked.1
        (outwardYZCanonicalRepairRealizedLeftAuxiliary linked)
        (outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked)
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical linked.1
        (outwardYZCanonicalRepairRealizedLeftAuxiliary linked)
        (outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked)
        partner).faceId
    (sourceFace ∈ outwardYZCanonicalRepairTargetLobe ∧
        targetFace ∈ outwardYZCanonicalRepairTargetLobe) ∨
      (sourceFace ∈ outwardYZCanonicalRepairRootLobe ∧
        targetFace ∈ outwardYZCanonicalRepairRootLobe) := by
  by_cases hspatial :
      linked.1 = outwardYZCanonicalRepairSwitchSpatialPivot
  · cases linked with
    | mk link hlink =>
        dsimp at hspatial
        subst link
        simpa only [outwardYZCanonicalRepairRealizedLeftAuxiliary,
          if_pos rfl] using
          outwardYZCanonicalRepairSpatialTerminal_pair_same_side
            outwardYZCanonicalRepairSpatialLeftAuxiliary_mem terminal
  · by_cases htemporal :
        linked.1 = outwardYZCanonicalRepairSwitchTemporalPivot
    · cases linked with
      | mk link hlink =>
          dsimp at hspatial htemporal
          subst link
          simpa only [outwardYZCanonicalRepairRealizedLeftAuxiliary,
            if_neg hspatial, if_pos rfl] using
            outwardYZCanonicalRepairTemporalTerminal_pair_same_side
              outwardYZCanonicalRepairTemporalLeftAuxiliary_mem terminal
    · exact outwardYZCanonicalRepairNonpivotTerminal_pair_same_side
        hspatial htemporal
        (outwardYZCanonicalRepairRealizedLeftAuxiliary_mem linked) terminal

theorem outwardYZCanonicalRepairTargetFaceStrandEdgeAt_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (edge : SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical)
    (hedge : edge ∈
      outwardYZCanonicalRepairTargetFaceStrandEdgesAt linked) :
    OutwardYZCanonicalRepairFaceStrandEdgeSameSide edge := by
  unfold outwardYZCanonicalRepairTargetFaceStrandEdgesAt
    slabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  have hside :=
    outwardYZCanonicalRepairTargetTerminal_pair_same_side linked terminal
  simpa only [OutwardYZCanonicalRepairFaceStrandEdgeSameSide,
    slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using hside

def outwardYZCanonicalRepairSwitchLinkedList :
    List {link // link ∈ boundaryCompleteSlabLinks 5} :=
  (boundaryCompleteSlabLinks 5).attach

def outwardYZCanonicalRepairTargetFaceStrandEdges :
    List (SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical) :=
  outwardYZCanonicalRepairSwitchLinkedList.flatMap
    outwardYZCanonicalRepairTargetFaceStrandEdgesAt

theorem outwardYZCanonicalRepairTargetFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical)
    (hedge : edge ∈ outwardYZCanonicalRepairTargetFaceStrandEdges) :
    OutwardYZCanonicalRepairFaceStrandEdgeSameSide edge := by
  unfold outwardYZCanonicalRepairTargetFaceStrandEdges at hedge
  obtain ⟨linked, _, hedgeLocal⟩ := List.mem_flatMap.mp hedge
  exact outwardYZCanonicalRepairTargetFaceStrandEdgeAt_same_side
    linked edge hedgeLocal

def outwardYZCanonicalRepairTargetMeasureIndexAssignment :
    SlabFusionWitnessAssignment :=
  outwardYZCanonicalRepairRealizedLeftAssignmentFrom
    outwardYZCanonicalRepairSwitchLinkedList

theorem outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem :
    outwardYZCanonicalRepairTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        (outwardYZCanonicalRepairSwitchLinkedList.map Subtype.val) :=
  outwardYZCanonicalRepairRealizedLeftAssignmentFrom_mem
    outwardYZCanonicalRepairSwitchLinkedList

structure OutwardYZCanonicalRepairTargetEdgeCertificate : Type where
  measureIndexAssignment : SlabFusionWitnessAssignment
  measureIndexAccepted : measureIndexAssignment ∈
    slabFusionWitnessAssignmentsOn 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      (outwardYZCanonicalRepairSwitchLinkedList.map Subtype.val)
  targetEdges : List (SlabFaceStrandEdge
    outwardYZCanonicalRepairSwitchLeftPhysical)
  targetEdges_eq : targetEdges =
    outwardYZCanonicalRepairTargetFaceStrandEdges
  everyTargetEdgeSameSide : ∀ edge, edge ∈ targetEdges →
    OutwardYZCanonicalRepairFaceStrandEdgeSameSide edge

def outwardYZCanonicalRepairTargetEdgeCertificate :
    OutwardYZCanonicalRepairTargetEdgeCertificate :=
  { measureIndexAssignment :=
      outwardYZCanonicalRepairTargetMeasureIndexAssignment
    measureIndexAccepted :=
      outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem
    targetEdges := outwardYZCanonicalRepairTargetFaceStrandEdges
    targetEdges_eq := rfl
    everyTargetEdgeSameSide :=
      outwardYZCanonicalRepairTargetFaceStrandEdge_same_side }

#print axioms outwardYZCanonicalRepairTargetTerminal_pair_same_side
#print axioms outwardYZCanonicalRepairTargetFaceStrandEdgeAt_same_side
#print axioms outwardYZCanonicalRepairTargetFaceStrandEdge_same_side
#print axioms outwardYZCanonicalRepairTargetMeasureIndexAssignment_mem
#print axioms outwardYZCanonicalRepairTargetEdgeCertificate

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetEdges
