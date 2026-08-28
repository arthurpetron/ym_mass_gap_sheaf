/-
# Basis-tagged global edges for the outward Y/Z target

The whole target has two representations with different jobs.  Its
equal-rank left assignment is the accepted finite measure index.  Its native
right-tree tag supplies the physical strand pairing.  Away from the unique
pivot the two descriptions use the ordinary canonical edge compiler.  At
the pivot the native tag contributes the four already-certified face pairs
`Y-Y` and `Z-Z`.

This file assembles those local clauses over the complete corrected-slab
link list and proves that every resulting directed face-strand edge stays on
one geometric side.  It does not yet identify this basis-tagged graph with
the older equal-rank observable-success predicate.

Constructive contract: explicit finite edge data and structural list
assembly only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeRightPairing
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetRealization

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetEdges

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeRightPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNonpivotPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. Literal native pivot edges -/

def outwardYZNativePivotCopy33 :
    SlabFaceStrandCopy outwardYZSwitchLeftPhysical where
  faceId := 33
  slot := ⟨0, by decide⟩

def outwardYZNativePivotCopy199 :
    SlabFaceStrandCopy outwardYZSwitchLeftPhysical where
  faceId := 199
  slot := ⟨0, by decide⟩

def outwardYZNativePivotCopy231 :
    SlabFaceStrandCopy outwardYZSwitchLeftPhysical where
  faceId := 231
  slot := ⟨0, by decide⟩

def outwardYZNativePivotCopy232 :
    SlabFaceStrandCopy outwardYZSwitchLeftPhysical where
  faceId := 232
  slot := ⟨0, by decide⟩

def outwardYZNativePivotEdge199To231 :
    SlabFaceStrandEdge outwardYZSwitchLeftPhysical where
  link := outwardYZSwitchPivot
  source := outwardYZNativePivotCopy199
  target := outwardYZNativePivotCopy231
  faceId_ne := by decide

def outwardYZNativePivotEdge231To199 :
    SlabFaceStrandEdge outwardYZSwitchLeftPhysical where
  link := outwardYZSwitchPivot
  source := outwardYZNativePivotCopy231
  target := outwardYZNativePivotCopy199
  faceId_ne := by decide

def outwardYZNativePivotEdge33To232 :
    SlabFaceStrandEdge outwardYZSwitchLeftPhysical where
  link := outwardYZSwitchPivot
  source := outwardYZNativePivotCopy33
  target := outwardYZNativePivotCopy232
  faceId_ne := by decide

def outwardYZNativePivotEdge232To33 :
    SlabFaceStrandEdge outwardYZSwitchLeftPhysical where
  link := outwardYZSwitchPivot
  source := outwardYZNativePivotCopy232
  target := outwardYZNativePivotCopy33
  faceId_ne := by decide

def outwardYZNativePivotFaceStrandEdges :
    List (SlabFaceStrandEdge outwardYZSwitchLeftPhysical) :=
  [outwardYZNativePivotEdge199To231,
   outwardYZNativePivotEdge231To199,
   outwardYZNativePivotEdge33To232,
   outwardYZNativePivotEdge232To33]

def OutwardYZFaceStrandEdgeSameSide
    (edge : SlabFaceStrandEdge outwardYZSwitchLeftPhysical) : Prop :=
  (slabPlaquetteAt 5 edge.source.faceId ∈ outwardYSurface ∧
    slabPlaquetteAt 5 edge.target.faceId ∈ outwardYSurface) ∨
  (slabPlaquetteAt 5 edge.source.faceId ∈ outwardZSurface ∧
    slabPlaquetteAt 5 edge.target.faceId ∈ outwardZSurface)

theorem outwardYZNativePivotFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge outwardYZSwitchLeftPhysical)
    (hedge : edge ∈ outwardYZNativePivotFaceStrandEdges) :
    OutwardYZFaceStrandEdgeSameSide edge := by
  simp only [outwardYZNativePivotFaceStrandEdges, List.mem_cons,
    List.not_mem_nil, or_false] at hedge
  rcases hedge with rfl | rfl | rfl | rfl <;>
    unfold OutwardYZFaceStrandEdgeSameSide <;> decide

/-! ## 2. Local basis-tagged target edge compiler -/

def outwardYZNativeTargetFaceStrandEdgesAt
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List (SlabFaceStrandEdge outwardYZSwitchLeftPhysical) :=
  if linked.1 = outwardYZSwitchPivot then
    outwardYZNativePivotFaceStrandEdges
  else
    slabLinkFaceStrandEdges 1 5 outwardYZSwitchLeftPhysical linked.1
      (outwardYZSwitchRealizedLeftAuxiliary linked)
      (outwardYZSwitchRealizedLeftAuxiliary_mem linked)

theorem outwardYZNativeTargetFaceStrandEdgeAt_same_side
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (edge : SlabFaceStrandEdge outwardYZSwitchLeftPhysical)
    (hedge : edge ∈ outwardYZNativeTargetFaceStrandEdgesAt linked) :
    OutwardYZFaceStrandEdgeSameSide edge := by
  by_cases hpivot : linked.1 = outwardYZSwitchPivot
  · have hedgePivot : edge ∈ outwardYZNativePivotFaceStrandEdges := by
      simpa only [outwardYZNativeTargetFaceStrandEdgesAt,
        if_pos hpivot] using hedge
    exact outwardYZNativePivotFaceStrandEdge_same_side edge hedgePivot
  · have hedgeLocal : edge ∈
        slabLinkFaceStrandEdges 1 5 outwardYZSwitchLeftPhysical linked.1
          (outwardYZSwitchRealizedLeftAuxiliary linked)
          (outwardYZSwitchRealizedLeftAuxiliary_mem linked) := by
      simpa only [outwardYZNativeTargetFaceStrandEdgesAt,
        if_neg hpivot] using hedge
    unfold slabLinkFaceStrandEdges at hedgeLocal
    obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedgeLocal
    have hside := outwardYZNonpivotTerminal_pair_same_side hpivot
      (outwardYZSwitchRealizedLeftAuxiliary_mem linked) terminal
    simpa only [OutwardYZFaceStrandEdgeSameSide,
      slabLinkFaceStrandEdgeOfTerminal,
      slabLinkPhysicalTerminalFaceStrandCopy,
      slabLinkFaceStrandOccurrenceToCopy] using hside

/-! ## 3. Whole-link assembly and global side invariant -/

def outwardYZSwitchLinkedList :
    List {link // link ∈ boundaryCompleteSlabLinks 5} :=
  (boundaryCompleteSlabLinks 5).attach

def outwardYZNativeTargetFaceStrandEdges :
    List (SlabFaceStrandEdge outwardYZSwitchLeftPhysical) :=
  outwardYZSwitchLinkedList.flatMap
    outwardYZNativeTargetFaceStrandEdgesAt

theorem outwardYZNativeTargetFaceStrandEdge_same_side
    (edge : SlabFaceStrandEdge outwardYZSwitchLeftPhysical)
    (hedge : edge ∈ outwardYZNativeTargetFaceStrandEdges) :
    OutwardYZFaceStrandEdgeSameSide edge := by
  unfold outwardYZNativeTargetFaceStrandEdges at hedge
  obtain ⟨linked, _, hedgeLocal⟩ := List.mem_flatMap.mp hedge
  exact outwardYZNativeTargetFaceStrandEdgeAt_same_side
    linked edge hedgeLocal

def outwardYZNativeTargetMeasureIndexAssignment :
    SlabFusionWitnessAssignment :=
  outwardYZSwitchRealizedLeftAssignmentFrom outwardYZSwitchLinkedList

theorem outwardYZNativeTargetMeasureIndexAssignment_mem :
    outwardYZNativeTargetMeasureIndexAssignment ∈
      slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchLeftPhysical
        (outwardYZSwitchLinkedList.map Subtype.val) :=
  outwardYZSwitchRealizedLeftAssignmentFrom_mem outwardYZSwitchLinkedList

/-- One structure keeps the finite measure index and native strand semantics
separate, so later observable code cannot identify them by equal rank. -/
structure OutwardYZNativeTargetBasisTaggedEdgeCertificate : Type where
  measureIndexAssignment : SlabFusionWitnessAssignment
  measureIndexAccepted : measureIndexAssignment ∈
    slabFusionWitnessAssignmentsOn 1 5 outwardYZSwitchLeftPhysical
      (outwardYZSwitchLinkedList.map Subtype.val)
  nativeEdges : List (SlabFaceStrandEdge outwardYZSwitchLeftPhysical)
  nativeEdges_eq : nativeEdges = outwardYZNativeTargetFaceStrandEdges
  everyNativeEdgeSameSide : forall edge, edge ∈ nativeEdges ->
    OutwardYZFaceStrandEdgeSameSide edge
  pivotCompiler : OutwardYZPivotNativeRightPairingCertificate

def outwardYZNativeTargetBasisTaggedEdgeCertificate :
    OutwardYZNativeTargetBasisTaggedEdgeCertificate :=
  { measureIndexAssignment := outwardYZNativeTargetMeasureIndexAssignment
    measureIndexAccepted :=
      outwardYZNativeTargetMeasureIndexAssignment_mem
    nativeEdges := outwardYZNativeTargetFaceStrandEdges
    nativeEdges_eq := rfl
    everyNativeEdgeSameSide :=
      outwardYZNativeTargetFaceStrandEdge_same_side
    pivotCompiler := outwardYZPivotNativeRightPairingCertificate }

#print axioms outwardYZNativePivotFaceStrandEdge_same_side
#print axioms outwardYZNativeTargetFaceStrandEdgeAt_same_side
#print axioms outwardYZNativeTargetFaceStrandEdge_same_side
#print axioms outwardYZNativeTargetMeasureIndexAssignment_mem
#print axioms outwardYZNativeTargetBasisTaggedEdgeCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetEdges
