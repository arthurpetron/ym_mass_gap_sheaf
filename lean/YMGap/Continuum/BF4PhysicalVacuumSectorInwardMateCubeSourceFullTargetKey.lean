/-
# A decidable exact key for complete-source lowered targets

The complete first-stretched source family carries function-valued lowered
physical fields and dependent presented fusion assignments.  Those values do
not themselves have a useful decidable equality.  This module serializes the
finite data that determine them:

* the root face and peel size;
* the lowered physical values on the complete slab face carrier;
* every displayed link's literal face order; and
* every displayed link's lowered auxiliary values on its canonical finite
  support.

All complete sources in the family have the same source physical field.
Outside the displayed slab face carrier, a supported peel removes zero
copies.  Equality of the finite physical words therefore gives equality of
the complete lowered physical functions.  Equality of the order and
auxiliary rows then reconstructs heterogeneous equality of the dependent
presented assignments.

This is only the exact decidable key needed by the downstream realized-fiber
partition.  No weighted sum or transition estimate is claimed here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
import YMGap.Continuum.CompactDualSlabExpandedTargetKey

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Finite words for a dependent presented assignment -/

private theorem mapFunctions_eq_on_mem
    {A B : Type} (items : List A) (left right : A -> B)
    (hmap : items.map left = items.map right) :
    forall item, item ∈ items -> left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := by
        injection hmap
      have htail : tail.map left = tail.map right := by
        injection hmap
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htailMem
      · exact heq ▸ hhead
      · exact ih htail item htailMem

/-- The literal incident-face order retained at every displayed link. -/
def presentedSlabFusionWitnessAssignmentOrderWords
    {K extent : Nat} {physical : SlabLabelling} (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) : List (List Nat) :=
  links.attach.map fun linked => (assignment linked).order.faceIds

/-- The lowered auxiliary values on the canonical finite support of every
displayed link.  The support length is independent of the chosen face order
because every presentation is a permutation of the incidence list. -/
def presentedSlabFusionWitnessAssignmentAuxiliaryWords
    {K extent : Nat} {physical : SlabLabelling} (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) : List (List Nat) :=
  links.attach.map fun linked =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent linked.1).length)
      (assignment linked).auxiliary

private theorem slabLinkFaceOrder_eq_of_faceIds_eq
    {extent : Nat} {link : SlabLink}
    (left right : SlabLinkFaceOrder extent link)
    (hfaces : left.faceIds = right.faceIds) : left = right := by
  cases left with
  | mk leftFaces leftPerm =>
      cases right with
      | mk rightFaces rightPerm =>
          dsimp only at hfaces
          cases hfaces
          rfl

private theorem presentedSlabLinkFusionWitness_eq_of_fields_eq
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (left right : PresentedSlabLinkFusionWitness K extent physical link)
    (horder : left.order = right.order)
    (hauxiliary : left.auxiliary = right.auxiliary) : left = right := by
  cases left with
  | mk leftOrder leftAuxiliary leftMem =>
      cases right with
      | mk rightOrder rightAuxiliary rightMem =>
          dsimp only at horder hauxiliary
          cases horder
          cases hauxiliary
          rfl

/-- Equality of the finite order and auxiliary rows determines the complete
dependent presented assignment, once the physical index is identified. -/
theorem presentedSlabFusionWitnessAssignment_heq_of_words_eq
    {K extent : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    {links : List SlabLink}
    (left : PresentedSlabFusionWitnessAssignment
      K extent leftPhysical links)
    (right : PresentedSlabFusionWitnessAssignment
      K extent rightPhysical links)
    (hphysical : leftPhysical = rightPhysical)
    (horders : presentedSlabFusionWitnessAssignmentOrderWords links left =
      presentedSlabFusionWitnessAssignmentOrderWords links right)
    (hauxiliaries :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords links left =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords links right) :
    HEq left right := by
  cases hphysical
  apply heq_of_eq
  funext linked
  have horderFaces := mapFunctions_eq_on_mem links.attach
    (fun item => (left item).order.faceIds)
    (fun item => (right item).order.faceIds)
    horders linked (List.mem_attach links linked)
  have hauxiliaryWord := mapFunctions_eq_on_mem links.attach
    (fun item =>
      finiteEdgeLabellingWord
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent item.1).length)
        (left item).auxiliary)
    (fun item =>
      finiteEdgeLabellingWord
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent item.1).length)
        (right item).auxiliary)
    hauxiliaries linked (List.mem_attach links linked)
  have hleftMem := (left linked).auxiliary_mem
  have hrightMem := (right linked).auxiliary_mem
  unfold orderedSlabLinkFusionWitnesses fusionWitnessesForSpins at hleftMem hrightMem
  simp only [List.length_map] at hleftMem hrightMem
  have hleftBounded := (List.mem_filter.mp hleftMem).1
  have hrightBounded := (List.mem_filter.mp hrightMem).1
  rw [(left linked).order.length_eq] at hleftBounded
  rw [(right linked).order.length_eq] at hrightBounded
  have hleftSupported :=
    (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent linked.1).length)
      (left linked).auxiliary hleftBounded).2
  have hrightSupported :=
    (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent linked.1).length)
      (right linked).auxiliary hrightBounded).2
  have hauxiliary : (left linked).auxiliary =
      (right linked).auxiliary :=
    edgeLabelling_eq_of_word_eq_of_supported
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent linked.1).length)
      (left linked).auxiliary (right linked).auxiliary
      hleftSupported hrightSupported hauxiliaryWord
  exact presentedSlabLinkFusionWitness_eq_of_fields_eq
    (left linked) (right linked)
    (slabLinkFaceOrder_eq_of_faceIds_eq
      (left linked).order (right linked).order horderFaces)
    hauxiliary

/-! ## 2. The exact decidable target key -/

/-- Root, size, and a lossless finite serialization of one lowered presented
target. -/
structure CubeInwardMateFullPeelTargetKey : Type where
  rootFaceId : Nat
  peelSize : Nat
  lowerPhysicalWord : List Nat
  lowerOrderWords : List (List Nat)
  lowerAuxiliaryWords : List (List Nat)
  deriving DecidableEq

/-- Serialize the exact fiber coordinates of flat adaptive inverse data. -/
def presentedAdaptiveInverseTargetKey
    {K extent : Nat} (data : PresentedAdaptiveInverseData K extent) :
    CubeInwardMateFullPeelTargetKey where
  rootFaceId := data.rootFaceId
  peelSize := data.peelSize
  lowerPhysicalWord := finiteEdgeLabellingWord
    (slabPhysicalFaceEdges extent) data.lowerPhysical
  lowerOrderWords := presentedSlabFusionWitnessAssignmentOrderWords
    (boundaryCompleteSlabLinks extent) data.lowerAssignment
  lowerAuxiliaryWords := presentedSlabFusionWitnessAssignmentAuxiliaryWords
    (boundaryCompleteSlabLinks extent) data.lowerAssignment

private theorem edgeLabelling_eq_of_word_eq_of_eq_off
    (edges : List Nat) (left right : EdgeLabelling)
    (hoff : forall edge, edge ∉ edges -> left edge = right edge)
    (hword : finiteEdgeLabellingWord edges left =
      finiteEdgeLabellingWord edges right) : left = right := by
  funext edge
  by_cases hedge : edge ∈ edges
  · exact mapFunctions_eq_on_mem edges left right hword edge hedge
  · exact hoff edge hedge

/-- Equal exact keys reconstruct the root, size, and dependent target when
the two lowered fields agree away from the displayed physical carrier. -/
theorem PresentedAdaptiveInverseData.target_eq_of_key_eq
    {K extent : Nat} (left right : PresentedAdaptiveInverseData K extent)
    (hoff : forall faceId, faceId ∉ slabPhysicalFaceEdges extent ->
      left.lowerPhysical faceId = right.lowerPhysical faceId)
    (hkey : presentedAdaptiveInverseTargetKey left =
      presentedAdaptiveInverseTargetKey right) :
    left.rootFaceId = right.rootFaceId ∧
      left.peelSize = right.peelSize ∧
      left.lowerPhysical = right.lowerPhysical ∧
      HEq left.lowerAssignment right.lowerAssignment := by
  have hroot := congrArg CubeInwardMateFullPeelTargetKey.rootFaceId hkey
  have hsize := congrArg CubeInwardMateFullPeelTargetKey.peelSize hkey
  have hphysicalWord := congrArg
    CubeInwardMateFullPeelTargetKey.lowerPhysicalWord hkey
  have horderWords := congrArg
    CubeInwardMateFullPeelTargetKey.lowerOrderWords hkey
  have hauxiliaryWords := congrArg
    CubeInwardMateFullPeelTargetKey.lowerAuxiliaryWords hkey
  unfold presentedAdaptiveInverseTargetKey at hroot hsize hphysicalWord horderWords hauxiliaryWords
  have hphysical : left.lowerPhysical = right.lowerPhysical :=
    edgeLabelling_eq_of_word_eq_of_eq_off
      (slabPhysicalFaceEdges extent)
      left.lowerPhysical right.lowerPhysical hoff hphysicalWord
  exact ⟨hroot, hsize, hphysical,
    presentedSlabFusionWitnessAssignment_heq_of_words_eq
      left.lowerAssignment right.lowerAssignment hphysical
      horderWords hauxiliaryWords⟩

/-! ## 3. Exactness on the complete first-stretched source family -/

/-- Supported component removal changes no physical value outside the
complete slab face carrier. -/
theorem EnumeratedCubeInwardMateFullSource.lowerPhysical_eq_physical_of_not_mem
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded)
    (faceId : Nat) (hface : faceId ∉ slabPhysicalFaceEdges 1) :
    entry.adaptiveInverseData.lowerPhysical faceId = physical faceId := by
  change lowerSlabPhysicalByFaceStrandSelection
      (certifiedStretchedComponentUnionSupportedSelection
        entry.source.1 entry.source.toPresented).closed.selected faceId =
    physical faceId
  unfold lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  rw [(certifiedStretchedComponentUnionSupportedSelection
    entry.source.1 entry.source.toPresented).selectionCount_eq_zero_of_not_physical
      faceId hface]
  exact Nat.sub_zero _

/-- The exact decidable fiber key of one enumerated complete source. -/
def EnumeratedCubeInwardMateFullSource.targetKey
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    CubeInwardMateFullPeelTargetKey :=
  presentedAdaptiveInverseTargetKey entry.adaptiveInverseData

/-- **Key exactness on the enumerated family.**  Equality of finite keys gives
exactly the common root, peel size, lowered physical field, and dependent
presented target needed by the fixed-fiber contraction theorem. -/
theorem EnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (left right : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hkey : EnumeratedCubeInwardMateFullSource.targetKey left =
      EnumeratedCubeInwardMateFullSource.targetKey right) :
    left.adaptiveInverseData.rootFaceId =
        right.adaptiveInverseData.rootFaceId ∧
      left.adaptiveInverseData.peelSize =
        right.adaptiveInverseData.peelSize ∧
      left.adaptiveInverseData.lowerPhysical =
        right.adaptiveInverseData.lowerPhysical ∧
      HEq left.adaptiveInverseData.lowerAssignment
        right.adaptiveInverseData.lowerAssignment := by
  apply PresentedAdaptiveInverseData.target_eq_of_key_eq
    left.adaptiveInverseData right.adaptiveInverseData
  · intro faceId hface
    rw [EnumeratedCubeInwardMateFullSource.lowerPhysical_eq_physical_of_not_mem
        left faceId hface,
      EnumeratedCubeInwardMateFullSource.lowerPhysical_eq_physical_of_not_mem
        right faceId hface]
  · exact hkey

#print axioms presentedSlabFusionWitnessAssignmentOrderWords
#print axioms presentedSlabFusionWitnessAssignmentAuxiliaryWords
#print axioms presentedSlabFusionWitnessAssignment_heq_of_words_eq
#print axioms CubeInwardMateFullPeelTargetKey
#print axioms presentedAdaptiveInverseTargetKey
#print axioms PresentedAdaptiveInverseData.target_eq_of_key_eq
#print axioms EnumeratedCubeInwardMateFullSource.lowerPhysical_eq_physical_of_not_mem
#print axioms EnumeratedCubeInwardMateFullSource.targetKey
#print axioms EnumeratedCubeInwardMateFullSource.target_eq_of_key_eq

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
