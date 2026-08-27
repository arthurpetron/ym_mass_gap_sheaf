/-
# Injective adaptive codes on a fixed component-removal fiber

The adaptive entropy carrier becomes a genuine inverse-fiber bound only after
fixing the data erased by component removal.  This module fixes a root face,
peel size, lowered physical target, and lowered auxiliary assignment.

For two production components with the same three-factor code, the physical
decoder gives the same complete physical drop and the full row table gives
the same complete auxiliary drop table.  Adding those drops back to the common
lowered targets reconstructs the same source physical labelling and the same
source assignment.  Therefore the code is injective on any duplicate-free
finite list of source configuration pairs equipped with explicit removal
witnesses, and that list has length at most `10240000^peelSize`.

Constructive contract: explicit per-source witnesses, finite attachment and
pigeonhole counting, and the existing algebraic reconstruction maps only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Reconstruction congruence -/

/-- Code-based assignment reconstruction depends only on the auxiliary word
table and the lowered assignment, never on the physical-face list. -/
theorem reconstructAssignment_eq_of_auxiliaryWords_eq
    (left right : SlabFaceStrandComponentDropCode)
    (extent : Nat) (links : List SlabLink)
    (leftTarget rightTarget : SlabFusionWitnessAssignment)
    (hauxiliary : left.auxiliaryWords = right.auxiliaryWords)
    (htarget : leftTarget = rightTarget) :
    left.reconstructAssignment extent links leftTarget =
      right.reconstructAssignment extent links rightTarget := by
  subst rightTarget
  unfold SlabFaceStrandComponentDropCode.reconstructAssignment
    SlabFaceStrandComponentDropCode.reconstructedAuxiliaryField
    SlabFaceStrandComponentDropCode.reconstructAuxiliaryAt
    SlabFaceStrandComponentDropCode.decodeAuxiliaryDrop
  rw [hauxiliary]

/-- At a common root and common lowered physical/auxiliary target, equality of
the three adaptive words reconstructs equality of both source fields. -/
theorem componentAdaptiveEntropyCode_eq_sourceData_eq
    {K extent : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent)}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent leftPhysical (boundaryCompleteSlabLinks extent)
        leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent rightPhysical (boundaryCompleteSlabLinks extent)
        rightAssignment hrightAssignment)
    (hroot : left.root.faceId = right.root.faceId)
    (hlowerPhysical :
      SlabFusionWitnessFaceStrandSeed.lowerPhysical left =
        SlabFusionWitnessFaceStrandSeed.lowerPhysical right)
    (hlowerAssignment :
      SlabFusionWitnessFaceStrandSeed.lowerAssignment left =
        SlabFusionWitnessFaceStrandSeed.lowerAssignment right)
    (hcode : componentAdaptiveEntropyCode left =
      componentAdaptiveEntropyCode right) :
    leftPhysical = rightPhysical ∧ leftAssignment = rightAssignment := by
  have hshape := congrArg ComponentAdaptiveEntropyCode.shape hcode
  have hphysical :=
    congrArg ComponentAdaptiveEntropyCode.physicalMultiplicity hcode
  have hrows := congrArg ComponentAdaptiveEntropyCode.auxiliaryRows hcode
  unfold componentAdaptiveEntropyCode at hshape hphysical hrows
  change componentPlaquettePaddedTourCode left =
    componentPlaquettePaddedTourCode right at hshape
  change componentDecodedPhysicalMultiplicityBinaryCode left =
    componentDecodedPhysicalMultiplicityBinaryCode right at hphysical
  change SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows left =
    SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows right at hrows
  have hdrop : forall faceId,
      slabFaceStrandSelectionCount left.selected faceId =
        slabFaceStrandSelectionCount right.selected faceId := by
    intro faceId
    rw [← componentPhysicalDropDecode_code left faceId,
      ← componentPhysicalDropDecode_code right faceId,
      hroot, hshape, hphysical]
  have hphysicalDrop :
      SlabFusionWitnessFaceStrandSeed.physicalDrop left =
        SlabFusionWitnessFaceStrandSeed.physicalDrop right := by
    funext faceId
    exact hdrop faceId
  have hauxiliary :
      (SlabFusionWitnessFaceStrandSeed.dropCode left).auxiliaryWords =
        (SlabFusionWitnessFaceStrandSeed.dropCode right).auxiliaryWords := by
    unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows at hrows
    unfold SlabFusionWitnessFaceStrandSeed.dropCode
      slabAuxiliaryDropWordsFrom
    exact pairedMap_eq_of_map_eq
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt left)
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt right)
      (boundaryCompleteSlabLinks extent) hrows
  constructor
  · calc
      leftPhysical =
          SlabFusionWitnessFaceStrandSeed.reconstructPhysical left :=
        (SlabFusionWitnessFaceStrandSeed.reconstructPhysical_eq left).symm
      _ = SlabFusionWitnessFaceStrandSeed.reconstructPhysical right := by
        unfold SlabFusionWitnessFaceStrandSeed.reconstructPhysical
        rw [hlowerPhysical, hphysicalDrop]
      _ = rightPhysical :=
        SlabFusionWitnessFaceStrandSeed.reconstructPhysical_eq right
  · calc
      leftAssignment =
          (SlabFusionWitnessFaceStrandSeed.dropCode left).reconstructAssignment
            extent (boundaryCompleteSlabLinks extent)
            (SlabFusionWitnessFaceStrandSeed.lowerAssignment left) :=
        (SlabFusionWitnessFaceStrandSeed.dropCode_reconstructCompleteAssignment
          left).symm
      _ =
          (SlabFusionWitnessFaceStrandSeed.dropCode right).reconstructAssignment
            extent (boundaryCompleteSlabLinks extent)
            (SlabFusionWitnessFaceStrandSeed.lowerAssignment right) :=
        reconstructAssignment_eq_of_auxiliaryWords_eq
          (SlabFusionWitnessFaceStrandSeed.dropCode left)
          (SlabFusionWitnessFaceStrandSeed.dropCode right)
          extent (boundaryCompleteSlabLinks extent)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment left)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment right)
          hauxiliary hlowerAssignment
      _ = rightAssignment :=
        SlabFusionWitnessFaceStrandSeed.dropCode_reconstructCompleteAssignment
          right

/-! ## 2. Explicit fixed-target removal witnesses -/

/-- Evidence that one source configuration pair lowers, by one rooted strand
component of the fixed size, to the displayed common target. -/
structure ComponentAdaptiveRemovalWitness
    (K extent rootFaceId peelSize : Nat)
    (targetPhysical : SlabLabelling)
    (targetAssignment : SlabFusionWitnessAssignment)
    (source : SlabLabelling × SlabFusionWitnessAssignment) : Type where
  sourceAssignment_mem : source.2 ∈
    slabFusionWitnessAssignmentsOn K extent source.1
      (boundaryCompleteSlabLinks extent)
  seed : SlabFusionWitnessFaceStrandSeed
    K extent source.1 (boundaryCompleteSlabLinks extent)
      source.2 sourceAssignment_mem
  rootFaceId_eq : seed.root.faceId = rootFaceId
  peelSize_eq : (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length =
    peelSize
  lowerPhysical_eq :
    SlabFusionWitnessFaceStrandSeed.lowerPhysical seed = targetPhysical
  lowerAssignment_eq :
    SlabFusionWitnessFaceStrandSeed.lowerAssignment seed = targetAssignment

/-- Encode the production seed carried by a fixed-target removal witness. -/
def ComponentAdaptiveRemovalWitness.code
    {K extent rootFaceId peelSize : Nat}
    {targetPhysical : SlabLabelling}
    {targetAssignment : SlabFusionWitnessAssignment}
    {source : SlabLabelling × SlabFusionWitnessAssignment}
    (witness : ComponentAdaptiveRemovalWitness K extent rootFaceId peelSize
      targetPhysical targetAssignment source) : ComponentAdaptiveEntropyCode :=
  componentAdaptiveEntropyCode witness.seed

/-- Equal codes on the fixed removal fiber imply equal source configuration
pairs. -/
theorem ComponentAdaptiveRemovalWitness.source_eq_of_code_eq
    {K extent rootFaceId peelSize : Nat}
    {targetPhysical : SlabLabelling}
    {targetAssignment : SlabFusionWitnessAssignment}
    {leftSource rightSource : SlabLabelling × SlabFusionWitnessAssignment}
    (left : ComponentAdaptiveRemovalWitness K extent rootFaceId peelSize
      targetPhysical targetAssignment leftSource)
    (right : ComponentAdaptiveRemovalWitness K extent rootFaceId peelSize
      targetPhysical targetAssignment rightSource)
    (hcode : left.code = right.code) :
    leftSource = rightSource := by
  have hsource := componentAdaptiveEntropyCode_eq_sourceData_eq
    left.seed right.seed
    (left.rootFaceId_eq.trans right.rootFaceId_eq.symm)
    (left.lowerPhysical_eq.trans right.lowerPhysical_eq.symm)
    (left.lowerAssignment_eq.trans right.lowerAssignment_eq.symm)
    hcode
  exact Prod.ext hsource.1 hsource.2

/-! ## 3. Finite inverse-fiber count -/

/-- Any explicit duplicate-free fixed-target source family has at most
`10240000^peelSize` elements. -/
theorem componentAdaptiveRemovalSources_length_le
    (K extent rootFaceId peelSize : Nat)
    (targetPhysical : SlabLabelling)
    (targetAssignment : SlabFusionWitnessAssignment)
    (sources : List (SlabLabelling × SlabFusionWitnessAssignment))
    (hsources : sources.Nodup)
    (witness : forall source, source ∈ sources ->
      ComponentAdaptiveRemovalWitness K extent rootFaceId peelSize
        targetPhysical targetAssignment source) :
    sources.length <= componentAdaptiveEntropyBase ^ peelSize := by
  let encode : {source // source ∈ sources} -> ComponentAdaptiveEntropyCode :=
    fun source => (witness source.1 source.2).code
  have hattachedNodup : sources.attach.Nodup :=
    attach_nodup_of_nodup sources hsources
  have hencodedNodup : (sources.attach.map encode).Nodup := by
    apply nodup_map_of_injOn encode sources.attach hattachedNodup
    intro left hleft right hright hcode
    apply Subtype.ext
    exact ComponentAdaptiveRemovalWitness.source_eq_of_code_eq
      (witness left.1 left.2) (witness right.1 right.2) hcode
  have hsubset : forall code, code ∈ sources.attach.map encode ->
      code ∈ componentAdaptiveEntropyCarrier extent rootFaceId peelSize := by
    intro code hcode
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcode
    have hmem := componentAdaptiveEntropyCode_mem_carrier
      (witness source.1 source.2).seed
    rw [(witness source.1 source.2).rootFaceId_eq,
      (witness source.1 source.2).peelSize_eq] at hmem
    exact hmem
  have hbound := nodup_subset_length_le
    (sources.attach.map encode)
    (componentAdaptiveEntropyCarrier extent rootFaceId peelSize)
    hencodedNodup hsubset
  have hattachLength : sources.attach.length = sources.length := by
    rw [← List.length_map Subtype.val, List.attach_map_subtype_val]
  calc
    sources.length = sources.attach.length := hattachLength.symm
    _ = (sources.attach.map encode).length := (List.length_map _).symm
    _ <= (componentAdaptiveEntropyCarrier extent rootFaceId peelSize).length :=
      hbound
    _ <= componentAdaptiveEntropyBase ^ peelSize :=
      componentAdaptiveEntropyCarrier_length_le
        extent rootFaceId peelSize

#print axioms reconstructAssignment_eq_of_auxiliaryWords_eq
#print axioms componentAdaptiveEntropyCode_eq_sourceData_eq
#print axioms ComponentAdaptiveRemovalWitness
#print axioms ComponentAdaptiveRemovalWitness.code
#print axioms ComponentAdaptiveRemovalWitness.source_eq_of_code_eq
#print axioms componentAdaptiveRemovalSources_length_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
