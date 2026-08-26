/-
# Decode the complete physical face drop from component-relative codes

The padded animal word recovers the rooted component's plaquette support, and
the binary weak-composition word recovers one selected-copy multiplicity in
that canonical decoded order.  This module joins those two left inverses.

The decoder is defined without a production witness: from an extent, a root
face identifier, a shape word, and a multiplicity word, it returns a total
physical-face drop function.  On the production words it is exactly the
selected-copy count at every face identifier.  Faces outside the physical
carrier and physical faces outside the decoded support are proved to carry
zero selected copies.

Constructive contract: finite list indexing, Boolean interval counts, and the
two existing literal decoders only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. A witness-independent total decoder -/

/-- Decode the plaquette support from a root face identifier and a padded
animal-tour word. -/
def componentPhysicalDropDecodedSupport
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1))) : List Z4Plaq :=
  decode z4Chain (slabPlaquetteAt extent rootFaceId) shapeCode

/-- Decode a total physical-face drop.  Off the corrected-slab carrier and off
the decoded component support, the result is zero.  On the support, the value
is read at the plaquette's first canonical decoded-support index. -/
def componentPhysicalDropDecode
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (multiplicityCode : List Nat) (faceId : Nat) : Nat :=
  if faceId ∈ slabPhysicalFaceEdges extent then
    let support :=
      componentPhysicalDropDecodedSupport extent rootFaceId shapeCode
    let plaquette := slabPlaquetteAt extent faceId
    if plaquette ∈ support then
      (weakCompositionBinaryDecode multiplicityCode).getD
        (listIndexOf plaquette support) 0
    else 0
  else 0

/-! ## 2. Zero off the decoded production support -/

private theorem boolCountFrom_falseLocal (start : Nat) : forall length : Nat,
    boolCountFrom (fun _ => false) start length = 0
  | 0 => rfl
  | length + 1 => by
      rw [boolCountFrom]
      simp only [boolIndicator, Nat.zero_add]
      exact boolCountFrom_falseLocal (start + 1) length

/-- If a face's plaquette is absent from the decoded production support, no
copy over that face belongs to the rooted component, so its selected-copy
count is zero. -/
theorem selectionCount_eq_zero_of_not_mem_decodedSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faceId : Nat)
    (hface : slabPlaquetteAt extent faceId ∉
      componentDecodedPlaquetteSupport seed) :
    slabFaceStrandSelectionCount seed.selected faceId = 0 := by
  unfold slabFaceStrandSelectionCount
  have hcount := boolCountFrom_congr
    (slabFaceStrandSelectionAt seed.selected faceId)
    (fun _ => false) 0 0 (physical faceId) (by
      intro offset hoffset
      let copy : SlabFaceStrandCopy physical :=
        { faceId := faceId, slot := ⟨offset, hoffset⟩ }
      have hcopy : copy ∉ seed.component := by
        intro hmem
        apply hface
        apply (componentDecodedPlaquetteSupport_sameSupport seed).1
        apply (mem_componentPlaquetteSupport_iff seed _).mpr
        exact ⟨copy, hmem, rfl⟩
      simp only [Nat.zero_add]
      change slabFaceStrandSelectionAt seed.selected faceId offset = false
      simp [slabFaceStrandSelectionAt, hoffset,
        SlabFaceStrandSeed.selected, copy, hcopy])
  exact hcount.trans (boolCountFrom_falseLocal 0 (physical faceId))

/-! ## 3. Exact production reconstruction -/

private theorem getD_map_of_ltLocal
    {A B : Type} (map : A -> B) (source : List A) (index : Nat)
    (hindex : index < source.length) (sourceFallback : A)
    (targetFallback : B) :
    (source.map map).getD index targetFallback =
      map (source.getD index sourceFallback) := by
  induction source generalizing index with
  | nil => simp at hindex
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simpa using induction index hindex

/-- The shape and multiplicity production words reconstruct the selected-copy
count at every ambient face identifier, including all zero cases. -/
theorem componentPhysicalDropDecode_code
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faceId : Nat) :
    componentPhysicalDropDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentDecodedPhysicalMultiplicityBinaryCode seed) faceId =
      slabFaceStrandSelectionCount seed.selected faceId := by
  by_cases hphysical : faceId ∈ slabPhysicalFaceEdges extent
  · unfold componentPhysicalDropDecode
    simp only [if_pos hphysical]
    change (if slabPlaquetteAt extent faceId ∈
        componentDecodedPlaquetteSupport seed then
      (weakCompositionBinaryDecode
        (componentDecodedPhysicalMultiplicityBinaryCode seed)).getD
          (listIndexOf (slabPlaquetteAt extent faceId)
            (componentDecodedPlaquetteSupport seed)) 0
      else 0) = slabFaceStrandSelectionCount seed.selected faceId
    by_cases hsupport : slabPlaquetteAt extent faceId ∈
        componentDecodedPlaquetteSupport seed
    · rw [if_pos hsupport,
        componentDecodedPhysicalMultiplicityBinaryDecode]
      unfold componentDecodedPhysicalMultiplicityWord
      have hindex := listIndexOf_lt_of_mem
        (slabPlaquetteAt extent faceId)
        (componentDecodedPlaquetteSupport seed) hsupport
      rw [getD_map_of_ltLocal _ _ _ hindex fallbackPlaquette 0,
        getD_listIndexOf_of_mem fallbackPlaquette
          (slabPlaquetteAt extent faceId)
          (componentDecodedPlaquetteSupport seed) hsupport,
        slabFaceIdOfPlaquette_slabPlaquetteAt hphysical]
    · rw [if_neg hsupport]
      exact
        (selectionCount_eq_zero_of_not_mem_decodedSupport
          seed faceId hsupport).symm
  · unfold componentPhysicalDropDecode
    rw [if_neg hphysical]
    exact
      (SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_physical
        seed faceId hphysical).symm

/-- At a common literal root face, equality of the two production code words
forces equality of the complete physical face-drop functions. -/
theorem componentProductionCodes_eq_physicalDrop_eq
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent physical links leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent physical links rightAssignment hrightAssignment)
    (hroot : left.root.faceId = right.root.faceId)
    (hshape : componentPlaquettePaddedTourCode left =
      componentPlaquettePaddedTourCode right)
    (hmultiplicity : componentDecodedPhysicalMultiplicityBinaryCode left =
      componentDecodedPhysicalMultiplicityBinaryCode right)
    (faceId : Nat) :
    slabFaceStrandSelectionCount left.selected faceId =
      slabFaceStrandSelectionCount right.selected faceId := by
  rw [← componentPhysicalDropDecode_code left faceId,
    ← componentPhysicalDropDecode_code right faceId,
    hroot, hshape, hmultiplicity]

#print axioms componentPhysicalDropDecodedSupport
#print axioms componentPhysicalDropDecode
#print axioms selectionCount_eq_zero_of_not_mem_decodedSupport
#print axioms componentPhysicalDropDecode_code
#print axioms componentProductionCodes_eq_physicalDrop_eq

end YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
