/-
# Component-relative physical strand multiplicities

The old exact reconstruction code stores one ambient slab face identifier per
selected physical strand copy.  The padded animal tour already recovers the
finite geometric support at a fixed root, so those ambient identifiers can be
replaced by one multiplicity per decoded plaquette.

This module constructively inverts a corrected-slab plaquette to its physical
face identifier, evaluates the selected-copy count in the decoder's canonical
support order, and proves that both the word length and its l1 mass are bounded
by the physical peel length.  The existing weak-composition compiler therefore
places the complete physical multiplicity word in a binary carrier of exact
size `4 ^ peelSize`.

Constructive contract: finite list search, duplicate-free weighted subset
accounting, and exact corrected-slab indexing only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
import YMGap.Continuum.FiniteSimpleWalk

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Constructive inverse indexing on the corrected slab -/

/-- The first corrected-slab face identifier carrying a requested plaquette,
with zero as the irrelevant off-slab fallback. -/
def slabFaceIdOfPlaquette (extent : Nat) (plaquette : Z4Plaq) : Nat :=
  listIndexOf plaquette (boundaryCompleteSlabPlaquettes extent)

/-- A plaquette in the corrected slab has a physical inverse face identifier. -/
theorem slabFaceIdOfPlaquette_physical
    {extent : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    slabFaceIdOfPlaquette extent plaquette ∈ slabPhysicalFaceEdges extent := by
  unfold slabFaceIdOfPlaquette slabPhysicalFaceEdges
  exact List.mem_range.mpr
    (listIndexOf_lt_of_mem plaquette _ hplaquette)

/-- Looking up the inverse face identifier recovers the requested plaquette. -/
theorem slabPlaquetteAt_faceIdOfPlaquette
    {extent : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    slabPlaquetteAt extent (slabFaceIdOfPlaquette extent plaquette) =
      plaquette := by
  unfold slabPlaquetteAt slabFaceIdOfPlaquette
  exact getD_listIndexOf_of_mem fallbackPlaquette plaquette _ hplaquette

/-- On the physical carrier, inverse indexing is a literal left inverse of
`slabPlaquetteAt`. -/
theorem slabFaceIdOfPlaquette_slabPlaquetteAt
    {extent faceId : Nat}
    (hfaceId : faceId ∈ slabPhysicalFaceEdges extent) :
    slabFaceIdOfPlaquette extent (slabPlaquetteAt extent faceId) = faceId := by
  apply slabPlaquetteAt_injective_on_physical
    (slabFaceIdOfPlaquette_physical (slabPlaquetteAt_mem hfaceId)) hfaceId
  exact slabPlaquetteAt_faceIdOfPlaquette (slabPlaquetteAt_mem hfaceId)

/-! ## 2. Canonical decoded component support -/

/-- The canonical plaquette order obtained by decoding the padded shape word. -/
def componentDecodedPlaquetteSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : List Z4Plaq :=
  decode z4Chain (slabPlaquetteAt extent seed.root.faceId)
    (componentPlaquettePaddedTourCode seed)

/-- The canonical decoded order has exactly the geometric component support. -/
theorem componentDecodedPlaquetteSupport_sameSupport
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    sameSupport (L := z4Chain.toLattice) (componentPlaquetteSupport seed)
      (componentDecodedPlaquetteSupport seed) :=
  componentPlaquettePaddedTourCode_decode_sameSupport seed

/-- The decoder never repeats a visited plaquette. -/
theorem componentDecodedPlaquetteSupport_nodup
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentDecodedPlaquetteSupport seed).Nodup := by
  unfold componentDecodedPlaquetteSupport
  exact decode_nodup z4Chain _ _

/-- Every plaquette in the geometric component support belongs to the corrected
slab plaquette carrier. -/
theorem componentPlaquetteSupport_subset_boundaryCompleteSlab
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ componentPlaquetteSupport seed) :
    plaquette ∈ boundaryCompleteSlabPlaquettes extent := by
  obtain ⟨copy, hcopy, hcopyEq⟩ :=
    (mem_componentPlaquetteSupport_iff seed plaquette).mp hplaquette
  rw [← hcopyEq]
  exact slabPlaquetteAt_mem
    (SlabFusionWitnessFaceStrandSeed.component_faceId_physical
      seed copy hcopy)

/-- Every plaquette in the canonical decoded order belongs to the corrected
slab plaquette carrier. -/
theorem componentDecodedPlaquetteSupport_subset_boundaryCompleteSlab
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ componentDecodedPlaquetteSupport seed) :
    plaquette ∈ boundaryCompleteSlabPlaquettes extent :=
  componentPlaquetteSupport_subset_boundaryCompleteSlab seed plaquette
    ((componentDecodedPlaquetteSupport_sameSupport seed).2 plaquette hplaquette)

/-- The decoded support length is bounded by physical peel length. -/
theorem componentDecodedPlaquetteSupport_length_le_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentDecodedPlaquetteSupport seed).length <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hlength := sameSupport_length_eq_of_nodup
    (componentDecodedPlaquetteSupport_sameSupport seed)
    (componentPlaquetteSupport_nodup seed)
    (componentDecodedPlaquetteSupport_nodup seed)
  calc
    (componentDecodedPlaquetteSupport seed).length =
        (componentPlaquetteSupport seed).length := hlength.symm
    _ <= (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length :=
      componentPlaquetteSupport_length_le_peelFaces seed

/-! ## 3. One selected-copy multiplicity per decoded plaquette -/

/-- The physical selected-copy count written in the canonical decoded
plaquette order. -/
def componentDecodedPhysicalMultiplicityWord
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : List Nat :=
  (componentDecodedPlaquetteSupport seed).map fun plaquette =>
    slabFaceStrandSelectionCount seed.selected
      (slabFaceIdOfPlaquette extent plaquette)

/-- The multiplicity word has at most one coordinate per peel entry. -/
theorem componentDecodedPhysicalMultiplicityWord_length_le_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (componentDecodedPhysicalMultiplicityWord seed).length <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentDecodedPhysicalMultiplicityWord
  rw [List.length_map]
  exact componentDecodedPlaquetteSupport_length_le_peelFaces seed

private theorem listNatWeight_eq_natListSum_map {A : Type}
    (weight : A -> Nat) : forall items : List A,
    listNatWeight weight items = natListSum (items.map weight)
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight, List.map_cons, natListSum]
      rw [listNatWeight_eq_natListSum_map weight tail]

private theorem listNatWeight_congrLocal {A : Type}
    (left right : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> left item = right item) ->
      listNatWeight left items = listNatWeight right items
  | [], _ => rfl
  | head :: tail, heq => by
      simp only [listNatWeight]
      rw [heq head List.mem_cons_self]
      apply congrArg (fun value => right head + value)
      apply listNatWeight_congrLocal left right tail
      intro item hitem
      exact heq item (List.mem_cons_of_mem head hitem)

/-- The multiplicity word's l1 mass is no larger than the complete physical
peel mass. -/
theorem componentDecodedPhysicalMultiplicityWord_l1_le_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    natListSum (componentDecodedPhysicalMultiplicityWord seed) <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  let multiplicity : Z4Plaq -> Nat := fun plaquette =>
    slabFaceStrandSelectionCount seed.selected
      (slabFaceIdOfPlaquette extent plaquette)
  let physicalPlaquettes : List Z4Plaq :=
    (slabPhysicalFaceEdges extent).map (slabPlaquetteAt extent)
  have hsubset : forall plaquette,
      plaquette ∈ componentDecodedPlaquetteSupport seed ->
        plaquette ∈ physicalPlaquettes := by
    intro plaquette hplaquette
    have hboundary :=
      componentDecodedPlaquetteSupport_subset_boundaryCompleteSlab
        seed plaquette hplaquette
    let faceId := slabFaceIdOfPlaquette extent plaquette
    have hfaceId : faceId ∈ slabPhysicalFaceEdges extent :=
      slabFaceIdOfPlaquette_physical hboundary
    apply List.mem_map.mpr
    exact ⟨faceId, hfaceId,
      slabPlaquetteAt_faceIdOfPlaquette hboundary⟩
  have hweighted := listNatWeight_le_of_nodup_mem multiplicity
    (componentDecodedPlaquetteSupport seed) physicalPlaquettes
    (componentDecodedPlaquetteSupport_nodup seed) hsubset
  calc
    natListSum (componentDecodedPhysicalMultiplicityWord seed) =
        listNatWeight multiplicity
          (componentDecodedPlaquetteSupport seed) := by
      rw [listNatWeight_eq_natListSum_map]
      unfold componentDecodedPhysicalMultiplicityWord multiplicity
      rfl
    _ <= listNatWeight multiplicity physicalPlaquettes := hweighted
    _ = listNatWeight
        (fun faceId => multiplicity (slabPlaquetteAt extent faceId))
        (slabPhysicalFaceEdges extent) := by
      unfold physicalPlaquettes
      exact listNatWeight_map (slabPlaquetteAt extent) multiplicity _
    _ = listNatWeight
        (slabFaceStrandSelectionCount seed.selected)
        (slabPhysicalFaceEdges extent) := by
      apply listNatWeight_congrLocal
      intro faceId hfaceId
      unfold multiplicity
      rw [slabFaceIdOfPlaquette_slabPlaquetteAt hfaceId]
    _ = natListSum
        ((slabPhysicalFaceEdges extent).map
          (slabFaceStrandSelectionCount seed.selected)) :=
      listNatWeight_eq_natListSum_map _ _
    _ = (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length :=
      (SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1
        seed).symm

/-! ## 4. The fixed `4^n` physical-multiplicity carrier -/

/-- Compile the physical multiplicity word at budget equal to peel length. -/
def componentDecodedPhysicalMultiplicityBinaryCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : List Nat :=
  weakCompositionBinaryCode
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length
    (componentDecodedPhysicalMultiplicityWord seed)

/-- The multiplicity compiler is literally decodable. -/
theorem componentDecodedPhysicalMultiplicityBinaryDecode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    weakCompositionBinaryDecode
        (componentDecodedPhysicalMultiplicityBinaryCode seed) =
      componentDecodedPhysicalMultiplicityWord seed := by
  unfold componentDecodedPhysicalMultiplicityBinaryCode
  exact weakCompositionBinaryDecode_code _ _

/-- Every production multiplicity code lies in the binary carrier indexed only
by physical peel length. -/
theorem componentDecodedPhysicalMultiplicityBinaryCode_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    componentDecodedPhysicalMultiplicityBinaryCode seed ∈
      allSeqs 2
        (2 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length) := by
  unfold componentDecodedPhysicalMultiplicityBinaryCode
  apply weakCompositionBinaryCode_mem_allSeqs
  · exact componentDecodedPhysicalMultiplicityWord_length_le_peelFaces seed
  · exact componentDecodedPhysicalMultiplicityWord_l1_le_peelFaces seed

/-- The physical-multiplicity carrier has exactly `4^peelSize` words. -/
theorem componentDecodedPhysicalMultiplicityCarrier_length
    (peelSize : Nat) :
    (allSeqs 2 (2 * peelSize)).length = 4 ^ peelSize := by
  rw [weakCompositionBinaryCarrier_length,
    two_pow_two_mul_eq_four_pow]

#print axioms slabFaceIdOfPlaquette
#print axioms slabFaceIdOfPlaquette_physical
#print axioms slabPlaquetteAt_faceIdOfPlaquette
#print axioms slabFaceIdOfPlaquette_slabPlaquetteAt
#print axioms componentDecodedPlaquetteSupport
#print axioms componentDecodedPlaquetteSupport_sameSupport
#print axioms componentDecodedPlaquetteSupport_nodup
#print axioms componentPlaquetteSupport_subset_boundaryCompleteSlab
#print axioms componentDecodedPlaquetteSupport_subset_boundaryCompleteSlab
#print axioms componentDecodedPlaquetteSupport_length_le_peelFaces
#print axioms componentDecodedPhysicalMultiplicityWord
#print axioms componentDecodedPhysicalMultiplicityWord_length_le_peelFaces
#print axioms componentDecodedPhysicalMultiplicityWord_l1_le_peelFaces
#print axioms componentDecodedPhysicalMultiplicityBinaryCode
#print axioms componentDecodedPhysicalMultiplicityBinaryDecode
#print axioms componentDecodedPhysicalMultiplicityBinaryCode_mem_carrier
#print axioms componentDecodedPhysicalMultiplicityCarrier_length

end YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
