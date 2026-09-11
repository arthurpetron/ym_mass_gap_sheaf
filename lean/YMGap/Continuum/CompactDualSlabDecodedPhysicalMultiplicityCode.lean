/-
# A reusable physical-multiplicity compiler on decoded slab supports

Once a padded animal word has produced a canonical plaquette order, the
remaining physical information is one selected strand-copy multiplicity per
decoded plaquette.  This module isolates exactly the data needed for that
second compiler: a duplicate-free decoded support in the corrected slab, a
physical multiplicity function, and an explicit common budget controlling
both support length and total physical mass.

The compiler writes those multiplicities in support order and applies the
existing weak-composition binary encoding.  Every production word lies in a
carrier of exact cardinality `4 ^ budget`, and decoding recovers the complete
multiplicity word literally.

Constructive contract: finite lists, exact corrected-slab inverse indexing,
and natural arithmetic only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, enlarged heartbeat budget,
or trusted external computation.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
import YMGap.Continuum.RootedZ4AnimalPaddedTourCode

namespace YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.RootedZ4AnimalPaddedTourCode
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. The minimal bound-carrying physical input -/

/-- A canonical corrected-slab support and its complete physical multiplicity
budget.  The selected multiplicity function is stored directly, so this
interface is independent of any particular strand-graph presentation. -/
structure SlabDecodedPhysicalMultiplicityData (extent : Nat) : Type where
  support : List Z4Plaq
  support_nodup : support.Nodup
  support_boundary : forall plaquette, plaquette ∈ support ->
    plaquette ∈ boundaryCompleteSlabPlaquettes extent
  multiplicity : Nat -> Nat
  budget : Nat
  support_length_le_budget : support.length <= budget
  total_multiplicity_le_budget :
    natListSum ((slabPhysicalFaceEdges extent).map multiplicity) <= budget

/-- One flat, observable input connecting the shape compiler to the physical
multiplicity compiler.  The geometric support is supplied only once; the
second compiler consumes the canonical support decoded from the first. -/
structure SlabRootedAnimalMultiplicityData (extent : Nat) : Type where
  root : Z4Plaq
  support : List Z4Plaq
  root_mem : root ∈ support
  support_nodup : support.Nodup
  connected : PolymerModel.connectedIn (L := z4Chain.toLattice) support
  budget : Nat
  support_length_le_budget : support.length <= budget
  support_boundary : forall plaquette, plaquette ∈ support ->
    plaquette ∈ boundaryCompleteSlabPlaquettes extent
  multiplicity : Nat -> Nat
  total_multiplicity_le_budget :
    natListSum ((slabPhysicalFaceEdges extent).map multiplicity) <= budget

/-- The first compiler's complete bound-carrying rooted-animal input. -/
def SlabRootedAnimalMultiplicityData.toBoundedRooted {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    BoundedRootedZ4AnimalData where
  root := data.root
  support := data.support
  root_mem := data.root_mem
  support_nodup := data.support_nodup
  connected := data.connected
  budget := data.budget
  support_length_le_budget := data.support_length_le_budget

/-- The first compiler's padded shape word. -/
def slabRootedAnimalShapeCode {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    List (Fin (z4Chain.D + 1)) :=
  boundedRootedZ4AnimalPaddedTourCode data.toBoundedRooted

/-- The canonical support order passed from the shape compiler to the physical
compiler. -/
def slabRootedAnimalDecodedSupport {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) : List Z4Plaq :=
  decode z4Chain data.root (slabRootedAnimalShapeCode data)

/-- The compiler boundary preserves the complete geometric support. -/
theorem slabRootedAnimalDecodedSupport_sameSupport {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    sameSupport (L := z4Chain.toLattice) data.support
      (slabRootedAnimalDecodedSupport data) :=
  boundedRootedZ4AnimalPaddedTourCode_decode_sameSupport data.toBoundedRooted

/-- The decoder's canonical support order is duplicate-free. -/
theorem slabRootedAnimalDecodedSupport_nodup {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    (slabRootedAnimalDecodedSupport data).Nodup := by
  unfold slabRootedAnimalDecodedSupport slabRootedAnimalShapeCode
  exact decode_nodup z4Chain _ _

/-- Every decoded plaquette remains in the corrected slab carrier. -/
theorem slabRootedAnimalDecodedSupport_boundary {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent)
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ slabRootedAnimalDecodedSupport data) :
    plaquette ∈ boundaryCompleteSlabPlaquettes extent :=
  data.support_boundary plaquette
    ((slabRootedAnimalDecodedSupport_sameSupport data).2
      plaquette hplaquette)

/-- Canonical decoding preserves cardinality and hence the explicit common
budget. -/
theorem slabRootedAnimalDecodedSupport_length_le_budget {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    (slabRootedAnimalDecodedSupport data).length <= data.budget := by
  have hlength := sameSupport_length_eq_of_nodup
    (slabRootedAnimalDecodedSupport_sameSupport data)
    data.support_nodup (slabRootedAnimalDecodedSupport_nodup data)
  calc
    (slabRootedAnimalDecodedSupport data).length = data.support.length :=
      hlength.symm
    _ <= data.budget := data.support_length_le_budget

/-- The canonical decoded-support input consumed by the second compiler. -/
def SlabRootedAnimalMultiplicityData.toDecodedPhysical {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    SlabDecodedPhysicalMultiplicityData extent where
  support := slabRootedAnimalDecodedSupport data
  support_nodup := slabRootedAnimalDecodedSupport_nodup data
  support_boundary := slabRootedAnimalDecodedSupport_boundary data
  multiplicity := data.multiplicity
  budget := data.budget
  support_length_le_budget :=
    slabRootedAnimalDecodedSupport_length_le_budget data
  total_multiplicity_le_budget := data.total_multiplicity_le_budget

/-! ## 2. The canonical multiplicity word and its two budgets -/

/-- One physical multiplicity per decoded plaquette, in decoder order. -/
def slabDecodedPhysicalMultiplicityWord {extent : Nat}
    (data : SlabDecodedPhysicalMultiplicityData extent) : List Nat :=
  data.support.map fun plaquette =>
    data.multiplicity (slabFaceIdOfPlaquette extent plaquette)

/-- The multiplicity word has at most one coordinate per budget unit. -/
theorem slabDecodedPhysicalMultiplicityWord_length_le_budget
    {extent : Nat} (data : SlabDecodedPhysicalMultiplicityData extent) :
    (slabDecodedPhysicalMultiplicityWord data).length <= data.budget := by
  unfold slabDecodedPhysicalMultiplicityWord
  rw [List.length_map]
  exact data.support_length_le_budget

private theorem listNatWeight_eq_natListSum_mapLocal {A : Type}
    (weight : A -> Nat) : forall items : List A,
    listNatWeight weight items = natListSum (items.map weight)
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight, List.map_cons, natListSum]
      rw [listNatWeight_eq_natListSum_mapLocal weight tail]

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

/-- The l1 mass of the support-ordered word is bounded by the stored complete
physical mass budget. -/
theorem slabDecodedPhysicalMultiplicityWord_l1_le_budget
    {extent : Nat} (data : SlabDecodedPhysicalMultiplicityData extent) :
    natListSum (slabDecodedPhysicalMultiplicityWord data) <= data.budget := by
  let supportMultiplicity : Z4Plaq -> Nat := fun plaquette =>
    data.multiplicity (slabFaceIdOfPlaquette extent plaquette)
  let physicalPlaquettes : List Z4Plaq :=
    (slabPhysicalFaceEdges extent).map (slabPlaquetteAt extent)
  have hsubset : forall plaquette, plaquette ∈ data.support ->
      plaquette ∈ physicalPlaquettes := by
    intro plaquette hplaquette
    have hboundary := data.support_boundary plaquette hplaquette
    let faceId := slabFaceIdOfPlaquette extent plaquette
    have hfaceId : faceId ∈ slabPhysicalFaceEdges extent :=
      slabFaceIdOfPlaquette_physical hboundary
    exact List.mem_map.mpr ⟨faceId, hfaceId,
      slabPlaquetteAt_faceIdOfPlaquette hboundary⟩
  have hweighted := listNatWeight_le_of_nodup_mem supportMultiplicity
    data.support physicalPlaquettes data.support_nodup hsubset
  calc
    natListSum (slabDecodedPhysicalMultiplicityWord data) =
        listNatWeight supportMultiplicity data.support := by
      rw [listNatWeight_eq_natListSum_mapLocal]
      unfold slabDecodedPhysicalMultiplicityWord supportMultiplicity
      rfl
    _ <= listNatWeight supportMultiplicity physicalPlaquettes := hweighted
    _ = listNatWeight
        (fun faceId => supportMultiplicity (slabPlaquetteAt extent faceId))
        (slabPhysicalFaceEdges extent) := by
      unfold physicalPlaquettes
      exact listNatWeight_map (slabPlaquetteAt extent) supportMultiplicity _
    _ = listNatWeight data.multiplicity
        (slabPhysicalFaceEdges extent) := by
      apply listNatWeight_congrLocal
      intro faceId hfaceId
      unfold supportMultiplicity
      rw [slabFaceIdOfPlaquette_slabPlaquetteAt hfaceId]
    _ = natListSum
        ((slabPhysicalFaceEdges extent).map data.multiplicity) :=
      listNatWeight_eq_natListSum_mapLocal _ _
    _ <= data.budget := data.total_multiplicity_le_budget

/-! ## 3. The fixed `4 ^ budget` binary carrier -/

/-- Compile the complete support-ordered multiplicity word. -/
def slabDecodedPhysicalMultiplicityBinaryCode {extent : Nat}
    (data : SlabDecodedPhysicalMultiplicityData extent) : List Nat :=
  weakCompositionBinaryCode data.budget
    (slabDecodedPhysicalMultiplicityWord data)

/-- The binary code decodes literally to the stored multiplicity word. -/
theorem slabDecodedPhysicalMultiplicityBinaryDecode {extent : Nat}
    (data : SlabDecodedPhysicalMultiplicityData extent) :
    weakCompositionBinaryDecode
        (slabDecodedPhysicalMultiplicityBinaryCode data) =
      slabDecodedPhysicalMultiplicityWord data := by
  unfold slabDecodedPhysicalMultiplicityBinaryCode
  exact weakCompositionBinaryDecode_code _ _

/-- Every production code belongs to the carrier indexed only by its stored
physical budget. -/
theorem slabDecodedPhysicalMultiplicityBinaryCode_mem_carrier
    {extent : Nat} (data : SlabDecodedPhysicalMultiplicityData extent) :
    slabDecodedPhysicalMultiplicityBinaryCode data ∈
      allSeqs 2 (2 * data.budget) := by
  unfold slabDecodedPhysicalMultiplicityBinaryCode
  apply weakCompositionBinaryCode_mem_allSeqs
  · exact slabDecodedPhysicalMultiplicityWord_length_le_budget data
  · exact slabDecodedPhysicalMultiplicityWord_l1_le_budget data

/-- The physical-multiplicity carrier has exactly `4 ^ budget` words. -/
theorem slabDecodedPhysicalMultiplicityCarrier_length (budget : Nat) :
    (allSeqs 2 (2 * budget)).length = 4 ^ budget :=
  componentDecodedPhysicalMultiplicityCarrier_length budget

/-- Equal binary codes recover equal support-ordered multiplicity words. -/
theorem slabDecodedPhysicalMultiplicityBinaryCode_eq_word_eq
    {extent : Nat}
    (left right : SlabDecodedPhysicalMultiplicityData extent)
    (hcode : slabDecodedPhysicalMultiplicityBinaryCode left =
      slabDecodedPhysicalMultiplicityBinaryCode right) :
    slabDecodedPhysicalMultiplicityWord left =
      slabDecodedPhysicalMultiplicityWord right := by
  rw [← slabDecodedPhysicalMultiplicityBinaryDecode left,
    ← slabDecodedPhysicalMultiplicityBinaryDecode right, hcode]

/-! ## 4. The connected two-compiler path -/

/-- The physical code obtained after passing through the canonical shape
decoder. -/
def slabRootedAnimalPhysicalMultiplicityBinaryCode {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) : List Nat :=
  slabDecodedPhysicalMultiplicityBinaryCode data.toDecodedPhysical

/-- The connected shape word lies in the common `625 ^ budget` carrier. -/
theorem slabRootedAnimalShapeCode_mem_carrier {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    slabRootedAnimalShapeCode data ∈
      rootedZ4AnimalPaddedTourCarrier data.budget :=
  boundedRootedZ4AnimalPaddedTourCode_mem_carrier data.toBoundedRooted

/-- The connected physical word lies in the common `4 ^ budget` carrier. -/
theorem slabRootedAnimalPhysicalMultiplicityBinaryCode_mem_carrier
    {extent : Nat} (data : SlabRootedAnimalMultiplicityData extent) :
    slabRootedAnimalPhysicalMultiplicityBinaryCode data ∈
      allSeqs 2 (2 * data.budget) :=
  slabDecodedPhysicalMultiplicityBinaryCode_mem_carrier
    data.toDecodedPhysical

/-- Decoding the connected physical word recovers its support-ordered
multiplicity list literally. -/
theorem slabRootedAnimalPhysicalMultiplicityBinaryDecode {extent : Nat}
    (data : SlabRootedAnimalMultiplicityData extent) :
    weakCompositionBinaryDecode
        (slabRootedAnimalPhysicalMultiplicityBinaryCode data) =
      slabDecodedPhysicalMultiplicityWord data.toDecodedPhysical :=
  slabDecodedPhysicalMultiplicityBinaryDecode data.toDecodedPhysical

#print axioms SlabDecodedPhysicalMultiplicityData
#print axioms SlabRootedAnimalMultiplicityData
#print axioms SlabRootedAnimalMultiplicityData.toBoundedRooted
#print axioms slabRootedAnimalShapeCode
#print axioms slabRootedAnimalDecodedSupport
#print axioms slabRootedAnimalDecodedSupport_sameSupport
#print axioms slabRootedAnimalDecodedSupport_nodup
#print axioms slabRootedAnimalDecodedSupport_boundary
#print axioms slabRootedAnimalDecodedSupport_length_le_budget
#print axioms SlabRootedAnimalMultiplicityData.toDecodedPhysical
#print axioms slabDecodedPhysicalMultiplicityWord
#print axioms slabDecodedPhysicalMultiplicityWord_length_le_budget
#print axioms slabDecodedPhysicalMultiplicityWord_l1_le_budget
#print axioms slabDecodedPhysicalMultiplicityBinaryCode
#print axioms slabDecodedPhysicalMultiplicityBinaryDecode
#print axioms slabDecodedPhysicalMultiplicityBinaryCode_mem_carrier
#print axioms slabDecodedPhysicalMultiplicityCarrier_length
#print axioms slabDecodedPhysicalMultiplicityBinaryCode_eq_word_eq
#print axioms slabRootedAnimalPhysicalMultiplicityBinaryCode
#print axioms slabRootedAnimalShapeCode_mem_carrier
#print axioms slabRootedAnimalPhysicalMultiplicityBinaryCode_mem_carrier
#print axioms slabRootedAnimalPhysicalMultiplicityBinaryDecode

end YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode
