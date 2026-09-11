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

namespace YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4FiniteBoxPacketState
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

#print axioms SlabDecodedPhysicalMultiplicityData
#print axioms slabDecodedPhysicalMultiplicityWord
#print axioms slabDecodedPhysicalMultiplicityWord_length_le_budget
#print axioms slabDecodedPhysicalMultiplicityWord_l1_le_budget
#print axioms slabDecodedPhysicalMultiplicityBinaryCode
#print axioms slabDecodedPhysicalMultiplicityBinaryDecode
#print axioms slabDecodedPhysicalMultiplicityBinaryCode_mem_carrier
#print axioms slabDecodedPhysicalMultiplicityCarrier_length
#print axioms slabDecodedPhysicalMultiplicityBinaryCode_eq_word_eq

end YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode
