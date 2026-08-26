/-
# A cutoff-independent global l1 budget for component auxiliary drops

The local trivalent conservation theorem bounds one link's internal drop mass
by three times its physical input drop mass.  This module performs the exact
global double count.  Complete-slab incidences are enumerated once face-major
and once link-major; the two duplicate-free lists are constructively proved to
be permutations.  Since every plaquette has four boundary links, the total
physical input mass read by all links is exactly four times the physical face
drop mass.

Zero-row sparsification preserves l1 mass.  Combining that equality, the
factor-three local conservation theorem, the factor-four incidence identity,
and the exact physical peel length gives total stored auxiliary drop mass at
most twelve times the physical peel length, independently of cutoff, extent,
and all spin labels.

Constructive contract: finite incidence permutations, Boolean recursion, and
natural arithmetic only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
import YMGap.Continuum.Z4ResidualListMultiplicityBound
import YMGap.Continuum.Z4SpinDependentIncidenceProductBound
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ResidualListMultiplicityBound
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Face-major and link-major complete-slab incidences -/

/-- One physical face identifier paired with one of its boundary links. -/
abbrev SlabFaceLinkIncidence := Nat × SlabLink

/-- Enumerate complete-slab incidences by physical face first. -/
def slabFaceMajorIncidences (extent : Nat) :
    List SlabFaceLinkIncidence :=
  (slabPhysicalFaceEdges extent).flatMap fun faceId =>
    (edgesOf (slabPlaquetteAt extent faceId)).map fun link =>
      (faceId, link)

/-- Enumerate the same complete-slab incidences by physical link first. -/
def slabLinkMajorIncidences (extent : Nat) :
    List SlabFaceLinkIncidence :=
  (boundaryCompleteSlabLinks extent).flatMap fun link =>
    (slabIncidentPlaqIds extent link).map fun faceId =>
      (faceId, link)

theorem mem_slabFaceMajorIncidences
    {extent : Nat} {incidence : SlabFaceLinkIncidence} :
    incidence ∈ slabFaceMajorIncidences extent ↔
      incidence.1 ∈ slabPhysicalFaceEdges extent ∧
      incidence.2 ∈ edgesOf (slabPlaquetteAt extent incidence.1) := by
  constructor
  · intro hmem
    obtain ⟨faceId, hface, hblock⟩ := List.mem_flatMap.mp hmem
    obtain ⟨link, hlink, heq⟩ := List.mem_map.mp hblock
    have hfaceEq : faceId = incidence.1 := by
      rw [← heq]
    have hlinkEq : link = incidence.2 := by
      rw [← heq]
    exact ⟨hfaceEq ▸ hface, hfaceEq ▸ hlinkEq ▸ hlink⟩
  · intro hparts
    apply List.mem_flatMap.mpr
    refine ⟨incidence.1, hparts.1, ?_⟩
    apply List.mem_map.mpr
    exact ⟨incidence.2, hparts.2, by cases incidence; rfl⟩

theorem mem_slabLinkMajorIncidences
    {extent : Nat} {incidence : SlabFaceLinkIncidence} :
    incidence ∈ slabLinkMajorIncidences extent ↔
      incidence.2 ∈ boundaryCompleteSlabLinks extent ∧
      incidence.1 ∈ slabIncidentPlaqIds extent incidence.2 := by
  constructor
  · intro hmem
    obtain ⟨link, hlink, hblock⟩ := List.mem_flatMap.mp hmem
    obtain ⟨faceId, hface, heq⟩ := List.mem_map.mp hblock
    have hfaceEq : faceId = incidence.1 := by
      rw [← heq]
    have hlinkEq : link = incidence.2 := by
      rw [← heq]
    exact ⟨hlinkEq ▸ hlink, hlinkEq ▸ hfaceEq ▸ hface⟩
  · intro hparts
    apply List.mem_flatMap.mpr
    refine ⟨incidence.2, hparts.1, ?_⟩
    apply List.mem_map.mpr
    exact ⟨incidence.1, hparts.2, by cases incidence; rfl⟩

private theorem incident_id_mem_edgesOf_slabPlaquetteAt
    {extent faceId : Nat} {link : SlabLink}
    (hface : faceId ∈ slabIncidentPlaqIds extent link) :
    link ∈ edgesOf (slabPlaquetteAt extent faceId) := by
  obtain ⟨plaquette, hindexed, hlink⟩ :=
    mem_slabIncidentPlaqIds.mp hface
  have hlookup : slabPlaquetteAt extent faceId = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  rw [hlookup]
  exact hlink

theorem slabCompleteIncidence_mem_iff
    {extent : Nat} {incidence : SlabFaceLinkIncidence} :
    incidence ∈ slabFaceMajorIncidences extent ↔
      incidence ∈ slabLinkMajorIncidences extent := by
  rw [mem_slabFaceMajorIncidences, mem_slabLinkMajorIncidences]
  constructor
  · intro hface
    have hlink : incidence.2 ∈ boundaryCompleteSlabLinks extent := by
      apply (mem_boundaryCompleteSlabLinks_iff extent incidence.2).mpr
      exact ⟨slabPlaquetteAt extent incidence.1,
        slabPlaquetteAt_mem hface.1, hface.2⟩
    have hincident :
        incidence.1 ∈ slabIncidentPlaqIds extent incidence.2 := by
      apply mem_slabIncidentPlaqIds.mpr
      exact ⟨slabPlaquetteAt extent incidence.1,
        slabPlaquetteAt_mem_enumerate hface.1, hface.2⟩
    exact ⟨hlink, hincident⟩
  · intro hlink
    exact ⟨slabIncidentPlaqId_physical hlink.2,
      incident_id_mem_edgesOf_slabPlaquetteAt hlink.2⟩

/-! ## 2. Duplicate-free incidence carriers -/

private theorem range_nodup_local :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

private theorem nodup_map_of_injective
    {A B : Type} (f : A → B)
    (hf : ∀ {left right}, f left = f right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective f hf hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hf heq) ▸ hitem)

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro heqItem
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead)
        hvalueItem

theorem slabFaceMajorIncidences_nodup (extent : Nat) :
    (slabFaceMajorIncidences extent).Nodup := by
  unfold slabFaceMajorIncidences slabPhysicalFaceEdges
  apply nodup_flatMap_of_disjoint_blocks
  · exact range_nodup_local _
  · intro faceId _
    apply nodup_map_of_injective (fun link => (faceId, link))
      (fun h => congrArg Prod.snd h)
    exact edgesOf_nodup _
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftLink, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightLink, _, hrightEq⟩ := List.mem_map.mp hright
    have hfirst : left = right := by
      exact congrArg Prod.fst (hleftEq.trans hrightEq.symm)
    exact hne hfirst

theorem slabLinkMajorIncidences_nodup (extent : Nat) :
    (slabLinkMajorIncidences extent).Nodup := by
  unfold slabLinkMajorIncidences
  apply nodup_flatMap_of_disjoint_blocks
  · exact boundaryCompleteSlabLinks_nodup extent
  · intro link _
    apply nodup_map_of_injective (fun faceId => (faceId, link))
      (fun h => congrArg Prod.fst h)
    exact slabIncidentPlaqIds_nodup extent link
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftId, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightId, _, hrightEq⟩ := List.mem_map.mp hright
    have hsecond : left = right := by
      exact congrArg Prod.snd (hleftEq.trans hrightEq.symm)
    exact hne hsecond

/-- The complete slab's face-major and link-major incidence lists enumerate
exactly the same duplicate-free pairs. -/
theorem slabFaceLinkIncidences_perm (extent : Nat) :
    (slabFaceMajorIncidences extent).Perm
      (slabLinkMajorIncidences extent) := by
  apply perm_of_nodup_mem_iff
    (slabFaceMajorIncidences extent)
    (slabLinkMajorIncidences extent)
    (slabFaceMajorIncidences_nodup extent)
    (slabLinkMajorIncidences_nodup extent)
  intro incidence
  exact slabCompleteIncidence_mem_iff

/-! ## 3. Contract the incidence permutation to an exact factor four -/

private theorem natListSum_map_flatMap
    {A B : Type} (block : A → List B) (weight : B → Nat) :
    ∀ source : List A,
    natListSum ((source.flatMap block).map weight) =
      natListSum (source.map fun item =>
        natListSum ((block item).map weight))
  | [] => by simp [natListSum]
  | head :: tail => by
      simp only [List.flatMap_cons, List.map_append, natListSum_append,
        List.map_cons, natListSum]
      rw [natListSum_map_flatMap block weight tail]

private theorem natListSum_map_const {A : Type} (value : Nat) :
    ∀ items : List A,
      natListSum (items.map fun _ => value) = items.length * value
  | [] => by simp [natListSum]
  | _ :: tail => by
      simp only [List.map_cons, natListSum, List.length_cons]
      rw [natListSum_map_const value tail]
      rw [Nat.add_mul]
      omega

private theorem natListSum_map_mul_left (factor : Nat) :
    ∀ values : List Nat,
      natListSum (values.map fun value => factor * value) =
        factor * natListSum values
  | [] => rfl
  | value :: values => by
      simp only [List.map_cons, natListSum]
      rw [natListSum_map_mul_left factor values]
      rw [Nat.mul_add]

/-- Weighting each incidence by its face value, face-major enumeration is
exactly four copies of the physical face sum. -/
theorem slabFaceMajorIncidences_weight_eq_four_mul
    (extent : Nat) (weight : Nat → Nat) :
    natListSum
        ((slabFaceMajorIncidences extent).map fun incidence =>
          weight incidence.1) =
      4 * natListSum ((slabPhysicalFaceEdges extent).map weight) := by
  unfold slabFaceMajorIncidences
  rw [natListSum_map_flatMap]
  have hblocks :
      natListSum
          ((slabPhysicalFaceEdges extent).map fun faceId =>
            natListSum
              (((edgesOf (slabPlaquetteAt extent faceId)).map fun link =>
                (faceId, link)).map fun incidence => weight incidence.1)) =
        natListSum
          ((slabPhysicalFaceEdges extent).map fun faceId =>
            4 * weight faceId) := by
    apply natListSum_map_congr
    intro faceId _
    rw [List.map_map]
    change natListSum
        ((edgesOf (slabPlaquetteAt extent faceId)).map fun _ =>
          weight faceId) = 4 * weight faceId
    rw [natListSum_map_const,
      edgesOf_length (slabPlaquetteAt extent faceId)]
  rw [hblocks]
  simpa only [List.map_map, Function.comp_apply] using
    (natListSum_map_mul_left 4
      ((slabPhysicalFaceEdges extent).map weight))

/-- Link-major weighting is the sum, over links, of their literal incident
physical face values. -/
theorem slabLinkMajorIncidences_weight_eq_link_sum
    (extent : Nat) (weight : Nat → Nat) :
    natListSum
        ((slabLinkMajorIncidences extent).map fun incidence =>
          weight incidence.1) =
      natListSum
        ((boundaryCompleteSlabLinks extent).map fun link =>
          natListSum ((slabIncidentPlaqIds extent link).map weight)) := by
  unfold slabLinkMajorIncidences
  rw [natListSum_map_flatMap]
  apply natListSum_map_congr
  intro link _
  rw [List.map_map]
  apply natListSum_map_congr
  intro faceId _
  rfl

/-- **Exact complete-slab incidence double count.**  The total physical face
mass read as link inputs counts every physical face exactly four times. -/
theorem slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum
    (extent : Nat) (weight : Nat → Nat) :
    natListSum
        ((boundaryCompleteSlabLinks extent).map fun link =>
          natListSum ((slabIncidentPlaqIds extent link).map weight)) =
      4 * natListSum ((slabPhysicalFaceEdges extent).map weight) := by
  have hperm :=
    (slabFaceLinkIncidences_perm extent).map fun incidence =>
      weight incidence.1
  have hsum := natListSum_perm hperm
  rw [slabFaceMajorIncidences_weight_eq_four_mul extent weight,
    slabLinkMajorIncidences_weight_eq_link_sum extent weight] at hsum
  exact hsum.symm

/-! ## 4. Convert local physical positions to literal face mass -/

private theorem finRange_map_get {A : Type} (entries : List A) :
    (List.finRange entries.length).map entries.get = entries := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    (List.ofFn_getElem (xs := entries))

/-- The physical-input side of the local conservation theorem is exactly the
sum of the selected strand counts on the link's literal incident faces. -/
theorem SlabLinkPartnerClosedFaceSelection.physicalDrop_l1_eq_incidentFace_l1
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.drop position.val) =
      natListSum
        ((slabIncidentPlaqIds extent link).map fun faceId =>
          slabFaceStrandSelectionCount selection.selected faceId) := by
  calc
    natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.drop position.val) =
      natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position =>
            slabFaceStrandSelectionCount selection.selected
              ((slabIncidentPlaqIds extent link).get position)) := by
        apply natListSum_map_congr
        intro position _
        exact SlabLinkPartnerClosedFaceSelection.drop_at_position
          selection position
    _ = natListSum
        ((slabIncidentPlaqIds extent link).map fun faceId =>
          slabFaceStrandSelectionCount selection.selected faceId) := by
      have hmapped := congrArg
        (List.map fun faceId =>
          slabFaceStrandSelectionCount selection.selected faceId)
        (finRange_map_get (slabIncidentPlaqIds extent link))
      have hsum := congrArg natListSum hmapped
      simpa only [List.map_map, Function.comp_apply] using hsum

/-! ## 5. Sparse-row erasure preserves l1 mass -/

/-- Total natural-valued mass stored across all auxiliary words. -/
def auxiliaryWordTableL1 : List (SlabLink × List Nat) → Nat
  | [] => 0
  | entry :: entries => natListSum entry.2 + auxiliaryWordTableL1 entries

/-- Boolean recognition of an all-zero word implies literal zero l1 mass. -/
theorem natListSum_eq_zero_of_finiteWordAllZeroB :
    ∀ word : List Nat, finiteWordAllZeroB word = true →
      natListSum word = 0
  | [], _ => rfl
  | value :: values, hzero => by
      have hparts : decide (value = 0) = true ∧
          finiteWordAllZeroB values = true := by
        simpa only [finiteWordAllZeroB, Bool.and_eq_true] using hzero
      have hvalue : value = 0 := of_decide_eq_true hparts.1
      rw [natListSum, hvalue,
        natListSum_eq_zero_of_finiteWordAllZeroB values hparts.2]

/-- Removing identically-zero rows preserves the total auxiliary l1 mass
exactly, without a duplicate-free hypothesis on link keys. -/
theorem sparseAuxiliaryWordTableL1_eq_full
    (wordAt : SlabLink → List Nat) :
    ∀ links : List SlabLink,
    auxiliaryWordTableL1
        (slabSparseAuxiliaryDropWordsFrom links wordAt) =
      natListSum (links.map fun link => natListSum (wordAt link))
  | [] => rfl
  | link :: links => by
      cases hzero : finiteWordAllZeroB (wordAt link) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte, auxiliaryWordTableL1,
            List.map_cons, natListSum]
          rw [sparseAuxiliaryWordTableL1_eq_full wordAt links]
      | true =>
          have hmass :=
            natListSum_eq_zero_of_finiteWordAllZeroB (wordAt link) hzero
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero, ↓reduceIte,
            List.map_cons, natListSum]
          rw [sparseAuxiliaryWordTableL1_eq_full wordAt links, hmass,
            Nat.zero_add]

/-! ## 6. The physical face sum is exactly the peel length -/

private theorem flatMap_replicate_length_eq_natListSum
    (multiplicity : Nat → Nat) :
    ∀ faceIds : List Nat,
    (faceIds.flatMap fun faceId =>
        List.replicate (multiplicity faceId) faceId).length =
      natListSum (faceIds.map multiplicity)
  | [] => rfl
  | faceId :: faceIds => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, List.map_cons, natListSum]
      rw [flatMap_replicate_length_eq_natListSum multiplicity faceIds]

/-- The serialized physical peel length is the total selected physical face
drop mass over the complete corrected-slab face carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length =
      natListSum
        ((slabPhysicalFaceEdges extent).map fun faceId =>
          slabFaceStrandSelectionCount seed.selected faceId) := by
  unfold SlabFusionWitnessFaceStrandSeed.peelFaces slabFaceDropList
  exact flatMap_replicate_length_eq_natListSum
    (slabFaceStrandSelectionCount seed.selected)
      (slabPhysicalFaceEdges extent)

/-! ## 7. Contract local conservation into the global factor twelve -/

private theorem natListSum_map_le
    {A : Type} (left right : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      natListSum (items.map left) ≤ natListSum (items.map right)
  | [], _ => Nat.le_refl 0
  | item :: items, hle => by
      simp only [List.map_cons, natListSum]
      exact Nat.add_le_add
        (hle item List.mem_cons_self)
        (natListSum_map_le left right items
          (fun next hnext => hle next (List.mem_cons_of_mem item hnext)))

private theorem SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_l1_le_three_mul_incidentFace_l1
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    natListSum
        (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link) ≤
      3 * natListSum
        ((slabIncidentPlaqIds extent link).map fun faceId =>
          slabFaceStrandSelectionCount seed.selected faceId) := by
  rw [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
    seed link hlink]
  let selection := seed.atLinkSelection ⟨link, hlink⟩
  have hlocal :=
    SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_l1_le_three_mul_physicalDrop_l1
      selection
  have hphysical :=
    SlabLinkPartnerClosedFaceSelection.physicalDrop_l1_eq_incidentFace_l1
      selection
  rw [hphysical] at hlocal
  change natListSum
      ((canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length).map selection.drop) ≤
    3 * natListSum
      ((slabIncidentPlaqIds extent link).map fun faceId =>
        slabFaceStrandSelectionCount seed.selected faceId)
  exact hlocal

/-- **Global cutoff-independent auxiliary l1 budget.**  For a rooted
component over the production complete-slab link carrier, zero-row sparse
encoding stores total auxiliary drop mass at most twelve times its physical
peel length. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWordTableL1_le_twelve_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    auxiliaryWordTableL1
        (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords ≤
      12 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  let weight : Nat → Nat := fun faceId =>
    slabFaceStrandSelectionCount seed.selected faceId
  let localMass : SlabLink → Nat := fun link =>
    natListSum ((slabIncidentPlaqIds extent link).map weight)
  have hsparse :
      auxiliaryWordTableL1
          (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords =
        natListSum
          ((boundaryCompleteSlabLinks extent).map fun link =>
            natListSum
              (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link)) := by
    unfold SlabFusionWitnessFaceStrandSeed.sparseDropCode
    exact sparseAuxiliaryWordTableL1_eq_full
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
      (boundaryCompleteSlabLinks extent)
  have hlocalSum :
      natListSum
          ((boundaryCompleteSlabLinks extent).map fun link =>
            natListSum
              (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link)) ≤
        natListSum
          ((boundaryCompleteSlabLinks extent).map fun link =>
            3 * localMass link) := by
    apply natListSum_map_le
    intro link hlink
    exact
      SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_l1_le_three_mul_incidentFace_l1
        seed link hlink
  have hscale :
      natListSum
          ((boundaryCompleteSlabLinks extent).map fun link =>
            3 * localMass link) =
        3 * natListSum
          ((boundaryCompleteSlabLinks extent).map localMass) := by
    simpa only [List.map_map, Function.comp_apply] using
      (natListSum_map_mul_left 3
        ((boundaryCompleteSlabLinks extent).map localMass))
  have hincidence :
      natListSum
          ((boundaryCompleteSlabLinks extent).map localMass) =
        4 * natListSum ((slabPhysicalFaceEdges extent).map weight) := by
    exact slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum
      extent weight
  have hpeel :
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length =
        natListSum ((slabPhysicalFaceEdges extent).map weight) := by
    exact
      SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1 seed
  rw [hsparse]
  rw [hscale, hincidence, ← hpeel] at hlocalSum
  omega

#print axioms slabCompleteIncidence_mem_iff
#print axioms slabFaceMajorIncidences_nodup
#print axioms slabLinkMajorIncidences_nodup
#print axioms slabFaceLinkIncidences_perm
#print axioms slabFaceMajorIncidences_weight_eq_four_mul
#print axioms slabLinkMajorIncidences_weight_eq_link_sum
#print axioms slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum
#print axioms SlabLinkPartnerClosedFaceSelection.physicalDrop_l1_eq_incidentFace_l1
#print axioms auxiliaryWordTableL1
#print axioms natListSum_eq_zero_of_finiteWordAllZeroB
#print axioms sparseAuxiliaryWordTableL1_eq_full
#print axioms SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWordTableL1_le_twelve_mul_peelFaces

end YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
