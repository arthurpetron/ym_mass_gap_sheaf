/-
# Pointwise bivalent contraction for the edge-touching double cube

The radius-zero edge-touching double cube has twenty-three physical link
blocks: twenty-two bivalent blocks and one four-valent shared block.  This
leaf gives the existing production link decoder an exact finite structural
schedule, keeps all forty-eight face-corner Boolean indices opaque, and
contracts the twenty-two bivalent factors around the signed shared-link
projector.

No Boolean assignment carrier is enumerated.  An assignment is an arbitrary
`List Bool`, queried only by `List.getD`.  No twelve-face sum, depth-forty-eight
recursion, bounded labelling family, or trajectory is unfolded or
materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeSharedLinkHaarNormalization
import YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
import YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector
import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjectorReordering

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjectorReordering
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeSharedLinkHaarNormalization

/-! ## 1. The production block decoder and its twenty-two-block complement -/

/-- Production quaternion blocks of all twenty-three touched links, in the
audited duplicate-free geometric order. -/
def radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks : List Nat :=
  radiusZeroEdgeTouchingDoubleCubeTouchedLinks.map
    (adjacentEvenActiveLinkIndex 0)

/-- Production block of the unique four-valent physical link. -/
def radiusZeroEdgeTouchingDoubleCubeSharedBlock : Nat :=
  adjacentEvenActiveLinkIndex 0
    radiusZeroEdgeTouchingDoubleCubeSharedLink

/-- The physical bivalent support is obtained by removing exactly the
certified shared link from the twenty-three-link support. -/
def radiusZeroEdgeTouchingDoubleCubeBivalentLinks : List Z4Link :=
  radiusZeroEdgeTouchingDoubleCubeTouchedLinks.filter (fun link =>
    decide (link ≠ radiusZeroEdgeTouchingDoubleCubeSharedLink))

/-- Production blocks of the twenty-two bivalent links. -/
def radiusZeroEdgeTouchingDoubleCubeBivalentBlocks : List Nat :=
  radiusZeroEdgeTouchingDoubleCubeBivalentLinks.map
    (adjacentEvenActiveLinkIndex 0)

theorem radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks_length :
    radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks.length = 23 := by
  simpa only [radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks,
    List.length_map] using
    radiusZeroEdgeTouchingDoubleCubeTouchedLinks_length

theorem radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks_nodup :
    radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks.Nodup := by
  unfold radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · exact radiusZeroEdgeTouchingDoubleCubeTouchedLinks_nodup
  · intro left hleft right hright hindex
    exact adjacentEvenActiveLinkIndex_injective_on
      (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active hleft)
      (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active hright)
      hindex

theorem radiusZeroEdgeTouchingDoubleCubeActiveLinkBlock_lt
    {block : Nat}
    (hblock : block ∈ radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks) :
    block < (adjacentEvenActiveLinks 0).length := by
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hblock
  exact adjacentEvenActiveLinkIndex_lt
    (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active hlink)

theorem radiusZeroEdgeTouchingDoubleCubeSharedBlock_lt :
    radiusZeroEdgeTouchingDoubleCubeSharedBlock <
      (adjacentEvenActiveLinks 0).length := by
  unfold radiusZeroEdgeTouchingDoubleCubeSharedBlock
  exact adjacentEvenActiveLinkIndex_lt
    (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
      radiusZeroEdgeTouchingDoubleCubeSharedLink_mem_touched)

theorem radiusZeroEdgeTouchingDoubleCubeBivalentLinks_length :
    radiusZeroEdgeTouchingDoubleCubeBivalentLinks.length = 22 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeBivalentLinks_nodup :
    radiusZeroEdgeTouchingDoubleCubeBivalentLinks.Nodup := by
  exact List.filter_sublist.nodup
    radiusZeroEdgeTouchingDoubleCubeTouchedLinks_nodup

theorem radiusZeroEdgeTouchingDoubleCubeBivalentLink_mem_touched
    {link : Z4Link}
    (hlink : link ∈ radiusZeroEdgeTouchingDoubleCubeBivalentLinks) :
    link ∈ radiusZeroEdgeTouchingDoubleCubeTouchedLinks := by
  exact (List.mem_filter.mp hlink).1

theorem radiusZeroEdgeTouchingDoubleCubeBivalentLink_ne_shared
    {link : Z4Link}
    (hlink : link ∈ radiusZeroEdgeTouchingDoubleCubeBivalentLinks) :
    link ≠ radiusZeroEdgeTouchingDoubleCubeSharedLink := by
  exact of_decide_eq_true (List.mem_filter.mp hlink).2

theorem radiusZeroEdgeTouchingDoubleCubeSharedLink_not_mem_bivalent :
    radiusZeroEdgeTouchingDoubleCubeSharedLink ∉
      radiusZeroEdgeTouchingDoubleCubeBivalentLinks := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeBivalentBlocks_length :
    radiusZeroEdgeTouchingDoubleCubeBivalentBlocks.length = 22 := by
  simpa only [radiusZeroEdgeTouchingDoubleCubeBivalentBlocks,
    List.length_map] using
    radiusZeroEdgeTouchingDoubleCubeBivalentLinks_length

theorem radiusZeroEdgeTouchingDoubleCubeBivalentBlocks_nodup :
    radiusZeroEdgeTouchingDoubleCubeBivalentBlocks.Nodup := by
  unfold radiusZeroEdgeTouchingDoubleCubeBivalentBlocks
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · exact radiusZeroEdgeTouchingDoubleCubeBivalentLinks_nodup
  · intro left hleft right hright hindex
    exact adjacentEvenActiveLinkIndex_injective_on
      (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
        (radiusZeroEdgeTouchingDoubleCubeBivalentLink_mem_touched hleft))
      (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
        (radiusZeroEdgeTouchingDoubleCubeBivalentLink_mem_touched hright))
      hindex

theorem radiusZeroEdgeTouchingDoubleCubeBivalentBlock_lt
    {block : Nat}
    (hblock : block ∈ radiusZeroEdgeTouchingDoubleCubeBivalentBlocks) :
    block < (adjacentEvenActiveLinks 0).length := by
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hblock
  exact adjacentEvenActiveLinkIndex_lt
    (radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
      (radiusZeroEdgeTouchingDoubleCubeBivalentLink_mem_touched hlink))

theorem radiusZeroEdgeTouchingDoubleCubeSharedBlock_not_mem_bivalent :
    radiusZeroEdgeTouchingDoubleCubeSharedBlock ∉
      radiusZeroEdgeTouchingDoubleCubeBivalentBlocks := by
  intro hmember
  obtain ⟨link, hlink, hindex⟩ := List.mem_map.mp hmember
  have hlinkActive :=
    radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
      (radiusZeroEdgeTouchingDoubleCubeBivalentLink_mem_touched hlink)
  have hsharedActive :=
    radiusZeroEdgeTouchingDoubleCubeTouchedLink_active
      radiusZeroEdgeTouchingDoubleCubeSharedLink_mem_touched
  have heq : link = radiusZeroEdgeTouchingDoubleCubeSharedLink := by
    apply adjacentEvenActiveLinkIndex_injective_on hlinkActive hsharedActive
    simpa only [radiusZeroEdgeTouchingDoubleCubeSharedBlock] using hindex
  exact radiusZeroEdgeTouchingDoubleCubeSharedLink_not_mem_bivalent
    (heq ▸ hlink)

/-! ## 2. Forty-eight face-corner tags and exact occurrence coverage -/

/-- Four independent cyclic matrix-index tags for each of the twelve audited
faces.  The first cube reuses the already-audited elementary-cube vertex-major
convention, and the second uses its disjoint translate by twenty four. -/
def radiusZeroEdgeTouchingDoubleCubeFaceTagCycles : List (List Nat) :=
  [[0, 9, 6, 3],
   [1, 4, 15, 12],
   [2, 13, 21, 10],
   [14, 16, 18, 22],
   [11, 23, 19, 7],
   [24, 33, 30, 27],
   [25, 28, 39, 36],
   [26, 37, 45, 34],
   [38, 40, 42, 46],
   [35, 47, 43, 31],
   [5, 8, 20, 17],
   [29, 32, 44, 41]]

def radiusZeroEdgeTouchingDoubleCubeFaceCornerTags : List Nat :=
  radiusZeroEdgeTouchingDoubleCubeFaceTagCycles.flatMap (fun cycle => cycle)

theorem radiusZeroEdgeTouchingDoubleCubeFaceTagCycles_length :
    radiusZeroEdgeTouchingDoubleCubeFaceTagCycles.length = 12 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceTagCycle_lengths :
    radiusZeroEdgeTouchingDoubleCubeFaceTagCycles.map List.length =
      List.replicate 12 4 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_length :
    radiusZeroEdgeTouchingDoubleCubeFaceCornerTags.length = 48 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_nodup :
    radiusZeroEdgeTouchingDoubleCubeFaceCornerTags.Nodup := by
  decide

/-- Turn one cyclic face-tag row into its four directed matrix-index edges. -/
def cyclicFourDoubleCubeTagEdges : List Nat → List (Nat × Nat)
  | [first, second, third, fourth] =>
      [(first, second), (second, third),
       (third, fourth), (fourth, first)]
  | _ => []

def radiusZeroEdgeTouchingDoubleCubeBoundaryTagEdges : List (Nat × Nat) :=
  radiusZeroEdgeTouchingDoubleCubeFaceTagCycles.flatMap
    cyclicFourDoubleCubeTagEdges

theorem radiusZeroEdgeTouchingDoubleCubeBoundaryTagEdges_length :
    radiusZeroEdgeTouchingDoubleCubeBoundaryTagEdges.length = 48 := by
  decide

/-- One tagged production occurrence, retaining its face identifier and its
independent external row/column tags. -/
structure TaggedDoubleCubeBoundaryOccurrence where
  faceId : Nat
  occurrence : OrientedFundamentalLinkOccurrence
  rowTag : Nat
  columnTag : Nat
  deriving DecidableEq

def radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences :
    List TaggedDoubleCubeBoundaryOccurrence :=
  (radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences.zip
      radiusZeroEdgeTouchingDoubleCubeBoundaryTagEdges).map (fun entry =>
    { faceId := entry.1.1
      occurrence := entry.1.2
      rowTag := entry.2.1
      columnTag := entry.2.2 })

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences_length :
    radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences.length = 48 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences_map_faceId :
    radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences.map
        (fun tagged => tagged.faceId) =
      radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences.map Prod.fst := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences_map_occurrence :
    radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences.map
        (fun tagged => tagged.occurrence) =
      radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences.map Prod.snd := by
  decide

/-! ## 3. The literal twenty-two-row bivalent table -/

structure TaggedDoubleCubeBivalentPair where
  physicalLink : Z4Link
  forwardRowTag : Nat
  forwardColumnTag : Nat
  reverseRowTag : Nat
  reverseColumnTag : Nat
  deriving DecidableEq

/-- Exact bivalent table in touched-link order, with the shared-link slot
omitted. -/
def radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs :
    List TaggedDoubleCubeBivalentPair :=
  [⟨((0, 0, 0, 1), .x0), 1, 4, 3, 0⟩,
   ⟨((0, 0, 0, 1), .x1), 0, 9, 10, 2⟩,
   ⟨((0, 1, 0, 1), .x0), 9, 6, 7, 11⟩,
   ⟨((1, 0, 0, 1), .x1), 5, 8, 6, 3⟩,
   ⟨((0, 0, 0, 1), .x2), 2, 13, 12, 1⟩,
   ⟨((0, 0, 1, 1), .x0), 14, 16, 15, 12⟩,
   ⟨((1, 0, 0, 1), .x2), 4, 15, 17, 5⟩,
   ⟨((0, 0, 1, 1), .x1), 13, 21, 22, 14⟩,
   ⟨((0, 1, 0, 1), .x2), 11, 23, 21, 10⟩,
   ⟨((1, 0, 1, 1), .x1), 16, 18, 20, 17⟩,
   ⟨((1, 1, 0, 1), .x2), 8, 20, 19, 7⟩,
   ⟨((0, 1, 1, 1), .x1), 24, 33, 34, 26⟩,
   ⟨((0, 2, 1, 1), .x0), 33, 30, 31, 35⟩,
   ⟨((1, 1, 1, 1), .x1), 29, 32, 30, 27⟩,
   ⟨((0, 1, 1, 1), .x2), 26, 37, 36, 25⟩,
   ⟨((0, 1, 2, 1), .x0), 38, 40, 39, 36⟩,
   ⟨((1, 1, 1, 1), .x2), 28, 39, 41, 29⟩,
   ⟨((0, 1, 2, 1), .x1), 37, 45, 46, 38⟩,
   ⟨((0, 2, 1, 1), .x2), 35, 47, 45, 34⟩,
   ⟨((0, 2, 2, 1), .x0), 47, 43, 42, 46⟩,
   ⟨((1, 1, 2, 1), .x1), 40, 42, 44, 41⟩,
   ⟨((1, 2, 1, 1), .x2), 32, 44, 43, 31⟩]

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs_length :
    radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs.length = 22 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs_map_physicalLink :
    radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs.map
        (fun pair => pair.physicalLink) =
      radiusZeroEdgeTouchingDoubleCubeBivalentLinks := by
  decide

def TaggedDoubleCubeBivalentPair.TagsInRange
    (pair : TaggedDoubleCubeBivalentPair) : Prop :=
  pair.forwardRowTag < 48 ∧ pair.forwardColumnTag < 48 ∧
    pair.reverseRowTag < 48 ∧ pair.reverseColumnTag < 48

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPair_tagsInRange
    {pair : TaggedDoubleCubeBivalentPair}
    (hpair : pair ∈ radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs) :
    pair.TagsInRange := by
  simp only [radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs,
    List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    unfold TaggedDoubleCubeBivalentPair.TagsInRange <;> decide

def TaggedDoubleCubeBivalentPair.OccurrenceSound
    (pair : TaggedDoubleCubeBivalentPair) : Prop :=
  (∃ tagged,
      tagged ∈ radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences ∧
      tagged.occurrence.physicalLink = pair.physicalLink ∧
      tagged.occurrence.positive = true ∧
      tagged.rowTag = pair.forwardRowTag ∧
      tagged.columnTag = pair.forwardColumnTag) ∧
  (∃ tagged,
      tagged ∈ radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences ∧
      tagged.occurrence.physicalLink = pair.physicalLink ∧
      tagged.occurrence.positive = false ∧
      tagged.rowTag = pair.reverseRowTag ∧
      tagged.columnTag = pair.reverseColumnTag)

theorem radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPair_occurrenceSound
    {pair : TaggedDoubleCubeBivalentPair}
    (hpair : pair ∈ radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs) :
    pair.OccurrenceSound := by
  simp only [radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs,
    List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    unfold TaggedDoubleCubeBivalentPair.OccurrenceSound <;> decide

/-! ## 4. Descriptor-level global coverage and shared order -/

structure DoubleCubeCoefficientDescriptor where
  physicalLink : Z4Link
  positive : Bool
  rowTag : Nat
  columnTag : Nat
  deriving DecidableEq

def taggedDoubleCubeBoundaryOccurrenceDescriptor
    (tagged : TaggedDoubleCubeBoundaryOccurrence) :
    DoubleCubeCoefficientDescriptor :=
  { physicalLink := tagged.occurrence.physicalLink
    positive := tagged.occurrence.positive
    rowTag := tagged.rowTag
    columnTag := tagged.columnTag }

def taggedDoubleCubeBivalentPairDescriptors
    (pair : TaggedDoubleCubeBivalentPair) :
    List DoubleCubeCoefficientDescriptor :=
  [{ physicalLink := pair.physicalLink
     positive := true
     rowTag := pair.forwardRowTag
     columnTag := pair.forwardColumnTag },
   { physicalLink := pair.physicalLink
     positive := false
     rowTag := pair.reverseRowTag
     columnTag := pair.reverseColumnTag }]

/-- The shared descriptors remain in inherited face order `R1 F1 R2 F2`. -/
def radiusZeroEdgeTouchingDoubleCubeSharedDescriptors :
    List DoubleCubeCoefficientDescriptor :=
  [{ physicalLink := radiusZeroEdgeTouchingDoubleCubeSharedLink
     positive := false, rowTag := 18, columnTag := 22 },
   { physicalLink := radiusZeroEdgeTouchingDoubleCubeSharedLink
     positive := true, rowTag := 23, columnTag := 19 },
   { physicalLink := radiusZeroEdgeTouchingDoubleCubeSharedLink
     positive := false, rowTag := 27, columnTag := 24 },
   { physicalLink := radiusZeroEdgeTouchingDoubleCubeSharedLink
     positive := true, rowTag := 25, columnTag := 28 }]

def radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors :
    List DoubleCubeCoefficientDescriptor :=
  radiusZeroEdgeTouchingDoubleCubeTaggedBoundaryOccurrences.map
    taggedDoubleCubeBoundaryOccurrenceDescriptor

/-- All twenty-two bivalent pairs followed by the inherited four-valent row.
The following permutation theorem proves that these are exactly the forty-eight
face-major occurrences, with none dropped or duplicated. -/
def radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors :
    List DoubleCubeCoefficientDescriptor :=
  radiusZeroEdgeTouchingDoubleCubeSharedDescriptors ++
    radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs.flatMap
      taggedDoubleCubeBivalentPairDescriptors

/-- Face-major positions of the shared `R F R F` row followed by the
twenty-two displayed bivalent rows.  This fixed list is a structural witness,
not a Boolean assignment carrier. -/
def radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions :
    List Nat :=
  [14, 17, 23, 24,
   4, 3, 0, 11, 1, 19, 40, 2, 8, 7, 12, 6, 5, 43, 9, 15, 16, 10,
   13, 42, 41, 18, 20, 31, 21, 39, 44, 22, 28, 27, 32, 26, 25, 47,
   29, 35, 36, 30, 37, 34, 33, 46, 45, 38]

/-- Local axiom-clean duplicate-freeness proof for `List.range`. -/
private theorem rangeNodupLocal (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

/-- Duplicate-free lists with identical membership are constructively
permutations.  The membership witness supplies each split, so no bulk
permutation decider or choice principle is involved. -/
private theorem permOfNodupMemIff {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := permOfNodupMemIff
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

theorem radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors_length :
    radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors.length = 48 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_length :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors.length = 48 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors_nodup :
    radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors.Nodup := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_nodup :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors.Nodup := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_length :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions.length = 48 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_nodup :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions.Nodup := by
  decide

/-- Closed check that every displayed position lies below forty eight. -/
private theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_all_lt :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions.all
        (fun position => decide (position < 48)) = true := by
  decide

/-- Closed coverage certificate for each canonical position below forty
eight. -/
private theorem radiusZeroEdgeTouchingDoubleCubeFinPosition_mem_resolved :
    ∀ position : Fin 48,
      position.1 ∈
        radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_mem_iff
    (position : Nat) :
    position ∈ radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions ↔
      position < 48 := by
  constructor
  · intro hmember
    have hcheck := List.all_eq_true.mp
      radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_all_lt
      position hmember
    exact of_decide_eq_true hcheck
  · intro hlt
    exact
      radiusZeroEdgeTouchingDoubleCubeFinPosition_mem_resolved ⟨position, hlt⟩

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_perm_range :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions.Perm
      (List.range 48) := by
  apply permOfNodupMemIff
  · exact
      radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_nodup
  · exact rangeNodupLocal 48
  · intro position
    exact
      (radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_mem_iff
        position).trans List.mem_range.symm

def defaultDoubleCubeCoefficientDescriptor : DoubleCubeCoefficientDescriptor :=
  { physicalLink := radiusZeroEdgeTouchingDoubleCubeSharedLink
    positive := false
    rowTag := 0
    columnTag := 0 }

def radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt
    (position : Nat) : DoubleCubeCoefficientDescriptor :=
  radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors.getD position
    defaultDoubleCubeCoefficientDescriptor

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_eq_reindex :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors =
      radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions.map
        radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt_range :
    (List.range 48).map
        radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt =
      radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_perm_faceMajor :
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors.Perm
      radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors := by
  rw [radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_eq_reindex]
  have hperm :=
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_perm_range.map
      radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt
  rw [radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt_range] at hperm
  exact hperm

/-! ## 5. Opaque-assignment schedule and pointwise Haar contraction -/

def doubleCubeTagValue (assignment : List Bool) (tag : Nat) : Bool :=
  assignment.getD tag false

def TaggedDoubleCubeBivalentPair.contraction
    (pair : TaggedDoubleCubeBivalentPair) (assignment : List Bool) :
    OrientedFundamentalContraction :=
  { block := adjacentEvenActiveLinkIndex 0 pair.physicalLink
    forwardRow := doubleCubeTagValue assignment pair.forwardRowTag
    forwardColumn := doubleCubeTagValue assignment pair.forwardColumnTag
    reverseRow := doubleCubeTagValue assignment pair.reverseRowTag
    reverseColumn := doubleCubeTagValue assignment pair.reverseColumnTag }

def radiusZeroEdgeTouchingDoubleCubeBivalentSchedule
    (assignment : List Bool) : List OrientedFundamentalContraction :=
  radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs.map
    (fun pair => pair.contraction assignment)

theorem radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_length
    (assignment : List Bool) :
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment).length = 22 := by
  simp only [radiusZeroEdgeTouchingDoubleCubeBivalentSchedule,
    List.length_map]
  exact radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs_length

theorem radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_blocks
    (assignment : List Bool) :
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment).map
        (fun step => step.block) =
      radiusZeroEdgeTouchingDoubleCubeBivalentBlocks := by
  have hmap := congrArg
    (List.map (fun link : Z4Link =>
      adjacentEvenActiveLinkIndex 0 link))
    radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs_map_physicalLink
  simpa only [radiusZeroEdgeTouchingDoubleCubeBivalentSchedule,
    TaggedDoubleCubeBivalentPair.contraction,
    radiusZeroEdgeTouchingDoubleCubeBivalentBlocks,
    List.map_map] using hmap

theorem radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_inRange
    (assignment : List Bool) :
    ContractionBlocksInRange
      (adjacentEvenActiveLinks 0).length
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment) := by
  intro step hstep
  apply radiusZeroEdgeTouchingDoubleCubeBivalentBlock_lt
  rw [← radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_blocks assignment]
  exact List.mem_map.mpr ⟨step, hstep, rfl⟩

theorem radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_nodup
    (assignment : List Bool) :
    ContractionBlocksNodup
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment) := by
  unfold ContractionBlocksNodup
  rw [radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_blocks assignment]
  exact radiusZeroEdgeTouchingDoubleCubeBivalentBlocks_nodup

theorem radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_avoids_shared
    (assignment : List Bool) :
    ∀ step,
      step ∈ radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment →
      step.block ≠ radiusZeroEdgeTouchingDoubleCubeSharedBlock := by
  intro step hstep heq
  apply radiusZeroEdgeTouchingDoubleCubeSharedBlock_not_mem_bivalent
  rw [← radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_blocks assignment]
  exact List.mem_map.mpr ⟨step, hstep, heq⟩

/-- Literal shared-link word in inherited face order `R1 F1 R2 F2`. -/
def radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm
    (assignment : List Bool) : ComplexRatPoly :=
  reverseForwardReverseForwardFundamentalTerm
    radiusZeroEdgeTouchingDoubleCubeSharedBlock
    (doubleCubeTagValue assignment 18)
    (doubleCubeTagValue assignment 22)
    (doubleCubeTagValue assignment 23)
    (doubleCubeTagValue assignment 19)
    (doubleCubeTagValue assignment 27)
    (doubleCubeTagValue assignment 24)
    (doubleCubeTagValue assignment 25)
    (doubleCubeTagValue assignment 28)

/-- Canonical `F1 F2 R1 R2` Haar normal form of the inherited shared word.
The external reverse pairs are not transposed here;
`reverseFundamentalCoefficient` performs the matrix transpose internally. -/
def radiusZeroEdgeTouchingDoubleCubeSharedCanonicalTerm
    (assignment : List Bool) : ComplexRatPoly :=
  twoForwardTwoReverseFundamentalTerm
    radiusZeroEdgeTouchingDoubleCubeSharedBlock
    (doubleCubeTagValue assignment 23)
    (doubleCubeTagValue assignment 19)
    (doubleCubeTagValue assignment 25)
    (doubleCubeTagValue assignment 28)
    (doubleCubeTagValue assignment 18)
    (doubleCubeTagValue assignment 22)
    (doubleCubeTagValue assignment 27)
    (doubleCubeTagValue assignment 24)

def radiusZeroEdgeTouchingDoubleCubeSharedProjector
    (assignment : List Bool) : RationalComplex :=
  orientedFourFundamentalHaarProjector
    (doubleCubeTagValue assignment 23)
    (doubleCubeTagValue assignment 19)
    (doubleCubeTagValue assignment 25)
    (doubleCubeTagValue assignment 28)
    (doubleCubeTagValue assignment 18)
    (doubleCubeTagValue assignment 22)
    (doubleCubeTagValue assignment 27)
    (doubleCubeTagValue assignment 24)

/-- A four-valent factor on `source` is independent of every distinct target
block. -/
theorem complexQuaternionBlockIndependent_reverseForwardReverseForwardFundamentalTerm
    {source target : Nat} (hne : source ≠ target)
    (firstReverseRow firstReverseColumn
      firstForwardRow firstForwardColumn
      secondReverseRow secondReverseColumn
      secondForwardRow secondForwardColumn : Bool) :
    ComplexQuaternionBlockIndependent target
      (reverseForwardReverseForwardFundamentalTerm source
        firstReverseRow firstReverseColumn
        firstForwardRow firstForwardColumn
        secondReverseRow secondReverseColumn
        secondForwardRow secondForwardColumn) := by
  unfold reverseForwardReverseForwardFundamentalTerm
    complexRatPolyMulFourLeft
  exact complexQuaternionBlockIndependent_mul
    (complexQuaternionBlockIndependent_mul
      (complexQuaternionBlockIndependent_mul
        (complexQuaternionBlockIndependent_reverseFundamentalCoefficient
          hne firstReverseRow firstReverseColumn)
        (complexQuaternionBlockIndependent_forwardFundamentalCoefficient
          hne firstForwardRow firstForwardColumn))
      (complexQuaternionBlockIndependent_reverseFundamentalCoefficient
        hne secondReverseRow secondReverseColumn))
    (complexQuaternionBlockIndependent_forwardFundamentalCoefficient
      hne secondForwardRow secondForwardColumn)

theorem radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm_baseIndependent
    (assignment : List Bool) :
    ComplexBaseIndependentOfSchedule
      (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment) := by
  intro step hstep
  apply
    complexQuaternionBlockIndependent_reverseForwardReverseForwardFundamentalTerm
  exact Ne.symm
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_avoids_shared
      assignment step hstep)

/-- The canonical rational-complex one is a left unit up to the rational
setoid. -/
private theorem rationalComplexOne_mul_eqv (value : RationalComplex) :
    RationalComplexEqv
      (YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics.rationalComplexMul
        rationalComplexOne value)
      value := by
  unfold
    YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics.rationalComplexMul
    rationalComplexOne RationalComplexEqv
  constructor
  · refine Q'.eqv_trans _ (value.1 + 0) _ ?_
      (QPoly.q_add_zero_eqv value.1)
    exact QPoly.q_add_congr
      (Q'.one_mul_eqv value.1)
      (Q'.eqv_trans _ (-(0 : Q')) _
        (Q'.neg_eqv_congr _ _ (QPoly.q_zero_mul value.2)) (by decide))
  · refine Q'.eqv_trans _ (value.2 + 0) _ ?_
      (QPoly.q_add_zero_eqv value.2)
    exact QPoly.q_add_congr
      (Q'.one_mul_eqv value.2)
      (QPoly.q_zero_mul value.1)

/-- Standalone arbitrary-block Haar value of the literal inherited shared
word.  Canonical `F F R R` is used only as an internal Haar normal form. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment))
      (radiusZeroEdgeTouchingDoubleCubeSharedProjector assignment) := by
  let blockCount := (adjacentEvenActiveLinks 0).length
  let literal := radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment
  let canonical :=
    radiusZeroEdgeTouchingDoubleCubeSharedCanonicalTerm assignment
  let projector :=
    radiusZeroEdgeTouchingDoubleCubeSharedProjector assignment
  have horder : RationalComplexEqv
      (finiteProductHaarComplex blockCount literal)
      (finiteProductHaarComplex blockCount canonical) := by
    exact finiteProductHaarComplex_mulFourLeft_reverseForwardReverseForward
      blockCount
      (reverseFundamentalCoefficient
        radiusZeroEdgeTouchingDoubleCubeSharedBlock
        (doubleCubeTagValue assignment 18)
        (doubleCubeTagValue assignment 22))
      (forwardFundamentalCoefficient
        radiusZeroEdgeTouchingDoubleCubeSharedBlock
        (doubleCubeTagValue assignment 23)
        (doubleCubeTagValue assignment 19))
      (reverseFundamentalCoefficient
        radiusZeroEdgeTouchingDoubleCubeSharedBlock
        (doubleCubeTagValue assignment 27)
        (doubleCubeTagValue assignment 24))
      (forwardFundamentalCoefficient
        radiusZeroEdgeTouchingDoubleCubeSharedBlock
        (doubleCubeTagValue assignment 25)
        (doubleCubeTagValue assignment 28))
  have honeContext : RationalComplexEqv
      (finiteProductHaarComplex blockCount canonical)
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul complexRatPolyOne canonical)) :=
    rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul blockCount canonical)
  have hprojector :=
    genericBlock_twoForwardTwoReverse_projector_with_complex_spectator
      blockCount radiusZeroEdgeTouchingDoubleCubeSharedBlock
      radiusZeroEdgeTouchingDoubleCubeSharedBlock_lt
      complexRatPolyOne
      (complexRatPolyOne_blockIndependent
        radiusZeroEdgeTouchingDoubleCubeSharedBlock)
      (doubleCubeTagValue assignment 23)
      (doubleCubeTagValue assignment 19)
      (doubleCubeTagValue assignment 25)
      (doubleCubeTagValue assignment 28)
      (doubleCubeTagValue assignment 18)
      (doubleCubeTagValue assignment 22)
      (doubleCubeTagValue assignment 27)
      (doubleCubeTagValue assignment 24)
  have hbridge := generic_rationalComplexMul_eqv
    (finiteProductHaarComplex blockCount complexRatPolyOne) projector
  have honeTransport := rationalComplexMul_congr
    (finiteProductHaarComplex_one blockCount)
    (rationalComplexEqv_refl projector)
  exact rationalComplexEqv_trans horder
    (rationalComplexEqv_trans honeContext
      (rationalComplexEqv_trans hprojector
        (rationalComplexEqv_trans hbridge
          (rationalComplexEqv_trans honeTransport
            (rationalComplexOne_mul_eqv projector)))))

/-- Literal grouped summand: the inherited shared word is the base, and each
bivalent schedule head is the next right-local Schur factor. -/
def radiusZeroEdgeTouchingDoubleCubeGroupedSummand
    (assignment : List Bool) : ComplexRatPoly :=
  contractionProductOver
    (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment)

def radiusZeroEdgeTouchingDoubleCubeContractedValue
    (assignment : List Bool) : RationalComplex :=
  schurDeltaProductFrom
    (radiusZeroEdgeTouchingDoubleCubeSharedProjector assignment)
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment)

/-- **Twenty-two bivalent contractions around the signed shared-link
projector.**  This theorem is pointwise in an opaque forty-eight-tag Boolean
assignment.  It contracts no global sum and retains the complete signed
four-valent kernel. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeGroupedSummand
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeGroupedSummand assignment))
      (radiusZeroEdgeTouchingDoubleCubeContractedValue assignment) := by
  have hfold :=
    finiteProductHaarComplex_distinctFundamentalContractionProduct
      (adjacentEvenActiveLinks 0).length
      (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment)
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_inRange assignment)
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_nodup assignment)
      (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm_baseIndependent
        assignment)
  have hinitial := schurDeltaProductFrom_congr_initial
    (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm
      assignment)
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment)
  exact rationalComplexEqv_trans hfold hinitial

/-! ## 6. The actual two-sheet external projector wiring -/

/-- The two-sheet network does not close the four-valent kernel by its
four-character diagonal trace.  Its external bivalent deltas produce the
cross-wired sum below, whose exact value is four. -/
theorem orientedFourFundamentalHaarProjector_twoSheetExternalWiringSum :
    RationalComplexEqv
      (rationalComplexFourBoolSum (fun firstA secondA firstB secondB =>
        orientedFourFundamentalHaarProjector
          firstA firstB secondA secondB
          firstB firstA secondB secondA))
      ((4 : Q'), 0) := by
  constructor <;> decide

#print axioms radiusZeroEdgeTouchingDoubleCubeActiveLinkBlocks_nodup
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedBlock_not_mem_bivalent
#print axioms radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs_map_physicalLink
#print axioms radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPair_occurrenceSound
#print axioms radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_nodup
#print axioms radiusZeroEdgeTouchingDoubleCubeResolvedDescriptorFacePositions_perm_range
#print axioms radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_eq_reindex
#print axioms radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptorAt_range
#print axioms radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_perm_faceMajor
#print axioms radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_inRange
#print axioms radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_nodup
#print axioms radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_avoids_shared
#print axioms complexQuaternionBlockIndependent_reverseForwardReverseForwardFundamentalTerm
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeGroupedSummand
#print axioms orientedFourFundamentalHaarProjector_twoSheetExternalWiringSum

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction
