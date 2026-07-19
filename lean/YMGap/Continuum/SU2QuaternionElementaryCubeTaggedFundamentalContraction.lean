/-
# Tagged elementary-cube fundamental contraction schedule

The six outward-oriented plaquette traces have twenty-four independent
Boolean corner indices before Haar contraction.  This leaf keeps those
indices distinct and numbers them vertex-major: three face-corner copies at
each of the eight geometric cube vertices.

The six cyclic tag rows are paired with the already verified twenty-four
oriented boundary occurrences.  A literal twelve-row table then selects the
forward and reverse occurrence of every physical cube link.  Mapping
an arbitrary symbolic assignment through that table produces the exact
`OrientedFundamentalContraction` schedule required by the finite
distinct-block Schur theorem.

No Boolean assignment carrier is enumerated.  The assignment is an opaque
`List Bool`, read only through `List.getD`; the eventual depth-24 recursive
sum must remain opaque.  This file proves the Haar theorem for one fixed
assignment and does not form the global trace-network sum.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
import YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring

namespace YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct

/-! ## 1. Twenty-four vertex-major face-corner tags -/

/-- The four cyclic corner tags on each outward-oriented face, in the exact
order of `radiusZeroElementaryCubeOutwardFaces`.  Although the rows are
face-major, tag numbers are vertex-major: each consecutive triple belongs to
one geometric vertex. -/
def radiusZeroElementaryCubeFaceTagCycles : List (List Nat) :=
  [[0, 9, 6, 3],
   [1, 4, 15, 12],
   [2, 13, 21, 10],
   [14, 16, 18, 22],
   [11, 23, 19, 7],
   [5, 8, 20, 17]]

/-- Face-major reading of the twenty-four independent tag identifiers. -/
def radiusZeroElementaryCubeFaceCornerTags : List Nat :=
  radiusZeroElementaryCubeFaceTagCycles.flatMap (fun cycle => cycle)

theorem radiusZeroElementaryCubeFaceTagCycles_length :
    radiusZeroElementaryCubeFaceTagCycles.length = 6 := by
  decide

theorem radiusZeroElementaryCubeFaceTagCycle_lengths :
    radiusZeroElementaryCubeFaceTagCycles.map List.length =
      [4, 4, 4, 4, 4, 4] := by
  decide

theorem radiusZeroElementaryCubeFaceCornerTags_length :
    radiusZeroElementaryCubeFaceCornerTags.length = 24 := by
  decide

theorem radiusZeroElementaryCubeFaceCornerTags_nodup :
    radiusZeroElementaryCubeFaceCornerTags.Nodup := by
  decide

theorem radiusZeroElementaryCubeFaceCornerTag_lt
    {tag : Nat}
    (htag : tag ∈ radiusZeroElementaryCubeFaceCornerTags) : tag < 24 := by
  simp only [radiusZeroElementaryCubeFaceCornerTags,
    radiusZeroElementaryCubeFaceTagCycles, List.flatMap_cons,
    List.flatMap_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at htag
  omega

/-- Turn one cyclic four-tag row into its four directed matrix-index edges. -/
def cyclicFourTagEdges : List Nat → List (Nat × Nat)
  | [first, second, third, fourth] =>
      [(first, second), (second, third),
       (third, fourth), (fourth, first)]
  | _ => []

/-- The twenty-four source/target tag pairs in outward face-occurrence
order. -/
def radiusZeroElementaryCubeBoundaryTagEdges : List (Nat × Nat) :=
  radiusZeroElementaryCubeFaceTagCycles.flatMap cyclicFourTagEdges

theorem radiusZeroElementaryCubeBoundaryTagEdges_length :
    radiusZeroElementaryCubeBoundaryTagEdges.length = 24 := by
  decide

/-- One already verified oriented physical occurrence together with its
still-independent trace-row and trace-column tags. -/
structure TaggedCubeBoundaryOccurrence where
  occurrence : OrientedFundamentalLinkOccurrence
  sourceTag : Nat
  targetTag : Nat
  deriving DecidableEq

/-- Zip the exact outward physical occurrence list with the exact cyclic tag
edge list.  Equal lengths are proved below, so no occurrence is dropped. -/
def radiusZeroElementaryCubeTaggedBoundaryOccurrences :
    List TaggedCubeBoundaryOccurrence :=
  (radiusZeroElementaryCubeBoundaryOccurrences.zip
    radiusZeroElementaryCubeBoundaryTagEdges).map (fun entry =>
      ⟨entry.1, entry.2.1, entry.2.2⟩)

theorem radiusZeroElementaryCubeTaggedBoundaryOccurrences_length :
    radiusZeroElementaryCubeTaggedBoundaryOccurrences.length = 24 := by
  decide

/-- Forgetting tags recovers the complete checked outward occurrence list in
its original order. -/
theorem radiusZeroElementaryCubeTaggedBoundaryOccurrences_map_occurrence :
    radiusZeroElementaryCubeTaggedBoundaryOccurrences.map
        (fun tagged => tagged.occurrence) =
      radiusZeroElementaryCubeBoundaryOccurrences := by
  decide

/-! ## 2. Literal opposite-orientation link-pair table -/

/-- One physical cube link and the two matrix-index pairs carried by its
selected forward and reverse occurrences. -/
structure TaggedCubeLinkPair where
  physicalLink : Z4Link
  forwardRowTag : Nat
  forwardColumnTag : Nat
  reverseRowTag : Nat
  reverseColumnTag : Nat
  deriving DecidableEq

/-- Exact table in the duplicate-free `geometricTouchedLinks` order. -/
def radiusZeroElementaryCubeTaggedLinkPairs : List TaggedCubeLinkPair :=
  [⟨((0, 0, 0, 1), .x0), 1, 4, 3, 0⟩,
   ⟨((0, 0, 0, 1), .x1), 0, 9, 10, 2⟩,
   ⟨((0, 1, 0, 1), .x0), 9, 6, 7, 11⟩,
   ⟨((1, 0, 0, 1), .x1), 5, 8, 6, 3⟩,
   ⟨((0, 0, 0, 1), .x2), 2, 13, 12, 1⟩,
   ⟨((0, 0, 1, 1), .x0), 14, 16, 15, 12⟩,
   ⟨((1, 0, 0, 1), .x2), 4, 15, 17, 5⟩,
   ⟨((0, 0, 1, 1), .x1), 13, 21, 22, 14⟩,
   ⟨((0, 1, 0, 1), .x2), 11, 23, 21, 10⟩,
   ⟨((0, 1, 1, 1), .x0), 23, 19, 18, 22⟩,
   ⟨((1, 0, 1, 1), .x1), 16, 18, 20, 17⟩,
   ⟨((1, 1, 0, 1), .x2), 8, 20, 19, 7⟩]

/-- The table's physical links are definitionally the audited duplicate-free
elementary-cube support, including its order. -/
theorem radiusZeroElementaryCubeTaggedLinkPairs_map_physicalLink :
    radiusZeroElementaryCubeTaggedLinkPairs.map
        (fun pair => pair.physicalLink) =
      radiusZeroElementaryCubeTouchedLinks := by
  decide

theorem radiusZeroElementaryCubeTaggedLinkPairs_length :
    radiusZeroElementaryCubeTaggedLinkPairs.length = 12 := by
  decide

/-- Every table tag is a valid index below the twenty-four-tag bound. -/
def TaggedCubeLinkPair.TagsInRange (pair : TaggedCubeLinkPair) : Prop :=
  pair.forwardRowTag < 24 ∧ pair.forwardColumnTag < 24 ∧
    pair.reverseRowTag < 24 ∧ pair.reverseColumnTag < 24

theorem radiusZeroElementaryCubeTaggedLinkPair_tagsInRange
    {pair : TaggedCubeLinkPair}
    (hpair : pair ∈ radiusZeroElementaryCubeTaggedLinkPairs) :
    pair.TagsInRange := by
  simp only [radiusZeroElementaryCubeTaggedLinkPairs, List.mem_cons,
    List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold TaggedCubeLinkPair.TagsInRange <;> decide

/-- The literal row really selects a positive occurrence and a negative
occurrence of its physical link, with the displayed tag
endpoints. -/
def TaggedCubeLinkPair.OccurrenceSound
    (pair : TaggedCubeLinkPair) : Prop :=
  (∃ tagged,
      tagged ∈ radiusZeroElementaryCubeTaggedBoundaryOccurrences ∧
      tagged.occurrence.physicalLink = pair.physicalLink ∧
      tagged.occurrence.positive = true ∧
      tagged.sourceTag = pair.forwardRowTag ∧
      tagged.targetTag = pair.forwardColumnTag) ∧
  (∃ tagged,
      tagged ∈ radiusZeroElementaryCubeTaggedBoundaryOccurrences ∧
      tagged.occurrence.physicalLink = pair.physicalLink ∧
      tagged.occurrence.positive = false ∧
      tagged.sourceTag = pair.reverseRowTag ∧
      tagged.targetTag = pair.reverseColumnTag)

theorem radiusZeroElementaryCubeTaggedLinkPair_occurrenceSound
    {pair : TaggedCubeLinkPair}
    (hpair : pair ∈ radiusZeroElementaryCubeTaggedLinkPairs) :
    pair.OccurrenceSound := by
  simp only [radiusZeroElementaryCubeTaggedLinkPairs, List.mem_cons,
    List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold TaggedCubeLinkPair.OccurrenceSound <;> decide

/-! ## 3. Assignment-dependent contraction schedule -/

/-- Read one tag without requiring a materialized bounded assignment type.
The default is irrelevant on the eventual length-24 recursive-sum branches. -/
def cubeTagValue (assignment : List Bool) (tag : Nat) : Bool :=
  assignment.getD tag false

/-- Convert one physical/tag row to the canonical one-link contraction
record. -/
def TaggedCubeLinkPair.contraction
    (pair : TaggedCubeLinkPair) (assignment : List Bool) :
    OrientedFundamentalContraction :=
  { block := adjacentEvenActiveLinkIndex 0 pair.physicalLink
    forwardRow := cubeTagValue assignment pair.forwardRowTag
    forwardColumn := cubeTagValue assignment pair.forwardColumnTag
    reverseRow := cubeTagValue assignment pair.reverseRowTag
    reverseColumn := cubeTagValue assignment pair.reverseColumnTag }

/-- The twelve bivalent link contractions for one still-symbolic assignment. -/
def radiusZeroElementaryCubeContractionSchedule
    (assignment : List Bool) : List OrientedFundamentalContraction :=
  radiusZeroElementaryCubeTaggedLinkPairs.map
    (fun pair => pair.contraction assignment)

theorem radiusZeroElementaryCubeContractionSchedule_length
    (assignment : List Bool) :
    (radiusZeroElementaryCubeContractionSchedule assignment).length = 12 := by
  simp only [radiusZeroElementaryCubeContractionSchedule, List.length_map]
  exact radiusZeroElementaryCubeTaggedLinkPairs_length

/-- Forgetting all tag values recovers exactly the audited twelve production
active-link blocks. -/
theorem radiusZeroElementaryCubeContractionSchedule_blocks
    (assignment : List Bool) :
    (radiusZeroElementaryCubeContractionSchedule assignment).map
        (fun step => step.block) =
      radiusZeroElementaryCubeActiveLinkBlocks := by
  have hmap := congrArg
    (List.map (fun link : Z4Link =>
      adjacentEvenActiveLinkIndex 0 link))
    radiusZeroElementaryCubeTaggedLinkPairs_map_physicalLink
  simpa only [radiusZeroElementaryCubeContractionSchedule,
    TaggedCubeLinkPair.contraction,
    radiusZeroElementaryCubeActiveLinkBlocks, List.map_map] using hmap

theorem radiusZeroElementaryCubeContractionSchedule_inRange
    (assignment : List Bool) :
    ContractionBlocksInRange
      (adjacentEvenActiveLinks 0).length
      (radiusZeroElementaryCubeContractionSchedule assignment) := by
  intro step hstep
  apply radiusZeroElementaryCubeActiveLinkBlock_lt
  rw [← radiusZeroElementaryCubeContractionSchedule_blocks assignment]
  exact List.mem_map.mpr ⟨step, hstep, rfl⟩

theorem radiusZeroElementaryCubeContractionSchedule_nodup
    (assignment : List Bool) :
    ContractionBlocksNodup
      (radiusZeroElementaryCubeContractionSchedule assignment) := by
  unfold ContractionBlocksNodup
  rw [radiusZeroElementaryCubeContractionSchedule_blocks assignment]
  exact radiusZeroElementaryCubeActiveLinkBlocks_nodup

/-! ## 4. One-shot fixed-assignment Schur theorem -/

/-- Haar-facing polynomial for one Boolean assignment, defined directly in
the right-local paired order required by the distinct-block theorem. -/
def radiusZeroElementaryCubePairedSummand
    (assignment : List Bool) : ComplexRatPoly :=
  fundamentalContractionProduct
    (radiusZeroElementaryCubeContractionSchedule assignment)

/-- Matching exact crossed-delta value for one assignment. -/
def radiusZeroElementaryCubeSchurDeltaValue
    (assignment : List Bool) : RationalComplex :=
  schurDeltaProduct
    (radiusZeroElementaryCubeContractionSchedule assignment)

/-- **All twelve bivalent cube links contract in one verified fold.**  This
theorem is pointwise in an opaque Boolean assignment.  It neither enumerates
the `2^24` assignments nor reduces the resulting delta product. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubePairedSummand
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubePairedSummand assignment))
      (radiusZeroElementaryCubeSchurDeltaValue assignment) := by
  exact finiteProductHaarComplex_fundamentalContractionProduct
    (adjacentEvenActiveLinks 0).length
    (radiusZeroElementaryCubeContractionSchedule assignment)
    (radiusZeroElementaryCubeContractionSchedule_inRange assignment)
    (radiusZeroElementaryCubeContractionSchedule_nodup assignment)

#print axioms radiusZeroElementaryCubeFaceCornerTags_nodup
#print axioms radiusZeroElementaryCubeTaggedBoundaryOccurrences_map_occurrence
#print axioms radiusZeroElementaryCubeTaggedLinkPairs_map_physicalLink
#print axioms radiusZeroElementaryCubeTaggedLinkPair_occurrenceSound
#print axioms radiusZeroElementaryCubeContractionSchedule_blocks
#print axioms radiusZeroElementaryCubeContractionSchedule_inRange
#print axioms radiusZeroElementaryCubeContractionSchedule_nodup
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubePairedSummand

end YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
