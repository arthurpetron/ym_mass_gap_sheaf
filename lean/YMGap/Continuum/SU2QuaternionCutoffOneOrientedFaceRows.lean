/-
# Geometry-generic oriented cutoff-one face rows

This leaf is the structural entry point for the global cutoff-one signed Haar
network.  It does not form a polynomial, perform a Boolean sum, or integrate a
Haar block.  Instead it attaches four fresh corner tags to every selected
production plaquette, records an explicit standard/reversed trace orientation,
and assigns every resulting fundamental occurrence to one common list of
touched physical-link blocks.

The numerical support position and the production face identifier are kept as
separate fields.  Tags use the former; the decoded plaquette uses the latter.
Consequently distinct selected faces have disjoint four-tag packets even though
their identifiers need not be consecutive in the box enumeration.
-/

import YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
import YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive

namespace YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Production rows and globally fresh corner tags -/

/-- An orientation may depend on both the position of a selected face inside
the support and its production face identifier. -/
abbrev CutoffOneFaceOrientationChoice :=
  Nat → Nat → FundamentalFaceOrientation

/-- The canonical production convention uses every plaquette in its standard
increasing-coordinate orientation. -/
def standardCutoffOneFaceOrientationChoice :
    CutoffOneFaceOrientationChoice :=
  fun _ _ => .standard

/-- One selected production plaquette together with its support position and
literal trace orientation. -/
structure CutoffOneOrientedFaceRow where
  supportPosition : Nat
  physicalFaceId : Nat
  plaquette : Z4Plaq
  orientation : FundamentalFaceOrientation
  deriving DecidableEq

/-- The globally allocated tag for one of the four corners of a selected
face.  The intended corner range is `0 <= corner < 4`. -/
def cutoffOneFaceCornerTag (supportPosition corner : Nat) : Nat :=
  4 * supportPosition + corner

def CutoffOneOrientedFaceRow.firstTag
    (row : CutoffOneOrientedFaceRow) : Nat :=
  cutoffOneFaceCornerTag row.supportPosition 0

def CutoffOneOrientedFaceRow.secondTag
    (row : CutoffOneOrientedFaceRow) : Nat :=
  cutoffOneFaceCornerTag row.supportPosition 1

def CutoffOneOrientedFaceRow.thirdTag
    (row : CutoffOneOrientedFaceRow) : Nat :=
  cutoffOneFaceCornerTag row.supportPosition 2

def CutoffOneOrientedFaceRow.fourthTag
    (row : CutoffOneOrientedFaceRow) : Nat :=
  cutoffOneFaceCornerTag row.supportPosition 3

def CutoffOneOrientedFaceRow.tags
    (row : CutoffOneOrientedFaceRow) : List Nat :=
  [row.firstTag, row.secondTag, row.thirdTag, row.fourthTag]

theorem CutoffOneOrientedFaceRow.tags_length
    (row : CutoffOneOrientedFaceRow) :
    row.tags.length = 4 := by
  rfl

/-- The tag allocation is injective on the intended corner range, globally
across all support positions. -/
theorem cutoffOneFaceCornerTag_injective
    {leftPosition rightPosition leftCorner rightCorner : Nat}
    (hleftCorner : leftCorner < 4)
    (hrightCorner : rightCorner < 4)
    (htag : cutoffOneFaceCornerTag leftPosition leftCorner =
      cutoffOneFaceCornerTag rightPosition rightCorner) :
    leftPosition = rightPosition ∧ leftCorner = rightCorner := by
  unfold cutoffOneFaceCornerTag at htag
  have hleftDiv : (4 * leftPosition + leftCorner) / 4 = leftPosition := by
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hleftCorner,
      Nat.add_zero]
  have hrightDiv : (4 * rightPosition + rightCorner) / 4 =
      rightPosition := by
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hrightCorner,
      Nat.add_zero]
  have hposition := congrArg (fun value : Nat => value / 4) htag
  change (4 * leftPosition + leftCorner) / 4 =
    (4 * rightPosition + rightCorner) / 4 at hposition
  rw [hleftDiv, hrightDiv] at hposition
  have hleftMod : (4 * leftPosition + leftCorner) % 4 = leftCorner := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hleftCorner]
  have hrightMod : (4 * rightPosition + rightCorner) % 4 =
      rightCorner := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrightCorner]
  have hcorner := congrArg (fun value : Nat => value % 4) htag
  change (4 * leftPosition + leftCorner) % 4 =
    (4 * rightPosition + rightCorner) % 4 at hcorner
  rw [hleftMod, hrightMod] at hcorner
  exact ⟨hposition, hcorner⟩

theorem CutoffOneOrientedFaceRow.tags_nodup
    (row : CutoffOneOrientedFaceRow) :
    row.tags.Nodup := by
  have cornerTag_ne :
      ∀ {leftCorner rightCorner : Nat},
        leftCorner < 4 → rightCorner < 4 → leftCorner ≠ rightCorner →
          cutoffOneFaceCornerTag row.supportPosition leftCorner ≠
            cutoffOneFaceCornerTag row.supportPosition rightCorner := by
    intro leftCorner rightCorner hleft hright hne htag
    exact hne (cutoffOneFaceCornerTag_injective hleft hright htag).2
  have h01 : cutoffOneFaceCornerTag row.supportPosition 0 ≠
      cutoffOneFaceCornerTag row.supportPosition 1 :=
    cornerTag_ne (by decide) (by decide) (by decide)
  have h02 : cutoffOneFaceCornerTag row.supportPosition 0 ≠
      cutoffOneFaceCornerTag row.supportPosition 2 :=
    cornerTag_ne (by decide) (by decide) (by decide)
  have h03 : cutoffOneFaceCornerTag row.supportPosition 0 ≠
      cutoffOneFaceCornerTag row.supportPosition 3 :=
    cornerTag_ne (by decide) (by decide) (by decide)
  have h12 : cutoffOneFaceCornerTag row.supportPosition 1 ≠
      cutoffOneFaceCornerTag row.supportPosition 2 :=
    cornerTag_ne (by decide) (by decide) (by decide)
  have h13 : cutoffOneFaceCornerTag row.supportPosition 1 ≠
      cutoffOneFaceCornerTag row.supportPosition 3 :=
    cornerTag_ne (by decide) (by decide) (by decide)
  have h23 : cutoffOneFaceCornerTag row.supportPosition 2 ≠
      cutoffOneFaceCornerTag row.supportPosition 3 :=
    cornerTag_ne (by decide) (by decide) (by decide)
  unfold CutoffOneOrientedFaceRow.tags
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem
    · exact h01 hmem
    · exact h02 hmem
    · exact h03 hmem
  · refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hmem | hmem
      · exact h12 hmem
      · exact h13 hmem
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        exact h23 hmem
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- Distinct support positions have disjoint four-tag packets. -/
theorem CutoffOneOrientedFaceRow.tags_disjoint_of_supportPosition_ne
    {left right : CutoffOneOrientedFaceRow}
    (hne : left.supportPosition ≠ right.supportPosition)
    (tag : Nat) (hleft : tag ∈ left.tags) (hright : tag ∈ right.tags) :
    False := by
  simp only [CutoffOneOrientedFaceRow.tags, List.mem_cons,
    List.not_mem_nil, or_false] at hleft hright
  rcases hleft with rfl | rfl | rfl | rfl <;>
    rcases hright with htag | htag | htag | htag <;>
    simp only [CutoffOneOrientedFaceRow.firstTag,
      CutoffOneOrientedFaceRow.secondTag,
      CutoffOneOrientedFaceRow.thirdTag,
      CutoffOneOrientedFaceRow.fourthTag,
      cutoffOneFaceCornerTag] at htag
  all_goals
    exact hne
      (cutoffOneFaceCornerTag_injective (by decide) (by decide) htag).1

def indexedCutoffOneOrientedFaceRow
    (n : Nat) (orientationAt : CutoffOneFaceOrientationChoice)
    (indexedFace : Nat × Nat) : CutoffOneOrientedFaceRow :=
  { supportPosition := indexedFace.1
    physicalFaceId := indexedFace.2
    plaquette := boxPlaquetteAt n indexedFace.2
    orientation := orientationAt indexedFace.1 indexedFace.2 }

/-- Rows for an arbitrary numerical support.  `enumerate support` supplies the
fresh tag packet index; `boxPlaquetteAt` supplies the literal production
plaquette. -/
def cutoffOneOrientedFaceRows
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List CutoffOneOrientedFaceRow :=
  (YMGap.Continuum.Z4FiniteBoxTrivalentResolution.enumerate support).map
    (indexedCutoffOneOrientedFaceRow n orientationAt)

def cutoffOneStandardFaceRows (n : Nat) (support : List Nat) :
    List CutoffOneOrientedFaceRow :=
  cutoffOneOrientedFaceRows standardCutoffOneFaceOrientationChoice n support

theorem cutoffOneOrientedFaceRows_length
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneOrientedFaceRows orientationAt n support).length =
      support.length := by
  unfold cutoffOneOrientedFaceRows
  rw [List.length_map]
  exact YMGap.Continuum.Z4FiniteBoxTrivalentResolution.enumerate_length support

theorem cutoffOneOrientedFaceRows_map_physicalFaceId
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneOrientedFaceRows orientationAt n support).map
        CutoffOneOrientedFaceRow.physicalFaceId = support := by
  unfold cutoffOneOrientedFaceRows indexedCutoffOneOrientedFaceRow
  simp only [List.map_map, Function.comp_apply]
  change (YMGap.Continuum.Z4FiniteBoxTrivalentResolution.enumerate support).map
    Prod.snd = support
  exact YMGap.Continuum.Z4UnitCubeEnumerationParity.enumerate_map_snd support

theorem cutoffOneOrientedFaceRows_map_supportPosition
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneOrientedFaceRows orientationAt n support).map
        CutoffOneOrientedFaceRow.supportPosition =
      List.range support.length := by
  unfold cutoffOneOrientedFaceRows indexedCutoffOneOrientedFaceRow
  simp only [List.map_map, Function.comp_apply]
  change (YMGap.Continuum.Z4FiniteBoxTrivalentResolution.enumerate support).map
    Prod.fst = List.range support.length
  exact YMGap.Continuum.Z4ExplicitSupportFaceBound.enumerate_map_fst_eq_range
    support

theorem cutoffOneOrientedFaceRows_supportPositions_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ((cutoffOneOrientedFaceRows orientationAt n support).map
      CutoffOneOrientedFaceRow.supportPosition).Nodup := by
  rw [cutoffOneOrientedFaceRows_map_supportPosition]
  exact List.nodup_range

theorem cutoffOneOrientedFaceRows_map_plaquette
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneOrientedFaceRows orientationAt n support).map
        CutoffOneOrientedFaceRow.plaquette =
      geometricPolymer n support := by
  unfold cutoffOneOrientedFaceRows indexedCutoffOneOrientedFaceRow
    geometricPolymer
  simpa only [List.map_map, Function.comp_apply] using
    congrArg (List.map (boxPlaquetteAt n))
      (YMGap.Continuum.Z4UnitCubeEnumerationParity.enumerate_map_snd support)

theorem CutoffOneOrientedFaceRow.supportPosition_lt
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hrow : row ∈ cutoffOneOrientedFaceRows orientationAt n support) :
    row.supportPosition < support.length := by
  unfold cutoffOneOrientedFaceRows at hrow
  obtain ⟨indexedFace, hindexed, rfl⟩ := List.mem_map.mp hrow
  exact YMGap.Continuum.Z4LinkIdentifierFreshness.enumerate_index_lt hindexed

theorem CutoffOneOrientedFaceRow.physicalFaceId_mem
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hrow : row ∈ cutoffOneOrientedFaceRows orientationAt n support) :
    row.physicalFaceId ∈ support := by
  have hmapped : row.physicalFaceId ∈
      (cutoffOneOrientedFaceRows orientationAt n support).map
        CutoffOneOrientedFaceRow.physicalFaceId :=
    List.mem_map.mpr ⟨row, hrow, rfl⟩
  rw [cutoffOneOrientedFaceRows_map_physicalFaceId] at hmapped
  exact hmapped

/-- Generated rows retain the literal box-enumeration decoding and the
orientation selected from their support position and production face ID. -/
theorem CutoffOneOrientedFaceRow.productionData_exact
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hrow : row ∈ cutoffOneOrientedFaceRows orientationAt n support) :
    row.plaquette = boxPlaquetteAt n row.physicalFaceId ∧
      row.orientation =
        orientationAt row.supportPosition row.physicalFaceId := by
  unfold cutoffOneOrientedFaceRows at hrow
  obtain ⟨indexedFace, hindexed, rfl⟩ := List.mem_map.mp hrow
  exact ⟨rfl, rfl⟩

theorem CutoffOneOrientedFaceRow.standard_orientation
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hrow : row ∈ cutoffOneStandardFaceRows n support) :
    row.orientation = .standard := by
  exact (row.productionData_exact hrow).2

theorem CutoffOneOrientedFaceRow.physicalFaceId_physical
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hrow : row ∈ cutoffOneOrientedFaceRows orientationAt n support) :
    row.physicalFaceId ∈
      YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.physicalFaceEdges n := by
  exact YMGap.Continuum.CayleyPruferInjection.mem_of_mem_sublists
    (YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.physicalFaceEdges n)
    support hsupport row.physicalFaceId
    (row.physicalFaceId_mem hrow)

/-- For a genuine cutoff-one support, every row is attached to an actual
entry of the production box plaquette enumeration, not to the `getD`
fallback. -/
theorem CutoffOneOrientedFaceRow.mem_boxPlaquette_enumerate
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hrow : row ∈ cutoffOneOrientedFaceRows orientationAt n support) :
    (row.physicalFaceId, row.plaquette) ∈
      YMGap.Continuum.Z4FiniteBoxTrivalentResolution.enumerate
        (YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquettes n) := by
  have hphysical := row.physicalFaceId_physical hsupport hrow
  have henumerated :=
    YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount.boxPlaquetteAt_mem_enumerate
      (physicalFaceId_lt hphysical)
  rw [(row.productionData_exact hrow).1]
  exact henumerated

/-- The complete fresh-tag carrier for one support. -/
def cutoffOneCornerTags (support : List Nat) : List Nat :=
  List.range (4 * support.length)

theorem cutoffOneCornerTags_length (support : List Nat) :
    (cutoffOneCornerTags support).length = 4 * support.length := by
  unfold cutoffOneCornerTags
  exact List.length_range

theorem cutoffOneCornerTags_nodup (support : List Nat) :
    (cutoffOneCornerTags support).Nodup := by
  unfold cutoffOneCornerTags
  exact List.nodup_range

theorem mem_cutoffOneCornerTags {support : List Nat} {tag : Nat} :
    tag ∈ cutoffOneCornerTags support ↔ tag < 4 * support.length := by
  unfold cutoffOneCornerTags
  exact List.mem_range

theorem CutoffOneOrientedFaceRow.tag_mem_cornerTags
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {row : CutoffOneOrientedFaceRow}
    (hrow : row ∈ cutoffOneOrientedFaceRows orientationAt n support)
    {tag : Nat} (htag : tag ∈ row.tags) :
    tag ∈ cutoffOneCornerTags support := by
  apply mem_cutoffOneCornerTags.mpr
  have hposition := row.supportPosition_lt hrow
  simp only [CutoffOneOrientedFaceRow.tags, List.mem_cons,
    List.not_mem_nil, or_false] at htag
  rcases htag with rfl | rfl | rfl | rfl <;>
    simp only [CutoffOneOrientedFaceRow.firstTag,
      CutoffOneOrientedFaceRow.secondTag,
      CutoffOneOrientedFaceRow.thirdTag,
      CutoffOneOrientedFaceRow.fourthTag,
      cutoffOneFaceCornerTag] <;>
    omega

/-! ## 2. Literal oriented occurrence descriptors -/

def CutoffOneOrientedFaceRow.link0
    (row : CutoffOneOrientedFaceRow) : Z4Link :=
  (row.plaquette.1, (dirsOf row.plaquette.2).1)

def CutoffOneOrientedFaceRow.link1
    (row : CutoffOneOrientedFaceRow) : Z4Link :=
  (row.plaquette.1, (dirsOf row.plaquette.2).2)

def CutoffOneOrientedFaceRow.link2
    (row : CutoffOneOrientedFaceRow) : Z4Link :=
  (addE row.plaquette.1 (dirsOf row.plaquette.2).2,
    (dirsOf row.plaquette.2).1)

def CutoffOneOrientedFaceRow.link3
    (row : CutoffOneOrientedFaceRow) : Z4Link :=
  (addE row.plaquette.1 (dirsOf row.plaquette.2).1,
    (dirsOf row.plaquette.2).2)

def CutoffOneOrientedFaceRow.boundaryLinks
    (row : CutoffOneOrientedFaceRow) : List Z4Link :=
  [row.link0, row.link1, row.link2, row.link3]

theorem CutoffOneOrientedFaceRow.boundaryLinks_eq_edgesOf
    (row : CutoffOneOrientedFaceRow) :
    row.boundaryLinks = edgesOf row.plaquette := by
  rfl

/-- One face-major fundamental matrix-coefficient occurrence.  Its block is
always derived from a caller-supplied common physical-link list. -/
structure CutoffOneLinkOccurrenceDescriptor where
  physicalLink : Z4Link
  positive : Bool
  rowTag : Nat
  columnTag : Nat
  deriving DecidableEq

def CutoffOneLinkOccurrenceDescriptor.block
    (links : List Z4Link)
    (descriptor : CutoffOneLinkOccurrenceDescriptor) : Nat :=
  listIndexOf descriptor.physicalLink links

/-- Forget tags and recover the literal stored-orientation occurrence. -/
def CutoffOneLinkOccurrenceDescriptor.toBoundaryOccurrence
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    OrientedFundamentalLinkOccurrence :=
  { physicalLink := descriptor.physicalLink
    sourceVertex := if descriptor.positive then
        descriptor.physicalLink.1
      else addE descriptor.physicalLink.1 descriptor.physicalLink.2
    targetVertex := if descriptor.positive then
        addE descriptor.physicalLink.1 descriptor.physicalLink.2
      else descriptor.physicalLink.1
    positive := descriptor.positive }

/-- The four coefficient descriptors in the exact standard/reversed
plaquette-trace factor order. -/
def CutoffOneOrientedFaceRow.coefficientDescriptors
    (row : CutoffOneOrientedFaceRow) :
    List CutoffOneLinkOccurrenceDescriptor :=
  match row.orientation with
  | .standard =>
      [⟨row.link0, true, row.firstTag, row.secondTag⟩,
       ⟨row.link3, true, row.secondTag, row.thirdTag⟩,
       ⟨row.link2, false, row.thirdTag, row.fourthTag⟩,
       ⟨row.link1, false, row.fourthTag, row.firstTag⟩]
  | .reversed =>
      [⟨row.link1, true, row.firstTag, row.secondTag⟩,
       ⟨row.link2, true, row.secondTag, row.thirdTag⟩,
       ⟨row.link3, false, row.thirdTag, row.fourthTag⟩,
       ⟨row.link0, false, row.fourthTag, row.firstTag⟩]

theorem CutoffOneOrientedFaceRow.coefficientDescriptors_length
    (row : CutoffOneOrientedFaceRow) :
    row.coefficientDescriptors.length = 4 := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

/-- Descriptor projection is exactly the established literal
standard/reversed plaquette boundary word. -/
theorem CutoffOneOrientedFaceRow.coefficientDescriptors_toBoundaryOccurrences
    (row : CutoffOneOrientedFaceRow) :
    row.coefficientDescriptors.map
        CutoffOneLinkOccurrenceDescriptor.toBoundaryOccurrence =
      plaquetteBoundaryOccurrences row.orientation row.plaquette := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

private theorem standardBoundaryOrder_perm {A : Type}
    (first second third fourth : A) :
    [first, fourth, third, second].Perm
      [first, second, third, fourth] := by
  exact List.Perm.cons first
    (List.reverse_perm [fourth, third, second]).symm

private theorem reversedBoundaryOrder_perm {A : Type}
    (first second third fourth : A) :
    [second, third, fourth, first].Perm
      [first, second, third, fourth] := by
  exact List.perm_middle
    (l₁ := [second, third, fourth]) (a := first) (l₂ := [])

theorem CutoffOneOrientedFaceRow.descriptorPhysicalLinks_perm_edgesOf
    (row : CutoffOneOrientedFaceRow) :
    (row.coefficientDescriptors.map
        CutoffOneLinkOccurrenceDescriptor.physicalLink).Perm
      (edgesOf row.plaquette) := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation
  · exact standardBoundaryOrder_perm _ _ _ _
  · exact reversedBoundaryOrder_perm _ _ _ _

theorem CutoffOneOrientedFaceRow.descriptor_physicalLink_mem_edgesOf
    {row : CutoffOneOrientedFaceRow}
    {descriptor : CutoffOneLinkOccurrenceDescriptor}
    (hdescriptor : descriptor ∈ row.coefficientDescriptors) :
    descriptor.physicalLink ∈ edgesOf row.plaquette := by
  have hmapped : descriptor.physicalLink ∈
      row.coefficientDescriptors.map
        CutoffOneLinkOccurrenceDescriptor.physicalLink :=
    List.mem_map.mpr ⟨descriptor, hdescriptor, rfl⟩
  exact (row.descriptorPhysicalLinks_perm_edgesOf.mem_iff).mp hmapped

/-! ## 3. Face-major flattening and the common touched-link blocks -/

def cutoffOneFaceMajorOccurrenceDescriptors
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    List CutoffOneLinkOccurrenceDescriptor :=
  (cutoffOneOrientedFaceRows orientationAt n support).flatMap
    CutoffOneOrientedFaceRow.coefficientDescriptors

theorem cutoffOneFaceMajorOccurrenceDescriptors_length
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support).length =
      support.length * 4 := by
  unfold cutoffOneFaceMajorOccurrenceDescriptors
  rw [YMGap.Continuum.CayleyPruferInjection.length_flatMap_const
    CutoffOneOrientedFaceRow.coefficientDescriptors 4
    (cutoffOneOrientedFaceRows orientationAt n support)
    (fun row _ => row.coefficientDescriptors_length)]
  rw [cutoffOneOrientedFaceRows_length]

private theorem faceMajorDescriptors_toBoundaryOccurrences :
    ∀ rows : List CutoffOneOrientedFaceRow,
    ((rows.flatMap CutoffOneOrientedFaceRow.coefficientDescriptors).map
        CutoffOneLinkOccurrenceDescriptor.toBoundaryOccurrence) =
      rows.flatMap (fun row =>
        plaquetteBoundaryOccurrences row.orientation row.plaquette)
  | [] => rfl
  | row :: rest => by
      simp only [List.flatMap_cons, List.map_append]
      rw [CutoffOneOrientedFaceRow.coefficientDescriptors_toBoundaryOccurrences,
        faceMajorDescriptors_toBoundaryOccurrences rest]

/-- Flattening the row descriptors and then forgetting their tags gives
exactly the flattening of the literal oriented plaquette occurrences. -/
theorem cutoffOneFaceMajorOccurrenceDescriptors_toBoundaryOccurrences
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support).map
        CutoffOneLinkOccurrenceDescriptor.toBoundaryOccurrence =
      (cutoffOneOrientedFaceRows orientationAt n support).flatMap
        (fun row =>
          plaquetteBoundaryOccurrences row.orientation row.plaquette) := by
  unfold cutoffOneFaceMajorOccurrenceDescriptors
  exact faceMajorDescriptors_toBoundaryOccurrences _

private theorem faceMajorDescriptorPhysicalLinks_perm_rowsBoundary :
    ∀ rows : List CutoffOneOrientedFaceRow,
    ((rows.flatMap CutoffOneOrientedFaceRow.coefficientDescriptors).map
        CutoffOneLinkOccurrenceDescriptor.physicalLink).Perm
      (rows.flatMap (fun row => edgesOf row.plaquette))
  | [] => List.Perm.refl []
  | row :: rest => by
      simp only [List.flatMap_cons, List.map_append]
      exact
        ((row.descriptorPhysicalLinks_perm_edgesOf).append_right
          ((rest.flatMap
            CutoffOneOrientedFaceRow.coefficientDescriptors).map
              CutoffOneLinkOccurrenceDescriptor.physicalLink)).trans
        ((faceMajorDescriptorPhysicalLinks_perm_rowsBoundary rest).append_left
          (edgesOf row.plaquette))

private theorem rowsBoundary_eq_mappedPlaquetteBoundary :
    ∀ rows : List CutoffOneOrientedFaceRow,
    rows.flatMap (fun row => edgesOf row.plaquette) =
      (rows.map CutoffOneOrientedFaceRow.plaquette).flatMap edgesOf
  | [] => rfl
  | row :: rest => by
      simp only [List.flatMap_cons, List.map_cons]
      rw [rowsBoundary_eq_mappedPlaquetteBoundary rest]

/-- The flattened descriptor carrier covers the geometric support boundary
once face-by-face; orientation only permutes the four slots inside each row. -/
theorem cutoffOneFaceMajorDescriptorPhysicalLinks_perm_geometricBoundary
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ((cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support).map
        CutoffOneLinkOccurrenceDescriptor.physicalLink).Perm
      ((geometricPolymer n support).flatMap edgesOf) := by
  unfold cutoffOneFaceMajorOccurrenceDescriptors
  have hperm := faceMajorDescriptorPhysicalLinks_perm_rowsBoundary
    (cutoffOneOrientedFaceRows orientationAt n support)
  rw [rowsBoundary_eq_mappedPlaquetteBoundary,
    cutoffOneOrientedFaceRows_map_plaquette] at hperm
  exact hperm

/-- The single common physical-link block carrier for the entire support. -/
def cutoffOneTouchedLinks (n : Nat) (support : List Nat) : List Z4Link :=
  geometricTouchedLinks (geometricPolymer n support)

theorem cutoffOneTouchedLinks_nodup (n : Nat) (support : List Nat) :
    (cutoffOneTouchedLinks n support).Nodup := by
  unfold cutoffOneTouchedLinks
  exact geometricTouchedLinks_nodup _

/-- Every face-major descriptor refers to a link in the one support-wide
touched-link carrier. -/
theorem cutoffOneFaceMajorOccurrenceDescriptor_physicalLink_mem_touched
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    {descriptor : CutoffOneLinkOccurrenceDescriptor}
    (hdescriptor : descriptor ∈
      cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support) :
    descriptor.physicalLink ∈ cutoffOneTouchedLinks n support := by
  unfold cutoffOneFaceMajorOccurrenceDescriptors at hdescriptor
  obtain ⟨row, hrow, hlocal⟩ := List.mem_flatMap.mp hdescriptor
  have hplaquette : row.plaquette ∈ geometricPolymer n support := by
    have hmapped : row.plaquette ∈
        (cutoffOneOrientedFaceRows orientationAt n support).map
          CutoffOneOrientedFaceRow.plaquette :=
      List.mem_map.mpr ⟨row, hrow, rfl⟩
    rw [cutoffOneOrientedFaceRows_map_plaquette] at hmapped
    exact hmapped
  unfold cutoffOneTouchedLinks
  apply mem_geometricTouchedLinks.mpr
  exact ⟨row.plaquette, hplaquette,
    row.descriptor_physicalLink_mem_edgesOf hlocal⟩

/-- Every face-major descriptor receives an in-range block in the same
support-wide touched-link list. -/
theorem cutoffOneFaceMajorOccurrenceDescriptor_block_lt
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    {descriptor : CutoffOneLinkOccurrenceDescriptor}
    (hdescriptor : descriptor ∈
      cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support) :
    descriptor.block (cutoffOneTouchedLinks n support) <
      (cutoffOneTouchedLinks n support).length := by
  unfold CutoffOneLinkOccurrenceDescriptor.block
  exact listIndexOf_lt_of_mem descriptor.physicalLink
    (cutoffOneTouchedLinks n support)
    (cutoffOneFaceMajorOccurrenceDescriptor_physicalLink_mem_touched
      hdescriptor)

/-- Reading the common block list at a descriptor's assigned block recovers
its literal physical link. -/
theorem cutoffOneFaceMajorOccurrenceDescriptor_getD_block
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    {descriptor : CutoffOneLinkOccurrenceDescriptor}
    (hdescriptor : descriptor ∈
      cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support)
    (fallback : Z4Link) :
    (cutoffOneTouchedLinks n support).getD
        (descriptor.block (cutoffOneTouchedLinks n support)) fallback =
      descriptor.physicalLink := by
  unfold CutoffOneLinkOccurrenceDescriptor.block
  exact getD_listIndexOf_of_mem fallback descriptor.physicalLink
    (cutoffOneTouchedLinks n support)
    (cutoffOneFaceMajorOccurrenceDescriptor_physicalLink_mem_touched
      hdescriptor)

/-! ## 4. Per-link occurrence buckets and the geometric valence bound -/

def cutoffOneLinkOccurrenceBucket
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (link : Z4Link) :
    List CutoffOneLinkOccurrenceDescriptor :=
  (cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support).filter
    (fun descriptor => decide (descriptor.physicalLink = link))

theorem mem_cutoffOneLinkOccurrenceBucket
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {link : Z4Link}
    {descriptor : CutoffOneLinkOccurrenceDescriptor} :
    descriptor ∈
        cutoffOneLinkOccurrenceBucket orientationAt n support link ↔
      descriptor ∈
          cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support ∧
        descriptor.physicalLink = link := by
  unfold cutoffOneLinkOccurrenceBucket
  simp only [List.mem_filter, decide_eq_true_eq]

theorem cutoffOneLinkOccurrenceBucket_descriptor_block_lt
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat} {link : Z4Link}
    {descriptor : CutoffOneLinkOccurrenceDescriptor}
    (hdescriptor : descriptor ∈
      cutoffOneLinkOccurrenceBucket orientationAt n support link) :
    descriptor.block (cutoffOneTouchedLinks n support) <
      (cutoffOneTouchedLinks n support).length := by
  exact cutoffOneFaceMajorOccurrenceDescriptor_block_lt
    (mem_cutoffOneLinkOccurrenceBucket.mp hdescriptor).1

private theorem descriptorFilter_length_eq_occurrenceCount
    (link : Z4Link) : ∀ descriptors :
      List CutoffOneLinkOccurrenceDescriptor,
    (descriptors.filter
      (fun descriptor => decide (descriptor.physicalLink = link))).length =
      occurrenceCount link
        (descriptors.map CutoffOneLinkOccurrenceDescriptor.physicalLink)
  | [] => rfl
  | descriptor :: rest => by
      by_cases hlink : descriptor.physicalLink = link
      · simp [hlink, occurrenceCount,
          descriptorFilter_length_eq_occurrenceCount link rest, Nat.add_comm]
      · simp [hlink, occurrenceCount,
          descriptorFilter_length_eq_occurrenceCount link rest]

private theorem occurrenceCount_perm_local (link : Z4Link) :
    ∀ {left right : List Z4Link}, left.Perm right →
      occurrenceCount link left = occurrenceCount link right
  | _, _, List.Perm.nil => rfl
  | _, _, List.Perm.cons _ hperm => by
      simp only [occurrenceCount]
      rw [occurrenceCount_perm_local link hperm]
  | _, _, List.Perm.swap first second rest => by
      simp only [occurrenceCount]
      omega
  | _, _, List.Perm.trans hleft hright =>
      (occurrenceCount_perm_local link hleft).trans
        (occurrenceCount_perm_local link hright)

theorem cutoffOneLinkOccurrenceBucket_length_eq_geometricIncidence
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (link : Z4Link) :
    (cutoffOneLinkOccurrenceBucket orientationAt n support link).length =
      (geometricIncidentPlaquettes
        (geometricPolymer n support) link).length := by
  unfold cutoffOneLinkOccurrenceBucket
  rw [descriptorFilter_length_eq_occurrenceCount]
  rw [occurrenceCount_perm_local link
    (cutoffOneFaceMajorDescriptorPhysicalLinks_perm_geometricBoundary
      orientationAt n support)]
  rw [occurrenceCount_flatMap_edgesOf]
  exact (geometricIncidentPlaquettes_length_eq_faceIncidenceCount
    (geometricPolymer n support) link).symm

/-- Every physical-link occurrence bucket of a valid cutoff-one support has
valence at most six. -/
theorem cutoffOneLinkOccurrenceBucket_length_le_six
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (link : Z4Link) :
    (cutoffOneLinkOccurrenceBucket orientationAt n support link).length ≤ 6 := by
  rw [cutoffOneLinkOccurrenceBucket_length_eq_geometricIncidence]
  exact geometricIncidentPlaquettes_length_le_six hsupport link

/-! ## Axiom audit -/

#print axioms cutoffOneFaceCornerTag_injective
#print axioms CutoffOneOrientedFaceRow.tags_nodup
#print axioms CutoffOneOrientedFaceRow.tags_disjoint_of_supportPosition_ne
#print axioms cutoffOneOrientedFaceRows_map_plaquette
#print axioms CutoffOneOrientedFaceRow.productionData_exact
#print axioms CutoffOneOrientedFaceRow.mem_boxPlaquette_enumerate
#print axioms CutoffOneOrientedFaceRow.coefficientDescriptors_toBoundaryOccurrences
#print axioms cutoffOneFaceMajorDescriptorPhysicalLinks_perm_geometricBoundary
#print axioms cutoffOneFaceMajorOccurrenceDescriptor_block_lt
#print axioms cutoffOneFaceMajorOccurrenceDescriptor_getD_block
#print axioms cutoffOneLinkOccurrenceBucket_length_eq_geometricIncidence
#print axioms cutoffOneLinkOccurrenceBucket_length_le_six

end YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
