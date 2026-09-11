/-
# Literal outward trace network for the edge-touching double cube

The production observable is the product of twelve separately summed
fundamental plaquette traces.  The audited face order is not obtained by
simply concatenating the two cube boundaries: the first cube occupies slots
`0,1,2,3,4,10`, while the translated cube occupies slots
`5,6,7,8,9,11`.  Consequently the literal outward mask in production order
is

    R S R S R R S R S R S S.

This leaf records those twelve oriented rows and connects their genuine
trace-expansion product to the existing descriptor-derived face-major
coefficient network.  Four Boolean binders are moved through Haar one face
at a time; the resulting face-major tag word is then constructively
permuted to the canonical names `0,...,47`.  At each fixed assignment the
twelve left-associated trace terms are reconciled with the forty-eight
individual coefficient factors only after finite-product Haar.

No depth-forty-eight Boolean tree is unfolded, simplified, reduced,
evaluated, or printed.  No raw polynomial equality between the grouped
plaquette product and the syntax-sensitive flattened factor word is used.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBooleanDeltaResolution
import YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeLiteralTraceNetwork

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeSharedLinkHaarNormalization
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeFaceWordBridge
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBooleanDeltaResolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence

/-! ## 1. Twelve literal outward rows in production order -/

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow0 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 0, 1), .p01), .reversed, 0, 9, 6, 3⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow1 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 0, 1), .p02), .standard, 1, 4, 15, 12⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow2 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 0, 1), .p12), .reversed, 2, 13, 21, 10⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow3 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 1, 1), .p01), .standard, 14, 16, 18, 22⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow4 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 1, 0, 1), .p02), .reversed, 11, 23, 19, 7⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow5 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 1, 1, 1), .p01), .reversed, 24, 33, 30, 27⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow6 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 1, 1, 1), .p02), .standard, 25, 28, 39, 36⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow7 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 1, 1, 1), .p12), .reversed, 26, 37, 45, 34⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow8 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 1, 2, 1), .p01), .standard, 38, 40, 42, 46⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow9 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 2, 1, 1), .p02), .reversed, 35, 47, 43, 31⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow10 :
    TaggedOrientedPlaquetteRow :=
  ⟨((1, 0, 0, 1), .p12), .standard, 5, 8, 20, 17⟩

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow11 :
    TaggedOrientedPlaquetteRow :=
  ⟨((1, 1, 1, 1), .p12), .standard, 29, 32, 44, 41⟩

/-- The twelve rows in the exact decoded production-face order. -/
def radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows :
    List TaggedOrientedPlaquetteRow :=
  [radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow0,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow1,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow2,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow3,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow4,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow5,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow6,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow7,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow8,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow9,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow10,
   radiusZeroEdgeTouchingDoubleCubeOutwardFaceRow11]

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_length :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.length = 12 := by
  decide

/-- Face identifiers, plaquettes, and orientations agree slot-for-slot with
the independently audited production boundary. -/
theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_geometry :
    (radiusZeroEdgeTouchingDoubleCubeFaceIds.zip
      radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows).map (fun entry =>
        ((entry.1, entry.2.plaquette), entry.2.orientation)) =
      radiusZeroEdgeTouchingDoubleCubeOutwardFaces := by
  rfl

/-- The literal production-order orientation mask. -/
theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_orientationMask :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.map
        (fun row => row.orientation) =
      radiusZeroEdgeTouchingDoubleCubeOutwardOrientationMask := by
  decide

/-- The four tags of every row are exactly the previously certified cyclic
face-tag rows. -/
theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_tags :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.map
        TaggedOrientedPlaquetteRow.tags =
      radiusZeroEdgeTouchingDoubleCubeFaceTagCycles := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_flatMap_tags :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.flatMap
        TaggedOrientedPlaquetteRow.tags =
      radiusZeroEdgeTouchingDoubleCubeFaceCornerTags := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_flatMap_tags_nodup :
    (radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.flatMap
      TaggedOrientedPlaquetteRow.tags).Nodup := by
  rw [radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_flatMap_tags]
  exact radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_nodup

/-! ## 2. Constructive reindexing of the forty-eight binder names -/

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

private theorem radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_all_lt :
    radiusZeroEdgeTouchingDoubleCubeFaceCornerTags.all
        (fun tag => decide (tag < 48)) = true := by
  decide

private theorem radiusZeroEdgeTouchingDoubleCubeFinTag_mem_faceCornerTags :
    ∀ tag : Fin 48,
      tag.1 ∈ radiusZeroEdgeTouchingDoubleCubeFaceCornerTags := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_mem_iff
    (tag : Nat) :
    tag ∈ radiusZeroEdgeTouchingDoubleCubeFaceCornerTags ↔ tag < 48 := by
  constructor
  · intro hmem
    have hcheck := List.all_eq_true.mp
      radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_all_lt tag hmem
    exact of_decide_eq_true hcheck
  · intro hlt
    exact radiusZeroEdgeTouchingDoubleCubeFinTag_mem_faceCornerTags
      ⟨tag, hlt⟩

/-- The production face-major tag word contains each canonical name exactly
once.  The proof uses a structural permutation witness, not a bulk
permutation decider. -/
theorem radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_perm_range :
    radiusZeroEdgeTouchingDoubleCubeFaceCornerTags.Perm
      (List.range 48) := by
  apply permOfNodupMemIff
  · exact radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_nodup
  · exact rangeNodupLocal 48
  · intro tag
    exact (radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_mem_iff tag).trans
      List.mem_range.symm

theorem rationalComplexNamedBoolSum_radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_eq_range
    (family : (Nat → Bool) → RationalComplex) :
    RationalComplexEqv
      (rationalComplexNamedBoolSum
        radiusZeroEdgeTouchingDoubleCubeFaceCornerTags family)
      (rationalComplexNamedBoolSum (List.range 48) family) :=
  rationalComplexNamedBoolSum_perm
    radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_perm_range family

/-! ## 3. Row descriptors are the production face-major word -/

/-- Forget the elementary-cube descriptor type while retaining its complete
physical-link, polarity, and tag data. -/
def cubeCoefficientDescriptorToDoubleCube
    (descriptor : CubeCoefficientDescriptor) :
    DoubleCubeCoefficientDescriptor :=
  { physicalLink := descriptor.physicalLink
    positive := descriptor.positive
    rowTag := descriptor.rowTag
    columnTag := descriptor.columnTag }

theorem cubeCoefficientDescriptorToDoubleCube_coefficient
    (descriptor : CubeCoefficientDescriptor)
    (assignment : List Bool) :
    (cubeCoefficientDescriptorToDoubleCube descriptor).coefficient
        assignment =
      descriptor.coefficient assignment := by
  rfl

def TaggedOrientedPlaquetteRow.doubleCubeCoefficientDescriptors
    (row : TaggedOrientedPlaquetteRow) :
    List DoubleCubeCoefficientDescriptor :=
  row.coefficientDescriptors.map cubeCoefficientDescriptorToDoubleCube

/-- This is the sole finite geometry identification needed by the trace
bridge: the twelve orientation-specific four-factor rows flatten to the
already audited forty-eight production occurrences, in the same order. -/
theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceDescriptorRows_flatten :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.flatMap
        TaggedOrientedPlaquetteRow.doubleCubeCoefficientDescriptors =
      radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors := by
  decide

theorem TaggedOrientedPlaquetteRow.factors_eq_doubleCubeDescriptors_map
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    complexRatPolyFourFactorRowFactors
        (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
        (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
        (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
        (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)
        row =
      (TaggedOrientedPlaquetteRow.doubleCubeCoefficientDescriptors row).map
        (fun descriptor => descriptor.coefficient assignment) := by
  rw [TaggedOrientedPlaquetteRow.factors_eq_descriptors_map]
  unfold TaggedOrientedPlaquetteRow.doubleCubeCoefficientDescriptors
  rw [List.map_map]
  apply congrArg (fun coefficient =>
    row.coefficientDescriptors.map coefficient)
  funext descriptor
  exact (cubeCoefficientDescriptorToDoubleCube_coefficient
    descriptor assignment).symm

private theorem flatMap_doubleCubeFourFactorRows_eq_map_flatMap_descriptors
    (assignment : List Bool) :
    ∀ rows : List TaggedOrientedPlaquetteRow,
      rows.flatMap
          (complexRatPolyFourFactorRowFactors
            (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
            (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
            (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
            (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)) =
        (rows.flatMap
            TaggedOrientedPlaquetteRow.doubleCubeCoefficientDescriptors).map
          (fun descriptor => descriptor.coefficient assignment)
  | [] => rfl
  | row :: rows => by
      simp only [List.flatMap_cons, List.map_append]
      rw [TaggedOrientedPlaquetteRow.factors_eq_doubleCubeDescriptors_map,
        flatMap_doubleCubeFourFactorRows_eq_map_flatMap_descriptors
          assignment rows]

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceCoefficientRows_eq_faceMajorWord
    (assignment : List Bool) :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.flatMap
        (complexRatPolyFourFactorRowFactors
          (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
          (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
          (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
          (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)) =
      radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
        assignment := by
  rw [flatMap_doubleCubeFourFactorRows_eq_map_flatMap_descriptors assignment,
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceDescriptorRows_flatten]
  rfl

/-! ## 4. Literal expansions and fixed-index products -/

/-- The twelve genuinely separate standard/reversed trace expansions. -/
def radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceExpansions :
    List ComplexRatPoly :=
  radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.map
    TaggedOrientedPlaquetteRow.traceExpansion

/-- The honest production observable before any Boolean Fubini step. -/
def radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct :
    ComplexRatPoly :=
  complexRatPolyProduct
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceExpansions

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTerms
    (assignment : List Bool) : List ComplexRatPoly :=
  radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.map
    (TaggedOrientedPlaquetteRow.traceTerm assignment)

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct
    (assignment : List Bool) : ComplexRatPoly :=
  complexRatPolyProduct
    (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTerms assignment)

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTermsAt
    (environment : Nat → Bool) : List ComplexRatPoly :=
  radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.map
    (TaggedOrientedPlaquetteRow.traceTermAt environment)

def radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
    (environment : Nat → Bool) : ComplexRatPoly :=
  complexRatPolyProduct
    (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTermsAt environment)

private theorem traceTermsAt_doubleCubeTagValue_eq_traceTerms :
    ∀ (rows : List TaggedOrientedPlaquetteRow)
      (assignment : List Bool),
      rows.map (TaggedOrientedPlaquetteRow.traceTermAt
          (fun tag => doubleCubeTagValue assignment tag)) =
        rows.map (TaggedOrientedPlaquetteRow.traceTerm assignment)
  | [], _ => rfl
  | row :: rows, assignment => by
      simp only [List.map_cons, List.cons.injEq]
      exact
        ⟨by
          simpa only [doubleCubeTagValue, cubeTagValue] using
            (TaggedOrientedPlaquetteRow.traceTermAt_cubeTagValue
              assignment row),
         traceTermsAt_doubleCubeTagValue_eq_traceTerms rows assignment⟩

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt_doubleCubeTagValue
    (assignment : List Bool) :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
        (fun tag => doubleCubeTagValue assignment tag) =
      radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct assignment := by
  unfold radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTermsAt
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTerms
  rw [traceTermsAt_doubleCubeTagValue_eq_traceTerms]

/-- Twelve left-associated plaquette summands and the flattened production
coefficient word have the same Haar value at every opaque assignment. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct_eq_faceMajor
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct assignment))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
            assignment))) := by
  have h :=
    finiteProductHaarComplex_fourFactorRowProducts_eq_flatMap
      (adjacentEvenActiveLinks 0).length
      (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
      (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
      (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
      (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)
      radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows
  rw [radiusZeroEdgeTouchingDoubleCubeOutwardFaceCoefficientRows_eq_faceMajorWord
    assignment] at h
  exact h

theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt_eq_faceMajor
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
          (fun tag => doubleCubeTagValue assignment tag)))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
            assignment))) := by
  rw [radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt_doubleCubeTagValue]
  exact
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct_eq_faceMajor
      assignment

/-! ## 5. Twelve-face Fubini and the opaque forty-eight-bit network -/

theorem radiusZeroEdgeTouchingDoubleCubeTraceTermsFromWord_eq_traceTermsAt_tagWord
    (assignment : List Bool) :
    taggedOrientedPlaquetteTraceTermsFromWord
        radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows assignment =
      radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTermsAt
        (boolTagWordEnvironment
          radiusZeroEdgeTouchingDoubleCubeFaceCornerTags assignment) := by
  unfold radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceTermsAt
  rw [← radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_flatMap_tags]
  exact taggedOrientedPlaquetteTraceTermsFromWord_eq_traceTermsAt_tagWord
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows assignment
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_flatMap_tags_nodup

theorem radiusZeroEdgeTouchingDoubleCubeTraceProductFromWord_eq_traceProductAt_tagWord
    (assignment : List Bool) :
    complexRatPolyProduct
        (taggedOrientedPlaquetteTraceTermsFromWord
          radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows assignment) =
      radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
        (boolTagWordEnvironment
          radiusZeroEdgeTouchingDoubleCubeFaceCornerTags assignment) := by
  unfold radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
  rw [radiusZeroEdgeTouchingDoubleCubeTraceTermsFromWord_eq_traceTermsAt_tagWord]

/-- The genuine twelve-expansion product becomes a named Boolean sum in the
literal production face order. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_namedBoolSum :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct)
      (rationalComplexNamedBoolSum
        radiusZeroEdgeTouchingDoubleCubeFaceCornerTags (fun environment =>
          finiteProductHaarComplex
            (adjacentEvenActiveLinks 0).length
            (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
              environment))) := by
  unfold radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct
    radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceExpansions
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.map
            TaggedOrientedPlaquetteRow.traceExpansion)))) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_traceExpansionProduct
      (adjacentEvenActiveLinks 0).length complexRatPolyOne
      radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr
      (4 * radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.length)
      (fun assignment =>
        finiteProductHaarComplex_foldl_one_eq_product
          (adjacentEvenActiveLinks 0).length
          (taggedOrientedPlaquetteTraceTermsFromWord
            radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows assignment))) ?_
  have hdepth :
      4 * radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows.length =
        radiusZeroEdgeTouchingDoubleCubeFaceCornerTags.length := by
    rw [radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_length,
      radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_length]
  rw [hdepth]
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr
      radiusZeroEdgeTouchingDoubleCubeFaceCornerTags.length
      (fun assignment => by
        rw [radiusZeroEdgeTouchingDoubleCubeTraceProductFromWord_eq_traceProductAt_tagWord]
        exact rationalComplexEqv_refl _)) ?_
  exact rationalComplexEqv_symm
    (rationalComplexNamedBoolSum_tagWord
      radiusZeroEdgeTouchingDoubleCubeFaceCornerTags (fun environment =>
        finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
            environment)))

/-- Haar of the literal product of twelve separately summed outward traces
is the symbolic depth-forty-eight sum of the face-major fixed terms. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorBoolSum :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct)
      (rationalComplexBoolSum 48 (fun assignment =>
        finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (complexRatPolyProduct
            (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
              assignment)))) := by
  refine rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_namedBoolSum ?_
  refine rationalComplexEqv_trans
    (rationalComplexNamedBoolSum_radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_eq_range
      (fun environment =>
        finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
            environment))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexNamedBoolSum_range 48 (fun environment =>
      finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt
          environment))) ?_
  exact rationalComplexBoolSum_congr 48 (fun assignment => by
    simpa only [doubleCubeTagValue] using
      (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProductAt_eq_faceMajor
        assignment))

/-- Polynomial-network form of the full literal trace bridge. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorNetwork :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct)
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork) := by
  refine rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorBoolSum ?_
  unfold radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_boolSum
      (adjacentEvenActiveLinks 0).length 48 (fun assignment =>
        complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
            assignment)))

/-- The literal twelve-plaquette observable reduces to the opaque sum of the
signed shared-link projector with all twenty-two crossed Schur contractions. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_contractedSum :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct)
      (rationalComplexBoolSum 48
        radiusZeroEdgeTouchingDoubleCubeContractedValue) := by
  refine rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorBoolSum ?_
  exact rationalComplexBoolSum_congr 48 (fun assignment =>
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_contractedValue
      assignment)

/-- **Exact literal double-cube integral.**  The product of the twelve
independently expanded, orientation-faithful plaquette traces has Haar value
`1/256`.  The proof composes the literal trace bridge with the already banked
structural component compression; it never unfolds the depth-forty-eight or
depth-sixteen Boolean recursions. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_exact :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct)
      (Q'.mkPos 1 256 (by decide), 0) :=
  rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorNetwork
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork_exact

#print axioms radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_geometry
#print axioms radiusZeroEdgeTouchingDoubleCubeOutwardFaceRows_tags
#print axioms radiusZeroEdgeTouchingDoubleCubeFaceCornerTags_perm_range
#print axioms radiusZeroEdgeTouchingDoubleCubeOutwardFaceDescriptorRows_flatten
#print axioms radiusZeroEdgeTouchingDoubleCubeOutwardFaceCoefficientRows_eq_faceMajorWord
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardFaceTraceProduct_eq_faceMajor
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_namedBoolSum
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorBoolSum
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_faceMajorNetwork
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_eq_contractedSum
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_exact

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeLiteralTraceNetwork
