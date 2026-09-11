/-
# Genuine outward elementary-cube trace-expansion product

The exact outward cube network already sums the Haar value of six fixed-index
trace terms over one vertex-major Boolean assignment.  The production
observable begins one level earlier: it is the product of six separately
summed plaquette trace expansions.  This leaf defines that honest product and
the environment-indexed fixed terms needed to connect the two forms.

The outward orientation mask remains literal: reversed, standard, reversed,
standard, reversed, standard.  A row-list induction moves exactly four local
binders at a time through finite-product Haar, a duplicate-free tag-word
decoder identifies the resulting face-major leaves, and constructive named
reindexing closes the genuine product at the exact value `1/16`.

No depth-twenty-four Boolean sum is unfolded, simplified, reduced, evaluated,
or printed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
import YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord
import YMGap.Continuum.SU2QuaternionElementaryCubeNamedBoolReindex
import YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceNetwork

namespace YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge
open YMGap.Continuum.SU2QuaternionElementaryCubeNamedBoolReindex
open YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceNetwork
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

/-! ## 1. One oriented row before and after its four Boolean binders -/

/-- The fixed four-index term selected from one oriented row. -/
def TaggedOrientedPlaquetteRow.traceTermBits
    (row : TaggedOrientedPlaquetteRow)
    (first second third fourth : Bool) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      standardPlaquetteTraceTerm
        row.block0 row.block1 row.block2 row.block3
        first second third fourth
  | .reversed =>
      reversedPlaquetteTraceTerm
        row.block0 row.block1 row.block2 row.block3
        first second third fourth

/-- Read one oriented row's four fixed indices from a total named
environment. -/
def TaggedOrientedPlaquetteRow.traceTermAt
    (environment : Nat → Bool)
    (row : TaggedOrientedPlaquetteRow) : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceTermBits row
    (environment row.firstTag)
    (environment row.secondTag)
    (environment row.thirdTag)
    (environment row.fourthTag)

/-- The genuine separately summed trace expansion of one oriented row. -/
def TaggedOrientedPlaquetteRow.traceExpansion
    (row : TaggedOrientedPlaquetteRow) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      standardPlaquetteTraceExpansion
        row.block0 row.block1 row.block2 row.block3
  | .reversed =>
      reversedPlaquetteTraceExpansion
        row.block0 row.block1 row.block2 row.block3

/-- Each row expansion is exactly four nested Boolean binders over its fixed
term family. -/
theorem TaggedOrientedPlaquetteRow.traceExpansion_eq_fourBoolSum
    (row : TaggedOrientedPlaquetteRow) :
    TaggedOrientedPlaquetteRow.traceExpansion row =
      complexRatPolyFourBoolSum
        (TaggedOrientedPlaquetteRow.traceTermBits row) := by
  obtain ⟨plaquette, orientation, firstTag, secondTag, thirdTag, fourthTag⟩ := row
  cases orientation <;> rfl

/-- Reading the total environment through the established cube accessor
recovers the existing list-assignment row term exactly. -/
theorem TaggedOrientedPlaquetteRow.traceTermAt_cubeTagValue
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    TaggedOrientedPlaquetteRow.traceTermAt
        (fun tag => cubeTagValue assignment tag) row =
      row.traceTerm assignment := by
  obtain ⟨plaquette, orientation, firstTag, secondTag, thirdTag, fourthTag⟩ := row
  cases orientation <;> rfl

/-! ## 2. Row-wise positional selection and Haar Fubini -/

/-- Consume four positional bits per oriented row, retaining `false` as the
total default on short words.  The recursion drops exactly the already-used
four-bit chunk and never materializes a Boolean assignment carrier. -/
def taggedOrientedPlaquetteTraceTermsFromWord :
    List TaggedOrientedPlaquetteRow → List Bool → List ComplexRatPoly
  | [], _ => []
  | row :: rows, assignment =>
      TaggedOrientedPlaquetteRow.traceTermBits row
          (assignment.getD 0 false)
          (assignment.getD 1 false)
          (assignment.getD 2 false)
          (assignment.getD 3 false) ::
        taggedOrientedPlaquetteTraceTermsFromWord rows
          (assignment.drop 4)

/-- **Row-list four-binder Fubini.**  The Haar value of an ordered product
of separately summed row expansions is the positional Boolean sum of the
same ordered fixed terms accumulated from the left.  The proof is structural
in the row list: each step exposes only one safe four-binder face, while the
remaining Boolean suffix stays opaque. -/
theorem finiteProductHaarComplex_mul_traceExpansionProduct :
    ∀ (blockCount : Nat) (spectator : ComplexRatPoly)
      (rows : List TaggedOrientedPlaquetteRow),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct (rows.map
              TaggedOrientedPlaquetteRow.traceExpansion))))
        (rationalComplexBoolSum (4 * rows.length) (fun assignment =>
          finiteProductHaarComplex blockCount
            ((taggedOrientedPlaquetteTraceTermsFromWord rows assignment).foldl
              complexRatPolyMul spectator)))
  | blockCount, spectator, [] => by
      simpa only [List.map_nil, complexRatPolyProduct, List.length_nil,
        Nat.mul_zero, rationalComplexBoolSum,
        taggedOrientedPlaquetteTraceTermsFromWord, List.foldl_nil] using
        (finiteProductHaarComplex_mul_one blockCount spectator)
  | blockCount, spectator, row :: rows => by
      simp only [List.map_cons, complexRatPolyProduct]
      rw [TaggedOrientedPlaquetteRow.traceExpansion_eq_fourBoolSum]
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_fourBoolSum_inner
          blockCount spectator
          (complexRatPolyProduct
            (rows.map TaggedOrientedPlaquetteRow.traceExpansion))
          (TaggedOrientedPlaquetteRow.traceTermBits row)) ?_
      refine rationalComplexEqv_trans
        (rationalComplexFourBoolSum_congr (fun first second third fourth =>
          rationalComplexEqv_trans
            (finiteProductHaarComplex_mul_assoc_context blockCount
              spectator
              (TaggedOrientedPlaquetteRow.traceTermBits row
                first second third fourth)
              (complexRatPolyProduct
                (rows.map TaggedOrientedPlaquetteRow.traceExpansion)))
            (finiteProductHaarComplex_mul_traceExpansionProduct
              blockCount
              (complexRatPolyMul spectator
                (TaggedOrientedPlaquetteRow.traceTermBits row
                  first second third fourth)) rows))) ?_
      rw [List.length_cons, Nat.mul_succ,
        rationalComplexBoolSum_add_four]
      exact rationalComplexFourBoolSum_congr
        (fun first second third fourth =>
          rationalComplexBoolSum_congr (4 * rows.length)
            (fun suffix => by
              simp only [taggedOrientedPlaquetteTraceTermsFromWord,
                List.getD_cons_zero, List.getD_cons_succ,
                List.drop_succ_cons, List.foldl_cons]
              exact rationalComplexEqv_refl _))

/-! ## 3. Positional chunks equal the named tag-word decoder -/

/-- Changing a total Boolean environment away from every tag used by the
row list leaves all selected trace terms unchanged. -/
private theorem traceTermsAt_congr_on_flatMap
    (rows : List TaggedOrientedPlaquetteRow)
    (left right : Nat → Bool)
    (hagrees : ∀ tag,
      tag ∈ rows.flatMap TaggedOrientedPlaquetteRow.tags →
        left tag = right tag) :
    rows.map (TaggedOrientedPlaquetteRow.traceTermAt left) =
      rows.map (TaggedOrientedPlaquetteRow.traceTermAt right) := by
  apply List.map_congr_left
  intro row hrow
  have hlift : ∀ tag, tag ∈ row.tags →
      tag ∈ rows.flatMap TaggedOrientedPlaquetteRow.tags := by
    intro tag htag
    exact List.mem_flatMap.mpr ⟨row, hrow, htag⟩
  have h0 : row.firstTag ∈ row.tags := by
    unfold TaggedOrientedPlaquetteRow.tags
    exact List.mem_cons_self
  have h1 : row.secondTag ∈ row.tags := by
    unfold TaggedOrientedPlaquetteRow.tags
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have h2 : row.thirdTag ∈ row.tags := by
    unfold TaggedOrientedPlaquetteRow.tags
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 : row.fourthTag ∈ row.tags := by
    unfold TaggedOrientedPlaquetteRow.tags
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  unfold TaggedOrientedPlaquetteRow.traceTermAt
  rw [hagrees row.firstTag (hlift _ h0),
      hagrees row.secondTag (hlift _ h1),
      hagrees row.thirdTag (hlift _ h2),
      hagrees row.fourthTag (hlift _ h3)]

/-- Under duplicate-free flattened row tags, consuming four positional bits
per row gives exactly the row map read from the total tag-word environment.
The statement is valid even for short bit words, which is essential because
Boolean-sum congruence quantifies over arbitrary lists. -/
theorem taggedOrientedPlaquetteTraceTermsFromWord_eq_traceTermsAt_tagWord
    (rows : List TaggedOrientedPlaquetteRow)
    (assignment : List Bool)
    (hnodup : (rows.flatMap TaggedOrientedPlaquetteRow.tags).Nodup) :
    taggedOrientedPlaquetteTraceTermsFromWord rows assignment =
      rows.map (TaggedOrientedPlaquetteRow.traceTermAt
        (boolTagWordEnvironment
          (rows.flatMap TaggedOrientedPlaquetteRow.tags) assignment)) := by
  induction rows generalizing assignment with
  | nil => rfl
  | cons row rows ih =>
      have hfull :
          (row.tags ++ rows.flatMap
            TaggedOrientedPlaquetteRow.tags).Nodup := by
        simpa only [List.flatMap_cons] using hnodup
      have hp := List.nodup_append.mp hfull
      have hword :
          (row.firstTag :: row.secondTag :: row.thirdTag ::
            row.fourthTag :: rows.flatMap
              TaggedOrientedPlaquetteRow.tags).Nodup := by
        simpa only [TaggedOrientedPlaquetteRow.tags,
          List.cons_append, List.nil_append] using hfull
      have h0 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                TaggedOrientedPlaquetteRow.tags)
              assignment row.firstTag =
            assignment.getD 0 false := by
        simpa only [TaggedOrientedPlaquetteRow.tags,
          List.cons_append, List.nil_append, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            []
            (row.secondTag :: row.thirdTag :: row.fourthTag ::
              rows.flatMap TaggedOrientedPlaquetteRow.tags)
            assignment row.firstTag hword)
      have h1 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                TaggedOrientedPlaquetteRow.tags)
              assignment row.secondTag =
            assignment.getD 1 false := by
        simpa only [TaggedOrientedPlaquetteRow.tags,
          List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            [row.firstTag]
            (row.thirdTag :: row.fourthTag ::
              rows.flatMap TaggedOrientedPlaquetteRow.tags)
            assignment row.secondTag hword)
      have h2 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                TaggedOrientedPlaquetteRow.tags)
              assignment row.thirdTag =
            assignment.getD 2 false := by
        simpa only [TaggedOrientedPlaquetteRow.tags,
          List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            [row.firstTag, row.secondTag]
            (row.fourthTag ::
              rows.flatMap TaggedOrientedPlaquetteRow.tags)
            assignment row.thirdTag hword)
      have h3 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                TaggedOrientedPlaquetteRow.tags)
              assignment row.fourthTag =
            assignment.getD 3 false := by
        simpa only [TaggedOrientedPlaquetteRow.tags,
          List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            [row.firstTag, row.secondTag, row.thirdTag]
            (rows.flatMap TaggedOrientedPlaquetteRow.tags)
            assignment row.fourthTag hword)
      have hhead :
          TaggedOrientedPlaquetteRow.traceTermBits row
              (assignment.getD 0 false) (assignment.getD 1 false)
              (assignment.getD 2 false) (assignment.getD 3 false) =
            TaggedOrientedPlaquetteRow.traceTermAt
              (boolTagWordEnvironment
                (row.tags ++ rows.flatMap
                  TaggedOrientedPlaquetteRow.tags) assignment) row := by
        unfold TaggedOrientedPlaquetteRow.traceTermAt
        rw [h0, h1, h2, h3]
      have htailMaps :
          rows.map (TaggedOrientedPlaquetteRow.traceTermAt
              (boolTagWordEnvironment
                (row.tags ++ rows.flatMap
                  TaggedOrientedPlaquetteRow.tags) assignment)) =
            rows.map (TaggedOrientedPlaquetteRow.traceTermAt
              (boolTagWordEnvironment
                (rows.flatMap TaggedOrientedPlaquetteRow.tags)
                (assignment.drop 4))) := by
        apply traceTermsAt_congr_on_flatMap
        intro tag htag
        have hfresh : tag ∉ row.tags := by
          intro hrow
          exact hp.2.2 tag hrow tag htag rfl
        simpa only [TaggedOrientedPlaquetteRow.tags,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_of_not_mem row.tags
            (rows.flatMap TaggedOrientedPlaquetteRow.tags)
            assignment tag hfresh)
      simp only [taggedOrientedPlaquetteTraceTermsFromWord,
        List.map_cons, List.flatMap_cons]
      rw [hhead, (ih (assignment.drop 4) hp.2.1).trans htailMaps.symm]

/-! ## 4. Six literal outward expansions -/

def radiusZeroElementaryCubeOutwardFaceTraceExpansion0 : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceExpansion
    radiusZeroElementaryCubeOutwardFaceRow0

def radiusZeroElementaryCubeOutwardFaceTraceExpansion1 : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceExpansion
    radiusZeroElementaryCubeOutwardFaceRow1

def radiusZeroElementaryCubeOutwardFaceTraceExpansion2 : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceExpansion
    radiusZeroElementaryCubeOutwardFaceRow2

def radiusZeroElementaryCubeOutwardFaceTraceExpansion3 : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceExpansion
    radiusZeroElementaryCubeOutwardFaceRow3

def radiusZeroElementaryCubeOutwardFaceTraceExpansion4 : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceExpansion
    radiusZeroElementaryCubeOutwardFaceRow4

def radiusZeroElementaryCubeOutwardFaceTraceExpansion5 : ComplexRatPoly :=
  TaggedOrientedPlaquetteRow.traceExpansion
    radiusZeroElementaryCubeOutwardFaceRow5

/-- The six separately summed traces in audited face order. -/
def radiusZeroElementaryCubeOutwardFaceTraceExpansions :
    List ComplexRatPoly :=
  [radiusZeroElementaryCubeOutwardFaceTraceExpansion0,
   radiusZeroElementaryCubeOutwardFaceTraceExpansion1,
   radiusZeroElementaryCubeOutwardFaceTraceExpansion2,
   radiusZeroElementaryCubeOutwardFaceTraceExpansion3,
   radiusZeroElementaryCubeOutwardFaceTraceExpansion4,
   radiusZeroElementaryCubeOutwardFaceTraceExpansion5]

/-- Audit that the named six-element list is exactly the row-map
construction used by the generic Fubini theorem. -/
theorem radiusZeroElementaryCubeOutwardFaceTraceExpansions_eq_map :
    radiusZeroElementaryCubeOutwardFaceTraceExpansions =
      radiusZeroElementaryCubeOutwardFaceRows.map
        TaggedOrientedPlaquetteRow.traceExpansion := by
  rfl

/-- The orientation choices in the genuine expansion list are literally
`reversed, standard, reversed, standard, reversed, standard`. -/
theorem radiusZeroElementaryCubeOutwardFaceTraceExpansions_orientation_mask :
    radiusZeroElementaryCubeOutwardFaceTraceExpansions =
      [reversedPlaquetteTraceExpansion
        radiusZeroElementaryCubeOutwardFaceRow0.block0
        radiusZeroElementaryCubeOutwardFaceRow0.block1
        radiusZeroElementaryCubeOutwardFaceRow0.block2
        radiusZeroElementaryCubeOutwardFaceRow0.block3,
       standardPlaquetteTraceExpansion
        radiusZeroElementaryCubeOutwardFaceRow1.block0
        radiusZeroElementaryCubeOutwardFaceRow1.block1
        radiusZeroElementaryCubeOutwardFaceRow1.block2
        radiusZeroElementaryCubeOutwardFaceRow1.block3,
       reversedPlaquetteTraceExpansion
        radiusZeroElementaryCubeOutwardFaceRow2.block0
        radiusZeroElementaryCubeOutwardFaceRow2.block1
        radiusZeroElementaryCubeOutwardFaceRow2.block2
        radiusZeroElementaryCubeOutwardFaceRow2.block3,
       standardPlaquetteTraceExpansion
        radiusZeroElementaryCubeOutwardFaceRow3.block0
        radiusZeroElementaryCubeOutwardFaceRow3.block1
        radiusZeroElementaryCubeOutwardFaceRow3.block2
        radiusZeroElementaryCubeOutwardFaceRow3.block3,
       reversedPlaquetteTraceExpansion
        radiusZeroElementaryCubeOutwardFaceRow4.block0
        radiusZeroElementaryCubeOutwardFaceRow4.block1
        radiusZeroElementaryCubeOutwardFaceRow4.block2
        radiusZeroElementaryCubeOutwardFaceRow4.block3,
       standardPlaquetteTraceExpansion
        radiusZeroElementaryCubeOutwardFaceRow5.block0
        radiusZeroElementaryCubeOutwardFaceRow5.block1
        radiusZeroElementaryCubeOutwardFaceRow5.block2
        radiusZeroElementaryCubeOutwardFaceRow5.block3] := by
  rfl

/-- **Genuine outward trace-expansion product.**  The outer multiplication is
the established tail-first product; each of its six factors still contains
its own four-index symbolic sum. -/
def radiusZeroElementaryCubeOutwardTraceExpansionProduct : ComplexRatPoly :=
  complexRatPolyProduct
    radiusZeroElementaryCubeOutwardFaceTraceExpansions

/-! ## 5. Environment-indexed fixed six-face product -/

def radiusZeroElementaryCubeOutwardFaceTraceTermsAt
    (environment : Nat → Bool) : List ComplexRatPoly :=
  radiusZeroElementaryCubeOutwardFaceRows.map
    (TaggedOrientedPlaquetteRow.traceTermAt environment)

def radiusZeroElementaryCubeOutwardFaceTraceProductAt
    (environment : Nat → Bool) : ComplexRatPoly :=
  complexRatPolyProduct
    (radiusZeroElementaryCubeOutwardFaceTraceTermsAt environment)

private theorem traceTermsAt_cubeTagValue_eq_traceTerms :
    ∀ (rows : List TaggedOrientedPlaquetteRow)
      (assignment : List Bool),
      rows.map (TaggedOrientedPlaquetteRow.traceTermAt
          (fun tag => cubeTagValue assignment tag)) =
        rows.map (TaggedOrientedPlaquetteRow.traceTerm assignment)
  | [], _ => rfl
  | row :: rows, assignment => by
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨TaggedOrientedPlaquetteRow.traceTermAt_cubeTagValue
          assignment row,
        traceTermsAt_cubeTagValue_eq_traceTerms rows assignment⟩

theorem radiusZeroElementaryCubeOutwardFaceTraceTermsAt_cubeTagValue
    (assignment : List Bool) :
    radiusZeroElementaryCubeOutwardFaceTraceTermsAt
        (fun tag => cubeTagValue assignment tag) =
      radiusZeroElementaryCubeOutwardFaceTraceTerms assignment := by
  exact traceTermsAt_cubeTagValue_eq_traceTerms
    radiusZeroElementaryCubeOutwardFaceRows assignment

/-- The named-environment fixed product specializes exactly to the existing
vertex-major fixed-assignment product. -/
theorem radiusZeroElementaryCubeOutwardFaceTraceProductAt_cubeTagValue
    (assignment : List Bool) :
    radiusZeroElementaryCubeOutwardFaceTraceProductAt
        (fun tag => cubeTagValue assignment tag) =
      radiusZeroElementaryCubeOutwardFaceTraceProduct assignment := by
  unfold radiusZeroElementaryCubeOutwardFaceTraceProductAt
    radiusZeroElementaryCubeOutwardFaceTraceProduct
  rw [radiusZeroElementaryCubeOutwardFaceTraceTermsAt_cubeTagValue]

/-! ## 6. The genuine product, the named cube network, and the exact value -/

/-- The concrete six-row positional decoder is exactly the named
face-major environment decoder. -/
theorem radiusZeroElementaryCubeTraceTermsFromWord_eq_traceTermsAt_tagWord
    (assignment : List Bool) :
    taggedOrientedPlaquetteTraceTermsFromWord
        radiusZeroElementaryCubeOutwardFaceRows assignment =
      radiusZeroElementaryCubeOutwardFaceTraceTermsAt
        (boolTagWordEnvironment
          radiusZeroElementaryCubeFaceCornerTags assignment) := by
  unfold radiusZeroElementaryCubeOutwardFaceTraceTermsAt
  rw [← radiusZeroElementaryCubeOutwardFaceRows_flatMap_tags]
  exact taggedOrientedPlaquetteTraceTermsFromWord_eq_traceTermsAt_tagWord
    radiusZeroElementaryCubeOutwardFaceRows assignment (by
      rw [radiusZeroElementaryCubeOutwardFaceRows_flatMap_tags]
      exact radiusZeroElementaryCubeFaceCornerTags_nodup)

/-- Consequently, the ordered fixed-term products agree before Haar. -/
theorem radiusZeroElementaryCubeTraceProductFromWord_eq_traceProductAt_tagWord
    (assignment : List Bool) :
    complexRatPolyProduct
        (taggedOrientedPlaquetteTraceTermsFromWord
          radiusZeroElementaryCubeOutwardFaceRows assignment) =
      radiusZeroElementaryCubeOutwardFaceTraceProductAt
        (boolTagWordEnvironment
          radiusZeroElementaryCubeFaceCornerTags assignment) := by
  unfold radiusZeroElementaryCubeOutwardFaceTraceProductAt
  rw [radiusZeroElementaryCubeTraceTermsFromWord_eq_traceTermsAt_tagWord]

/-- **Full genuine-product wiring.**  Finite-product Haar of the product of
the six separately summed outward trace expansions equals the named
face-major Boolean sum of the six fixed-term products.  This theorem is the
load-bearing Fubini bridge: factor order and the literal R/S/R/S/R/S
orientation mask are preserved throughout. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_namedBoolSum :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceExpansionProduct)
      (rationalComplexNamedBoolSum
        radiusZeroElementaryCubeFaceCornerTags (fun environment =>
          finiteProductHaarComplex
            (adjacentEvenActiveLinks 0).length
            (radiusZeroElementaryCubeOutwardFaceTraceProductAt
              environment))) := by
  unfold radiusZeroElementaryCubeOutwardTraceExpansionProduct
  rw [radiusZeroElementaryCubeOutwardFaceTraceExpansions_eq_map]
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroElementaryCubeOutwardFaceRows.map
            TaggedOrientedPlaquetteRow.traceExpansion)))) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_traceExpansionProduct
      (adjacentEvenActiveLinks 0).length complexRatPolyOne
      radiusZeroElementaryCubeOutwardFaceRows) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr
      (4 * radiusZeroElementaryCubeOutwardFaceRows.length)
      (fun assignment =>
        finiteProductHaarComplex_foldl_one_eq_product
          (adjacentEvenActiveLinks 0).length
          (taggedOrientedPlaquetteTraceTermsFromWord
            radiusZeroElementaryCubeOutwardFaceRows assignment))) ?_
  have hdepth :
      4 * radiusZeroElementaryCubeOutwardFaceRows.length =
        radiusZeroElementaryCubeFaceCornerTags.length := by
    rw [radiusZeroElementaryCubeOutwardFaceRows_length,
      radiusZeroElementaryCubeFaceCornerTags_length]
  rw [hdepth]
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr
      radiusZeroElementaryCubeFaceCornerTags.length
      (fun assignment => by
        rw [radiusZeroElementaryCubeTraceProductFromWord_eq_traceProductAt_tagWord]
        exact rationalComplexEqv_refl _)) ?_
  exact rationalComplexEqv_symm
    (rationalComplexNamedBoolSum_tagWord
      radiusZeroElementaryCubeFaceCornerTags (fun environment =>
        finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (radiusZeroElementaryCubeOutwardFaceTraceProductAt environment)))

/-- The genuine six-expansion product and the earlier preassembled outward
trace network have the same finite-product Haar value.  This compatibility
is structural: named face-major binders are permuted to canonical tag order,
converted to positional assignments, and then reassembled by Boolean Haar
linearity. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_traceNetwork :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceExpansionProduct)
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceNetwork) := by
  refine rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_namedBoolSum ?_
  refine rationalComplexEqv_trans
    (rationalComplexNamedBoolSum_radiusZeroElementaryCubeFaceCornerTags_eq_range
      (fun environment =>
        finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (radiusZeroElementaryCubeOutwardFaceTraceProductAt environment))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexNamedBoolSum_range 24 (fun environment =>
      finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubeOutwardFaceTraceProductAt environment))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr 24 (fun assignment => by
      change RationalComplexEqv
        (finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (radiusZeroElementaryCubeOutwardFaceTraceProductAt
            (fun tag => cubeTagValue assignment tag)))
        (finiteProductHaarComplex
          (adjacentEvenActiveLinks 0).length
          (radiusZeroElementaryCubeOutwardFaceTraceProduct assignment))
      rw [radiusZeroElementaryCubeOutwardFaceTraceProductAt_cubeTagValue]
      exact rationalComplexEqv_refl _)) ?_
  exact rationalComplexEqv_symm (by
    unfold radiusZeroElementaryCubeOutwardTraceNetwork
    exact finiteProductHaarComplex_boolSum
      (adjacentEvenActiveLinks 0).length 24
      radiusZeroElementaryCubeOutwardFaceTraceProduct)

/-- **Exact genuine outward cube integral.**  The orientation-faithful
outward product of all six independently expanded fundamental plaquette
traces has exact twelve-link Haar value `1/16`.  No depth-twenty-four Boolean
tree is reduced.  The canonical all-standard representative remains the
separate orientation fence recorded in the work plan. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_exact :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceExpansionProduct)
      (Q'.mkPos 1 16 (by decide), 0) :=
  rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_traceNetwork
    finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_exact

#print axioms TaggedOrientedPlaquetteRow.traceExpansion_eq_fourBoolSum
#print axioms TaggedOrientedPlaquetteRow.traceTermAt_cubeTagValue
#print axioms finiteProductHaarComplex_mul_traceExpansionProduct
#print axioms taggedOrientedPlaquetteTraceTermsFromWord_eq_traceTermsAt_tagWord
#print axioms radiusZeroElementaryCubeOutwardFaceTraceExpansions_eq_map
#print axioms radiusZeroElementaryCubeOutwardFaceTraceExpansions_orientation_mask
#print axioms radiusZeroElementaryCubeOutwardFaceTraceTermsAt_cubeTagValue
#print axioms radiusZeroElementaryCubeOutwardFaceTraceProductAt_cubeTagValue
#print axioms radiusZeroElementaryCubeTraceTermsFromWord_eq_traceTermsAt_tagWord
#print axioms radiusZeroElementaryCubeTraceProductFromWord_eq_traceProductAt_tagWord
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_namedBoolSum
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_traceNetwork
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_exact

end YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct
