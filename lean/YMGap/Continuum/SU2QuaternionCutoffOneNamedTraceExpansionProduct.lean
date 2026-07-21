/-
# Geometry-generic cutoff-one trace-expansion product

For an arbitrary cutoff-one support and an arbitrary standard/reversed
orientation choice, this leaf starts from the literal product of separately
summed fundamental plaquette traces.  It moves exactly four Boolean binders
per face through finite-product Haar and identifies the resulting positional
word with a named Boolean sum over the fresh face-corner tags supplied by
`SU2QuaternionCutoffOneOrientedFaceRows`.

The proof is structural in the face-row list.  It never constructs a Boolean
assignment family, unfolds a support-sized binder tree, or changes a face
orientation.  The common quaternion-block carrier is the geometric touched-
link list of the support, so the fixed terms produced here are ready for the
subsequent link-bucket regrouping theorem.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
import YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord

namespace YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation "PhysicalZ4Link" =>
  YMGap.Continuum.ClusterCount4DProgress.Z4Link

/-! ## 1. One geometry-generic oriented face -/

def cutoffOneOrientedFaceBlock0
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow) : Nat :=
  listIndexOf row.link0 links

def cutoffOneOrientedFaceBlock1
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow) : Nat :=
  listIndexOf row.link1 links

def cutoffOneOrientedFaceBlock2
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow) : Nat :=
  listIndexOf row.link2 links

def cutoffOneOrientedFaceBlock3
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow) : Nat :=
  listIndexOf row.link3 links

/-- The fixed four-index coefficient term of one oriented production face,
with every physical link read in one common block carrier. -/
def cutoffOneOrientedFaceTraceTermBits
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow)
    (first second third fourth : Bool) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      standardPlaquetteTraceTerm
        (cutoffOneOrientedFaceBlock0 links row)
        (cutoffOneOrientedFaceBlock1 links row)
        (cutoffOneOrientedFaceBlock2 links row)
        (cutoffOneOrientedFaceBlock3 links row)
        first second third fourth
  | .reversed =>
      reversedPlaquetteTraceTerm
        (cutoffOneOrientedFaceBlock0 links row)
        (cutoffOneOrientedFaceBlock1 links row)
        (cutoffOneOrientedFaceBlock2 links row)
        (cutoffOneOrientedFaceBlock3 links row)
        first second third fourth

/-- Read one face's four fresh corner indices from a total named
environment. -/
def cutoffOneOrientedFaceTraceTermAt
    (links : List PhysicalZ4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) : ComplexRatPoly :=
  cutoffOneOrientedFaceTraceTermBits links row
    (environment row.firstTag)
    (environment row.secondTag)
    (environment row.thirdTag)
    (environment row.fourthTag)

/-- The literal separately summed trace expansion of one oriented face. -/
def cutoffOneOrientedFaceTraceExpansion
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      standardPlaquetteTraceExpansion
        (cutoffOneOrientedFaceBlock0 links row)
        (cutoffOneOrientedFaceBlock1 links row)
        (cutoffOneOrientedFaceBlock2 links row)
        (cutoffOneOrientedFaceBlock3 links row)
  | .reversed =>
      reversedPlaquetteTraceExpansion
        (cutoffOneOrientedFaceBlock0 links row)
        (cutoffOneOrientedFaceBlock1 links row)
        (cutoffOneOrientedFaceBlock2 links row)
        (cutoffOneOrientedFaceBlock3 links row)

theorem cutoffOneOrientedFaceTraceExpansion_eq_fourBoolSum
    (links : List PhysicalZ4Link) (row : CutoffOneOrientedFaceRow) :
    cutoffOneOrientedFaceTraceExpansion links row =
      complexRatPolyFourBoolSum
        (cutoffOneOrientedFaceTraceTermBits links row) := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

/-! ## 2. Structural face-wise Haar Fubini -/

/-- Consume four positional bits per face, retaining `false` as the total
default on short Boolean words. -/
def cutoffOneOrientedFaceTraceTermsFromWord
    (links : List PhysicalZ4Link) :
    List CutoffOneOrientedFaceRow → List Bool → List ComplexRatPoly
  | [], _ => []
  | row :: rows, assignment =>
      cutoffOneOrientedFaceTraceTermBits links row
          (assignment.getD 0 false)
          (assignment.getD 1 false)
          (assignment.getD 2 false)
          (assignment.getD 3 false) ::
        cutoffOneOrientedFaceTraceTermsFromWord links rows
          (assignment.drop 4)

/-- Four-binder Fubini for an arbitrary geometry-generic face-row list.
The suffix remains symbolic at every induction step. -/
theorem finiteProductHaarComplex_mul_cutoffOneOrientedFaceTraceExpansionProduct :
    ∀ (blockCount : Nat) (spectator : ComplexRatPoly)
      (links : List PhysicalZ4Link) (rows : List CutoffOneOrientedFaceRow),
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyProduct (rows.map
              (cutoffOneOrientedFaceTraceExpansion links)))))
        (rationalComplexBoolSum (4 * rows.length) (fun assignment =>
          finiteProductHaarComplex blockCount
            ((cutoffOneOrientedFaceTraceTermsFromWord links rows assignment).foldl
              complexRatPolyMul spectator)))
  | blockCount, spectator, links, [] => by
      simpa only [List.map_nil, complexRatPolyProduct, List.length_nil,
        Nat.mul_zero, rationalComplexBoolSum,
        cutoffOneOrientedFaceTraceTermsFromWord, List.foldl_nil] using
        (finiteProductHaarComplex_mul_one blockCount spectator)
  | blockCount, spectator, links, row :: rows => by
      simp only [List.map_cons, complexRatPolyProduct]
      rw [cutoffOneOrientedFaceTraceExpansion_eq_fourBoolSum]
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_mul_fourBoolSum_inner
          blockCount spectator
          (complexRatPolyProduct
            (rows.map (cutoffOneOrientedFaceTraceExpansion links)))
          (cutoffOneOrientedFaceTraceTermBits links row)) ?_
      refine rationalComplexEqv_trans
        (rationalComplexFourBoolSum_congr (fun first second third fourth =>
          rationalComplexEqv_trans
            (finiteProductHaarComplex_mul_assoc_context blockCount
              spectator
              (cutoffOneOrientedFaceTraceTermBits links row
                first second third fourth)
              (complexRatPolyProduct
                (rows.map (cutoffOneOrientedFaceTraceExpansion links))))
            (finiteProductHaarComplex_mul_cutoffOneOrientedFaceTraceExpansionProduct
              blockCount
              (complexRatPolyMul spectator
                (cutoffOneOrientedFaceTraceTermBits links row
                  first second third fourth)) links rows))) ?_
      rw [List.length_cons, Nat.mul_succ,
        rationalComplexBoolSum_add_four]
      exact rationalComplexFourBoolSum_congr
        (fun first second third fourth =>
          rationalComplexBoolSum_congr (4 * rows.length)
            (fun suffix => by
              simp only [cutoffOneOrientedFaceTraceTermsFromWord,
                List.getD_cons_zero, List.getD_cons_succ,
                List.drop_succ_cons, List.foldl_cons]
              exact rationalComplexEqv_refl _))

/-! ## 3. The fresh face-major tag word -/

/-- The actual face-major word of the fresh tags allocated by the N0 rows. -/
def cutoffOneFaceMajorCornerTags
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List Nat :=
  (cutoffOneOrientedFaceRows orientationAt n support).flatMap
    CutoffOneOrientedFaceRow.tags

private theorem cutoffOneRowTagsFlatMap_length :
    ∀ rows : List CutoffOneOrientedFaceRow,
      (rows.flatMap CutoffOneOrientedFaceRow.tags).length =
        4 * rows.length
  | [] => rfl
  | row :: rows => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        row.tags_length, cutoffOneRowTagsFlatMap_length rows]
      omega

theorem cutoffOneFaceMajorCornerTags_length
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneFaceMajorCornerTags orientationAt n support).length =
      4 * support.length := by
  unfold cutoffOneFaceMajorCornerTags
  rw [cutoffOneRowTagsFlatMap_length,
    cutoffOneOrientedFaceRows_length]

private theorem cutoffOneRowTagsFlatMap_eq_supportPositionPackets :
    ∀ rows : List CutoffOneOrientedFaceRow,
      rows.flatMap CutoffOneOrientedFaceRow.tags =
        (rows.map CutoffOneOrientedFaceRow.supportPosition).flatMap
          (fun position =>
            [cutoffOneFaceCornerTag position 0,
             cutoffOneFaceCornerTag position 1,
             cutoffOneFaceCornerTag position 2,
             cutoffOneFaceCornerTag position 3])
  | [] => rfl
  | row :: rows => by
      simp only [List.flatMap_cons, List.map_cons,
        CutoffOneOrientedFaceRow.tags,
        CutoffOneOrientedFaceRow.firstTag,
        CutoffOneOrientedFaceRow.secondTag,
        CutoffOneOrientedFaceRow.thirdTag,
        CutoffOneOrientedFaceRow.fourthTag]
      rw [cutoffOneRowTagsFlatMap_eq_supportPositionPackets rows]

private theorem cutoffOneCornerTagPackets_eq_range :
    ∀ count : Nat,
      (List.range count).flatMap (fun position =>
          [cutoffOneFaceCornerTag position 0,
           cutoffOneFaceCornerTag position 1,
           cutoffOneFaceCornerTag position 2,
           cutoffOneFaceCornerTag position 3]) =
        List.range (4 * count)
  | 0 => rfl
  | count + 1 => by
      rw [List.range_succ, List.flatMap_append,
        cutoffOneCornerTagPackets_eq_range count]
      simp only [List.flatMap_singleton, cutoffOneFaceCornerTag,
        Nat.mul_succ]
      rw [show 4 * count + 4 =
        ((((4 * count) + 1) + 1) + 1) + 1 by omega]
      rw [List.range_succ, List.range_succ,
        List.range_succ, List.range_succ]
      simp only [Nat.add_zero, Nat.add_assoc,
        List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append]

/-- The face-major reading is not merely fresh: because support positions
are enumerated consecutively, it is exactly the canonical N0 carrier
`0, ..., 4 * |support| - 1`. -/
theorem cutoffOneFaceMajorCornerTags_eq_cornerTags
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    cutoffOneFaceMajorCornerTags orientationAt n support =
      cutoffOneCornerTags support := by
  unfold cutoffOneFaceMajorCornerTags cutoffOneCornerTags
  rw [cutoffOneRowTagsFlatMap_eq_supportPositionPackets,
    cutoffOneOrientedFaceRows_map_supportPosition]
  exact cutoffOneCornerTagPackets_eq_range support.length

private theorem cutoffOneCornerTagRange_nodup :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨cutoffOneCornerTagRange_nodup count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

/-- Freshness is global, not merely face-local: the exact face-major tag word
is the canonical finite range, hence has no repetitions constructively. -/
theorem cutoffOneFaceMajorCornerTags_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneFaceMajorCornerTags orientationAt n support).Nodup := by
  rw [cutoffOneFaceMajorCornerTags_eq_cornerTags]
  unfold cutoffOneCornerTags
  exact cutoffOneCornerTagRange_nodup (4 * support.length)

/-! ## 4. Positional chunks equal the named environment decoder -/

private theorem cutoffOneTraceTermsAt_congr_on_flatMap
    (links : List PhysicalZ4Link) (rows : List CutoffOneOrientedFaceRow)
    (left right : Nat → Bool)
    (hagrees : ∀ tag,
      tag ∈ rows.flatMap CutoffOneOrientedFaceRow.tags →
        left tag = right tag) :
    rows.map (cutoffOneOrientedFaceTraceTermAt links left) =
      rows.map (cutoffOneOrientedFaceTraceTermAt links right) := by
  apply List.map_congr_left
  intro row hrow
  have hlift : ∀ tag, tag ∈ row.tags →
      tag ∈ rows.flatMap CutoffOneOrientedFaceRow.tags := by
    intro tag htag
    exact List.mem_flatMap.mpr ⟨row, hrow, htag⟩
  have h0 : row.firstTag ∈ row.tags := by
    unfold CutoffOneOrientedFaceRow.tags
    exact List.mem_cons_self
  have h1 : row.secondTag ∈ row.tags := by
    unfold CutoffOneOrientedFaceRow.tags
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have h2 : row.thirdTag ∈ row.tags := by
    unfold CutoffOneOrientedFaceRow.tags
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 : row.fourthTag ∈ row.tags := by
    unfold CutoffOneOrientedFaceRow.tags
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  unfold cutoffOneOrientedFaceTraceTermAt
  rw [hagrees row.firstTag (hlift _ h0),
      hagrees row.secondTag (hlift _ h1),
      hagrees row.thirdTag (hlift _ h2),
      hagrees row.fourthTag (hlift _ h3)]

/-- The four-bit positional chunks generated by face-wise Fubini are exactly
the fixed terms read through the face-major named environment. -/
theorem cutoffOneOrientedFaceTraceTermsFromWord_eq_traceTermsAt_tagWord
    (links : List PhysicalZ4Link) (rows : List CutoffOneOrientedFaceRow)
    (assignment : List Bool)
    (hnodup : (rows.flatMap CutoffOneOrientedFaceRow.tags).Nodup) :
    cutoffOneOrientedFaceTraceTermsFromWord links rows assignment =
      rows.map (cutoffOneOrientedFaceTraceTermAt links
        (boolTagWordEnvironment
          (rows.flatMap CutoffOneOrientedFaceRow.tags) assignment)) := by
  induction rows generalizing assignment with
  | nil => rfl
  | cons row rows ih =>
      have hfull :
          (row.tags ++ rows.flatMap
            CutoffOneOrientedFaceRow.tags).Nodup := by
        simpa only [List.flatMap_cons] using hnodup
      have hp := List.nodup_append.mp hfull
      have hword :
          (row.firstTag :: row.secondTag :: row.thirdTag ::
            row.fourthTag :: rows.flatMap
              CutoffOneOrientedFaceRow.tags).Nodup := by
        simpa only [CutoffOneOrientedFaceRow.tags,
          List.cons_append, List.nil_append] using hfull
      have h0 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                CutoffOneOrientedFaceRow.tags)
              assignment row.firstTag =
            assignment.getD 0 false := by
        simpa only [CutoffOneOrientedFaceRow.tags,
          List.cons_append, List.nil_append, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            []
            (row.secondTag :: row.thirdTag :: row.fourthTag ::
              rows.flatMap CutoffOneOrientedFaceRow.tags)
            assignment row.firstTag hword)
      have h1 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                CutoffOneOrientedFaceRow.tags)
              assignment row.secondTag =
            assignment.getD 1 false := by
        simpa only [CutoffOneOrientedFaceRow.tags,
          List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            [row.firstTag]
            (row.thirdTag :: row.fourthTag ::
              rows.flatMap CutoffOneOrientedFaceRow.tags)
            assignment row.secondTag hword)
      have h2 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                CutoffOneOrientedFaceRow.tags)
              assignment row.thirdTag =
            assignment.getD 2 false := by
        simpa only [CutoffOneOrientedFaceRow.tags,
          List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            [row.firstTag, row.secondTag]
            (row.fourthTag ::
              rows.flatMap CutoffOneOrientedFaceRow.tags)
            assignment row.thirdTag hword)
      have h3 :
          boolTagWordEnvironment
              (row.tags ++ rows.flatMap
                CutoffOneOrientedFaceRow.tags)
              assignment row.fourthTag =
            assignment.getD 3 false := by
        simpa only [CutoffOneOrientedFaceRow.tags,
          List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_lookup_of_nodup
            [row.firstTag, row.secondTag, row.thirdTag]
            (rows.flatMap CutoffOneOrientedFaceRow.tags)
            assignment row.fourthTag hword)
      have hhead :
          cutoffOneOrientedFaceTraceTermBits links row
              (assignment.getD 0 false) (assignment.getD 1 false)
              (assignment.getD 2 false) (assignment.getD 3 false) =
            cutoffOneOrientedFaceTraceTermAt links
              (boolTagWordEnvironment
                (row.tags ++ rows.flatMap
                  CutoffOneOrientedFaceRow.tags) assignment) row := by
        unfold cutoffOneOrientedFaceTraceTermAt
        rw [h0, h1, h2, h3]
      have htailMaps :
          rows.map (cutoffOneOrientedFaceTraceTermAt links
              (boolTagWordEnvironment
                (row.tags ++ rows.flatMap
                  CutoffOneOrientedFaceRow.tags) assignment)) =
            rows.map (cutoffOneOrientedFaceTraceTermAt links
              (boolTagWordEnvironment
                (rows.flatMap CutoffOneOrientedFaceRow.tags)
                (assignment.drop 4))) := by
        apply cutoffOneTraceTermsAt_congr_on_flatMap
        intro tag htag
        have hfresh : tag ∉ row.tags := by
          intro hrow
          exact hp.2.2 tag hrow tag htag rfl
        simpa only [CutoffOneOrientedFaceRow.tags,
          List.length_cons, List.length_nil] using
          (boolTagWordEnvironment_append_of_not_mem row.tags
            (rows.flatMap CutoffOneOrientedFaceRow.tags)
            assignment tag hfresh)
      simp only [cutoffOneOrientedFaceTraceTermsFromWord,
        List.map_cons, List.flatMap_cons]
      rw [hhead, (ih (assignment.drop 4) hp.2.1).trans htailMaps.symm]

/-! ## 5. The literal cutoff-one expansion product -/

def cutoffOneOrientedFaceTraceExpansions
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List ComplexRatPoly :=
  (cutoffOneOrientedFaceRows orientationAt n support).map
    (cutoffOneOrientedFaceTraceExpansion
      (cutoffOneTouchedLinks n support))

/-- The genuine product of all separately summed oriented plaquette traces,
in production support order. -/
def cutoffOneOrientedFaceTraceExpansionProduct
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : ComplexRatPoly :=
  complexRatPolyProduct
    (cutoffOneOrientedFaceTraceExpansions orientationAt n support)

def cutoffOneOrientedFaceTraceTermsAt
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    List ComplexRatPoly :=
  (cutoffOneOrientedFaceRows orientationAt n support).map
    (cutoffOneOrientedFaceTraceTermAt
      (cutoffOneTouchedLinks n support) environment)

def cutoffOneOrientedFaceTraceProductAt
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    ComplexRatPoly :=
  complexRatPolyProduct
    (cutoffOneOrientedFaceTraceTermsAt
      orientationAt n support environment)

/-- **Geometry-generic literal-face Fubini bridge.**  For every support and
every standard/reversed choice, finite-product Haar of the literal product
of separately expanded plaquette traces is the named Boolean sum of the
fixed face-major products.  The theorem preserves support order, factor
order, every orientation choice, and the common touched-link block carrier. -/
theorem finiteProductHaarComplex_cutoffOneOrientedFaceTraceExpansionProduct_eq_namedBoolSum
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (cutoffOneOrientedFaceTraceExpansionProduct
          orientationAt n support))
      (rationalComplexNamedBoolSum
        (cutoffOneCornerTags support)
        (fun environment =>
          finiteProductHaarComplex
            (cutoffOneTouchedLinks n support).length
            (cutoffOneOrientedFaceTraceProductAt
              orientationAt n support environment))) := by
  rw [← cutoffOneFaceMajorCornerTags_eq_cornerTags
    orientationAt n support]
  unfold cutoffOneOrientedFaceTraceExpansionProduct
    cutoffOneOrientedFaceTraceExpansions
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul
        (cutoffOneTouchedLinks n support).length
        (complexRatPolyProduct
          ((cutoffOneOrientedFaceRows orientationAt n support).map
            (cutoffOneOrientedFaceTraceExpansion
              (cutoffOneTouchedLinks n support)))))) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_cutoffOneOrientedFaceTraceExpansionProduct
      (cutoffOneTouchedLinks n support).length complexRatPolyOne
      (cutoffOneTouchedLinks n support)
      (cutoffOneOrientedFaceRows orientationAt n support)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr
      (4 * (cutoffOneOrientedFaceRows orientationAt n support).length)
      (fun assignment =>
        finiteProductHaarComplex_foldl_one_eq_product
          (cutoffOneTouchedLinks n support).length
          (cutoffOneOrientedFaceTraceTermsFromWord
            (cutoffOneTouchedLinks n support)
            (cutoffOneOrientedFaceRows orientationAt n support)
            assignment))) ?_
  have hdepth :
      4 * (cutoffOneOrientedFaceRows orientationAt n support).length =
        (cutoffOneFaceMajorCornerTags
          orientationAt n support).length := by
    rw [cutoffOneOrientedFaceRows_length,
      cutoffOneFaceMajorCornerTags_length]
  rw [hdepth]
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr
      (cutoffOneFaceMajorCornerTags orientationAt n support).length
      (fun assignment => by
        rw [cutoffOneOrientedFaceTraceTermsFromWord_eq_traceTermsAt_tagWord
          (cutoffOneTouchedLinks n support)
          (cutoffOneOrientedFaceRows orientationAt n support)
          assignment
          (cutoffOneFaceMajorCornerTags_nodup orientationAt n support)]
        exact rationalComplexEqv_refl _)) ?_
  exact rationalComplexEqv_symm
    (rationalComplexNamedBoolSum_tagWord
      (cutoffOneFaceMajorCornerTags orientationAt n support)
      (fun environment =>
        finiteProductHaarComplex
          (cutoffOneTouchedLinks n support).length
          (cutoffOneOrientedFaceTraceProductAt
            orientationAt n support environment)))

#print axioms cutoffOneOrientedFaceTraceExpansion_eq_fourBoolSum
#print axioms finiteProductHaarComplex_mul_cutoffOneOrientedFaceTraceExpansionProduct
#print axioms cutoffOneFaceMajorCornerTags_nodup
#print axioms cutoffOneFaceMajorCornerTags_length
#print axioms cutoffOneFaceMajorCornerTags_eq_cornerTags
#print axioms cutoffOneOrientedFaceTraceTermsFromWord_eq_traceTermsAt_tagWord
#print axioms finiteProductHaarComplex_cutoffOneOrientedFaceTraceExpansionProduct_eq_namedBoolSum

end YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct
