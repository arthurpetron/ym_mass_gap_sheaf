/-
# Two ordered copies of the same original spatial slice

The first N blocks are the canonical boxed spatial links at `start`; the
next N blocks are the SAME ordered list at `start+1`. Both are placed in
one original slab, and their different times prove that the images are
disjoint. The explicit coordinate pins retain all box-fringe links.

This ordering is the input for a finite kinetic factor followed by Haar
integration of the first N blocks. No transfer operator, stationarity,
iteration estimate, or change to the original action is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

local notation:max "N" width:arg => List.length (baseLinks width)
local notation "nlinks" extent => List.length (boundaryCompleteSlabLinks extent)

private theorem images_disjoint {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) (b : Nat)
    (hl : b ∈ (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
      (show start ≤ extent by omega)).image)
    (hr : b ∈ (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).image) : False := by
  have hb := (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).physical b hr
  have h0 := (BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff hw
    (show start ≤ extent by omega) hb).mp hl
  have h1 := (BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff hw ht hb).mp hr
  have ht0 := h0.2.2.2.2
  have ht1 := h1.2.2.2.2
  omega

/-- Concatenate the lower and upper placements without changing either
single-slice order. The source carrier has exactly N+N blocks. -/
def embedding {width start extent : Nat} (hw : width ≤ extent) (ht : start+1 ≤ extent) :
    BlockEmbedding (N width + N width) (nlinks extent) where
  image := (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
    (show start ≤ extent by omega)).image ++
    (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).image
  length := by simp only [List.length_append, BlockEmbedding.length]
  nodup := by
    refine List.nodup_append.mpr
      ⟨(BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start ≤ extent by omega)).nodup,
        (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).nodup, ?_⟩
    intro a ha b hb he
    subst b
    exact images_disjoint hw ht a ha hb
  physical := by
    intro b hb
    rcases List.mem_append.mp hb with hl | hr
    · exact (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start ≤ extent by omega)).physical b hl
    · exact (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).physical b hr

theorem embedding_mem_iff {width start extent b : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) (hb : b < nlinks extent) :
    b ∈ (embedding hw ht).image ↔
      SliceLink width start (correctedSlabLinkAt extent b) ∨
      SliceLink width (start+1) (correctedSlabLinkAt extent b) := by
  change b ∈ (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
    (show start ≤ extent by omega)).image ++
    (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).image ↔ _
  rw [List.mem_append,
    BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff hw
      (show start ≤ extent by omega) hb,
    BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff hw ht hb]

private theorem getD_append_left {A : Type} (xs ys : List A) (fallback : A) :
    ∀ i, i < xs.length → (xs++ys).getD i fallback = xs.getD i fallback := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons a xs ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

private theorem getD_append_right {A : Type} (xs ys : List A) (fallback : A) (i : Nat) :
    (xs++ys).getD (i+xs.length) fallback = ys.getD i fallback := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change (xs++ys).getD (i+xs.length) fallback = ys.getD i fallback
      exact ih

/-- The first N coordinates use the original single-slice order at start. -/
theorem lower_block {width start extent i : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) (hi : i < N width) :
    (embedding hw ht).block i =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start ≤ extent by omega)).block i := by
  apply getD_append_left
  simpa only [BlockEmbedding.length] using hi

/-- After the first N coordinates, the SAME source order occurs at start+1. -/
theorem upper_block {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) (i : Nat) :
    (embedding hw ht).block (N width+i) =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).block i := by
  let lower := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
    (show start ≤ extent by omega)
  let upper := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht
  change (lower.image++upper.image).getD (N width+i) 0 = upper.image.getD i 0
  rw [show N width+i = i+lower.image.length by rw [lower.length]; omega]
  exact getD_append_right lower.image upper.image 0 i

theorem lower_link_block {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) {link : Z4Link}
    (hl : link ∈ baseLinks width) :
    (embedding hw ht).block ((baseLinks width).idxOf link) =
      (boundaryCompleteSlabLinks extent).idxOf (timeShiftLink start link) :=
  (lower_block hw ht (List.idxOf_lt_length_of_mem hl)).trans
    (BF4ExactSlabFixedSpatialSliceCarrier.embedding_block hw
      (show start ≤ extent by omega) hl)

theorem upper_link_block {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) {link : Z4Link}
    (hl : link ∈ baseLinks width) :
    (embedding hw ht).block (N width+(baseLinks width).idxOf link) =
      (boundaryCompleteSlabLinks extent).idxOf (timeShiftLink (start+1) link) :=
  (upper_block hw ht _).trans
    (BF4ExactSlabFixedSpatialSliceCarrier.embedding_block hw ht hl)

/-- The head coordinate is the actual lower spatial-link quaternion. -/
theorem lower_link_pin {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) {link : Z4Link}
    (hl : link ∈ baseLinks width) :
    QuaternionPrefixPolyQuaternionEqv (nlinks extent)
      ((embedding hw ht).quaternion
        (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf link)))
      (correctedSlabLinkPolynomial extent (timeShiftLink start link)) := by
  have hi := List.idxOf_lt_length_of_mem hl
  have hm := BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_physical hw
    (show start ≤ extent by omega) (List.mem_map.mpr ⟨link, hl, rfl⟩)
  rw [correctedSlabLinkPolynomial_of_mem hm]
  have h := (embedding hw ht).quaternion_coordinate
    (show (baseLinks width).idxOf link < N width + N width by omega)
  rw [lower_link_block hw ht hl] at h
  exact h

/-- The tail coordinate is the actual upper spatial-link quaternion. -/
theorem upper_link_pin {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) {link : Z4Link}
    (hl : link ∈ baseLinks width) :
    QuaternionPrefixPolyQuaternionEqv (nlinks extent)
      ((embedding hw ht).quaternion
        (PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf link)))
      (correctedSlabLinkPolynomial extent (timeShiftLink (start+1) link)) := by
  have hi := List.idxOf_lt_length_of_mem hl
  have hm := BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_physical hw ht
    (List.mem_map.mpr ⟨link, hl, rfl⟩)
  rw [correctedSlabLinkPolynomial_of_mem hm]
  have h := (embedding hw ht).quaternion_coordinate
    (show N width+(baseLinks width).idxOf link < N width + N width by omega)
  rw [upper_link_block hw ht hl] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.embedding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.embedding_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.lower_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.upper_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.lower_link_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.upper_link_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.lower_link_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier.upper_link_pin
