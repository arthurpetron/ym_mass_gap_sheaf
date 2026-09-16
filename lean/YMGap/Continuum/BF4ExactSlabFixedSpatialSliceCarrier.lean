/-
# One fixed spatial slice of original quaternion link coordinates

Enumerate the boxed spatial links at time zero using only the width. Their
time translates retain the same order and length, and the supplied room
guards place every link inside the original ambient slab carrier. The
resulting block embedding sends each source coordinate quaternion to the
literal corrected-slab polynomial of that translated link.

This is the single-slice coordinate input for recoding the original spatial
and kinetic factors. It does not construct a stationary vacuum or assert
an estimate for an iterated transfer operator.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

local notation "nlinks" extent => List.length (boundaryCompleteSlabLinks extent)

local instance (width time : Nat) (link : Z4Link) : Decidable (SliceLink width time link) := by
  unfold SliceLink
  infer_instance

/-- The canonical source list depends on width alone. Unused box-fringe
links are retained as original normalized Haar coordinates. -/
def baseLinks (width : Nat) : List Z4Link :=
  (boundaryCompleteSlabLinks width).filter fun link => decide (SliceLink width 0 link)

theorem baseLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ baseLinks width ↔ SliceLink width 0 link := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr
      ⟨BF4ExactSlabFixedSpatialBoundaryCarrier.sliceLink_physical
        (Nat.le_refl width) (Nat.zero_le width) h, decide_eq_true h⟩

theorem baseLinks_nodup (width : Nat) : (baseLinks width).Nodup :=
  List.filter_sublist.nodup (boundaryCompleteSlabLinks_nodup _)

/-- Place the same ordered source links at one arbitrary time. -/
def sliceLinks (width time : Nat) : List Z4Link :=
  (baseLinks width).map (timeShiftLink time)

theorem sliceLinks_mem_iff (width time : Nat) (link : Z4Link) :
    link ∈ sliceLinks width time ↔ SliceLink width time link := by
  constructor
  · intro h
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp h
    have hs' := (baseLinks_mem_iff width source).mp hs
    rcases source with ⟨⟨x,y,z,t⟩,dir⟩
    refine ⟨hs'.1, hs'.2.1, hs'.2.2.1, hs'.2.2.2.1, ?_⟩
    have he : t = 0 := hs'.2.2.2.2
    change t + time = time
    rw [he, Nat.zero_add]
  · intro h
    rcases link with ⟨⟨x,y,z,t⟩,dir⟩
    have hs : SliceLink width 0 ((x,y,z,0),dir) :=
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩
    apply List.mem_map.mpr
    refine ⟨((x,y,z,0),dir), (baseLinks_mem_iff width _).mpr hs, ?_⟩
    have he : t = time := h.2.2.2.2
    change ((x,y,z,0 + time),dir) = ((x,y,z,t),dir)
    rw [Nat.zero_add, he]

private theorem shift_injective (time : Nat) {a b : Z4Link}
    (h : timeShiftLink time a = timeShiftLink time b) : a = b := by
  rcases a with ⟨⟨x,y,z,t⟩,dir⟩
  rcases b with ⟨⟨x',y',z',t'⟩,dir'⟩
  simpa only [timeShiftLink, timeShiftVertex, Prod.mk.injEq,
    Nat.add_right_cancel_iff] using h

theorem sliceLinks_nodup (width time : Nat) : (sliceLinks width time).Nodup :=
  nodup_map_of_injOn _ _ (baseLinks_nodup width)
    (fun _ _ _ _ => shift_injective time)

/-- In particular the carrier size does not grow with time or ambient extent. -/
theorem sliceLinks_length (width time : Nat) :
    (sliceLinks width time).length = (baseLinks width).length := List.length_map _

theorem sliceLinks_physical {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) {link : Z4Link}
    (hl : link ∈ sliceLinks width time) : link ∈ boundaryCompleteSlabLinks extent :=
  BF4ExactSlabFixedSpatialBoundaryCarrier.sliceLink_physical hw ht
    ((sliceLinks_mem_iff width time link).mp hl)

/-- Explicit injective placement of the one width-only source carrier. -/
def embedding {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent) :
    BlockEmbedding (baseLinks width).length (nlinks extent) where
  image := (sliceLinks width time).map (boundaryCompleteSlabLinks extent).idxOf
  length := by rw [List.length_map, sliceLinks_length]
  nodup := nodup_map_of_injOn _ _ (sliceLinks_nodup width time)
    (fun _ ha _ hb => idxOf_injective_on_members (sliceLinks_physical hw ht ha)
      (sliceLinks_physical hw ht hb))
  physical := by
    intro b hb
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp hb
    exact List.idxOf_lt_length_of_mem (sliceLinks_physical hw ht hl)

/-- Every physical ambient block belongs to the image precisely when its
literal link belongs to the specified boxed spatial slice. -/
theorem embedding_mem_iff {width time extent b : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) (hb : b < nlinks extent) :
    b ∈ (embedding hw ht).image ↔ SliceLink width time (correctedSlabLinkAt extent b) := by
  constructor
  · intro h
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp h
    rw [correctedSlabLinkAt_idxOf (sliceLinks_physical hw ht hl)]
    exact (sliceLinks_mem_iff width time link).mp hl
  · intro h
    have hl := (sliceLinks_mem_iff width time _).mpr h
    apply List.mem_map.mpr
    refine ⟨correctedSlabLinkAt extent b, hl, ?_⟩
    apply correctedSlabLinkAt_injective_on_physical
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem (sliceLinks_physical hw ht hl)))
      (List.mem_range.mpr hb)
    exact correctedSlabLinkAt_idxOf (sliceLinks_physical hw ht hl)

theorem embedding_block {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) {link : Z4Link}
    (hl : link ∈ baseLinks width) :
    (embedding hw ht).block ((baseLinks width).idxOf link) =
      (boundaryCompleteSlabLinks extent).idxOf (timeShiftLink time link) := by
  have hi := List.idxOf_lt_length_of_mem hl
  change (((baseLinks width).map (timeShiftLink time)).map
    (boundaryCompleteSlabLinks extent).idxOf).getD _ 0 = _
  rw [List.map_map]
  rw [← List.getElem_eq_getD (h := by rw [List.length_map]; exact hi), List.getElem_map]
  exact congrArg (fun link =>
    (boundaryCompleteSlabLinks extent).idxOf (timeShiftLink time link))
    (eq_of_beq (List.findIdx_getElem (w := hi)))

/-- The source coordinate is the original ambient link quaternion, allowing
only the zero padding inherent in the exact block embedding. -/
theorem link_pin {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) {link : Z4Link}
    (hl : link ∈ baseLinks width) :
    QuaternionPrefixPolyQuaternionEqv (nlinks extent)
      ((embedding hw ht).quaternion
        (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf link)))
      (correctedSlabLinkPolynomial extent (timeShiftLink time link)) := by
  have hm : timeShiftLink time link ∈ sliceLinks width time :=
    List.mem_map.mpr ⟨link, hl, rfl⟩
  rw [correctedSlabLinkPolynomial_of_mem (sliceLinks_physical hw ht hm)]
  have h := (embedding hw ht).quaternion_coordinate (List.idxOf_lt_length_of_mem hl)
  rw [embedding_block hw ht hl] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.baseLinks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.baseLinks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.baseLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.embedding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.embedding_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.link_pin
