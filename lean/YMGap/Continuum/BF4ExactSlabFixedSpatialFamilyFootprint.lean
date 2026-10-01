/-
# Literal common footprint of a signed spatial plaquette family

The family is allowed to repeat faces and to have arbitrary signed coefficients.
Its observable footprint is the deduplicated list of actual fixed-slice link
slots, so its size is at most four times the number of listed faces. Strict
spatial padding makes each such slot an original active kinetic block.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
  (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
  (faceSlots)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
  (familySlots familyObservableBlocks familySpectatorBlocks
    familyObservableBlocks_lt familyObservableBlocks_nodup
    spatialSpan_familySpectator_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
  (incident_mem_baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
  (face_edge_box)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
  (StrictSliceLink active_index_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks)
open YMGap.Continuum.Z4UnitCubeEnumerationParity
  (nodup_subset_length_le)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
  (RatPoly polyZero)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
  (RatPolyCoeffEqv)
open YMGap.Continuum.SU2QuaternionAngularDerivative
  (angularDerivative)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (angularDerivative_blockIndependent_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Four actual link slots per listed face, before deduplication. -/
theorem familySlots_length (width : Nat) : ∀ qs : List Z4Plaq,
    (familySlots width qs).length = 4 * qs.length
  | [] => rfl
  | face :: rest => by
      have hedges : (edgesOf face).length = 4 := by
        rcases face with ⟨vertex, plane⟩
        cases plane <;> rfl
      simp only [familySlots, List.length_append, faceSlots, List.length_map,
        hedges, familySlots_length width rest, List.length_cons]
      omega

/-- Deduplication of physical slots never costs more than four per face,
even when the supplied family itself has repetitions. -/
theorem familyObservableBlocks_length_le_four (width : Nat) (qs : List Z4Plaq) :
    (familyObservableBlocks width qs).length ≤ 4 * qs.length := by
  have hsub : ∀ b, b ∈ familyObservableBlocks width qs →
      b ∈ familySlots width qs := by
    intro b hb
    exact of_decide_eq_true (List.mem_filter.mp hb).2
  have h := nodup_subset_length_le
    (familyObservableBlocks width qs) (familySlots width qs)
    (familyObservableBlocks_nodup width qs) hsub
  rw [familySlots_length width qs] at h
  exact h

/-- A literal edge of a face from a strictly smaller spatial box is active
at the larger width; the physical link and its actual slice index are kept. -/
theorem faceSlot_active_after_padding {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq)
    (hf : face ∈ spatialFaces base) (b : Nat)
    (hb : b ∈ faceSlots width face) : b ∈ activeBlocks width := by
  obtain ⟨link, hedge, hindex⟩ := List.mem_map.mp hb
  subst b
  have hbase := (spatialFaces_mem_iff base face).mp hf
  have hbox := face_edge_box hbase.1 hbase.2.1 hbase.2.2.1 hedge
  have hfaceWidth : face ∈ spatialFaces width :=
    spatialFaces_mono (Nat.le_of_lt hwidth) hf
  have hlink : link ∈ baseLinks width :=
    incident_mem_baseLinks hfaceWidth hedge
  apply (active_index_iff width link hlink).mpr
  exact ⟨(baseLinks_mem_iff width link).mp hlink,
    by omega, by omega, by omega⟩

private theorem familySlots_active_after_padding {base width : Nat}
    (hwidth : base < width) : ∀ (qs : List Z4Plaq),
      (∀ face, face ∈ qs → face ∈ spatialFaces base) →
      ∀ b, b ∈ familySlots width qs → b ∈ activeBlocks width
  | [], _, _, hb => False.elim (List.not_mem_nil hb)
  | face :: rest, hqs, b, hb => by
      rcases List.mem_append.mp hb with hface | hrest
      · exact faceSlot_active_after_padding hwidth face
          (hqs face List.mem_cons_self) b hface
      · exact familySlots_active_after_padding hwidth rest
          (fun p hp => hqs p (List.mem_cons_of_mem face hp)) b hrest

/-- Every block in the ONE common family footprint is an original active
kinetic block after strict padding. No Nodup assumption on faces is needed. -/
theorem familyObservableBlocks_active_after_padding {base width : Nat}
    (hwidth : base < width) (qs : List Z4Plaq)
    (hqs : ∀ face, face ∈ qs → face ∈ spatialFaces base)
    (b : Nat) (hb : b ∈ familyObservableBlocks width qs) :
    b ∈ activeBlocks width := by
  have hslots : b ∈ familySlots width qs :=
    of_decide_eq_true (List.mem_filter.mp hb).2
  exact familySlots_active_after_padding hwidth qs hqs b hslots

/-- The concrete link at a block, as data rather than a propositional
existence witness. -/
def linkAt (width b : Nat) (hb : b < N width) : Z4Link :=
  (baseLinks width)[b]

theorem linkAt_mem (width b : Nat) (hb : b < N width) :
    linkAt width b hb ∈ baseLinks width :=
  List.getElem_mem hb

private theorem familySlots_has_link (width : Nat) :
    ∀ (qs : List Z4Plaq) (b : Nat), b ∈ familySlots width qs →
      ∃ link : Z4Link, b = (baseLinks width).idxOf link
  | [], _, hb => False.elim (List.not_mem_nil hb)
  | face :: rest, b, hb => by
      rcases List.mem_append.mp hb with hface | hrest
      · obtain ⟨link, _, hindex⟩ := List.mem_map.mp hface
        exact ⟨link, hindex.symm⟩
      · obtain ⟨link, hindex⟩ := familySlots_has_link width rest b hrest
        exact ⟨link, hindex⟩

/-- On the computable common footprint, the selected physical link has
precisely the supplied original block index. A literal face link witnesses
the first-occurrence index only inside this equality proof; no existential
witness is eliminated into the Type-valued selected link. -/
theorem linkAt_idxOf (width : Nat) (qs : List Z4Plaq) (b : Nat)
    (hb : b ∈ familyObservableBlocks width qs) :
    (baseLinks width).idxOf
      (linkAt width b (familyObservableBlocks_lt width qs b hb)) = b := by
  have hblt := familyObservableBlocks_lt width qs b hb
  have hslots : b ∈ familySlots width qs :=
    of_decide_eq_true (List.mem_filter.mp hb).2
  obtain ⟨link, hindex⟩ := familySlots_has_link width qs b hslots
  have hidxlt : (baseLinks width).idxOf link < N width := by
    rw [← hindex]
    exact hblt
  have hget : (baseLinks width)[(baseLinks width).idxOf link]'
      hidxlt = link :=
    eq_of_beq (List.findIdx_getElem (w := hidxlt))
  have hselected : linkAt width b hblt = link := by
    subst b
    simpa only [linkAt] using hget
  rw [hselected]
  exact hindex.symm

/-- The complete signed family has zero coefficientwise angular derivative
on each block of its common spectator complement. -/
theorem spatialSpan_spectator_derivative_zero (width : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (b : Nat)
    (hb : b ∈ familySpectatorBlocks width qs)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv
      (angularDerivative (4*b+i) (4*b+j) (spatialSpan width c qs)) polyZero :=
  angularDerivative_blockIndependent_zero hi hj
    (spatialSpan_familySpectator_independent width c qs b hb)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.familySlots_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.familyObservableBlocks_length_le_four
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.faceSlot_active_after_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.familyObservableBlocks_active_after_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.linkAt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.linkAt_mem
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.linkAt_idxOf
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint.spatialSpan_spectator_derivative_zero
