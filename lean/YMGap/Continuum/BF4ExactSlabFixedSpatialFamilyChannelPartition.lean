/-
# One common active footprint for an entire signed spatial plaquette family

The active blocks are the union of the literal edge slots of every face in
the family. The complementary spectator list is formed once on the complete
slice carrier. In particular, repeated faces and arbitrary signed coefficients
do not turn this into a sum of one-face channel comparisons.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (characterFace_independent_index)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
  (faceSlots faceSlot_mem)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyAdd
    quaternionBlockIndependent_polySmul)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks plaquette

/-- All face-edge slots, with repetitions allowed in this bookkeeping list. -/
def familySlots (width : Nat) : List Z4Plaq → List Nat
  | [] => []
  | face :: qs => faceSlots width face ++ familySlots width qs

/-- The common active footprint, deduplicated by filtering the full carrier. -/
def familyObservableBlocks (width : Nat) (qs : List Z4Plaq) : List Nat :=
  (List.range (N width)).filter (fun i => decide (i ∈ familySlots width qs))

/-- Every retained block untouched by every member of the family. -/
def familySpectatorBlocks (width : Nat) (qs : List Z4Plaq) : List Nat :=
  (List.range (N width)).filter (fun i => !decide (i ∈ familySlots width qs))

theorem familyObservableBlocks_lt (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hi : i ∈ familyObservableBlocks width qs) : i < N width :=
  List.mem_range.mp (List.mem_filter.mp hi).1

theorem familySpectatorBlocks_lt (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hi : i ∈ familySpectatorBlocks width qs) : i < N width :=
  List.mem_range.mp (List.mem_filter.mp hi).1

theorem familyObservableBlocks_nodup (width : Nat) (qs : List Z4Plaq) :
    (familyObservableBlocks width qs).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))

theorem familySpectatorBlocks_nodup (width : Nat) (qs : List Z4Plaq) :
    (familySpectatorBlocks width qs).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))

theorem familySpectator_not_slots (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hi : i ∈ familySpectatorBlocks width qs) : i ∉ familySlots width qs := by
  have h := (List.mem_filter.mp hi).2
  intro hm
  simp [hm] at h

theorem familySpectator_not_observable (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hs : i ∈ familySpectatorBlocks width qs) :
    i ∉ familyObservableBlocks width qs := by
  intro ho
  have hs' := (List.mem_filter.mp hs).2
  have ho' := (List.mem_filter.mp ho).2
  simp_all

theorem familySpectator_observable_cover (width : Nat) (qs : List Z4Plaq) :
    (familySpectatorBlocks width qs ++ familyObservableBlocks width qs).Perm
      (List.range (N width)) := by
  simpa only [familySpectatorBlocks, familyObservableBlocks, Bool.not_not] using
    (List.filter_append_perm
      (fun i => !decide (i ∈ familySlots width qs)) (List.range (N width)))

theorem faceSlot_mem_familySlots (width : Nat) :
    ∀ (qs : List Z4Plaq) (face : Z4Plaq), face ∈ qs →
      ∀ (i : Nat), i ∈ faceSlots width face → i ∈ familySlots width qs
  | [], _, hface, _, _ => False.elim (List.not_mem_nil hface)
  | first :: rest, face, hface, i, hi => by
      rcases List.mem_cons.mp hface with hfirst | hrest
      · subst face
        exact List.mem_append.mpr (Or.inl hi)
      · exact List.mem_append.mpr
          (Or.inr (faceSlot_mem_familySlots width rest face hrest i hi))

private theorem spatialSpan_independent_of_not_slots (width : Nat)
    (c : Z4Plaq → Q') : ∀ (qs : List Z4Plaq) (i : Nat),
      i < N width → i ∉ familySlots width qs →
      QuaternionBlockIndependent i (spatialSpan width c qs)
  | [], _, _, _ => by
      intro term ht
      exact False.elim (List.not_mem_nil ht)
  | face :: qs, i, hi, hnot => by
      have hnotFace : i ∉ faceSlots width face := by
        intro hm
        exact hnot (List.mem_append.mpr (Or.inl hm))
      have hnotTail : i ∉ familySlots width qs := by
        intro hm
        exact hnot (List.mem_append.mpr (Or.inr hm))
      change QuaternionBlockIndependent i (polyAdd
        (polySmul (c face) (characterPolynomial (plaquette width face).scalar 1))
        (spatialSpan width c qs))
      apply quaternionBlockIndependent_polyAdd
      · apply quaternionBlockIndependent_polySmul
        apply characterFace_independent_index width face i 1 hi
        intro l hl _ heq
        apply hnotFace
        rw [← heq]
        exact faceSlot_mem width face hl
      · exact spatialSpan_independent_of_not_slots width c qs i hi hnotTail

/-- The complete signed family, including repetitions, omits every block
outside the union of its literal face supports. -/
theorem spatialSpan_familySpectator_independent (width : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (i : Nat)
    (hi : i ∈ familySpectatorBlocks width qs) :
    QuaternionBlockIndependent i (spatialSpan width c qs) :=
  spatialSpan_independent_of_not_slots width c qs i
    (familySpectatorBlocks_lt width qs i hi)
    (familySpectator_not_slots width qs i hi)

#print axioms spatialSpan_familySpectator_independent

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
