/-
# Active and spectator channels for one literal spatial plaquette

The channel split is a Boolean partition of the complete fixed-width slice
carrier.  The source remains arbitrary; only the plaquette insertion is
shown independent of spectator blocks.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (characterFace_independent_index)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- The physical block slots touched by the selected face. -/
def faceSlots (width : Nat) (face : Z4Plaq) : List Nat :=
  (edgesOf face).map (fun l => (baseLinks width).idxOf l)

/-- The complete-carrier filter selecting the four-or-fewer face slots. -/
def observableBlocks (width : Nat) (face : Z4Plaq) : List Nat :=
  (List.range (N width)).filter (fun i => decide (i ∈ faceSlots width face))

/-- The complementary complete-carrier filter. -/
def spectatorBlocks (width : Nat) (face : Z4Plaq) : List Nat :=
  (List.range (N width)).filter (fun i => !decide (i ∈ faceSlots width face))

theorem observableBlocks_lt (width : Nat) (face : Z4Plaq) (i : Nat)
    (hi : i ∈ observableBlocks width face) : i < N width := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

theorem spectatorBlocks_lt (width : Nat) (face : Z4Plaq) (i : Nat)
    (hi : i ∈ spectatorBlocks width face) : i < N width := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

theorem spectator_not_observable (width : Nat) (face : Z4Plaq) (i : Nat)
    (hs : i ∈ spectatorBlocks width face) :
    i ∉ observableBlocks width face := by
  intro ho
  have hs' := (List.mem_filter.mp hs).2
  have ho' := (List.mem_filter.mp ho).2
  simp_all

theorem faceSlot_mem (width : Nat) (face : Z4Plaq) {l : Z4Link}
    (hl : l ∈ edgesOf face) :
    (baseLinks width).idxOf l ∈ faceSlots width face := by
  exact List.mem_map.mpr ⟨l, hl, rfl⟩

theorem spectator_observable_cover (width : Nat) (face : Z4Plaq) :
    (spectatorBlocks width face ++ observableBlocks width face).Perm
      (List.range (N width)) := by
  simpa only [spectatorBlocks, observableBlocks, Bool.not_not] using
    (List.filter_append_perm
      (fun i => !decide (i ∈ faceSlots width face)) (List.range (N width)))

theorem plaquette_spectator_independent (width : Nat) (face : Z4Plaq) (i : Nat)
    (hi : i ∈ spectatorBlocks width face) :
    QuaternionBlockIndependent i
      (characterPolynomial (plaquette width face).scalar 1) := by
  apply characterFace_independent_index width face i 1
    (spectatorBlocks_lt width face i hi)
  intro l hl hlbase heq
  have hslot : (baseLinks width).idxOf l ∈ faceSlots width face :=
    faceSlot_mem width face hl
  have hobs : i ∈ observableBlocks width face := by
    apply List.mem_filter.mpr
    have hslot_i : i ∈ faceSlots width face := by
      simpa [heq] using hslot
    exact ⟨by
      exact (List.mem_filter.mp (show i ∈ spectatorBlocks width face from hi)).1,
      by simp [hslot_i]⟩
  exact False.elim (spectator_not_observable width face i hi hobs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition.observableBlocks_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition.spectatorBlocks_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition.spectator_not_observable
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition.spectator_observable_cover
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition.plaquette_spectator_independent
