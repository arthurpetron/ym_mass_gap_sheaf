/-
# The original short-core replicas live in a volume-independent region

The existing literal two-probe animal and its faithful radius theorem
put every original 12..32-face core within radius 33 of the lower probe.
Its physical face indices form a duplicate-free sublist with at most
6*67^4 entries, independently of margin and cutoff. Both original replica
labelings vanish outside it. No count of labelings or weighted sum is
inferred from this finite support localization alone.
-/

import YMGap.Continuum.Z4LinfFiniteRegion
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
import YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow

namespace YMGap.Continuum.BF4ExactSlabShortCoreLocalization

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4LinfFiniteRegion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabTwoProbeAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (singletonCarrier)
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion (selected_nodup)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FinitePolynomialSubsetExpansion

def nearbyIds (extent : Nat) (root : Z4Plaq) (radius : Nat) : List Nat :=
  (slabPhysicalFaceEdges extent).filter (fun id => decide (linfDist root (slabPlaquetteAt extent id) ≤ radius))

theorem nearbyIds_physical {extent radius id : Nat} {root : Z4Plaq}
    (hi : id ∈ nearbyIds extent root radius) : id ∈ slabPhysicalFaceEdges extent :=
  (List.mem_filter.mp hi).1

theorem nearbyIds_nodup (extent : Nat) (root : Z4Plaq) (radius : Nat) :
    (nearbyIds extent root radius).Nodup := (CayleyParentInj.range_nodup _).filter _

theorem nearbyIds_length_le (extent : Nat) (root : Z4Plaq) (radius : Nat) :
    (nearbyIds extent root radius).length ≤ ((2*radius+1)*(2*radius+1)*(2*radius+1)*(2*radius+1))*6 := by
  have hn := CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent)
    (nearbyIds extent root radius) (nearbyIds_nodup extent root radius)
    (fun _ ha _ hb he => slabPlaquetteAt_injective_on_physical (nearbyIds_physical ha) (nearbyIds_physical hb) he)
  have hc := CayleyPruferInjection.nodup_subset_length_le
    ((nearbyIds extent root radius).map (slabPlaquetteAt extent)) (region root radius) hn (by
      intro face hf
      obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
      exact mem_region_of_linf root _ radius (of_decide_eq_true (List.mem_filter.mp hi).2))
  rw [List.length_map, region_length] at hc
  exact hc

theorem shortOtherCores_connecting {threshold margin : Nat} {ids : List Nat}
    (hi : ids ∈ shortOtherCores threshold margin) :
    ids ∈ connectingAnchors (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) :=
  (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp hi).1).1).1

theorem short_core_radius {margin : Nat} {ids : List Nat}
    (hs : ids ∈ shortOtherCores 33 margin) (id : Nat) (hi : id ∈ ids) :
    linfDist (sliceFace margin 0) (slabPlaquetteAt (responseExtent margin) id) ≤ 33 := by
  have hc := shortOtherCores_connecting hs
  have hn := selected_nodup (CayleyParentInj.range_nodup _) (connecting_selected hc)
  have hphys := fun j hj => selected_mem (connecting_selected hc) j hj
  let P := singletonCarrier (sliceFace margin 0)
  let Q := singletonCarrier (sliceFace margin 3)
  have h := rootedAnimal_linf_size_floor
    (augmentedAnimal P Q (responseExtent margin) ids hn hphys (connecting_keep hc) (connecting_fixed hc))
    (slabPlaquetteAt (responseExtent margin) id)
    ((augmented_mem P Q (responseExtent margin) ids _).mpr (Or.inr (List.mem_map.mpr ⟨id,hi,rfl⟩)))
  have hb := Nat.le_trans h (augmented_size_le P Q (responseExtent margin) ids)
  change linfDist (sliceFace margin 0) (slabPlaquetteAt (responseExtent margin) id)+1 ≤ 1+1+ids.length at hb
  have hsize := (shortOtherCores_window hs).2.1
  omega

def shortNearbyIds (margin : Nat) : List Nat := nearbyIds (responseExtent margin) (sliceFace margin 0) 33

def shortFaceCapacity : Nat := 120906726

theorem shortNearbyIds_length_le (margin : Nat) : (shortNearbyIds margin).length ≤ shortFaceCapacity :=
  nearbyIds_length_le (responseExtent margin) (sliceFace margin 0) 33

theorem shortNearbyIds_nodup (margin : Nat) : (shortNearbyIds margin).Nodup :=
  nearbyIds_nodup (responseExtent margin) (sliceFace margin 0) 33

theorem short_core_subset {margin : Nat} {ids : List Nat}
    (hs : ids ∈ shortOtherCores 33 margin) (id : Nat) (hi : id ∈ ids) : id ∈ shortNearbyIds margin :=
  List.mem_filter.mpr ⟨selected_mem (connecting_selected (shortOtherCores_connecting hs)) id hi,
    decide_eq_true (short_core_radius hs id hi)⟩

/-- Original labels, including all nonphysical indices, are zero off the local list. -/
theorem short_pair_outside {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (id : Nat) (hi : id ∉ shortNearbyIds margin) : pair.1 id = 0 ∧ pair.2 id = 0 :=
  outside K ids pair hp id (fun hid => hi (short_core_subset hs id hid))

end YMGap.Continuum.BF4ExactSlabShortCoreLocalization

#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.nearbyIds
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.nearbyIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.nearbyIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.nearbyIds_length_le
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.shortOtherCores_connecting
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.short_core_radius
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.shortNearbyIds
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.shortFaceCapacity
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.shortNearbyIds_length_le
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.shortNearbyIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.short_core_subset
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreLocalization.short_pair_outside
