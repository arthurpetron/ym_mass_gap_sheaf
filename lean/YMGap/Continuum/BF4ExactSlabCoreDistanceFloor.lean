/-
# Pay original probe-to-exterior distance with actual core faces

The existing faithful animal decoder has L-infinity radius bounded by its
number of visited faces minus one. Applied to the proved probe-augmented
animal, it gives distance+1 <= M+|core|. The original exterior witness then
forces |core| >= distance+1-M (Nat subtraction). For a singleton carrier,
the core itself pays the entire distance, with no loss of a factor of two.

The protected-root instance uses the proved original embedded-exterior
separation, not a replacement box or an assumed metric-to-graph bridge.
-/

import YMGap.Continuum.BF4ExactSlabActiveCoreCount
import YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.BF4ExactSlabCoreDistanceFloor

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder

theorem rootedAnimal_linf_size_floor (animal : RootedConnectedAnimal z4Chain)
    (q : Z4Plaq) (hq : q ∈ animal.support) : linfDist animal.root q+1 ≤ animal.support.length := by
  have hs := rootedAnimalTourCode_decode_sameSupport animal
  have hd := z4_linf_decode_dist_floor animal.root (rootedAnimalTourCode animal) q (hs.1 q hq)
  have hn := CayleyPruferInjection.nodup_subset_length_le
    (decode z4Chain animal.root (rootedAnimalTourCode animal)) animal.support
    (decode_nodup z4Chain animal.root (rootedAnimalTourCode animal)) hs.2
  exact Nat.le_trans hd hn

theorem fixed_core_linf_size_floor {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hf : core extent links ids = ids) (id : Nat) (hi : id ∈ ids) :
    linfDist probe.animal.root (slabPlaquetteAt extent id)+1 ≤ probe.animal.support.length+ids.length := by
  have h := rootedAnimal_linf_size_floor (augmentedAnimal probe extent ids hn hphys hf) (slabPlaquetteAt extent id)
    ((augmented_mem_iff probe extent ids _).mpr (Or.inr (List.mem_map.mpr ⟨id, hi, rfl⟩)))
  exact Nat.le_trans h (augmented_length_le probe extent ids)

theorem active_core_linf_floor {extent distance : Nat} {links : List Z4Link} (probe : ProbeCarrier links)
    {keep : Nat → Bool} {ambient anchor : List Nat} (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (ha : anchor ∈ activeAnchors extent links keep ambient)
    (hsep : ∀ id, id ∈ ambient → keep id = false → distance ≤ linfDist probe.animal.root (slabPlaquetteAt extent id)) :
    distance+1 ≤ probe.animal.support.length+anchor.length := by
  obtain ⟨id, hi, ho, _⟩ := active_anchor_path ha
  have hs := (List.mem_filter.mp (List.mem_filter.mp ha).1).1
  have hf : core extent links anchor = anchor := of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2
  have hsize := fixed_core_linf_size_floor probe extent anchor ((selected_sublist hs).nodup hn)
    (fun j hj => hphys j (selected_mem hs j hj)) hf id hi
  have hd := hsep id (selected_mem hs id hi) ho
  omega

theorem boundary_core_distance_floor {half padding distance : Nat} {links : List Z4Link} (probe : ProbeCarrier links)
    {anchor : List Nat} (ha : anchor ∈ activeAnchors (centralExtent (half+padding)) links (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding))))
    (hsep : ∀ id, id ∈ exteriorIds half padding →
      distance ≤ linfDist probe.animal.root (slabPlaquetteAt (centralExtent (half+padding)) id)) :
    distance+1-probe.animal.support.length ≤ anchor.length := by
  have h := active_core_linf_floor probe (CayleyParentInj.range_nodup _) (fun _ hi => hi) ha (by
    intro id hi ho
    apply hsep id
    refine List.mem_filter.mpr ⟨hi, ?_⟩
    change Bool.not (boundaryKeep half padding id) = true
    rw [ho]
    rfl)
  omega

theorem protected_root_core_size_floor {half padding margin : Nat} {links : List Z4Link} (probe : ProbeCarrier links)
    (hr : ProtectedRoot half padding margin probe.animal.root)
    {anchor : List Nat} (ha : anchor ∈ activeAnchors (centralExtent (half+padding)) links (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding)))) :
    margin+1-probe.animal.support.length ≤ anchor.length :=
  boundary_core_distance_floor probe ha (fun _ hi => exterior_linf_floor hr hi)

end YMGap.Continuum.BF4ExactSlabCoreDistanceFloor

#print axioms YMGap.Continuum.BF4ExactSlabCoreDistanceFloor.rootedAnimal_linf_size_floor
#print axioms YMGap.Continuum.BF4ExactSlabCoreDistanceFloor.fixed_core_linf_size_floor
#print axioms YMGap.Continuum.BF4ExactSlabCoreDistanceFloor.active_core_linf_floor
#print axioms YMGap.Continuum.BF4ExactSlabCoreDistanceFloor.boundary_core_distance_floor
#print axioms YMGap.Continuum.BF4ExactSlabCoreDistanceFloor.protected_root_core_size_floor
