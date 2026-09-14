/-
# The genuine bounded-degree lattice of local tagged spatial occurrences

The carrier retains the original replica and plaquette, restricted to the
already proved short-core window. Its boundary is the projected plaquette
boundary. Neighbor lists are the literal local candidates, filtered only by
membership in this fixed carrier. Every shared-link neighbor is included.
This supplies the actual bounded-degree lattice needed by the constructive
BFS/forest compiler; no graph or degree axiom is assumed.
-/

import YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents
import YMGap.Continuum.FiniteRootedForestCount

namespace YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors

local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

abbrev LocalOccurrence (margin : Nat) := {x : Occurrence // x ∈ rootCarrier margin}

instance (margin : Nat) : DecidableEq (LocalOccurrence margin) := inferInstanceAs
  (DecidableEq {x : Occurrence // x ∈ rootCarrier margin})

theorem raw_neighbor_mem (margin : Nat) (x y : Occurrence) (hy : y ∈ rootCarrier margin)
    (link : Z4Link) (hxl : link ∈ edgesOf (project x)) (hyl : link ∈ edgesOf (project y)) :
    y ∈ neighbors margin x := by
  have hlocal := (mem_cartesian_iff _ _ _).mp hy
  have ht := localFace_time margin y.2 hlocal.2
  have hn := z4_sound (project x) (project y) link (decide_eq_true hxl) (decide_eq_true hyl)
  apply (mem_cartesian_iff _ _ _).mpr
  refine ⟨hlocal.1,?_⟩
  apply List.mem_map.mpr
  refine ⟨(y.2.1.2.2.2-(margin-33),project y),
    (mem_cartesian_iff _ _ _).mpr ⟨List.mem_range.mpr ht.2,hn⟩,?_⟩
  change faceAt (margin-33+(y.2.1.2.2.2-(margin-33))) (faceAt 0 y.2)=y.2
  rw [faceAt_twice,show margin-33+(y.2.1.2.2.2-(margin-33))=y.2.1.2.2.2 by omega,faceAt_own]

def localTest (margin : Nat) (y : Occurrence) : Bool := decide (y ∈ rootCarrier margin)

theorem localTest_sound {margin : Nat} {y : Occurrence} (h : localTest margin y=true) :
    y ∈ rootCarrier margin := of_decide_eq_true h

def localCandidates (margin : Nat) (x : Occurrence) : List Occurrence :=
  (neighbors margin x).filter (localTest margin)

theorem candidate_local {margin : Nat} {x y : Occurrence}
    (hy : y ∈ localCandidates margin x) : y ∈ rootCarrier margin := by
  have hfilter : y ∈ neighbors margin x ∧ localTest margin y=true := List.mem_filter.mp hy
  exact localTest_sound hfilter.2

def localNeighbors (margin : Nat) (x : LocalOccurrence margin) : List (LocalOccurrence margin) :=
  (localCandidates margin x.val).attach.map
    (fun y => (⟨y.val,candidate_local y.property⟩ : LocalOccurrence margin))

theorem localNeighbors_length_le (margin : Nat) (x : LocalOccurrence margin) :
    (localNeighbors margin x).length ≤ 3216 := by
  rw [localNeighbors,List.length_map,List.length_attach,localCandidates]
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (neighbors_length margin x.val))

def occurrenceLattice (margin : Nat) : Lattice where
  Link := Z4Link
  Plaquette := LocalOccurrence margin
  boundary := fun x link => z4Boundary (project x.val) link

theorem localNeighbors_complete (margin : Nat) (x y : LocalOccurrence margin)
    (adj : (occurrenceLattice margin).Adjacent x y) : y ∈ localNeighbors margin x := by
  have hraw := raw_neighbor_mem margin x.val y.val y.property adj.link
    (of_decide_eq_true adj.on_p) (of_decide_eq_true adj.on_q)
  have hfiltered : y.val ∈ localCandidates margin x.val :=
    List.mem_filter.mpr ⟨hraw,decide_eq_true y.property⟩
  apply List.mem_map.mpr
  exact ⟨⟨y.val,hfiltered⟩,List.mem_attach _ _,Subtype.ext rfl⟩

def boundedLattice (margin : Nat) : BddLattice where
  toLattice := occurrenceLattice margin
  decEq := inferInstanceAs (DecidableEq (LocalOccurrence margin))
  nbrs := localNeighbors margin
  D := 3216
  deg_le := localNeighbors_length_le margin
  adjacent_mem_nbrs := localNeighbors_complete margin

def rootPool (margin : Nat) : List (LocalOccurrence margin) := (rootCarrier margin).attach

theorem rootPool_complete (margin : Nat) (x : LocalOccurrence margin) : x ∈ rootPool margin :=
  List.mem_attach _ _

theorem rootPool_length_le (margin : Nat) : (rootPool margin).length ≤ 241813452 := by
  rw [rootPool,List.length_attach]
  exact rootCarrier_length_le margin

theorem local_forest_carrier_bound (margin S : Nat) :
    (FiniteRootedForestCount.carrier (rootPool margin) (boundedLattice margin).D S).length ≤ 7200000^S := by
  apply FiniteRootedForestCount.carrier_length_le (rootPool margin) 3216 900000 S (by decide)
  exact Nat.le_trans (Nat.mul_le_mul_right 3216 (rootPool_length_le margin)) (by decide)

end YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice

#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.raw_neighbor_mem
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.localTest
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.localTest_sound
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.localCandidates
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.candidate_local
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.localNeighbors
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.localNeighbors_length_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.occurrenceLattice
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.localNeighbors_complete
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.boundedLattice
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.rootPool
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.rootPool_complete
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.rootPool_length_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice.local_forest_carrier_bound
