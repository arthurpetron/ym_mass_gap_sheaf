/-
# Original spatial occurrences have distinct, locally enumerated neighbors

An occurrence retains its replica tag and its complete original plaquette,
including time. The occurrence list is duplicate-free although its projection
need not be. Even projected incidence selects a DISTINCT occurrence across
each projected boundary link. On an original short pair all such neighbors
are in an explicit list of 2*67*24 = 3216 candidates, and all roots lie in a
list of size at most 2*shortFaceCapacity, independently of cutoff and margin.

These are necessary geometric inputs to a forest count, not that count or
an aggregate signed-remainder estimate. No source occurrence is discarded.
-/

import YMGap.Continuum.FiniteEvenIncidenceNeighbor
import YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle
import YMGap.Continuum.BF4ExactSlabTwoCapLocalCode

namespace YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle
open YMGap.Continuum.PairedPositiveFaceLabellings

local infix:50 " ≈ " => Q'.eqv
local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

abbrev Occurrence := Bool × Z4Plaq

def occurrences (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : List Occurrence :=
  (spatialOddFaces margin pair.1).map (fun f => (false,f)) ++
    (spatialOddFaces margin pair.2).map (fun f => (true,f))

def project (x : Occurrence) : Z4Plaq := faceAt 0 x.2

theorem occurrences_length (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (occurrences margin pair).length = pairSpatial margin pair := by
  simp only [occurrences,List.length_append,List.length_map,pairSpatial]

theorem occurrences_nodup (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (occurrences margin pair).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_,?_,?_⟩
  · exact nodup_map_of_injOn _ _ ((oddFaces_nodup _ _).filter _)
      (fun _ _ _ _ he => congrArg Prod.snd he)
  · exact nodup_map_of_injOn _ _ ((oddFaces_nodup _ _).filter _)
      (fun _ _ _ _ he => congrArg Prod.snd he)
  · intro x hx y hy he
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hx
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hy
    have ht := congrArg Prod.fst (ha.trans (he.trans hb.symm))
    contradiction

theorem occurrences_project (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (occurrences margin pair).map project = projectedFaces margin pair := by
  simp only [occurrences,projectedFaces,spatialList,List.map_append,List.map_map,project,
    Function.comp_def]

theorem incidence_filter_length (link : Z4Link) : ∀ xs : List Occurrence,
    (xs.filter (fun x => z4Boundary (project x) link)).length =
      faceIncidenceCount link (xs.map project)
  | [] => rfl
  | x::xs => by
    by_cases hh : link ∈ edgesOf (project x)
    · simp only [List.filter_cons,z4Boundary,hh,decide_true,↓reduceIte,
        List.length_cons,List.map_cons,faceIncidenceCount]
      have ih := incidence_filter_length link xs
      change (xs.filter (fun x => decide (link ∈ edgesOf (project x)))).length = _ at ih
      rw [ih]
      omega
    · simp only [List.filter_cons,z4Boundary,hh,decide_false,Bool.false_eq_true,↓reduceIte,
        List.map_cons,faceIncidenceCount,Nat.zero_add]
      exact incidence_filter_length link xs

def original_neighbor (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (x : Occurrence) (hx : x ∈ occurrences margin pair)
    (link : Z4Link) (hl : link ∈ edgesOf (project x)) :
    Σ' y : Occurrence, y ∈ occurrences margin pair ∧ y ≠ x ∧ link ∈ edgesOf (project y) := by
  have heven : ((occurrences margin pair).filter
      (fun y => z4Boundary (project y) link)).length % 2 = 0 := by
    rw [incidence_filter_length,occurrences_project]
    exact original_projectedFaces_closed margin pair hne link
  let selected := FiniteEvenIncidenceNeighbor.neighbor (occurrences margin pair)
    (fun y => z4Boundary (project y) link) (occurrences_nodup margin pair) x hx
    (decide_eq_true hl) heven
  exact ⟨selected.1,selected.2.1,selected.2.2.1,of_decide_eq_true selected.2.2.2⟩

theorem occurrence_face_mem {margin : Nat} {pair : EdgeLabelling × EdgeLabelling}
    {x : Occurrence} (hx : x ∈ occurrences margin pair) : x.2 ∈ spatialList margin pair := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_left _ hf
  · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_right _ hf

def rootCarrier (margin : Nat) : List Occurrence := cartesian [false,true] (localFaces margin)

theorem rootCarrier_length_le (margin : Nat) :
    (rootCarrier margin).length ≤ 2*shortFaceCapacity := by
  rw [rootCarrier,cartesian_length,localFaces,List.length_map]
  exact Nat.mul_le_mul_left 2 (shortNearbyIds_length_le margin)

theorem original_occurrence_local {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (x : Occurrence) (hx : x ∈ occurrences margin pair) : x ∈ rootCarrier margin := by
  apply (mem_cartesian_iff _ _ _).mpr
  refine ⟨?_,spatialList_local hs hp x.2 (occurrence_face_mem hx)⟩
  cases x.1 <;> simp only [List.mem_cons,true_or,or_true]

def neighbors (margin : Nat) (x : Occurrence) : List Occurrence :=
  cartesian [false,true] ((cartesian (List.range 67) (z4Nbrs (project x))).map
    (fun tf => faceAt (margin-33+tf.1) tf.2))

theorem neighbors_length (margin : Nat) (x : Occurrence) :
    (neighbors margin x).length = 3216 := by
  rw [neighbors,cartesian_length,List.length_map,cartesian_length,List.length_range,z4Nbrs_length]
  rfl

theorem original_neighbor_mem {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (x y : Occurrence) (hy : y ∈ occurrences margin pair)
    (link : Z4Link) (hxlink : link ∈ edgesOf (project x))
    (hylink : link ∈ edgesOf (project y)) : y ∈ neighbors margin x := by
  have hlocal := spatialList_local hs hp y.2 (occurrence_face_mem hy)
  have ht := localFace_time margin y.2 hlocal
  have hn := z4_sound (project x) (project y) link (decide_eq_true hxlink) (decide_eq_true hylink)
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · cases y.1 <;> simp only [List.mem_cons,true_or,or_true]
  · apply List.mem_map.mpr
    refine ⟨(y.2.1.2.2.2-(margin-33),project y),
      (mem_cartesian_iff _ _ _).mpr ⟨List.mem_range.mpr ht.2,hn⟩,?_⟩
    change faceAt (margin-33+(y.2.1.2.2.2-(margin-33))) (faceAt 0 y.2)=y.2
    rw [faceAt_twice,show margin-33+(y.2.1.2.2.2-(margin-33))=y.2.1.2.2.2 by omega,
      faceAt_own]

def original_local_neighbor {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (x : Occurrence) (hx : x ∈ occurrences margin pair) :
    Σ' y : Occurrence, y ∈ occurrences margin pair ∧ y ≠ x ∧ y ∈ neighbors margin x := by
  let link : Z4Link := ((project x).1,(dirsOf (project x).2).1)
  have hl : link ∈ edgesOf (project x) := List.mem_cons_self
  let selected := original_neighbor margin pair hne x hx link hl
  exact ⟨selected.1,selected.2.1,selected.2.2.1,
    original_neighbor_mem hs hp x selected.1 selected.2.1 link hl selected.2.2.2⟩

end YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors

#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.occurrences
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.occurrences_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.occurrences_nodup
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.occurrences_project
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.incidence_filter_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.original_neighbor
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.occurrence_face_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.rootCarrier
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.rootCarrier_length_le
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.original_occurrence_local
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.neighbors
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.neighbors_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.original_neighbor_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors.original_local_neighbor
