/-
# Same-depth chart alignment and spatial separation of omitted faces

Increasing the recentering margin from r to r+d shifts the source chart
by d in space and 2*d in time. The selected temporal windows then agree
exactly, including the last spatial slice and the strict temporal-face
endpoint. Membership in the translated selection is therefore precisely
the translated spatial base box inside the larger selected chain.

Every omitted target face is separated from a recentered fixed base face
by at least r+1 in the actual lattice L-infinity distance. The root time
is arbitrary, and omitted temporal plaquettes are not discarded. These
are geometric inputs to a selected-action comparison, not that estimate,
an equality of states, or a spatial/continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
import YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedChain
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
import YMGap.Continuum.SepLatticeZ4Linf

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding (Placement)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedChain
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.SepLatticeZ4Linf

def chartExtent (base r H t : Nat) : Nat :=
  adjacentEvenExtent (paddedWidth base r+t+H)

def chartIds (base r H t : Nat) : List Nat :=
  chainIds (chartExtent base r H t) (paddedWidth base r)
    (paddedWidth base r+1) (t+(2*H+t))

theorem chartExtent_add (base r d H t : Nat) :
    chartExtent base (r+d) H t = chartExtent base r H t+4*d := by
  unfold chartExtent adjacentEvenExtent centralExtent paddedWidth
  omega

/-- The time shift is twice the spatial shift, so both selected windows agree. -/
theorem chart_start_shift (base r d : Nat) :
    paddedWidth base r+1+2*d = paddedWidth base (r+d)+1 := by
  unfold paddedWidth
  omega

/-- Concrete ambient placement, including the original fringe link carrier. -/
def placement (base r d H t : Nat) : Placement where
  source := chartExtent base r H t
  target := chartExtent base (r+d) H t
  space := d
  time := 2*d
  space_room := by rw [chartExtent_add]; omega
  time_room := by rw [chartExtent_add]; omega

def translatedChartIds (base r d H t : Nat) : List Nat :=
  (chartIds base r H t).map (placement base r d H t).faceId

theorem chartIds_physical {base r H t id : Nat} (hi : id ∈ chartIds base r H t) :
    id ∈ slabPhysicalFaceEdges (chartExtent base r H t) := chainIds_physical hi

theorem chartIds_nodup (base r H t : Nat) : (chartIds base r H t).Nodup :=
  chainIds_nodup _ _ _ _

/-- The actual original face named by every translated numerical ID. -/
theorem placement_faceId_pin (base r d H t : Nat) {id : Nat}
    (hi : id ∈ chartIds base r H t) :
    slabPlaquetteAt (chartExtent base (r+d) H t) ((placement base r d H t).faceId id) =
      shiftFace d (2*d) (slabPlaquetteAt (chartExtent base r H t) id) :=
  (placement base r d H t).faceId_pin (chartIds_physical hi)

theorem translatedChartIds_faces_pin (base r d H t : Nat) :
    (translatedChartIds base r d H t).map (slabPlaquetteAt (chartExtent base (r+d) H t)) =
      (chartIds base r H t).map
        (fun id => shiftFace d (2*d) (slabPlaquetteAt (chartExtent base r H t) id)) :=
  translatedIds_faces_pin (placement base r d H t).space_room
    (placement base r d H t).time_room _ _ _

/-- Every translated smaller selected face occurs in the larger selected chain. -/
theorem translatedChartIds_subset (base r d H t : Nat) {id : Nat}
    (hi : id ∈ translatedChartIds base r d H t) :
    id ∈ chartIds base (r+d) H t := by
  change id ∈ chainIds (chartExtent base (r+d) H t) (paddedWidth base (r+d))
    (paddedWidth base (r+d)+1) (t+(2*H+t))
  rw [← chart_start_shift base r d]
  exact translatedIds_subset_chain (placement base r d H t).space_room
    (placement base r d H t).time_room
    (show paddedWidth base r+d ≤ paddedWidth base (r+d) by unfold paddedWidth; omega) hi

/-- Inside the target selected chain, only the spatial base mask remains.
The time lower bound and both orientation-dependent upper bounds coincide. -/
theorem translatedChartIds_mem_iff (base r d H t : Nat) {id : Nat}
    (hi : id ∈ chartIds base (r+d) H t) :
    id ∈ translatedChartIds base r d H t ↔
      d ≤ (slabPlaquetteAt (chartExtent base (r+d) H t) id).1.1 ∧
      (slabPlaquetteAt (chartExtent base (r+d) H t) id).1.1 < paddedWidth base r+d ∧
      d ≤ (slabPlaquetteAt (chartExtent base (r+d) H t) id).1.2.1 ∧
      (slabPlaquetteAt (chartExtent base (r+d) H t) id).1.2.1 < paddedWidth base r+d ∧
      d ≤ (slabPlaquetteAt (chartExtent base (r+d) H t) id).1.2.2.1 ∧
      (slabPlaquetteAt (chartExtent base (r+d) H t) id).1.2.2.1 < paddedWidth base r+d := by
  have hw : paddedWidth base r ≤ chartExtent base r H t+1 := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hs : paddedWidth base r+1+(t+(2*H+t)) ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hraw := translatedIds_mem_iff (placement base r d H t).space_room
    (placement base r d H t).time_room hw hs id
  change (id ∈ translatedChartIds base r d H t ↔
    id ∈ slabPhysicalFaceEdges (chartExtent base (r+d) H t) ∧
      TranslatedWindow d (2*d) (paddedWidth base r) (paddedWidth base r+1)
        (t+(2*H+t)) (slabPlaquetteAt (chartExtent base (r+d) H t) id)) at hraw
  constructor
  · intro hm
    obtain ⟨ha, hau, hb, hbu, hc, hcu, _, _⟩ := (hraw.mp hm).2
    exact ⟨ha, hau, hb, hbu, hc, hcu⟩
  · intro hm
    obtain ⟨ha, hau, hb, hbu, hc, hcu⟩ := hm
    have htarget := (chainIds_mem_iff (chartExtent base (r+d) H t)
      (paddedWidth base (r+d)) (paddedWidth base (r+d)+1) (t+(2*H+t)) id).mp hi
    obtain ⟨hid, _, _, _, hl, hlast⟩ := htarget
    have hstart := chart_start_shift base r d
    apply hraw.mpr
    refine ⟨hid, ha, hau, hb, hbu, hc, hcu, by omega, ?_⟩
    rcases hlast with hsp | htemp
    · exact Or.inl ⟨hsp.1, by omega⟩
    · exact Or.inr ⟨htemp.1, by omega⟩

private theorem near_recentered_spatial_box (base r d timeOrigin : Nat)
    {p q : Z4Plaq} (hp : p ∈ spatialFaces base)
    (hd : linfDist (shiftFace (r+d+1) timeOrigin p) q < r+1) :
    d ≤ q.1.1 ∧ q.1.1 < paddedWidth base r+d ∧
    d ≤ q.1.2.1 ∧ q.1.2.1 < paddedWidth base r+d ∧
    d ≤ q.1.2.2.1 ∧ q.1.2.2.1 < paddedWidth base r+d := by
  obtain ⟨⟨a, b, c, z⟩, plane⟩ := p
  obtain ⟨⟨a', b', c', z'⟩, plane'⟩ := q
  have hbase := (spatialFaces_mem_iff base _).mp hp
  change a < base ∧ b < base ∧ c < base ∧ z = 0 ∧
    (dirsOf plane).2 ≠ Dir4.x3 at hbase
  obtain ⟨ha, hb, hc, _, _⟩ := hbase
  have h0 := Nat.lt_of_le_of_lt
    (le_linfDist_comp (shiftFace (r+d+1) timeOrigin ((a,b,c,z),plane))
      ((a',b',c',z'),plane') Dir4.x0) hd
  have h1 := Nat.lt_of_le_of_lt
    (le_linfDist_comp (shiftFace (r+d+1) timeOrigin ((a,b,c,z),plane))
      ((a',b',c',z'),plane') Dir4.x1) hd
  have h2 := Nat.lt_of_le_of_lt
    (le_linfDist_comp (shiftFace (r+d+1) timeOrigin ((a,b,c,z),plane))
      ((a',b',c',z'),plane') Dir4.x2) hd
  simp only [cPlaq, vComp, shiftFace, shiftVertex, natDist] at h0 h1 h2
  change d ≤ a' ∧ a' < paddedWidth base r+d ∧
    d ≤ b' ∧ b' < paddedWidth base r+d ∧
    d ≤ c' ∧ c' < paddedWidth base r+d
  unfold paddedWidth
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Omitted target faces are far in space, whatever their orientation or
the root's time. No temporal plaquette action factor is silently excluded. -/
theorem omitted_separation (base r d H t timeOrigin : Nat) {p : Z4Plaq}
    (hp : p ∈ spatialFaces base) {id : Nat}
    (hi : id ∈ chartIds base (r+d) H t)
    (ho : id ∉ translatedChartIds base r d H t) :
    r+1 ≤ linfDist (shiftFace (r+d+1) timeOrigin p)
      (slabPlaquetteAt (chartExtent base (r+d) H t) id) := by
  by_cases hd : r+1 ≤ linfDist (shiftFace (r+d+1) timeOrigin p)
      (slabPlaquetteAt (chartExtent base (r+d) H t) id)
  · exact hd
  · exact False.elim (ho ((translatedChartIds_mem_iff base r d H t hi).mpr
      (near_recentered_spatial_box base r d timeOrigin hp (Nat.lt_of_not_ge hd))))

#print axioms chartExtent
#print axioms chartIds
#print axioms chartExtent_add
#print axioms chart_start_shift
#print axioms placement
#print axioms translatedChartIds
#print axioms chartIds_physical
#print axioms chartIds_nodup
#print axioms placement_faceId_pin
#print axioms translatedChartIds_faces_pin
#print axioms translatedChartIds_subset
#print axioms translatedChartIds_mem_iff
#print axioms omitted_separation

end YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
