/-
# The four ORIGINAL crossing faces over a translated plaquette probe

At every half-size, the four selected face IDs are literal translations of
the extent-one IDs 2,4,20,40. Their exposed links are exactly the four probe
links, and no other central crossing face exposes those links. The lower
action splits into a detached spectator region and at most 24 collar faces.
These are geometric statements, with no coupling or representation cutoff.
They do not assert a positive interacting or thermodynamic centered norm.
-/

import YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
import YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
import YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding

namespace YMGap.Continuum.BF4ExactSlabBulkProbeInterface

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound

def translatedId (half id : Nat) : Nat := shiftFaceId 1 (centralExtent half) half half id

theorem source_room (half : Nat) : 1+half ≤ centralExtent half := by
  unfold centralExtent
  omega

theorem translatedId_physical {half id : Nat} (hi : id ∈ slabPhysicalFaceEdges 1) :
    translatedId half id ∈ slabPhysicalFaceEdges (centralExtent half) :=
  shiftFaceId_physical (source_room half) (source_room half) hi

theorem translatedId_pin {half id : Nat} (hi : id ∈ slabPhysicalFaceEdges 1) :
    slabPlaquetteAt (centralExtent half) (translatedId half id) =
      shiftFace half half (slabPlaquetteAt 1 id) :=
  shiftFaceId_pin (source_room half) (source_room half) hi

theorem translated_side (half : Nat) (p : Z4Plaq) :
    plaquetteHalfSide half (shiftFace half half p) = plaquetteHalfSide 0 p := by
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := p
  cases t with
  | zero =>
      cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide,
        shiftFace, shiftVertex, Nat.zero_add, Nat.le_refl, Nat.lt_irrefl, ↓reduceIte]
  | succ t =>
      have hle : ¬ t+1+half ≤ half := by omega
      have hlt : ¬ t+1+half < half := by omega
      have heq : t+1+half ≠ half := by omega
      have hzero : ¬ t+1 ≤ 0 := by omega
      cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide,
        shiftFace, shiftVertex, hle, hlt, heq, hzero,
        Nat.not_lt_zero, Nat.succ_ne_zero, ↓reduceIte]

theorem translatedId_fixed {half id : Nat} (hi : id ∈ centralFixedFaceIds 0) :
    translatedId half id ∈ centralFixedFaceIds half := by
  have hp := (mem_centralFixedFaceIds.mp hi).1
  apply mem_centralFixedFaceIds.mpr
  refine ⟨translatedId_physical hp, ?_⟩
  rw [translatedId_pin hp, translated_side]
  exact (mem_centralFixedFaceIds.mp hi).2

def probeFace (half : Nat) : Z4Plaq := shiftFace half half (slabPlaquetteAt 1 0)
def probeLinks (half : Nat) : List Z4Link := edgesOf (probeFace half)
def crossingIds (half : Nat) : List Nat := [2,4,20,40].map (translatedId half)

theorem source_crossing_fixed {id : Nat} (hi : id ∈ [2,4,20,40]) :
    id ∈ centralFixedFaceIds 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> decide

theorem crossingIds_fixed {half id : Nat} (hi : id ∈ crossingIds half) :
    id ∈ centralFixedFaceIds half := by
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hi
  exact translatedId_fixed (source_crossing_fixed hs)

theorem crossingIds_nodup (half : Nat) : (crossingIds half).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _ (by decide)
    (fun _ hi _ hj he => shiftFaceId_injective (source_room half) (source_room half)
      (mem_centralFixedFaceIds.mp (source_crossing_fixed hi)).1
      (mem_centralFixedFaceIds.mp (source_crossing_fixed hj)).1 he)

theorem crossingIds_length (half : Nat) : (crossingIds half).length = 4 := by
  simp only [crossingIds, List.length_map, List.length_cons, List.length_nil]

theorem exposed_shift (space time : Nat) (p : Z4Plaq) :
    faceLinkA (shiftFace space time p) = shiftLink space time (faceLinkA p) := rfl

theorem crossingIds_links (half : Nat) :
    (crossingIds half).map (fun id => faceLinkA (slabPlaquetteAt (centralExtent half) id)) =
      probeLinks half := by
  have hsource : [2,4,20,40].map (fun id => faceLinkA (slabPlaquetteAt 1 id)) =
      edgesOf (slabPlaquetteAt 1 0) := by decide
  unfold crossingIds probeLinks probeFace
  rw [edgesOf_shiftFace, ← hsource, List.map_map, List.map_map]
  apply List.map_congr_left
  intro id hi
  change faceLinkA (slabPlaquetteAt (centralExtent half) (translatedId half id)) =
    shiftLink half half (faceLinkA (slabPlaquetteAt 1 id))
  rw [translatedId_pin (mem_centralFixedFaceIds.mp (source_crossing_fixed hi)).1, exposed_shift]

theorem probeLinks_length (half : Nat) : (probeLinks half).length = 4 := rfl

/-- Exact selection criterion: no spectator crossing face has a probe link. -/
theorem crossingIds_iff_exposed {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    id ∈ crossingIds half ↔ faceLinkA (slabPlaquetteAt (centralExtent half) id) ∈ probeLinks half := by
  rw [← crossingIds_links]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨id, h, rfl⟩
  · intro h
    obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hjf := crossingIds_fixed hj
    have hjid := slabPlaquetteAt_injective_on_physical
      (mem_centralFixedFaceIds.mp hjf).1 (mem_centralFixedFaceIds.mp hi).1
      (fixed_face_eq_of_exposed_eq (mem_centralFixedFaceIds.mp hjf).2
        (mem_centralFixedFaceIds.mp hi).2 he)
    simpa only [hjid] using hj

theorem spectator_exposed_not_mem {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (hs : id ∉ crossingIds half) :
    faceLinkA (slabPlaquetteAt (centralExtent half) id) ∉ probeLinks half :=
  fun h => hs ((crossingIds_iff_exposed hi).mpr h)

def lowerCollar (half : Nat) : List Nat :=
  collarIds (centralExtent half) (probeLinks half) [] (centralLowerFaceIds half)

def lowerSpectators (half : Nat) : List Nat :=
  detachedIds (centralExtent half) (probeLinks half) [] (centralLowerFaceIds half)

theorem lower_partition (half : Nat) :
    (lowerCollar half ++ lowerSpectators half).Perm (centralLowerFaceIds half) :=
  region_partition _ _ _ _

theorem lowerCollar_length_le (half : Nat) : (lowerCollar half).length ≤ 24 := by
  have h := collarIds_length_le (centralExtent half) (probeLinks half) [] (centralLowerFaceIds half)
    (BF4ExactSlabBoundaryCutoffRecoding.lowerFaceIds_nodup half)
    (fun _ hi => (mem_centralLowerFaceIds.mp hi).1)
  simpa only [probeLinks_length, List.length_nil] using h

theorem lowerSpectators_disjoint (half : Nat) :
    LinksDisjoint (probeLinks half) (faceLinks (centralExtent half) (lowerSpectators half)) := by
  have h := detached_disjoint (centralExtent half) (probeLinks half) [] (centralLowerFaceIds half)
  simpa only [faceLinks, List.flatMap_nil, List.append_nil] using h

end YMGap.Continuum.BF4ExactSlabBulkProbeInterface

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.source_room
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.translatedId_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.translatedId_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.translated_side
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.translatedId_fixed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.source_crossing_fixed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.crossingIds_fixed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.crossingIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.crossingIds_length
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.exposed_shift
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.crossingIds_links
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.probeLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.crossingIds_iff_exposed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.spectator_exposed_not_mem
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.lower_partition
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.lowerCollar_length_le
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterface.lowerSpectators_disjoint
