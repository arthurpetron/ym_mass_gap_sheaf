/-
# Degree of an actual fixed-spatial plaquette character

The literal slice plaquette word has degree one in each of its selected
incident physical link slots.  This is a finite transport statement for the
actual `baseLinks`/`orientedLink`/`plaquette` definitions; it adds no energy,
variance, positivity, or continuum assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
import YMGap.Continuum.BF4ExactSlabSelectedFaceFold
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (face_edge_box)
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors (spatial_face_edge)
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-- Every incident link of a selected spatial face belongs to the SAME slice carrier. -/
theorem incident_mem_baseLinks {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {l : Z4Link} (hl : l ∈ edgesOf face) :
    l ∈ baseLinks width := by
  obtain ⟨hx,hy,hz,ht,hsp⟩ := (spatialFaces_mem_iff width face).mp hf
  have hb := face_edge_box hx hy hz hl
  have he := spatial_face_edge face hsp l hl
  exact (baseLinks_mem_iff width l).mpr
    ⟨he.1, hb.1, hb.2.1, hb.2.2, he.2.trans ht⟩

private def entryDegree (link : Z4Link) (entry : OrientedBF4Link) : Nat :=
  if entry.link = link then 1 else 0

private theorem entry_degree (width : Nat) (link : Z4Link)
    (hl : link ∈ baseLinks width) {entry : OrientedBF4Link}
    (he : entry.link ∈ baseLinks width) :
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf link)
      (entryDegree link entry)
      (orientedLink width entry) := by
  unfold entryDegree orientedLink
  by_cases h : entry.link = link
  · rw [if_pos h]
    simp only [YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.link, if_pos he]
    have hvar := hasPolyQuaternionBlockDegree_coordinateVariable
      ((baseLinks width).idxOf link) ((baseLinks width).idxOf link)
    cases hr : entry.reverse
    · simpa [h, hr] using hvar
    · simpa [h, hr] using hvar.conj
  · simp only [if_neg h]
    have hidx : (baseLinks width).idxOf link ≠
        (baseLinks width).idxOf entry.link := by
      intro hh
      exact h (idxOf_injective_on_members hl he hh).symm
    have hvar := hasPolyQuaternionBlockDegree_coordinateVariable
      ((baseLinks width).idxOf entry.link) ((baseLinks width).idxOf link)
    cases hr : entry.reverse
    · simpa [YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.link,
        if_pos he, hr, hidx] using hvar
    · simpa [YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.link,
        if_pos he, hr, hidx] using hvar.conj

private theorem word_degree (width : Nat) (link : Z4Link)
    (hl : link ∈ baseLinks width) :
    ∀ (es : List OrientedBF4Link) (q : PolyQuaternion) (d : Nat),
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf link) d q →
    (∀ e, e ∈ es → e.link ∈ baseLinks width) →
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf link)
      (d + occurrenceCount link (es.map OrientedBF4Link.link))
      (es.foldl (fun p e => PolyQuaternion.mul p (orientedLink width e)) q)
  | [], _, _, h, _ => by simpa using h
  | e :: es, _, _, h, hp => by
      have he := entry_degree width link hl
        (hp e List.mem_cons_self)
      have hs := word_degree width link hl es _ _
        (h.mul he) (fun f hf => hp f (List.mem_cons_of_mem e hf))
      simpa [occurrenceCount, entryDegree, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hs

theorem plaquette_degree (width : Nat) {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {link : Z4Link}
    (hl : link ∈ edgesOf face) :
    HasPolyQuaternionBlockDegree ((baseLinks width).idxOf link) 1
      (plaquette width face) := by
  have hlink := incident_mem_baseLinks hf hl
  have hword := word_degree width link hlink
    (orientedPlaquetteBoundary face) PolyQuaternion.one 0
    ⟨hasQuaternionBlockDegree_one _, hasQuaternionBlockDegree_zero _ 0,
      hasQuaternionBlockDegree_zero _ 0, hasQuaternionBlockDegree_zero _ 0⟩
    (fun e he => incident_mem_baseLinks hf (orientedPlaquetteBoundary_link_mem_edgesOf he))
  have hcount :
      occurrenceCount link ((orientedPlaquetteBoundary face).map OrientedBF4Link.link) = 1 := by
    have he := occurrenceCount_edgesOf link face
    rw [if_pos hl] at he
    simp only [orientedPlaquetteBoundary, edgesOf, List.map_cons, List.map_nil,
      occurrenceCount] at he ⊢
    omega
  unfold plaquette
  exact HasPolyQuaternionBlockDegree.relabel
    (by rw [hcount]) hword

theorem plaquette_character_degree (width : Nat) {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {link : Z4Link}
    (hl : link ∈ edgesOf face) :
    HasQuaternionBlockDegree ((baseLinks width).idxOf link) 1
      (characterPolynomial (plaquette width face).scalar 1) := by
  simpa [characterPolynomial] using
    (plaquette_degree width hf hl).scalar.smul 2

theorem plaquette_character_head_degree (width : Nat) {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) {link : Z4Link}
    (hl : link ∈ edgesOf face) :
    HasQuaternionBlockDegree 0 1
      (reindexQuaternionPolynomial
        (headSwapBlockInvolution (List.length (baseLinks width))
          ((baseLinks width).idxOf link)
          (List.idxOf_lt_length_of_mem (incident_mem_baseLinks hf hl)))
        (characterPolynomial (plaquette width face).scalar 1)) := by
  apply blockDegree_reindex
    (headSwapBlockInvolution (List.length (baseLinks width))
      ((baseLinks width).idxOf link)
      (List.idxOf_lt_length_of_mem (incident_mem_baseLinks hf hl)))
    (Nat.lt_of_le_of_lt (Nat.zero_le _)
      (List.idxOf_lt_length_of_mem (incident_mem_baseLinks hf hl)))
    (headSwapBlockInvolution_map_zero _ _ _)
  exact plaquette_character_degree width hf hl

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree.incident_mem_baseLinks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree.plaquette_degree
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree.plaquette_character_degree
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree.plaquette_character_head_degree
