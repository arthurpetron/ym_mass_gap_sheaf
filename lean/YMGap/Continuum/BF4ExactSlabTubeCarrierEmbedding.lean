/-
# All sixteen tube links on the ORIGINAL carrier, with every spectator

The four ordered links on each of four time slices are distinct physical
links at every margin. Their actual slab indices construct an embedding,
then a full carrier permutation. No finite table of volume-dependent link
indices is assumed, and no remaining link is discarded.
-/

import YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion
import YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep

namespace YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

local notation "links" margin => boundaryCompleteSlabLinks (responseExtent margin)

def baseLinks : List Z4Link := (List.range 4).flatMap (sliceLinks 0)

def tubeLinks (margin : Nat) : List Z4Link := baseLinks.map (shiftLink margin margin)

private def fallback : Z4Link := ((0,0,0,0),.x0)

def sourceLink (margin i : Nat) : Z4Link := shiftLink margin margin (baseLinks.getD i fallback)

theorem baseLinks_length : baseLinks.length = 16 := rfl
theorem baseLinks_nodup : baseLinks.Nodup := by decide +kernel

theorem slice_links_physical (margin : Nat) (time : Fin 4) :
    ∀ link, link ∈ sliceLinks margin time.val → link ∈ links margin := by
  intro link hl
  rw [← slice_word_links] at hl
  apply (mem_boundaryCompleteSlabLinks_iff _ _).mpr
  refine ⟨sliceFace margin time.val, slice_physical margin time, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals simp [faceLinkA, faceLinkB, faceLinkC, faceLinkD, edgesOf]

private theorem base_physical : ∀ link, link ∈ baseLinks → link ∈ boundaryCompleteSlabLinks 3 := by
  intro link hl
  obtain ⟨time,ht,hmem⟩ := List.mem_flatMap.mp hl
  exact slice_links_physical 0 ⟨time,List.mem_range.mp ht⟩ link hmem

theorem tubeLinks_physical (margin : Nat) : ∀ link, link ∈ tubeLinks margin → link ∈ links margin := by
  intro link hl
  obtain ⟨l,hbase,rfl⟩ := List.mem_map.mp hl
  exact shiftLink_mem (by unfold responseExtent centralExtent; omega)
    (by unfold responseExtent centralExtent; omega) (base_physical l hbase)

private theorem shiftLink_injective (margin : Nat) {a b : Z4Link}
    (h : shiftLink margin margin a = shiftLink margin margin b) : a = b := by
  rcases a with ⟨⟨a0,a1,a2,a3⟩,da⟩
  rcases b with ⟨⟨b0,b1,b2,b3⟩,db⟩
  simpa only [shiftLink, shiftVertex, Prod.mk.injEq, Nat.add_right_cancel_iff] using h

theorem tubeLinks_nodup (margin : Nat) : (tubeLinks margin).Nodup :=
  nodup_map_of_injOn _ _ baseLinks_nodup (fun _ _ _ _ => shiftLink_injective margin)

def tubeEmbedding (margin : Nat) : BlockEmbedding 16 (links margin).length where
  image := (tubeLinks margin).map (fun link => (links margin).idxOf link)
  length := by rw [List.length_map, tubeLinks, List.length_map, baseLinks_length]
  nodup := nodup_map_of_injOn _ _ (tubeLinks_nodup margin)
    (fun _ ha _ hb => idxOf_injective_on_members (tubeLinks_physical margin _ ha) (tubeLinks_physical margin _ hb))
  physical := by
    intro i hi
    obtain ⟨link,hl,rfl⟩ := List.mem_map.mp hi
    exact List.idxOf_lt_length_of_mem (tubeLinks_physical margin link hl)

/-- A permutation of the entire physical carrier, not only a sixteen-link subspace. -/
def carrierEmbedding (margin : Nat) : BlockEmbedding (links margin).length (links margin).length :=
  complete (tubeEmbedding margin)

theorem carrier_size (margin : Nat) : 16 ≤ (links margin).length := source_le_target (tubeEmbedding margin)

private theorem getD_map {A B : Type} (f : A → B) (xs : List A) (a : A) (b : B) :
    ∀ i, i < xs.length → (xs.map f).getD i b = f (xs.getD i a) := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

theorem tubeEmbedding_block (margin i : Nat) (hi : i < 16) :
    (tubeEmbedding margin).block i = (links margin).idxOf (sourceLink margin i) := by
  unfold BlockEmbedding.block tubeEmbedding
  rw [getD_map _ _ fallback 0 i (by rw [tubeLinks, List.length_map, baseLinks_length]; exact hi)]
  rw [tubeLinks, getD_map _ _ fallback fallback i (by rw [baseLinks_length]; exact hi)]
  rfl

theorem carrierEmbedding_block (margin i : Nat) (hi : i < 16) :
    (carrierEmbedding margin).block i = (links margin).idxOf (sourceLink margin i) :=
  (complete_block (tubeEmbedding margin) hi).trans (tubeEmbedding_block margin i hi)

theorem sourceLink_physical (margin i : Nat) (hi : i < 16) : sourceLink margin i ∈ links margin := by
  have hb : baseLinks.getD i fallback ∈ baseLinks := by
    rw [← List.getElem_eq_getD (h := by rw [baseLinks_length]; exact hi)]
    exact List.getElem_mem _
  exact tubeLinks_physical margin _ (List.mem_map.mpr ⟨_,hb,rfl⟩)

theorem carrier_link_pin (margin i : Nat) (hi : i < 16) :
    QuaternionPrefixPolyQuaternionEqv (links margin).length
      ((carrierEmbedding margin).quaternion (PolyQuaternion.coordinateVariable i))
      (correctedSlabLinkPolynomial (responseExtent margin) (sourceLink margin i)) := by
  have h := (carrierEmbedding margin).quaternion_coordinate (Nat.lt_of_lt_of_le hi (carrier_size margin))
  rw [carrierEmbedding_block margin i hi] at h
  rw [correctedSlabLinkPolynomial_of_mem (sourceLink_physical margin i hi)]
  exact h

theorem base_link_pin (time edge : Fin 4) :
    baseLinks.getD (4*time.val+edge.val) fallback = (sliceLinks 0 time.val).getD edge.val fallback := by
  revert time edge
  decide +kernel

theorem sliceLinks_shift (margin time : Nat) :
    (sliceLinks 0 time).map (shiftLink margin margin) = sliceLinks margin time := by
  simp [sliceLinks, shiftLink, shiftVertex, Nat.add_comm]

/-- The abstract block (4*t+e) is the literal e-th plaquette link on slice t. -/
theorem sourceLink_slice (margin : Nat) (time edge : Fin 4) :
    sourceLink margin (4*time.val+edge.val) = (sliceLinks margin time.val).getD edge.val fallback := by
  unfold sourceLink
  rw [base_link_pin, ← sliceLinks_shift margin time.val,
    getD_map _ _ fallback fallback edge.val (by change edge.val < 4; exact edge.isLt)]

end YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.baseLinks
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.tubeLinks
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.sourceLink
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.baseLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.baseLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.slice_links_physical
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.tubeLinks_physical
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.tubeLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.tubeEmbedding
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.carrierEmbedding
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.carrier_size
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.tubeEmbedding_block
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.carrierEmbedding_block
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.sourceLink_physical
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.carrier_link_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.base_link_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.sliceLinks_shift
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding.sourceLink_slice
