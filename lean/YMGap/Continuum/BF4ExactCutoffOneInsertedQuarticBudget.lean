/-
# Literal inserted cutoff-one local degree and quartic-location budget

For at most two inner24 insertion occurrences, closed affine parity produces
total raw-link degrees 0, 2 or 4. Every degree-four link occurs on an insertion
boundary. The actual degree-four list has length at most eight, and at most
four for a repeated face. Original action weights and repeated polynomial
factors remain those of the imported literal integrand.

This does not bound intermediate contraction sizes or evaluate charged Haar
values, and supplies no scaling, retention or Clay closure.
-/

import YMGap.Continuum.BF4ExactCutoffOneInsertedActiveCarrier

namespace YMGap.Continuum.BF4ExactCutoffOneInsertedQuarticBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneInsertedActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneInsertedDegree
open YMGap.Continuum.BF4ExactCutoffOneInsertedMask
open YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
  (boundaryCompleteSlabPlaquettes boundaryCompleteSlabLinks)

/-- Literal selected-action ceiling: every actual inner24 face is selected. -/
def innerFaceCeiling : EdgeLabelling :=
  fun id => if id ∈ activeHypercubeSlabFaceIds then 1 else 0

/-- Small certificate on the actual 116 raw links and original 72-face list. -/
theorem innerFaceCeiling_degree_check :
    (List.range 116).all (fun block =>
      decide (cutoffOneSlabSelectedBlockDegree block innerFaceCeiling ≤ 3)) =
        true := by
  decide +kernel

theorem innerFaceCeiling_degree_le_three (block : Nat) (hb : block < 116) :
    cutoffOneSlabSelectedBlockDegree block innerFaceCeiling ≤ 3 :=
  of_decide_eq_true (List.all_eq_true.mp innerFaceCeiling_degree_check
    block (List.mem_range.mpr hb))

private theorem inner_id_lt (id : Nat)
    (hi : id ∈ activeHypercubeSlabFaceIds) : id < 72 :=
  of_decide_eq_true
    (List.all_eq_true.mp activeHypercubeSlabFaceIds_spec.2.2 id hi)

private theorem selected_degree_mono (block : Nat)
    (physical : EdgeLabelling) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces →
        physical ((boundaryCompleteSlabPlaquettes 1).idxOf face) ≤
          innerFaceCeiling ((boundaryCompleteSlabPlaquettes 1).idxOf face)) →
      cutoffOneFacesSelectedBlockDegree block physical faces ≤
        cutoffOneFacesSelectedBlockDegree block innerFaceCeiling faces
  | [], _ => Nat.le_refl 0
  | face :: rest, hfaces => by
      simp only [cutoffOneFacesSelectedBlockDegree]
      exact Nat.add_le_add
        (Nat.mul_le_mul_right _ (hfaces face List.mem_cons_self))
        (selected_degree_mono block physical rest
          (fun other ho => hfaces other (List.mem_cons_of_mem face ho)))

/-- The ceiling is produced from affine support of the ORIGINAL action. -/
theorem affine_selected_degree_le_three (physical : EdgeLabelling)
    (hl : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (ha : affineMask physical ids ∈ embeddedBinarySurfaceMasks)
    (block : Nat) (hb : block < 116) :
    cutoffOneSlabSelectedBlockDegree block physical ≤ 3 := by
  apply Nat.le_trans
    (selected_degree_mono block physical (boundaryCompleteSlabPlaquettes 1) ?_)
    (innerFaceCeiling_degree_le_three block hb)
  intro face hf
  have hs := affine_action_inner_support physical hl ids hi ha face hf
  unfold innerFaceCeiling
  split
  · exact hl _
  · rcases hs with hz | hin
    · simpa only [hz] using Nat.le_refl 0
    · contradiction

private theorem insertion_degree_le_length (block : Nat) (hb : block < 116) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds) →
      slabFacesBlockDegree block (insertedFaces ids) ≤ ids.length
  | [], _ => Nat.le_refl 0
  | id :: rest, hi => by
      have hid := inner_id_lt id (hi id List.mem_cons_self)
      have hf : slabFaceBlockDegree block (slabPlaquetteAt 1 id) ≤ 1 := by
        rw [slabFaceBlockDegree_eq_incidenceBit block id hb hid]
        split <;> decide
      have hr := insertion_degree_le_length block hb rest
        (fun other ho => hi other (List.mem_cons_of_mem id ho))
      change slabFaceBlockDegree block (slabPlaquetteAt 1 id) +
        slabFacesBlockDegree block (insertedFaces rest) ≤ rest.length + 1
      omega

/-- Full action-plus-occurrence degree; no charge-mask polynomial substitution. -/
def insertedTotalDegree (physical : EdgeLabelling) (ids : List Nat)
    (block : Nat) : Nat :=
  cutoffOneSlabSelectedBlockDegree block physical +
    slabFacesBlockDegree block (insertedFaces ids)

/-- This is the degree of the SAME original heat-weighted polynomial. -/
theorem inserted_integrand_blockDegree (block : Nat) (w : Q')
    (physical : EdgeLabelling) (hl : ∀ id, physical id ≤ 1)
    (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds) :
    HasQuaternionBlockDegree block (insertedTotalDegree physical ids block)
      (exactCutoffOneInsertedIntegrand w physical (insertedFaces ids)) :=
  exactCutoffOneInsertedIntegrand_blockDegree block w physical
    (insertedFaces ids) hl
    (insertedFaces_physical ids (fun id hm => inner_id_lt id (hi id hm)))

theorem inserted_total_degree_cases (physical : EdgeLabelling)
    (hl : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (hn : ids.length ≤ 2)
    (ha : affineMask physical ids ∈ embeddedBinarySurfaceMasks)
    (block : Nat) (hb : block < 116) :
    insertedTotalDegree physical ids block = 0 ∨
      insertedTotalDegree physical ids block = 2 ∨
      insertedTotalDegree physical ids block = 4 := by
  have hs := affine_selected_degree_le_three physical hl ids hi ha block hb
  have hd := insertion_degree_le_length block hb ids hi
  have he := (inserted_parity_allowed_iff_mem physical hl ids
    (fun id hm => inner_id_lt id (hi id hm))).mpr ha block hb
  unfold insertedTotalDegree
  omega

/-- Degree four requires a positive insertion occurrence incidence. -/
theorem quartic_has_insertion_incidence (physical : EdgeLabelling)
    (hl : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (ha : affineMask physical ids ∈ embeddedBinarySurfaceMasks)
    (block : Nat) (hb : block < 116)
    (hq : insertedTotalDegree physical ids block = 4) :
    0 < slabFacesBlockDegree block (insertedFaces ids) := by
  have hs := affine_selected_degree_le_three physical hl ids hi ha block hb
  unfold insertedTotalDegree at hq
  omega

/-- Actual raw blocks of one literal insertion boundary, retaining occurrences. -/
def insertionBoundaryBlocks (id : Nat) : List Nat :=
  (orientedPlaquetteBoundary (slabPlaquetteAt 1 id)).map
    (fun entry => (boundaryCompleteSlabLinks 1).idxOf entry.link)

def insertionBoundaryCarrier : List Nat → List Nat
  | [] => []
  | id :: rest => insertionBoundaryBlocks id ++ insertionBoundaryCarrier rest

theorem insertionBoundaryBlocks_length (id : Nat) :
    (insertionBoundaryBlocks id).length = 4 := by
  rw [insertionBoundaryBlocks, List.length_map, orientedPlaquetteBoundary_length]

theorem insertionBoundaryCarrier_length : ∀ ids : List Nat,
    (insertionBoundaryCarrier ids).length = 4 * ids.length
  | [] => rfl
  | id :: rest => by
      rw [insertionBoundaryCarrier, List.length_append,
        insertionBoundaryBlocks_length, insertionBoundaryCarrier_length,
        List.length_cons]
      omega

private theorem positive_word_degree_mem (block : Nat) :
    ∀ entries : List OrientedBF4Link,
      0 < slabWordBlockDegree block entries →
      block ∈ entries.map
        (fun entry => (boundaryCompleteSlabLinks 1).idxOf entry.link)
  | [], h => by simp only [slabWordBlockDegree] at h; omega
  | entry :: rest, h => by
      simp only [slabWordBlockDegree, slabEntryBlockDegree] at h
      simp only [List.map_cons]
      by_cases he : block = (boundaryCompleteSlabLinks 1).idxOf entry.link
      · exact List.mem_cons.mpr (Or.inl he)
      · rw [if_neg he] at h
        exact List.mem_cons_of_mem _
          (positive_word_degree_mem block rest (by omega))

theorem positive_insertion_degree_mem_carrier (block : Nat) :
    ∀ ids : List Nat,
      0 < slabFacesBlockDegree block (insertedFaces ids) →
      block ∈ insertionBoundaryCarrier ids
  | [], h => by simp only [insertedFaces, List.map_nil, slabFacesBlockDegree] at h; omega
  | id :: rest, h => by
      simp only [insertedFaces, List.map_cons, slabFacesBlockDegree] at h
      change block ∈ insertionBoundaryBlocks id ++ insertionBoundaryCarrier rest
      by_cases hf : 0 < slabFaceBlockDegree block (slabPlaquetteAt 1 id)
      · exact List.mem_append.mpr (Or.inl
          (positive_word_degree_mem block
            (orientedPlaquetteBoundary (slabPlaquetteAt 1 id)) hf))
      · have hr : 0 < slabFacesBlockDegree block (insertedFaces rest) := by
          change 0 < slabFacesBlockDegree block (rest.map (slabPlaquetteAt 1))
          omega
        exact List.mem_append.mpr (Or.inr
          (positive_insertion_degree_mem_carrier block rest hr))

/-- Actual distinct degree-four raw blocks, selected from the original carrier. -/
def quarticBlocks (physical : EdgeLabelling) (ids : List Nat) : List Nat :=
  (List.range 116).filter (fun block =>
    decide (insertedTotalDegree physical ids block = 4))

/-- Check distinctness of this literal finite carrier without generic range lemmas. -/
private theorem raw_carrier_nodup : (List.range 116).Nodup := by
  decide +kernel

theorem quarticBlocks_subset_insertionCarrier (physical : EdgeLabelling)
    (hl : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (ha : affineMask physical ids ∈ embeddedBinarySurfaceMasks) :
    ∀ block, block ∈ quarticBlocks physical ids →
      block ∈ insertionBoundaryCarrier ids := by
  intro block hm
  have hp := List.mem_filter.mp hm
  exact positive_insertion_degree_mem_carrier block ids
    (quartic_has_insertion_incidence physical hl ids hi ha block
      (List.mem_range.mp hp.1) (of_decide_eq_true hp.2))

/-- Decidable occurrence deletion, used only to count the explicit Nat carrier. -/
private def eraseNat (item : Nat) : List Nat → List Nat
  | [] => []
  | first :: rest => if first = item then rest else first :: eraseNat item rest

private theorem eraseNat_length (item : Nat) :
    ∀ carrier : List Nat, item ∈ carrier →
      (eraseNat item carrier).length + 1 = carrier.length
  | [], hm => absurd hm List.not_mem_nil
  | first :: rest, hm => by
      by_cases he : first = item
      · rw [eraseNat, if_pos he, List.length_cons]
      · rw [eraseNat, if_neg he, List.length_cons, List.length_cons]
        have hr : item ∈ rest :=
          (List.mem_cons.mp hm).resolve_left (fun h => he h.symm)
        exact congrArg (fun n : Nat => n + 1) (eraseNat_length item rest hr)

private theorem mem_eraseNat (item : Nat) :
    ∀ (carrier : List Nat) (other : Nat),
      other ∈ carrier → other ≠ item → other ∈ eraseNat item carrier
  | [], _, hm, _ => absurd hm List.not_mem_nil
  | first :: rest, other, hm, hne => by
      by_cases he : first = item
      · rw [eraseNat, if_pos he]
        rcases List.mem_cons.mp hm with hfirst | hrest
        · exact absurd (hfirst.trans he) hne
        · exact hrest
      · rw [eraseNat, if_neg he]
        rcases List.mem_cons.mp hm with hfirst | hrest
        · rw [hfirst]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_eraseNat item rest other hrest hne)

private theorem nat_nodup_subset_length_le :
    ∀ (items carrier : List Nat), items.Nodup →
      (∀ item, item ∈ items → item ∈ carrier) → items.length ≤ carrier.length
  | [], _, _, _ => Nat.zero_le _
  | first :: rest, carrier, hnd, hsub => by
      have hp := List.nodup_cons.mp hnd
      have hfirst := hsub first List.mem_cons_self
      have htail : ∀ other, other ∈ rest → other ∈ eraseNat first carrier := by
        intro other hm
        exact mem_eraseNat first carrier other
          (hsub other (List.mem_cons_of_mem first hm))
          (fun he => hp.1 (he ▸ hm))
      have ih := nat_nodup_subset_length_le rest (eraseNat first carrier) hp.2 htail
      calc
        rest.length + 1 ≤ (eraseNat first carrier).length + 1 :=
          Nat.add_le_add_right ih 1
        _ = carrier.length := eraseNat_length first carrier hfirst

theorem quarticBlocks_length_le_eight (physical : EdgeLabelling)
    (hl : ∀ id, physical id ≤ 1) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ activeHypercubeSlabFaceIds)
    (hn : ids.length ≤ 2)
    (ha : affineMask physical ids ∈ embeddedBinarySurfaceMasks) :
    (quarticBlocks physical ids).length ≤ 8 := by
  have hc := nat_nodup_subset_length_le
    (quarticBlocks physical ids) (insertionBoundaryCarrier ids)
    (List.filter_sublist.nodup raw_carrier_nodup)
    (quarticBlocks_subset_insertionCarrier physical hl ids hi ha)
  rw [insertionBoundaryCarrier_length] at hc
  omega

theorem repeated_quarticBlocks_length_le_four (physical : EdgeLabelling)
    (hl : ∀ item, physical item ≤ 1) (id : Nat)
    (hi : id ∈ activeHypercubeSlabFaceIds)
    (ha : affineMask physical [id, id] ∈ embeddedBinarySurfaceMasks) :
    (quarticBlocks physical [id, id]).length ≤ 4 := by
  have hinner : ∀ item, item ∈ [id, id] → item ∈ activeHypercubeSlabFaceIds := by
    intro item hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hm
    simpa only [hm] using hi
  have hs : ∀ block, block ∈ quarticBlocks physical [id, id] →
      block ∈ insertionBoundaryBlocks id := by
    intro block hm
    have hc := quarticBlocks_subset_insertionCarrier physical hl [id, id]
      hinner ha block hm
    simpa only [insertionBoundaryCarrier, List.append_nil,
      List.mem_append, or_self] using hc
  have hc := nat_nodup_subset_length_le
    (quarticBlocks physical [id, id]) (insertionBoundaryBlocks id)
    (List.filter_sublist.nodup raw_carrier_nodup) hs
  rw [insertionBoundaryBlocks_length] at hc
  exact hc

#print axioms innerFaceCeiling
#print axioms innerFaceCeiling_degree_check
#print axioms innerFaceCeiling_degree_le_three
#print axioms inner_id_lt
#print axioms selected_degree_mono
#print axioms affine_selected_degree_le_three
#print axioms insertion_degree_le_length
#print axioms insertedTotalDegree
#print axioms inserted_integrand_blockDegree
#print axioms inserted_total_degree_cases
#print axioms quartic_has_insertion_incidence
#print axioms insertionBoundaryBlocks
#print axioms insertionBoundaryCarrier
#print axioms insertionBoundaryBlocks_length
#print axioms insertionBoundaryCarrier_length
#print axioms positive_word_degree_mem
#print axioms positive_insertion_degree_mem_carrier
#print axioms quarticBlocks
#print axioms raw_carrier_nodup
#print axioms quarticBlocks_subset_insertionCarrier
#print axioms eraseNat
#print axioms eraseNat_length
#print axioms mem_eraseNat
#print axioms nat_nodup_subset_length_le
#print axioms quarticBlocks_length_le_eight
#print axioms repeated_quarticBlocks_length_le_four

end YMGap.Continuum.BF4ExactCutoffOneInsertedQuarticBudget
