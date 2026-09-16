/-
# Ordered original spatial coordinates for an arbitrary finite time chain

Concatenate the same boxed spatial-link list at start through start+steps,
including both endpoints and every box-fringe coordinate. The resulting
carrier has (steps+1)*N blocks, independently of the ambient extent and
start time. Explicit room guards place it injectively in the original slab.

The first slice, tail chain, first adjacent pair, and final slice retain
their existing coordinate order. These are the placement identities used
to identify the complete original action with finite polynomial iteration;
no stationary normalization or analytic estimate is supplied here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks sliceLinks)
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

local notation:max "N" width:arg => List.length (baseLinks width)
local notation "nlinks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Chronological concatenation, with the final spatial slice included. -/
def chainLinks (width start : Nat) : Nat → List Z4Link
  | 0 => sliceLinks width start
  | steps + 1 => sliceLinks width start ++ chainLinks width (start + 1) steps

/-- Exact boxed spatial-link membership in the inclusive time interval. -/
theorem chainLinks_mem_iff (width start steps : Nat) (link : Z4Link) :
    link ∈ chainLinks width start steps ↔
      SliceLink width link.1.2.2.2 link ∧
      start ≤ link.1.2.2.2 ∧ link.1.2.2.2 ≤ start + steps := by
  induction steps generalizing start with
  | zero =>
      rw [chainLinks, BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_mem_iff]
      constructor
      · intro h
        have he := h.2.2.2.2
        exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩, by omega, by omega⟩
      · rintro ⟨h, hlo, hhi⟩
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by omega⟩
  | succ steps ih =>
      rw [chainLinks, List.mem_append,
        BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_mem_iff, ih]
      constructor
      · intro h
        rcases h with h | ⟨h, hlo, hhi⟩
        · have he := h.2.2.2.2
          exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩, by omega, by omega⟩
        · exact ⟨h, by omega, by omega⟩
      · rintro ⟨h, hlo, hhi⟩
        by_cases he : link.1.2.2.2 = start
        · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, he⟩
        · exact Or.inr ⟨h, by omega, by omega⟩

theorem chainLinks_length (width start steps : Nat) :
    (chainLinks width start steps).length = (steps + 1) * N width := by
  induction steps generalizing start with
  | zero =>
      simp only [chainLinks, BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_length,
        Nat.zero_add, Nat.one_mul]
  | succ steps ih =>
      rw [chainLinks, List.length_append,
        BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_length, ih]
      simp only [Nat.succ_mul]
      omega

theorem chainLinks_nodup (width start steps : Nat) :
    (chainLinks width start steps).Nodup := by
  induction steps generalizing start with
  | zero => exact BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_nodup width start
  | succ steps ih =>
      change (sliceLinks width start ++ chainLinks width (start + 1) steps).Nodup
      refine List.nodup_append.mpr
        ⟨BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_nodup width start,
          ih (start + 1), ?_⟩
      intro a ha b hb he
      subst b
      have ht := ((BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_mem_iff
        width start a).mp ha).2.2.2.2
      have hl := ((chainLinks_mem_iff width (start + 1) steps a).mp hb).2.1
      omega

theorem chainLinks_physical {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start + steps ≤ extent) {link : Z4Link}
    (hl : link ∈ chainLinks width start steps) :
    link ∈ boundaryCompleteSlabLinks extent := by
  obtain ⟨hs, _, hlast⟩ := (chainLinks_mem_iff width start steps link).mp hl
  exact BF4ExactSlabFixedSpatialBoundaryCarrier.sliceLink_physical hw (by omega) hs

/-- A computed injection of the entire chronological chain into one original slab. -/
def embedding {width start extent : Nat} (steps : Nat)
    (hw : width ≤ extent) (ht : start + steps ≤ extent) :
    BlockEmbedding ((steps + 1) * N width) (nlinks extent) where
  image := (chainLinks width start steps).map (boundaryCompleteSlabLinks extent).idxOf
  length := by rw [List.length_map, chainLinks_length]
  nodup := nodup_map_of_injOn _ _ (chainLinks_nodup width start steps)
    (fun _ ha _ hb => idxOf_injective_on_members
      (chainLinks_physical hw ht ha) (chainLinks_physical hw ht hb))
  physical := by
    intro b hb
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp hb
    exact List.idxOf_lt_length_of_mem (chainLinks_physical hw ht hl)

theorem embedding_mem_iff {width start steps extent b : Nat}
    (hw : width ≤ extent) (ht : start + steps ≤ extent) (hb : b < nlinks extent) :
    b ∈ (embedding steps hw ht).image ↔
      correctedSlabLinkAt extent b ∈ chainLinks width start steps := by
  constructor
  · intro h
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp h
    rw [correctedSlabLinkAt_idxOf (chainLinks_physical hw ht hl)]
    exact hl
  · intro hl
    apply List.mem_map.mpr
    refine ⟨correctedSlabLinkAt extent b, hl, ?_⟩
    apply correctedSlabLinkAt_injective_on_physical
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem (chainLinks_physical hw ht hl)))
      (List.mem_range.mpr hb)
    exact correctedSlabLinkAt_idxOf (chainLinks_physical hw ht hl)

private theorem getD_append_left {A : Type} (xs ys : List A) (fallback : A) :
    ∀ i, i < xs.length → (xs ++ ys).getD i fallback = xs.getD i fallback := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons a xs ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

private theorem getD_append_right {A : Type} (xs ys : List A) (fallback : A) (i : Nat) :
    (xs ++ ys).getD (i + xs.length) fallback = ys.getD i fallback := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change (xs ++ ys).getD (i + xs.length) fallback = ys.getD i fallback
      exact ih

/-- The initial N blocks are the existing slice placement at start. -/
theorem head_block {width start steps extent i : Nat}
    (hw : width ≤ extent) (ht : start + steps ≤ extent) (hi : i < N width) :
    (embedding steps hw ht).block i =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start ≤ extent by omega)).block i := by
  cases steps with
  | zero => rfl
  | succ steps =>
      change ((chainLinks width start (steps + 1)).map
        (boundaryCompleteSlabLinks extent).idxOf).getD i 0 =
        ((sliceLinks width start).map (boundaryCompleteSlabLinks extent).idxOf).getD i 0
      rw [chainLinks, List.map_append]
      apply getD_append_left
      simpa only [List.length_map, BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_length] using hi

/-- Removing the initial N positions leaves exactly the chain at start+1. -/
theorem tail_block {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start + (steps + 1) ≤ extent) (i : Nat) :
    (embedding (steps + 1) hw ht).block (N width + i) =
      (embedding steps (start := start + 1) hw
        (show start + 1 + steps ≤ extent by omega)).block i := by
  change ((chainLinks width start (steps + 1)).map
    (boundaryCompleteSlabLinks extent).idxOf).getD (N width + i) 0 =
    ((chainLinks width (start + 1) steps).map (boundaryCompleteSlabLinks extent).idxOf).getD i 0
  rw [chainLinks, List.map_append]
  rw [show N width + i =
    i + ((sliceLinks width start).map (boundaryCompleteSlabLinks extent).idxOf).length by
      rw [List.length_map, BF4ExactSlabFixedSpatialSliceCarrier.sliceLinks_length]
      omega]
  exact getD_append_right _ _ 0 i

/-- The initial two slices have precisely the established adjacent-pair order. -/
theorem pair_block {width start steps extent i : Nat}
    (hw : width ≤ extent) (ht : start + (steps + 1) ≤ extent)
    (hi : i < N width + N width) :
    (embedding (steps + 1) hw ht).block i =
      (BF4ExactSlabFixedSpatialPairCarrier.embedding hw
        (show start + 1 ≤ extent by omega)).block i := by
  have hs : start + 1 ≤ extent := by omega
  by_cases hfirst : i < N width
  · exact (head_block hw ht hfirst).trans
      (BF4ExactSlabFixedSpatialPairCarrier.lower_block hw hs hfirst).symm
  · have hlast : i - N width < N width := by omega
    have hindex : i = N width + (i - N width) := by omega
    rw [hindex]
    exact (tail_block hw ht (i - N width)).trans
      ((head_block hw (show start + 1 + steps ≤ extent by omega) hlast).trans
        (BF4ExactSlabFixedSpatialPairCarrier.upper_block hw hs (i - N width)).symm)

/-- The final N positions are the same source slice order at start+steps. -/
theorem final_block {width start steps extent i : Nat}
    (hw : width ≤ extent) (ht : start + steps ≤ extent) (hi : i < N width) :
    (embedding steps hw ht).block (steps * N width + i) =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).block i := by
  induction steps generalizing start with
  | zero =>
      simpa only [Nat.zero_mul, Nat.zero_add] using
        (head_block (steps := 0) hw ht hi)
  | succ steps ih =>
      have hs : start + 1 + steps ≤ extent := by omega
      have h := (tail_block hw ht (steps * N width + i)).trans
        (ih (start := start + 1) hs)
      have htime : start + 1 + steps = start + (steps + 1) := by omega
      have hindex : (steps + 1) * N width + i = N width + (steps * N width + i) := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [htime, hindex] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.chainLinks
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.chainLinks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.chainLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.chainLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.chainLinks_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.embedding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.embedding_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.head_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.tail_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.pair_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier.final_block
