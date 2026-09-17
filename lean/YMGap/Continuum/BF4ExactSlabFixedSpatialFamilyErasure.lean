/-
# Exact coordinate erasures for the original heat-and-fringe family

The retained labels are the original active links followed by all inactive
source coordinates. Inactive labels carry the polynomial unit, not a new
heat kernel. Filtering an erased label list therefore selects precisely
the original heat factors which remain. Single and pair cuts are pinned
to the existing constructive eraseIndex lists, including fringe cases.

These are finite polynomial and list identities. They construct neither
a centered-observable decomposition nor a bound on the signed family cost.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
import YMGap.Continuum.QuaternionHaarFamilyErasure

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex select_perm mem_of_mem_erase)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.QuaternionHaarFamilyErasure

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks activeBlocks

def labels (width : Nat) : List Nat := activeBlocks width ++ fringeBlocks width

def coordinateFactor (w : Q') (K width i : Nat) : RatPoly :=
  if i ∈ activeBlocks width then heatAt i (N width+i) w K else polyOne

def remainingHeat (width : Nat) (ids : List Nat) : List Nat :=
  ids.filter (fun i => decide (i ∈ activeBlocks width))

private theorem range_nodup (count : Nat) : (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hr : right = count := List.mem_singleton.mp hright
      rw [heq, hr] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

theorem labels_nodup (width : Nat) : (labels width).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨activeBlocks_nodup width, ?_, ?_⟩
  · exact List.filter_sublist.nodup (range_nodup (N width))
  · intro i hi j hj he
    subst j
    exact ((fringeBlocks_mem_iff width i).mp hj).2 hi

theorem labels_lt (width i : Nat) (hi : i ∈ labels width) : i < N width := by
  rcases List.mem_append.mp hi with ha | hf
  · exact activeBlocks_lt width i ha
  · exact fringeBlocks_lt width i hf

theorem family_eq_indexed (w : Q') (K width : Nat) (tests : Nat → RatPoly) :
    family w K width tests =
      (labels width).map (fun i => (coordinateFactor w K width i, jump (N width) (tests i))) := by
  unfold family labels
  rw [List.map_append]
  have ha : (activeBlocks width).map (fun i => (heatAt i (N width+i) w K, jump (N width) (tests i))) =
      (activeBlocks width).map (fun i => (coordinateFactor w K width i, jump (N width) (tests i))) := by
    apply List.map_congr_left
    intro i hi
    rw [coordinateFactor, if_pos hi]
  have hf : (fringeBlocks width).map (fun i => (polyOne, jump (N width) (tests i))) =
      (fringeBlocks width).map (fun i => (coordinateFactor w K width i, jump (N width) (tests i))) := by
    apply List.map_congr_left
    intro i hi
    rw [coordinateFactor, if_neg ((fringeBlocks_mem_iff width i).mp hi).2]
  rw [ha, hf]

private theorem remaining_cons_pos (width : Nat) {i : Nat} {ids : List Nat}
    (hi : i ∈ activeBlocks width) : remainingHeat width (i::ids) = i::remainingHeat width ids :=
  List.filter_cons_of_pos (decide_eq_true hi)

private theorem remaining_cons_neg (width : Nat) {i : Nat} {ids : List Nat}
    (hi : i ∉ activeBlocks width) : remainingHeat width (i::ids) = remainingHeat width ids :=
  List.filter_cons_of_neg (fun h => hi (of_decide_eq_true h))

set_option maxHeartbeats 800000 in
/-- Unit factors disappear coefficientwise; no Haar normalization is used. -/
theorem product_pin (w : Q') (K width : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (polynomialProduct (coordinateFactor w K width) ids)
      (productHeat (N width) w K (remainingHeat width ids)) := by
  induction ids with
  | nil => exact RatPolyCoeffEqv.refl polyOne
  | cons i ids ih =>
      by_cases hi : i ∈ activeBlocks width
      · rw [remaining_cons_pos width hi]
        change RatPolyCoeffEqv
          (polyMul (coordinateFactor w K width i) (polynomialProduct (coordinateFactor w K width) ids))
          (polyMul (heatAt i (N width+i) w K) (productHeat (N width) w K (remainingHeat width ids)))
        rw [coordinateFactor, if_pos hi]
        exact ih.mul_left _
      · rw [remaining_cons_neg width hi]
        change RatPolyCoeffEqv
          (polyMul (coordinateFactor w K width i) (polynomialProduct (coordinateFactor w K width) ids))
          (productHeat (N width) w K (remainingHeat width ids))
        rw [coordinateFactor, if_neg hi]
        exact (RatPolyCoeffEqv.one_mul _).trans ih

private theorem remaining_all (width : Nat) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → i ∈ activeBlocks width) → remainingHeat width ids = ids
  | [], _ => rfl
  | i::ids, h => by
      rw [remaining_cons_pos width (h i List.mem_cons_self),
        remaining_all width ids (fun j hj => h j (List.mem_cons_of_mem i hj))]

private theorem remaining_none (width : Nat) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → i ∉ activeBlocks width) → remainingHeat width ids = []
  | [], _ => rfl
  | i::ids, h => by
      rw [remaining_cons_neg width (h i List.mem_cons_self)]
      exact remaining_none width ids (fun j hj => h j (List.mem_cons_of_mem i hj))

theorem remainingHeat_labels (width : Nat) : remainingHeat width (labels width) = activeBlocks width := by
  change ((activeBlocks width ++ fringeBlocks width).filter _ ) = _
  rw [List.filter_append]
  change remainingHeat width (activeBlocks width) ++ remainingHeat width (fringeBlocks width) = _
  rw [remaining_all width _ (fun _ hi => hi),
    remaining_none width _ (fun i hi => ((fringeBlocks_mem_iff width i).mp hi).2), List.append_nil]

theorem remainingHeat_lt (width : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) (i : Nat) (hi : i ∈ remainingHeat width ids) : i < N width :=
  hids i (List.mem_filter.mp hi).1

private theorem remaining_perm (width : Nat) {ids js : List Nat} (hp : ids.Perm js) :
    (remainingHeat width ids).Perm (remainingHeat width js) := by
  induction hp with
  | nil => exact List.Perm.nil
  | cons i hp ih =>
      by_cases hi : i ∈ activeBlocks width
      · rw [remaining_cons_pos width hi, remaining_cons_pos width hi]
        exact List.Perm.cons i ih
      · rw [remaining_cons_neg width hi, remaining_cons_neg width hi]
        exact ih
  | swap i j ids =>
      by_cases hi : i ∈ activeBlocks width <;> by_cases hj : j ∈ activeBlocks width
      · simpa only [remaining_cons_pos width hi, remaining_cons_pos width hj] using
          List.Perm.swap i j (remainingHeat width ids)
      · simp only [remaining_cons_pos width hi, remaining_cons_neg width hj]
        exact List.Perm.refl _
      · simp only [remaining_cons_neg width hi, remaining_cons_pos width hj]
        exact List.Perm.refl _
      · simp only [remaining_cons_neg width hi, remaining_cons_neg width hj]
        exact List.Perm.refl _
  | trans hp hq ihp ihq => exact ihp.trans ihq

private theorem erase_absent (i : Nat) : ∀ ids : List Nat, i ∉ ids → eraseIndex i ids = ids
  | [], _ => rfl
  | j::ids, h => by
      have hji : j ≠ i := fun he => h (List.mem_cons.mpr (Or.inl he.symm))
      have ht : i ∉ ids := fun hi => h (List.mem_cons_of_mem j hi)
      rw [eraseIndex, if_neg hji, erase_absent i ids ht]

/-- Includes the inactive case: erasing its label removes no heat factor. -/
theorem single_remaining_perm {width i : Nat} {rest : List Nat}
    (hm : (i,rest) ∈ singleCuts (labels width)) :
    (remainingHeat width rest).Perm (eraseIndex i (activeBlocks width)) := by
  have hp := remaining_perm width (singleCuts_perm hm)
  rw [remainingHeat_labels] at hp
  by_cases hi : i ∈ activeBlocks width
  · rw [remaining_cons_pos width hi] at hp
    exact List.Perm.cons_inv (hp.symm.trans (select_perm i hi))
  · rw [remaining_cons_neg width hi] at hp
    rw [erase_absent i (activeBlocks width) hi]
    exact hp.symm

/-- Both selected labels are retained in the erasure order, even when a
selected label is a fringe unit rather than a heat factor. -/
theorem pair_remaining_perm {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) :
    (remainingHeat width rest).Perm (eraseIndex j (eraseIndex i (activeBlocks width))) := by
  have hp := remaining_perm width (pairCuts_perm hm)
  rw [remainingHeat_labels] at hp
  by_cases hi : i ∈ activeBlocks width
  · rw [remaining_cons_pos width hi] at hp
    by_cases hj : j ∈ activeBlocks width
    · rw [remaining_cons_pos width hj] at hp
      have hpi := select_perm i hi
      have hrest : (eraseIndex i (activeBlocks width)).Perm (j::remainingHeat width rest) :=
        List.Perm.cons_inv (hpi.symm.trans hp)
      have hj' : j ∈ eraseIndex i (activeBlocks width) := hrest.mem_iff.mpr List.mem_cons_self
      exact List.Perm.cons_inv (hrest.symm.trans (select_perm j hj'))
    · rw [remaining_cons_neg width hj] at hp
      rw [erase_absent j (eraseIndex i (activeBlocks width))
        (fun h => hj (mem_of_mem_erase i h))]
      exact List.Perm.cons_inv (hp.symm.trans (select_perm i hi))
  · rw [remaining_cons_neg width hi] at hp
    rw [erase_absent i (activeBlocks width) hi]
    by_cases hj : j ∈ activeBlocks width
    · rw [remaining_cons_pos width hj] at hp
      exact List.Perm.cons_inv (hp.symm.trans (select_perm j hj))
    · rw [remaining_cons_neg width hj] at hp
      rw [erase_absent j (activeBlocks width) hj]
      exact hp.symm

theorem single_selected_lt {width i : Nat} {rest : List Nat}
    (hm : (i,rest) ∈ singleCuts (labels width)) : i < N width :=
  labels_lt width i ((singleCuts_perm hm).mem_iff.mpr List.mem_cons_self)

theorem single_remaining_lt {width i : Nat} {rest : List Nat}
    (hm : (i,rest) ∈ singleCuts (labels width)) (k : Nat) (hk : k ∈ remainingHeat width rest) : k < N width :=
  labels_lt width k ((singleCuts_perm hm).mem_iff.mpr
    (List.mem_cons_of_mem i (List.mem_filter.mp hk).1))

theorem single_remaining_not_mem {width i : Nat} {rest : List Nat}
    (hm : (i,rest) ∈ singleCuts (labels width)) : i ∉ remainingHeat width rest := by
  have hn := (singleCuts_perm hm).nodup_iff.mp (labels_nodup width)
  exact fun hi => (List.nodup_cons.mp hn).1 (List.mem_filter.mp hi).1

theorem pair_left_lt {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) : i < N width :=
  labels_lt width i ((pairCuts_perm hm).mem_iff.mpr List.mem_cons_self)

theorem pair_right_lt {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) : j < N width :=
  labels_lt width j ((pairCuts_perm hm).mem_iff.mpr (List.mem_cons_of_mem i List.mem_cons_self))

theorem pair_ne {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) : i ≠ j := by
  have hn := (pairCuts_perm hm).nodup_iff.mp (labels_nodup width)
  exact fun he => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl he))

theorem pair_remaining_lt {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) (k : Nat) (hk : k ∈ remainingHeat width rest) : k < N width :=
  labels_lt width k ((pairCuts_perm hm).mem_iff.mpr
    (List.mem_cons_of_mem i (List.mem_cons_of_mem j (List.mem_filter.mp hk).1)))

theorem pair_remaining_not_mem_left {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) : i ∉ remainingHeat width rest := by
  have hn := (pairCuts_perm hm).nodup_iff.mp (labels_nodup width)
  exact fun hi => (List.nodup_cons.mp hn).1 (List.mem_cons_of_mem j (List.mem_filter.mp hi).1)

theorem pair_remaining_not_mem_right {width i j : Nat} {rest : List Nat}
    (hm : (i,j,rest) ∈ pairCuts (labels width)) : j ∉ remainingHeat width rest := by
  have hn := (pairCuts_perm hm).nodup_iff.mp (labels_nodup width)
  exact fun hj => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (List.mem_filter.mp hj).1

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.labels
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.coordinateFactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.remainingHeat
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.labels_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.labels_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.family_eq_indexed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.product_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.remainingHeat_labels
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.remainingHeat_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.single_remaining_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_remaining_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.single_selected_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.single_remaining_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.single_remaining_not_mem
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_left_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_right_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_ne
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_remaining_lt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_remaining_not_mem_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure.pair_remaining_not_mem_right
