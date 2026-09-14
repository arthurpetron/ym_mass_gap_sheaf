/-
# The complete original leading coefficient has at most one accepted term

The unchanged selected-support and paired-label enumeration is duplicate
free. Every accepted original leading pair is exactly (tubeLabelling,zero),
including nonphysical indices. Consequently leadingCount is at most one.
Membership of that pair in the original filters, hence positivity of the
count, is not assumed or established here.
-/

import YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount
import YMGap.Continuum.PairedPositiveFaceLabellingUniqueness
import YMGap.Continuum.FiniteSelectionOrder
import YMGap.Continuum.CayleyInjection

namespace YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.PairedPositiveFaceLabellingUniqueness
open YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount
open YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder
open YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow
open YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem support_mem_iff {K : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ labels K ids) (id : Nat) : id ∈ ids ↔ 0 < pair.1 id ∨ 0 < pair.2 id := by
  constructor
  · exact covers K ids pair hp id
  · intro h
    by_cases hi : id ∈ ids
    · exact hi
    · have hz := outside K ids pair hp id hi
      rcases h with h | h
      all_goals omega

theorem selected_support_eq {K : Nat} {ambient left right : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hn : ambient.Nodup)
    (hl : left ∈ selections ambient) (hr : right ∈ selections ambient)
    (hpl : pair ∈ labels K left) (hpr : pair ∈ labels K right) : left = right :=
  CayleyInjection.sublists_eq_of_mem_iff ambient left right hn
    (by simpa only [selections_eq_sublists] using hl)
    (by simpa only [selections_eq_sublists] using hr)
    (fun id => (support_mem_iff hpl id).trans (support_mem_iff hpr id).symm)

theorem retainedPairs_nodup (K margin time : Nat) : (retainedPairs K margin time).Nodup := by
  have hn : (slabPhysicalFaceEdges (responseExtent margin)).Nodup := CayleyParentInj.range_nodup _
  unfold retainedPairs
  apply flatMap_nodup
  · exact (selections_nodup _ hn).filter _
  · intro ids hs
    exact ((labels_nodup K ids ((selected_sublist (List.mem_filter.mp hs).1).nodup hn)).filter _).filter _
  · intro left hl right hr hne pair hpl hpr
    exact hne (selected_support_eq hn (List.mem_filter.mp hl).1 (List.mem_filter.mp hr).1
      (List.mem_filter.mp (List.mem_filter.mp hpl).1).1
      (List.mem_filter.mp (List.mem_filter.mp hpr).1).1)

theorem empty_positive_label (extent : Nat) (state : EdgeLabelling)
    (he : positiveFaces extent state = []) (id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    state id = 0 := by
  by_cases hz : state id = 0
  · exact hz
  · have hf : slabPlaquetteAt extent id ∈ positiveFaces extent state :=
      List.mem_filter.mpr ⟨slabPlaquetteAt_mem hi,by
        rw [idxOf_slabPlaquetteAt hi]
        exact decide_eq_true (by omega)⟩
    rw [he] at hf
    exact False.elim (List.not_mem_nil hf)

theorem leading_pair_pin {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ (retainedPairs K margin time).filter (leadingKeep margin)) :
    pair = (tubeLabelling margin,zeroEdgeLabelling) := by
  have hk := Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2
  have he : pairPower margin pair = 36 := of_decide_eq_true hk.1
  have hc := Bool.and_eq_true_iff.mp hk.2
  obtain ⟨selected,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  have hb := (retained_minimal_power_fundamental hs hm he).2
  have hw := retained_minimal_window hs hm he
  have hl := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
  have hout (id : Nat) (hi : id ∉ slabPhysicalFaceEdges (responseExtent margin)) :=
    outside K selected pair hl id (fun hid => hi (selected_mem (List.mem_filter.mp hs).1 id hid))
  have hempty := accepted_partition_empty margin pair.2 (fun id hi => (hb id hi).2) hw.2 hc.2
  apply Prod.ext
  · funext id
    by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
    · exact accepted_mixed_label_pin margin pair.1 (fun i hi => (hb i hi).1) hw.1 hc.1 id hi
    · simpa only [tubeLabelling,hi,false_and,↓reduceIte] using (hout id hi).1
  · funext id
    by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
    · exact empty_positive_label _ _ hempty id hi
    · exact (hout id hi).2

theorem pinned_nodup_length_le_one {A : Type} (target : A) : ∀ xs : List A,
    xs.Nodup → (∀ x, x ∈ xs → x = target) → xs.length ≤ 1
  | [], _, _ => Nat.zero_le _
  | [_], _, _ => Nat.le_refl _
  | a::b::xs, hn, hp => by
      have he := (hp a List.mem_cons_self).trans
        (hp b (List.mem_cons_of_mem a List.mem_cons_self)).symm
      exact False.elim ((List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl he)))

theorem leadingCount_le_one (K margin time : Nat) : leadingCount K margin time ≤ 1 :=
  pinned_nodup_length_le_one (tubeLabelling margin,zeroEdgeLabelling) _
    ((retainedPairs_nodup K margin time).filter _) (fun _ hp => leading_pair_pin hp)

theorem leadingCount_zero_or_one (K margin time : Nat) :
    leadingCount K margin time = 0 ∨ leadingCount K margin time = 1 := by
  have hb := leadingCount_le_one K margin time
  by_cases hz : leadingCount K margin time = 0
  · exact Or.inl hz
  · exact Or.inr (by omega)

theorem leadingCoefficient_zero_or_one (K margin time : Nat) :
    leadingCoefficient K margin time ≈ 0 ∨ leadingCoefficient K margin time ≈ 1 := by
  have hc := leadingCoefficient_count K margin time
  rcases leadingCount_zero_or_one K margin time with hz | ho
  · rw [hz] at hc
    exact Or.inl hc
  · rw [ho] at hc
    exact Or.inr hc

end YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness

#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.support_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.selected_support_eq
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.retainedPairs_nodup
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.empty_positive_label
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.leading_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.pinned_nodup_length_le_one
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.leadingCount_le_one
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.leadingCount_zero_or_one
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness.leadingCoefficient_zero_or_one
