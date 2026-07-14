/-
# Exact split at merged-residual compatibility

The merged-compatible region has an injective exact allocation into the old
occurrence carrier.  This file isolates its exact complement by a finite
Boolean filter.  Since the two original residual sides are separately
compatible source subfamilies, failure of compatibility of their uncoloured
union has a constructive bounded witness crossing from the left residual to
the right residual.
-/

import YMGap.Continuum.XiExceptionalMergedPathSafeGlobal
import YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier

namespace YMGap.Continuum.XiExceptionalMergedIncompatibleSplit

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiNonexceptionalTargetValidity
open YMGap.Continuum.XiExceptionalParallelSourceSide
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier
open YMGap.Continuum.XiExceptionalMergedResidualCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## The exact finite partition -/

def mergedResidualCompatibleB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  familyCompatibleB
    (selectByBits Gamma (mergedResidualBits Gamma qP b1 b2 entry))

def mergedCompatibleSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (mergedResidualCompatibleB Gamma qP b1 b2)

def mergedIncompatibleSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (fun entry => !(mergedResidualCompatibleB Gamma qP b1 b2 entry))

theorem exceptionalSource_mergedCompatibility_partition
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≈
      qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (mergedCompatibleSource Gamma qP b1 b2) +
        qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (mergedIncompatibleSource Gamma qP b1 b2) := by
  exact qListSum_filter_partition
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (mergedResidualCompatibleB Gamma qP b1 b2)
    (fullExceptionalSource Gamma qP b1 b2)

/-! ## A finite cross-side compatibility check -/

def crossResidualCompatibleB
    (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) : Bool :=
  (occurrenceIndices Gamma.length).all (fun i =>
    (!left.at i) ||
      (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)))

private theorem occurrenceIndices_sound : ∀ {n i : Nat},
    i ∈ occurrenceIndices n → i < n
  | 0, _, hi => by cases hi
  | n + 1, 0, _ => by omega
  | n + 1, i + 1, hi => by
      have ht : i ∈ occurrenceIndices n := by
        rcases List.mem_cons.mp hi with hzero | htail
        · cases hzero
        · obtain ⟨j, hj, hji⟩ := List.mem_map.mp htail
          injection hji with h
          subst j
          exact hj
      have := occurrenceIndices_sound ht
      omega

private theorem exists_false_of_all_false (f : a → Bool) :
    ∀ xs : List a, xs.all f = false → ∃ x, x ∈ xs ∧ f x = false
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : f x with
      | false => exact ⟨x, List.mem_cons_self, hx⟩
      | true =>
          have ht : xs.all f = false := by
            simp only [List.all_cons, hx, Bool.true_and] at h
            exact h
          obtain ⟨y, hy, hfy⟩ := exists_false_of_all_false f xs ht
          exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩

theorem crossResidualCompatibleB_sound
    (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (hcross : crossResidualCompatibleB Gamma left right = true) :
    ∀ i, i < Gamma.length → left.at i = true →
      ∀ j, j < Gamma.length → right.at j = true →
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = true := by
  intro i hi hleft j hj hright
  have hiAll := List.all_eq_true.mp hcross i (occurrenceIndices_complete hi)
  have hjAll : (occurrenceIndices Gamma.length).all (fun k =>
      (!right.at k) || compatibleB (polyAt Gamma i) (polyAt Gamma k)) = true := by
    cases hl : left.at i <;> simp_all
  have hout := List.all_eq_true.mp hjAll j (occurrenceIndices_complete hj)
  cases hr : right.at j <;> simp_all

theorem unionBits_compatible_of_cross
    (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (hleft : familyCompatibleB (selectByBits Gamma left) = true)
    (hright : familyCompatibleB (selectByBits Gamma right) = true)
    (hcross : crossResidualCompatibleB Gamma left right = true) :
    familyCompatibleB
      (selectByBits Gamma (unionBits left right)) = true := by
  have hcrossSound := crossResidualCompatibleB_sound Gamma left right hcross
  apply selectByBits_familyCompatible_of_pairwise
  intro i j hi hj hij hui huj
  rw [unionBits_at] at hui huj
  cases hiLeft : left.at i with
  | true =>
      cases hjLeft : left.at j with
      | true =>
          exact selectByBits_pairwise_compatible Gamma left i j hi hj hij
            hiLeft hjLeft hleft
      | false =>
          have hjRight : right.at j = true := by
            cases hr : right.at j <;> simp_all
          exact hcrossSound i hi hiLeft j hj hjRight
  | false =>
      have hiRight : right.at i = true := by
        cases hr : right.at i <;> simp_all
      cases hjRight : right.at j with
      | true =>
          exact selectByBits_pairwise_compatible Gamma right i j hi hj hij
            hiRight hjRight hright
      | false =>
          have hjLeft : left.at j = true := by
            cases hl : left.at j <;> simp_all
          rw [compatibleB_symm]
          exact hcrossSound j hj hjLeft i hi hiRight

theorem leftPathResidual_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB (selectByBits Gamma
      (leftPathResidual Gamma qP b1 b2 entry)) = true :=
  exceptional_left_submask_compatible Gamma qP b1 b2 entry _
    (leftPathResidual_submask_left Gamma qP b1 b2 entry)

theorem rightPathResidual_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB (selectByBits Gamma
      (rightPathResidual Gamma qP b1 b2 entry)) = true :=
  exceptional_right_submask_compatible Gamma qP b1 b2 entry _
    (rightPathResidual_submask_right Gamma qP b1 b2 entry)

theorem crossResidualCompatibleB_false_of_merged_incompatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hincompatible : mergedResidualCompatibleB Gamma qP b1 b2 entry = false) :
    crossResidualCompatibleB Gamma
      (leftPathResidual Gamma qP b1 b2 entry)
      (rightPathResidual Gamma qP b1 b2 entry) = false := by
  cases hcross : crossResidualCompatibleB Gamma
      (leftPathResidual Gamma qP b1 b2 entry)
      (rightPathResidual Gamma qP b1 b2 entry) with
  | false => rfl
  | true =>
      have hcompatible := unionBits_compatible_of_cross Gamma
        (leftPathResidual Gamma qP b1 b2 entry)
        (rightPathResidual Gamma qP b1 b2 entry)
        (leftPathResidual_compatible Gamma qP b1 b2 entry)
        (rightPathResidual_compatible Gamma qP b1 b2 entry) hcross
      have htrue : mergedResidualCompatibleB Gamma qP b1 b2 entry = true := by
        simpa [mergedResidualCompatibleB, mergedResidualBits] using hcompatible
      rw [hincompatible] at htrue
      cases htrue

/-! ## Constructive crossing-conflict witness -/

/-- Every merged-incompatible exceptional entry contains an actual bounded
left/right residual conflict.  This is an occurrence witness, so duplicate
polymer values cannot blur which source side supplied either endpoint. -/
theorem merged_incompatible_cross_conflict
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hincompatible : mergedResidualCompatibleB Gamma qP b1 b2 entry = false) :
    ∃ i, i < Gamma.length ∧
      (leftPathResidual Gamma qP b1 b2 entry).at i = true ∧
      ∃ j, j < Gamma.length ∧
        (rightPathResidual Gamma qP b1 b2 entry).at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  have hcross := crossResidualCompatibleB_false_of_merged_incompatible
    Gamma qP b1 b2 entry hincompatible
  unfold crossResidualCompatibleB at hcross
  obtain ⟨i, hiMem, hiFalse⟩ := exists_false_of_all_false _ _ hcross
  have hi : i < Gamma.length := occurrenceIndices_sound hiMem
  have hleft : (leftPathResidual Gamma qP b1 b2 entry).at i = true := by
    cases hl : (leftPathResidual Gamma qP b1 b2 entry).at i with
    | true => rfl
    | false =>
        simp only [hl, Bool.not_false, Bool.true_or] at hiFalse
        cases hiFalse
  have hinner : (occurrenceIndices Gamma.length).all (fun j =>
      (!(rightPathResidual Gamma qP b1 b2 entry).at j) ||
        compatibleB (polyAt Gamma i) (polyAt Gamma j)) = false := by
    simpa only [hleft, Bool.not_true, Bool.false_or] using hiFalse
  obtain ⟨j, hjMem, hjFalse⟩ := exists_false_of_all_false _ _ hinner
  have hj : j < Gamma.length := occurrenceIndices_sound hjMem
  have hright : (rightPathResidual Gamma qP b1 b2 entry).at j = true := by
    cases hr : (rightPathResidual Gamma qP b1 b2 entry).at j with
    | true => rfl
    | false =>
        simp only [hr, Bool.not_false, Bool.true_or] at hjFalse
        cases hjFalse
  have hconflict : compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
    simpa only [hright, Bool.not_true, Bool.false_or] using hjFalse
  exact ⟨i, hi, hleft, j, hj, hright, hconflict⟩

theorem mergedIncompatibleSource_cross_conflict
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ mergedIncompatibleSource Gamma qP b1 b2) :
    ∃ i, i < Gamma.length ∧
      (leftPathResidual Gamma qP b1 b2 entry).at i = true ∧
      ∃ j, j < Gamma.length ∧
        (rightPathResidual Gamma qP b1 b2 entry).at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  exact merged_incompatible_cross_conflict Gamma qP b1 b2 entry
    (by simpa [mergedIncompatibleSource] using (List.mem_filter.mp hentry).2)

#print axioms exceptionalSource_mergedCompatibility_partition
#print axioms crossResidualCompatibleB_sound
#print axioms unionBits_compatible_of_cross
#print axioms leftPathResidual_compatible
#print axioms rightPathResidual_compatible
#print axioms crossResidualCompatibleB_false_of_merged_incompatible
#print axioms merged_incompatible_cross_conflict
#print axioms mergedIncompatibleSource_cross_conflict

end YMGap.Continuum.XiExceptionalMergedIncompatibleSplit
