/-
# A zero-weight fence for the unpruned branch packing

The full switched-left mask is sufficient to recover every source branch,
but it is not a valid terminal background for the canonical path.  Whenever
the marked polymer is nonempty, that mask contains the marked occurrence
itself.  The terminal background predicate includes compatibility with the
path start, so the resulting target term is exactly zero up to `Q'.eqv`.

This kernel-checked fence rules out using the unpruned structural packing as
the weighted injection without a compatibility-preserving refinement.
-/

import YMGap.Continuum.XiExceptionalBranchPacking

namespace YMGap.Continuum.XiExceptionalBranchPackingFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A terminal-background zero witness -/

theorem compatibleB_self_eq_false {X : Polymer L} (hne : X ≠ []) :
    compatibleB X X = false := by
  cases X with
  | nil => exact absurd rfl hne
  | cons p X => simp [compatibleB]

theorem occurrenceWalkWeight_eqv_zero_of_bg_witness
    (w : Q') (qP b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec Gamma.length)
    (bg : Polymer L → Bool) (T : Polymer L)
    (hT : T ∈ selectByBits Gamma background)
    (hbg : bg T = false) :
    chainCodeWeight w qP b2 Gamma label (polyAt Gamma i) bg
        (eraseOccChainCode Gamma
          (occurrenceChainCodeOfWalk walk background)) ≈ 0 := by
  induction walk generalizing bg with
  | single i =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode,
        chainCodeWeight]
      cases hgate : qP (polyAt Gamma i) && b2 (polyAt Gamma i) with
      | false => exact Q'.eqv_refl 0
      | true =>
          simp only [hgate, if_true]
          have hall : (selectByBits Gamma background).all
              (fun U => (qP U && bg U) &&
                compatibleB (polyAt Gamma i) U) = false := by
            cases h : (selectByBits Gamma background).all
                (fun U => (qP U && bg U) &&
                  compatibleB (polyAt Gamma i) U) with
            | false => rfl
            | true =>
                have hbad := List.all_eq_true.mp h T hT
                simp [hbg] at hbad
          unfold admissibleFamilyWeight
          rw [hall]
          exact Q'.mul_zero_eqv _
  | @cons i k j hedge rest ih =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode,
        chainCodeWeight]
      rw [CWalk.start_eq]
      cases hgate : qP (polyAt Gamma k) &&
          !(compatibleB (polyAt Gamma i) (polyAt Gamma k)) with
      | false =>
          simp only [hgate, Bool.false_eq_true, if_false]
          exact Q'.mul_zero_eqv _
      | true =>
          simp only [hgate, if_true]
          have hnext : (fun U => bg U &&
              compatibleB (polyAt Gamma i) U) T = false := by
            simp [hbg]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (ih (fun U => bg U && compatibleB (polyAt Gamma i) U)
                hnext)) ?_
          exact Q'.mul_zero_eqv _

theorem occurrenceWalkWeight_eqv_zero_of_start_in_background
    (w : Q') (qP b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec Gamma.length)
    (hstart : polyAt Gamma i ∈ selectByBits Gamma background)
    (hself : compatibleB (polyAt Gamma i) (polyAt Gamma i) = false) :
    chainCodeWeight w qP b2 Gamma label (polyAt Gamma i) (fun _ => true)
        (eraseOccChainCode Gamma
          (occurrenceChainCodeOfWalk walk background)) ≈ 0 := by
  cases walk with
  | single i =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode,
        chainCodeWeight]
      cases hgate : qP (polyAt Gamma i) && b2 (polyAt Gamma i) with
      | false => exact Q'.eqv_refl 0
      | true =>
          simp only [hgate, if_true]
          have hall : (selectByBits Gamma background).all
              (fun U => (qP U && true) &&
                compatibleB (polyAt Gamma i) U) = false := by
            cases h : (selectByBits Gamma background).all
                (fun U => (qP U && true) &&
                  compatibleB (polyAt Gamma i) U) with
            | false => rfl
            | true =>
                have hbad := List.all_eq_true.mp h (polyAt Gamma i) hstart
                simp [hself] at hbad
          unfold admissibleFamilyWeight
          rw [hall]
          exact Q'.mul_zero_eqv _
  | @cons i k j hedge rest =>
      simp only [occurrenceChainCodeOfWalk, eraseOccChainCode,
        chainCodeWeight]
      rw [CWalk.start_eq]
      cases hgate : qP (polyAt Gamma k) &&
          !(compatibleB (polyAt Gamma i) (polyAt Gamma k)) with
      | false =>
          simp only [hgate, Bool.false_eq_true, if_false]
          exact Q'.mul_zero_eqv _
      | true =>
          simp only [hgate, if_true]
          have hbg : (fun U => true &&
              compatibleB (polyAt Gamma i) U) (polyAt Gamma i) = false := by
            simp [hself]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (occurrenceWalkWeight_eqv_zero_of_bg_witness w qP b2 Gamma
                label rest background
                (fun U => true && compatibleB (polyAt Gamma i) U)
                (polyAt Gamma i) hstart hbg)) ?_
          exact Q'.mul_zero_eqv _

/-! ## 2. The packed exceptional code is zero for a nonempty mark -/

theorem marked_mem_packed_terminal_background
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 entry.1) ∈
      selectByBits Gamma (switchedBranchCode Gamma b2 entry.1).1 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  have hat : (switchedBranchCode Gamma b2 pair).1.at
      (exceptionalMarkedIndex Gamma b1 b2 pair) = true := by
    unfold switchedBranchCode
    rw [bitsFromMask_at Gamma.length _ 0
      (exceptionalMarkedIndex Gamma b1 b2 pair) facts.marked_lt]
    simp only [Nat.zero_add]
    unfold switchedLeft swapLeftMask
    rw [facts.marked_reached]
    exact facts.marked_right_true
  exact selectByBits_mem_of_at_true Gamma
    (switchedBranchCode Gamma b2 pair).1
    (exceptionalMarkedIndex Gamma b1 b2 pair) facts.marked_lt hat

theorem exceptionalBranchCarrierCode_weight_eqv_zero_of_mark_nonempty
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hne : polyAt Gamma
      (exceptionalMarkedIndex Gamma b1 b2 entry.1) ≠ []) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (exceptionalBranchCarrierCode Gamma qP b1 b2 entry) ≈ 0 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let switched := switchedBranchCode Gamma b2 pair
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hq : qP (polyAt Gamma
      (exceptionalMarkedIndex Gamma b1 b2 pair)) = true :=
    facts.right_q _ facts.marked_lt facts.marked_right_true
  have hhead : (qP (polyAt Gamma
      (exceptionalMarkedIndex Gamma b1 b2 pair)) &&
        b1 (polyAt Gamma
          (exceptionalMarkedIndex Gamma b1 b2 pair))) = true :=
    (Bool.and_eq_true _ _).mpr ⟨hq, facts.marked_b1⟩
  have hchain := occurrenceWalkWeight_eqv_zero_of_start_in_background
    w qP b2 Gamma label path.indexWalk switched.1
    (marked_mem_packed_terminal_background Gamma qP b1 b2 entry)
    (compatibleB_self_eq_false hne)
  change carrierXiCodeWeight w qP b1 b2 Gamma label
    ((polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair),
        eraseOccChainCode Gamma
          (occurrenceChainCodeOfWalk path.indexWalk switched.1)),
      selectByBits Gamma switched.2) ≈ 0
  unfold carrierXiCodeWeight carrierCodeWeight
  simp only [Prod.fst, Prod.snd]
  rw [if_pos hhead]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hchain) ?_
  exact Q'.zero_mul_eqv _

#print axioms compatibleB_self_eq_false
#print axioms occurrenceWalkWeight_eqv_zero_of_bg_witness
#print axioms occurrenceWalkWeight_eqv_zero_of_start_in_background
#print axioms marked_mem_packed_terminal_background
#print axioms exceptionalBranchCarrierCode_weight_eqv_zero_of_mark_nonempty

end YMGap.Continuum.XiExceptionalBranchPackingFence
