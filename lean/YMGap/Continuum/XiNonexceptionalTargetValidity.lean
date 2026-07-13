/-
# The nonexceptional component switch lands in the opposite restriction

For an admissible source pair, switch the disagreement component rooted at
left occurrences carrying `b2`.  If no reached right-only occurrence carries
`b1`, the switched left family avoids both `b1` and `b2`, while the switched
right family is unrestricted apart from `qP`.  Internal compatibility is
preserved occurrence by occurrence.  Thus the nonexceptional source maps
exactly into the opposite restricted product.
-/

import YMGap.Continuum.XiAdmissibleSourceSwitch

namespace YMGap.Continuum.XiNonexceptionalTargetValidity

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalSourcePartition
open YMGap.Continuum.XiExceptionalSwitchedCompatibility
open YMGap.Continuum.XiAdmissibleSourceSwitch

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

theorem anyIndex_true_of_point : ∀ (n : Nat) (p : Nat → Bool) (i : Nat),
    i < n → p i = true → anyIndex n p = true
  | 0, _, _, hi, _ => by omega
  | _ + 1, p, 0, _, hp => by simp [anyIndex, hp]
  | n + 1, p, i + 1, hi, hp => by
      unfold anyIndex
      apply (Bool.or_eq_true _ _).mpr
      exact Or.inr (anyIndex_true_of_point n (fun j => p (j + 1)) i
        (by omega) hp)

theorem nonexceptional_of_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (hmem : pair ∈ nonexceptionalSourceCodes Gamma qP b1 b2) :
    sourceAdmissible Gamma qP b1 b2 pair = true ∧
      exceptionalSourceCode Gamma b1 b2 pair = false := by
  have hp := (List.mem_filter.mp hmem).2
  have hsides := (Bool.and_eq_true _ _).mp hp
  exact ⟨hsides.1, eq_false_of_not_true hsides.2⟩

private theorem unreached_left_b2_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair)
    (i : Nat) (hi : i < Gamma.length)
    (hleft : pair.1.at i = true)
    (hunreached : forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = false) :
    b2 (polyAt Gamma i) = false := by
  cases hright : pair.2.at i with
  | true => exact facts.right_avoid i hi hright
  | false =>
      cases hb2 : b2 (polyAt Gamma i) with
      | false => rfl
      | true =>
          have hseed : forwardSeed Gamma.length (bitMask pair.1)
              (bitMask pair.2) (predAt Gamma b2) i = true := by
            simp [forwardSeed, decide_eq_true hi, leftOnly, bitMask,
              hleft, hright, predAt, hb2]
          have hreach := forwardSeed_reached Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) hseed
          rw [hunreached] at hreach
          cases hreach

private theorem reached_right_b1_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair)
    (hnonexceptional : exceptionalSourceCode Gamma b1 b2 pair = false)
    (i : Nat) (hi : i < Gamma.length)
    (hright : pair.2.at i = true)
    (hreached : forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true) :
    b1 (polyAt Gamma i) = false := by
  cases hleft : pair.1.at i with
  | true => exact facts.left_avoid i hi hleft
  | false =>
      cases hb1 : b1 (polyAt Gamma i) with
      | false => rfl
      | true =>
          have hmarked : reachedMarkedAt Gamma b1 b2 pair i = true := by
            unfold reachedMarkedAt
            simp [decide_eq_true hi, rightOnly, hleft, hright, hb1, hreached]
          have hex : exceptionalSourceCode Gamma b1 b2 pair = true := by
            unfold exceptionalSourceCode
            exact anyIndex_true_of_point Gamma.length
              (reachedMarkedAt Gamma b1 b2 pair) i hi hmarked
          rw [hnonexceptional] at hex
          cases hex

theorem switchedLeft_target_predicate
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair)
    (hnonexceptional : exceptionalSourceCode Gamma b1 b2 pair = false)
    (i : Nat) (hi : i < Gamma.length)
    (hout : switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true) :
    (qP (polyAt Gamma i) &&
      !(b1 (polyAt Gamma i) || b2 (polyAt Gamma i))) = true := by
  cases hcut : forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i with
  | false =>
      have hleft : pair.1.at i = true := by
        simpa [switchedLeft, swapLeftMask, hcut, bitMask] using hout
      have hq := facts.left_q i hi hleft
      have hb1 := facts.left_avoid i hi hleft
      have hb2 := unreached_left_b2_false Gamma qP b1 b2 pair facts
        i hi hleft hcut
      simp [hq, hb1, hb2]
  | true =>
      have hright : pair.2.at i = true := by
        simpa [switchedLeft, swapLeftMask, hcut, bitMask] using hout
      have hq := facts.right_q i hi hright
      have hb1 := reached_right_b1_false Gamma qP b1 b2 pair facts
        hnonexceptional i hi hright hcut
      have hb2 := facts.right_avoid i hi hright
      simp [hq, hb1, hb2]

theorem switchedRight_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair)
    (i : Nat) (hi : i < Gamma.length)
    (hout : switchedRight Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true) :
    qP (polyAt Gamma i) = true := by
  cases hcut : forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i with
  | false =>
      have hright : pair.2.at i = true := by
        simpa [switchedRight, swapRightMask, hcut, bitMask] using hout
      exact facts.right_q i hi hright
  | true =>
      have hleft : pair.1.at i = true := by
        simpa [switchedRight, swapRightMask, hcut, bitMask] using hout
      exact facts.left_q i hi hleft

theorem selectByBits_familyCompatible_of_pairwise :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length),
      (∀ i j, i < Gamma.length → j < Gamma.length → i ≠ j →
        bits.at i = true → bits.at j = true →
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = true) →
      familyCompatibleB (selectByBits Gamma bits) = true
  | [], .nil, _ => rfl
  | X :: Gamma, .cons false tail, h => by
      rw [selectByBits_cons_false]
      apply selectByBits_familyCompatible_of_pairwise Gamma tail
      intro i j hi hj hij hbi hbj
      exact h (i + 1) (j + 1) (by simp; omega) (by simp; omega)
        (fun hs => hij (Nat.succ.inj hs)) hbi hbj
  | X :: Gamma, .cons true tail, h => by
      rw [selectByBits_cons_true, familyCompatibleB_cons]
      apply (Bool.and_eq_true _ _).mpr
      constructor
      · apply List.all_eq_true.mpr
        intro Y hY
        have hYmask : Y ∈ maskFamily Gamma (bitMask tail) := by
          rw [maskFamily_toMask_eq_selectByBits]
          exact hY
        obtain ⟨j, hj, hbit, hval⟩ :=
          mem_maskFamily_occurrence Gamma (bitMask tail) hYmask
        have hc := h 0 (j + 1) (by simp) (by simp; omega) (by omega)
          rfl hbit
        simpa [polyAt_cons_zero, polyAt_cons_succ, hval] using hc
      · apply selectByBits_familyCompatible_of_pairwise Gamma tail
        intro i j hi hj hij hbi hbj
        exact h (i + 1) (j + 1) (by simp; omega) (by simp; omega)
          (fun hs => hij (Nat.succ.inj hs)) hbi hbj

theorem switched_left_family_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair) :
    familyCompatibleB
      (leftFamily Gamma (switchedBranchCode Gamma b2 pair)) = true := by
  unfold leftFamily
  apply selectByBits_familyCompatible_of_pairwise
  intro i j hi hj hij hbi hbj
  have hsi := switchedCode_at_left Gamma b2 pair i hi
  have hsj := switchedCode_at_left Gamma b2 pair j hj
  rw [hbi] at hsi
  rw [hbj] at hsj
  have hguard := switchedLeft_sameSide_guard Gamma.length
    (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
    (predAt Gamma b2)
    (sameSide_guard_incAtDistinct Gamma (bitMask pair.1) facts.left_pairwise)
    (sameSide_guard_incAtDistinct Gamma (bitMask pair.2) facts.right_pairwise)
    i j hi hj hsi.symm hsj.symm
  exact compatibleB_of_incAtDistinct_symConflict_false Gamma hij hguard

theorem switched_right_family_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair) :
    familyCompatibleB
      (rightFamily Gamma (switchedBranchCode Gamma b2 pair)) = true := by
  unfold rightFamily
  apply selectByBits_familyCompatible_of_pairwise
  intro i j hi hj hij hbi hbj
  have hsi := switchedCode_at_right Gamma b2 pair i hi
  have hsj := switchedCode_at_right Gamma b2 pair j hj
  rw [hbi] at hsi
  rw [hbj] at hsj
  have hguard := switchedRight_sameSide_guard Gamma.length
    (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
    (predAt Gamma b2)
    (sameSide_guard_incAtDistinct Gamma (bitMask pair.1) facts.left_pairwise)
    (sameSide_guard_incAtDistinct Gamma (bitMask pair.2) facts.right_pairwise)
    i j hi hj hsi.symm hsj.symm
  exact compatibleB_of_incAtDistinct_symConflict_false Gamma hij hguard

theorem nonexceptional_switched_target_admissible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (hadmiss : sourceAdmissible Gamma qP b1 b2 pair = true)
    (hnonexceptional : exceptionalSourceCode Gamma b1 b2 pair = false) :
    sourceAdmissible Gamma qP (fun X => b1 X || b2 X) (fun _ => false)
      (switchedBranchCode Gamma b2 pair) = true := by
  let facts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair hadmiss
  let switched := switchedBranchCode Gamma b2 pair
  have hleftTarget : (leftFamily Gamma switched).all
      (fun X => qP X && !(b1 X || b2 X)) = true := by
    unfold leftFamily
    rw [← maskFamily_toMask_eq_selectByBits]
    apply maskFamily_all_of_pointwise
    intro i hi hbit
    have hout : switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true := by
      rw [← switchedCode_at_left Gamma b2 pair i hi]
      simpa [switched, bitMask] using hbit
    exact switchedLeft_target_predicate Gamma qP b1 b2 pair facts
      hnonexceptional i hi hout
  have hrightQ : (rightFamily Gamma switched).all qP = true := by
    unfold rightFamily
    rw [← maskFamily_toMask_eq_selectByBits]
    apply maskFamily_all_of_pointwise
    intro i hi hbit
    have hout : switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true := by
      rw [← switchedCode_at_right Gamma b2 pair i hi]
      simpa [switched, bitMask] using hbit
    exact switchedRight_q Gamma qP b1 b2 pair facts i hi hout
  have hleftParts :
      (leftFamily Gamma switched).all qP = true ∧
        (leftFamily Gamma switched).all
          (fun X => !((fun X => b1 X || b2 X) X)) = true := by
    have hboth :
        ((leftFamily Gamma switched).all qP &&
          (leftFamily Gamma switched).all (fun X => !(b1 X || b2 X))) =
            true := by
      rw [all_and]
      exact hleftTarget
    exact (Bool.and_eq_true _ _).mp hboth
  have hrightAvoid : (rightFamily Gamma switched).all
      (fun X => !((fun _ : Polymer L => false) X)) = true := by
    apply List.all_eq_true.mpr
    intro X _
    rfl
  unfold sourceAdmissible
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · apply (Bool.and_eq_true _ _).mpr
    exact ⟨(Bool.and_eq_true _ _).mpr hleftParts,
      switched_left_family_compatible Gamma qP b1 b2 pair facts⟩
  · apply (Bool.and_eq_true _ _).mpr
    exact ⟨(Bool.and_eq_true _ _).mpr ⟨hrightQ, hrightAvoid⟩,
      switched_right_family_compatible Gamma qP b1 b2 pair facts⟩

theorem nonexceptional_switched_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (pair : MaskPair Gamma.length)
    (hadmiss : sourceAdmissible Gamma qP b1 b2 pair = true)
    (hnonexceptional : exceptionalSourceCode Gamma b1 b2 pair = false) :
    occurrencePairWeight w qP (fun X => b1 X || b2 X) (fun _ => false)
        Gamma label (switchedBranchCode Gamma b2 pair) ≈
      occurrencePairWeight w qP b1 b2 Gamma label pair := by
  have htarget := nonexceptional_switched_target_admissible
    Gamma qP b1 b2 pair hadmiss hnonexceptional
  have htargetEq := occurrencePairWeight_eq_source_activity w qP
    (fun X => b1 X || b2 X) (fun _ => false) Gamma label
    (switchedBranchCode Gamma b2 pair) htarget
  have hsourceEq := occurrencePairWeight_eq_source_activity w qP b1 b2
    Gamma label pair hadmiss
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq htargetEq)
    (Q'.eqv_trans _ _ _
      (switchedBranchCode_familyActivity_preserved w Gamma b2 label pair)
      (Q'.eqv_symm (Q'.eqv_of_eq hsourceEq)))

#print axioms anyIndex_true_of_point
#print axioms nonexceptional_of_mem
#print axioms switchedLeft_target_predicate
#print axioms switchedRight_q
#print axioms selectByBits_familyCompatible_of_pairwise
#print axioms switched_left_family_compatible
#print axioms switched_right_family_compatible
#print axioms nonexceptional_switched_target_admissible
#print axioms nonexceptional_switched_weight_eqv_source

end YMGap.Continuum.XiNonexceptionalTargetValidity
