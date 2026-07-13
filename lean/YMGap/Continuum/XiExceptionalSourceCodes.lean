/-
# Concrete occurrence source codes for the exceptional Xi branch

This file turns the length-indexed masks of
`XiExceptionalOccurrenceCodes` into the function-valued masks used by the
recovered-component machinery.  It also extracts the pointwise consequences
of source admissibility and chooses a canonical reached marked occurrence by
a bounded Boolean search.
-/

import YMGap.Continuum.XiExceptionalOccurrenceCodes

namespace YMGap.Continuum.XiExceptionalSourceCodes

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

abbrev OccBitVec (n : Nat) :=
  YMGap.Continuum.XiExceptionalOccurrenceCodes.BitVec n

/-! ## 1. Length-indexed masks as occurrence functions -/

def bitMask {n : Nat} (bits : OccBitVec n) : Nat → Bool :=
  fun i => bits.at i

theorem selectByBits_mem_of_at_true :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length) (i : Nat),
      i < Gamma.length → bits.at i = true →
        (polyAt Gamma i) ∈ selectByBits Gamma bits
  | [], .nil, i, hi, _ => by
      simp only [List.length_nil] at hi
      omega
  | x :: xs, .cons false tail, 0, _, hi => by cases hi
  | x :: xs, .cons true tail, 0, _, _ => List.mem_cons_self
  | x :: xs, .cons false tail, i + 1, hi, hbit => by
      simp only [List.length_cons] at hi
      exact selectByBits_mem_of_at_true xs tail i (by omega) hbit
  | x :: xs, .cons true tail, i + 1, hi, hbit => by
      simp only [List.length_cons] at hi
      exact List.mem_cons_of_mem x
        (selectByBits_mem_of_at_true xs tail i (by omega) hbit)

theorem maskFamilyFrom_eq_selectByBits_of_shift :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length)
      (mask : Nat → Bool) (offset : Nat),
      (∀ i, mask (offset + i) = bits.at i) →
        maskFamilyFrom Gamma mask offset = selectByBits Gamma bits
  | [], .nil, _, _, _ => by simp [maskFamilyFrom, selectByBits]
  | X :: Gamma, .cons false tail, mask, offset, h => by
      have hhead : mask offset = false := by
        simpa using h 0
      simp only [maskFamilyFrom, hhead, Bool.false_eq_true, ↓reduceIte,
        selectByBits_cons_false]
      apply maskFamilyFrom_eq_selectByBits_of_shift Gamma tail mask (offset + 1)
      intro i
      rw [show offset + 1 + i = offset + (i + 1) by omega]
      exact h (i + 1)
  | X :: Gamma, .cons true tail, mask, offset, h => by
      have hhead : mask offset = true := by
        simpa using h 0
      simp only [maskFamilyFrom, hhead, ↓reduceIte, selectByBits_cons_true]
      congr 1
      apply maskFamilyFrom_eq_selectByBits_of_shift Gamma tail mask (offset + 1)
      intro i
      rw [show offset + 1 + i = offset + (i + 1) by omega]
      exact h (i + 1)

theorem maskFamily_toMask_eq_selectByBits
    (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length) :
    maskFamily Gamma (bitMask bits) = selectByBits Gamma bits := by
  unfold maskFamily
  apply maskFamilyFrom_eq_selectByBits_of_shift Gamma bits (bitMask bits) 0
  intro i
  simp [bitMask]

theorem all_selectByBits_pointwise
    (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length)
    (q : Polymer L → Bool)
    (hall : (selectByBits Gamma bits).all q = true) :
    ∀ i, i < Gamma.length → bits.at i = true →
      q (polyAt Gamma i) = true := by
  intro i hi hbit
  exact List.all_eq_true.mp hall (polyAt Gamma i)
    (selectByBits_mem_of_at_true Gamma bits i hi hbit)

theorem bitVec_at_false_of_ge : ∀ {n : Nat} (bits : OccBitVec n)
    (i : Nat), n ≤ i → bits.at i = false
  | 0, .nil, _, _ => rfl
  | _ + 1, .cons _ _, 0, h => by omega
  | n + 1, .cons _ tail, i + 1, h =>
      bitVec_at_false_of_ge tail i (by omega)

/-! ## 2. Internal compatibility at distinct selected occurrences -/

theorem selectByBits_pairwise_compatible :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length)
      (i j : Nat),
      i < Gamma.length → j < Gamma.length → i ≠ j →
      bits.at i = true → bits.at j = true →
      familyCompatibleB (selectByBits Gamma bits) = true →
      compatibleB (polyAt Gamma i) (polyAt Gamma j) = true
  | [], .nil, i, _, hi, _, _, _, _, _ => by
      simp only [List.length_nil] at hi
      omega
  | X :: Gamma, .cons false tail, 0, j, _, _, _, hi, _, _ => by cases hi
  | X :: Gamma, .cons true tail, 0, 0, _, _, hij, _, _, _ =>
      absurd rfl hij
  | X :: Gamma, .cons true tail, 0, j + 1, _, hj, _, _, hjbit, hcompat => by
      simp only [List.length_cons] at hj
      rw [selectByBits_cons_true, familyCompatibleB_cons] at hcompat
      have hp := (Bool.and_eq_true _ _).mp hcompat
      exact List.all_eq_true.mp hp.1 (polyAt Gamma j)
        (selectByBits_mem_of_at_true Gamma tail j (by omega) hjbit)
  | X :: Gamma, .cons false tail, i + 1, 0, _, _, _, _, hj, _ => by cases hj
  | X :: Gamma, .cons true tail, i + 1, 0, hi, _, _, hibit, _, hcompat => by
      rw [compatibleB_symm]
      exact selectByBits_pairwise_compatible (X :: Gamma) (.cons true tail)
        0 (i + 1) (by simp) hi (by omega) rfl hibit hcompat
  | X :: Gamma, .cons false tail, i + 1, j + 1,
      hi, hj, hij, hibit, hjbit, hcompat => by
      simp only [List.length_cons] at hi hj
      exact selectByBits_pairwise_compatible Gamma tail i j (by omega) (by omega)
        (fun h => hij (congrArg Nat.succ h)) hibit hjbit hcompat
  | X :: Gamma, .cons true tail, i + 1, j + 1,
      hi, hj, hij, hibit, hjbit, hcompat => by
      simp only [List.length_cons] at hi hj
      rw [selectByBits_cons_true, familyCompatibleB_cons] at hcompat
      exact selectByBits_pairwise_compatible Gamma tail i j (by omega) (by omega)
        (fun h => hij (congrArg Nat.succ h)) hibit hjbit
        ((Bool.and_eq_true _ _).mp hcompat).2

/-! ## 3. Bounded Boolean search for the marked occurrence -/

def anyIndex : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => p 0 || anyIndex n (fun i => p (i + 1))

def firstTrueIndex : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p =>
      if p 0 then 0 else firstTrueIndex n (fun i => p (i + 1)) + 1

theorem firstTrueIndex_of_any : ∀ (n : Nat) (p : Nat → Bool),
    anyIndex n p = true →
      firstTrueIndex n p < n ∧ p (firstTrueIndex n p) = true
  | 0, _, h => by cases h
  | n + 1, p, h => by
      cases hp : p 0 with
      | true => simp [firstTrueIndex, hp]
      | false =>
          have htail : anyIndex n (fun i => p (i + 1)) = true := by
            simpa [anyIndex, hp] using h
          have ih := firstTrueIndex_of_any n (fun i => p (i + 1)) htail
          simp only [firstTrueIndex, hp, Bool.false_eq_true, ↓reduceIte]
          exact ⟨by omega, ih.2⟩

/-! ## 4. The concrete exceptional source list -/

def sourceAdmissible (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (pair : MaskPair Gamma.length) : Bool :=
  let left := leftFamily Gamma pair
  let right := rightFamily Gamma pair
  (((left.all qP && left.all (fun X => !(b1 X))) &&
      familyCompatibleB left) &&
    ((right.all qP && right.all (fun X => !(b2 X))) &&
      familyCompatibleB right))

def reachedMarkedAt (Gamma : List (Polymer L))
    (b1 b2 : Polymer L → Bool) (pair : MaskPair Gamma.length)
    (i : Nat) : Bool :=
  (decide (i < Gamma.length) &&
      rightOnly (pair.1.at i) (pair.2.at i)) &&
    (b1 (polyAt Gamma i) &&
      forwardComponent Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i)

def exceptionalSourceCode (Gamma : List (Polymer L))
    (b1 b2 : Polymer L → Bool) (pair : MaskPair Gamma.length) : Bool :=
  anyIndex Gamma.length (reachedMarkedAt Gamma b1 b2 pair)

def exceptionalSourceCodes (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) : List (MaskPair Gamma.length) :=
  (maskPairs Gamma.length).filter (fun pair =>
    sourceAdmissible Gamma qP b1 b2 pair &&
      exceptionalSourceCode Gamma b1 b2 pair)

def exceptionalMarkedIndex (Gamma : List (Polymer L))
    (b1 b2 : Polymer L → Bool) (pair : MaskPair Gamma.length) : Nat :=
  firstTrueIndex Gamma.length (reachedMarkedAt Gamma b1 b2 pair)

theorem nodup_filter_bool (p : a → Bool) :
    ∀ (xs : List a), xs.Nodup → (xs.filter p).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
      have hp := List.nodup_cons.mp hnd
      rw [List.filter_cons]
      cases hx : p x with
      | false =>
          simp only [hx, Bool.false_eq_true, ↓reduceIte]
          exact nodup_filter_bool p xs hp.2
      | true =>
          simp only [hx, ↓reduceIte]
          apply List.nodup_cons.mpr
          constructor
          · intro hmem
            exact hp.1 (List.mem_filter.mp hmem).1
          · exact nodup_filter_bool p xs hp.2

theorem exceptionalSourceCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (exceptionalSourceCodes Gamma qP b1 b2).Nodup := by
  unfold exceptionalSourceCodes
  exact nodup_filter_bool _ _ (maskPairs_nodup Gamma.length)

theorem exceptionalSourceCode_marked
    (Gamma : List (Polymer L)) (b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (hex : exceptionalSourceCode Gamma b1 b2 pair = true) :
    let marked := exceptionalMarkedIndex Gamma b1 b2 pair
    marked < Gamma.length ∧
      pair.1.at marked = false ∧ pair.2.at marked = true ∧
      b1 (polyAt Gamma marked) = true ∧
      forwardComponent Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) marked = true := by
  dsimp only [exceptionalMarkedIndex]
  have hm := firstTrueIndex_of_any Gamma.length
    (reachedMarkedAt Gamma b1 b2 pair) hex
  unfold reachedMarkedAt at hm
  have hp := (Bool.and_eq_true _ _).mp hm.2
  have hleft := (Bool.and_eq_true _ _).mp hp.1
  have hrightOnly := (Bool.and_eq_true _ _).mp hleft.2
  have htail := (Bool.and_eq_true _ _).mp hp.2
  have hnotLeft : pair.1.at (firstTrueIndex Gamma.length
      (reachedMarkedAt Gamma b1 b2 pair)) = false :=
    eq_false_of_not_true hrightOnly.1
  exact ⟨hm.1, hnotLeft, hrightOnly.2, htail.1, htail.2⟩

/-! ## 5. All graph and predicate facts carried by a source member -/

structure ExceptionalSourceFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) : Type where
  source_admissible : sourceAdmissible Gamma qP b1 b2 pair = true
  exceptional : exceptionalSourceCode Gamma b1 b2 pair = true
  marked_lt : exceptionalMarkedIndex Gamma b1 b2 pair < Gamma.length
  marked_left_false :
    pair.1.at (exceptionalMarkedIndex Gamma b1 b2 pair) = false
  marked_right_true :
    pair.2.at (exceptionalMarkedIndex Gamma b1 b2 pair) = true
  marked_b1 :
    b1 (polyAt Gamma (exceptionalMarkedIndex Gamma b1 b2 pair)) = true
  marked_reached :
    forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
      (exceptionalMarkedIndex Gamma b1 b2 pair) = true
  left_q : ∀ i, i < Gamma.length → pair.1.at i = true →
    qP (polyAt Gamma i) = true
  right_q : ∀ i, i < Gamma.length → pair.2.at i = true →
    qP (polyAt Gamma i) = true
  left_pairwise : ∀ i j, i ≠ j → pair.1.at i = true →
    pair.1.at j = true → compatibleB (polyAt Gamma i) (polyAt Gamma j) = true
  right_pairwise : ∀ i j, i ≠ j → pair.2.at i = true →
    pair.2.at j = true → compatibleB (polyAt Gamma i) (polyAt Gamma j) = true
  right_good : ∀ i, pair.2.at i = true → predAt Gamma b2 i = false
  left_family_compatible :
    familyCompatibleB (leftFamily Gamma pair) = true
  right_family_compatible :
    familyCompatibleB (rightFamily Gamma pair) = true

def exceptionalSourceFactsOfMem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (hmem : pair ∈ exceptionalSourceCodes Gamma qP b1 b2) :
    ExceptionalSourceFacts Gamma qP b1 b2 pair := by
  have hfilter := (List.mem_filter.mp hmem).2
  have hparts := (Bool.and_eq_true _ _).mp hfilter
  have hadmiss := hparts.1
  have hex := hparts.2
  have hm := exceptionalSourceCode_marked Gamma b1 b2 pair hex
  unfold sourceAdmissible at hadmiss
  have hsides := (Bool.and_eq_true _ _).mp hadmiss
  have hleft := (Bool.and_eq_true _ _).mp hsides.1
  have hleftPred := (Bool.and_eq_true _ _).mp hleft.1
  have hright := (Bool.and_eq_true _ _).mp hsides.2
  have hrightPred := (Bool.and_eq_true _ _).mp hright.1
  have hleftQ := all_selectByBits_pointwise Gamma pair.1 qP hleftPred.1
  have hrightQ := all_selectByBits_pointwise Gamma pair.2 qP hrightPred.1
  have hleftPair : ∀ i j, i ≠ j → pair.1.at i = true →
      pair.1.at j = true → compatibleB (polyAt Gamma i) (polyAt Gamma j) = true := by
    intro i j hij hi hj
    have hiN : i < Gamma.length := by
      cases hlt : decide (i < Gamma.length) with
      | true => exact of_decide_eq_true hlt
      | false =>
          have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
          have hiOut : pair.1.at i = false :=
            bitVec_at_false_of_ge pair.1 i (by omega)
          rw [hi] at hiOut
          exact absurd hiOut (by decide)
    have hjN : j < Gamma.length := by
      cases hlt : decide (j < Gamma.length) with
      | true => exact of_decide_eq_true hlt
      | false =>
          have hnlt : ¬ j < Gamma.length := of_decide_eq_false hlt
          have hjOut : pair.1.at j = false :=
            bitVec_at_false_of_ge pair.1 j (by omega)
          rw [hj] at hjOut
          exact absurd hjOut (by decide)
    exact selectByBits_pairwise_compatible Gamma pair.1 i j hiN hjN hij
      hi hj hleft.2
  have hrightPair : ∀ i j, i ≠ j → pair.2.at i = true →
      pair.2.at j = true → compatibleB (polyAt Gamma i) (polyAt Gamma j) = true := by
    intro i j hij hi hj
    have hiN : i < Gamma.length := by
      cases hlt : decide (i < Gamma.length) with
      | true => exact of_decide_eq_true hlt
      | false =>
          have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
          have hiOut : pair.2.at i = false :=
            bitVec_at_false_of_ge pair.2 i (by omega)
          rw [hi] at hiOut
          exact absurd hiOut (by decide)
    have hjN : j < Gamma.length := by
      cases hlt : decide (j < Gamma.length) with
      | true => exact of_decide_eq_true hlt
      | false =>
          have hnlt : ¬ j < Gamma.length := of_decide_eq_false hlt
          have hjOut : pair.2.at j = false :=
            bitVec_at_false_of_ge pair.2 j (by omega)
          rw [hj] at hjOut
          exact absurd hjOut (by decide)
    exact selectByBits_pairwise_compatible Gamma pair.2 i j hiN hjN hij
      hi hj hright.2
  have hrightGood : ∀ i, pair.2.at i = true → predAt Gamma b2 i = false := by
    intro i hi
    cases hlt : decide (i < Gamma.length) with
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
        have hiOut : pair.2.at i = false :=
          bitVec_at_false_of_ge pair.2 i (by omega)
        rw [hi] at hiOut
        exact absurd hiOut (by decide)
    | true =>
        have hiN := of_decide_eq_true hlt
        have hbnot := all_selectByBits_pointwise Gamma pair.2
          (fun X => !(b2 X)) hrightPred.2 i hiN hi
        have hbfalse : b2 (polyAt Gamma i) = false :=
          eq_false_of_not_true hbnot
        simp [predAt, hbfalse]
  exact
    { source_admissible := hadmiss
      exceptional := hex
      marked_lt := hm.1
      marked_left_false := hm.2.1
      marked_right_true := hm.2.2.1
      marked_b1 := hm.2.2.2.1
      marked_reached := hm.2.2.2.2
      left_q := hleftQ
      right_q := hrightQ
      left_pairwise := hleftPair
      right_pairwise := hrightPair
      right_good := hrightGood
      left_family_compatible := hleft.2
      right_family_compatible := hright.2 }

/-! ## 6. A finite branch-preserving switch code -/

/-- Restrict an arbitrary occurrence function to its first `n` bits. -/
def bitsFromMask : (n : Nat) → (Nat → Bool) → Nat → OccBitVec n
  | 0, _, _ => .nil
  | n + 1, mask, offset =>
      .cons (mask offset) (bitsFromMask n mask (offset + 1))

theorem bitsFromMask_at : ∀ (n : Nat) (mask : Nat → Bool)
    (offset i : Nat), i < n →
      (bitsFromMask n mask offset).at i = mask (offset + i)
  | 0, _, _, _, hi => by omega
  | _ + 1, _, _, 0, _ => rfl
  | n + 1, mask, offset, i + 1, hi => by
      change (bitsFromMask n mask (offset + 1)).at i =
        mask (offset + (i + 1))
      rw [bitsFromMask_at n mask (offset + 1) i (by omega)]
      congr 1
      omega

/-- The source-dependent component switch, retained as two finite bit
vectors.  Unlike an exterior-only code, this records every off-path branch
bit. -/
def switchedBranchCode (Gamma : List (Polymer L))
    (b2 : Polymer L → Bool) (pair : MaskPair Gamma.length) :
    MaskPair Gamma.length :=
  let left := bitMask pair.1
  let right := bitMask pair.2
  (bitsFromMask Gamma.length
      (switchedLeft Gamma.length (incAtDistinct Gamma) left right
        (predAt Gamma b2)) 0,
    bitsFromMask Gamma.length
      (switchedRight Gamma.length (incAtDistinct Gamma) left right
        (predAt Gamma b2)) 0)

theorem switchedLeft_false_of_ge
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : Gamma.length ≤ i) :
    switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = false := by
  have hl := bitVec_at_false_of_ge pair.1 i hi
  have hr := bitVec_at_false_of_ge pair.2 i hi
  unfold switchedLeft swapLeftMask bitMask
  cases forwardComponent Gamma.length (incAtDistinct Gamma)
      (fun i => pair.1.at i) (fun i => pair.2.at i) (predAt Gamma b2) i <;>
    simp [hl, hr]

theorem switchedRight_false_of_ge
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : Gamma.length ≤ i) :
    switchedRight Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = false := by
  have hl := bitVec_at_false_of_ge pair.1 i hi
  have hr := bitVec_at_false_of_ge pair.2 i hi
  unfold switchedRight swapRightMask bitMask
  cases forwardComponent Gamma.length (incAtDistinct Gamma)
      (fun i => pair.1.at i) (fun i => pair.2.at i) (predAt Gamma b2) i <;>
    simp [hl, hr]

/-- **Branch preservation.**  On the concrete exceptional source, the two
finite switched masks are injective.  Reverse recovery reconstructs the
source-dependent cut, and the fixed-cut involution then reconstructs every
input occurrence bit, including all branches not used by the selected path. -/
theorem switchedBranchCode_injective_on_source
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair1 pair2 : MaskPair Gamma.length)
    (hmem1 : pair1 ∈ exceptionalSourceCodes Gamma qP b1 b2)
    (hmem2 : pair2 ∈ exceptionalSourceCodes Gamma qP b1 b2)
    (hcode : switchedBranchCode Gamma b2 pair1 =
      switchedBranchCode Gamma b2 pair2) :
    pair1 = pair2 := by
  let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 hmem1
  let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair2 hmem2
  have hleftCode : (switchedBranchCode Gamma b2 pair1).1 =
      (switchedBranchCode Gamma b2 pair2).1 :=
    congrArg Prod.fst hcode
  have hrightCode : (switchedBranchCode Gamma b2 pair1).2 =
      (switchedBranchCode Gamma b2 pair2).2 :=
    congrArg Prod.snd hcode
  have houtLeft : ∀ i,
      switchedLeft Gamma.length (incAtDistinct Gamma)
          (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2) i =
        switchedLeft Gamma.length (incAtDistinct Gamma)
          (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2) i := by
    intro i
    cases hi : decide (i < Gamma.length) with
    | true =>
        have hiN := of_decide_eq_true hi
        have hat := congrArg (fun bits => bits.at i) hleftCode
        unfold switchedBranchCode at hat
        simpa [bitsFromMask_at Gamma.length _ 0 i hiN] using hat
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hi
        rw [switchedLeft_false_of_ge Gamma b2 pair1 i (by omega),
          switchedLeft_false_of_ge Gamma b2 pair2 i (by omega)]
  have houtRight : ∀ i,
      switchedRight Gamma.length (incAtDistinct Gamma)
          (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2) i =
        switchedRight Gamma.length (incAtDistinct Gamma)
          (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2) i := by
    intro i
    cases hi : decide (i < Gamma.length) with
    | true =>
        have hiN := of_decide_eq_true hi
        have hat := congrArg (fun bits => bits.at i) hrightCode
        unfold switchedBranchCode at hat
        simpa [bitsFromMask_at Gamma.length _ 0 i hiN] using hat
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hi
        rw [switchedRight_false_of_ge Gamma b2 pair1 i (by omega),
          switchedRight_false_of_ge Gamma b2 pair2 i (by omega)]
  have hinj := distinct_switched_pair_injective Gamma b2
    (bitMask pair1.1) (bitMask pair1.2)
    (bitMask pair2.1) (bitMask pair2.2)
    facts1.left_pairwise facts1.right_pairwise facts1.right_good
    facts2.left_pairwise facts2.right_pairwise facts2.right_good
    houtLeft houtRight
  apply Prod.ext
  · exact BitVec.ext hinj.1
  · exact BitVec.ext hinj.2

#print axioms maskFamily_toMask_eq_selectByBits
#print axioms all_selectByBits_pointwise
#print axioms selectByBits_pairwise_compatible
#print axioms firstTrueIndex_of_any
#print axioms exceptionalSourceCodes_nodup
#print axioms exceptionalSourceCode_marked
#print axioms exceptionalSourceFactsOfMem
#print axioms bitsFromMask_at
#print axioms switchedLeft_false_of_ge
#print axioms switchedRight_false_of_ge
#print axioms switchedBranchCode_injective_on_source

end YMGap.Continuum.XiExceptionalSourceCodes
