/-
# Exact weight of the unconditional path-safe router

At a safe occurrence the router leaves the residual sides in their two target
slots.  At an unsafe occurrence it swaps precisely when the left bit is set.
Source admissibility excludes the only bad state (both residual bits set), so
this source-derived cut is an exact occurrence-mask swap.  Hence the
path-safe target has exactly the exceptional source weight without a
`rightSafe` hypothesis.
-/

import YMGap.Continuum.XiExceptionalPathSafeInjection

namespace YMGap.Continuum.XiExceptionalPathSafeExactWeight

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathBitWeight
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalPathSafeInjection

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact router algebra under unsafe exclusivity -/

def pathSafeSwapCut (safe : Nat → Bool) (left : OccBitVec n) : Nat → Bool :=
  fun i => (!safe i) && left.at i

theorem routedBackground_eq_pathSafeSwap_on
    (safe : Nat → Bool) (left right : OccBitVec n)
    (hunsafeExclusive : ∀ i, i < n → safe i = false →
      left.at i = true → right.at i = false)
    (i : Nat) (hi : i < n) :
    bitMask (routedBackground safe left) i =
      swapLeftMask (pathSafeSwapCut safe left)
        (bitMask left) (bitMask right) i := by
  change (routedBackground safe left).at i =
    swapLeftMask (pathSafeSwapCut safe left)
      (bitMask left) (bitMask right) i
  rw [routedBackground_at safe left i hi]
  unfold pathSafeSwapCut bitMask swapLeftMask
  cases hs : safe i with
  | true => simp [hs]
  | false =>
      cases hl : left.at i with
      | false => simp [hs, hl]
      | true => simp [hs, hl, hunsafeExclusive i hi hs hl]

theorem routedExternal_eq_pathSafeSwap_on
    (safe : Nat → Bool) (left right : OccBitVec n)
    (hunsafeExclusive : ∀ i, i < n → safe i = false →
      left.at i = true → right.at i = false)
    (i : Nat) (hi : i < n) :
    bitMask (routedExternal safe left right) i =
      swapRightMask (pathSafeSwapCut safe left)
        (bitMask left) (bitMask right) i := by
  change (routedExternal safe left right).at i =
    swapRightMask (pathSafeSwapCut safe left)
      (bitMask left) (bitMask right) i
  rw [routedExternal_at safe left right i hi]
  unfold pathSafeSwapCut bitMask swapRightMask
  cases hs : safe i with
  | true => simp [hs]
  | false =>
      cases hl : left.at i with
      | false => simp [hs, hl]
      | true => simp [hs, hl, hunsafeExclusive i hi hs hl]

theorem routedMaskWeight_preserved_of_unsafe_exclusive
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length)
    (hunsafeExclusive : ∀ i, i < Gamma.length → safe i = false →
      left.at i = true → right.at i = false) :
    maskWeight w Gamma label (bitMask (routedBackground safe left)) *
        maskWeight w Gamma label
          (bitMask (routedExternal safe left right)) ≈
      maskWeight w Gamma label (bitMask left) *
        maskWeight w Gamma label (bitMask right) := by
  rw [maskWeight_congr_on w Gamma label
      (bitMask (routedBackground safe left))
      (swapLeftMask (pathSafeSwapCut safe left)
        (bitMask left) (bitMask right))
      (routedBackground_eq_pathSafeSwap_on safe left right hunsafeExclusive),
    maskWeight_congr_on w Gamma label
      (bitMask (routedExternal safe left right))
      (swapRightMask (pathSafeSwapCut safe left)
        (bitMask left) (bitMask right))
      (routedExternal_eq_pathSafeSwap_on safe left right hunsafeExclusive)]
  exact maskWeight_swap_preserved w Gamma label
    (pathSafeSwapCut safe left) (bitMask left) (bitMask right)

theorem routedFamilyActivity_preserved_of_unsafe_exclusive
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length)
    (hunsafeExclusive : ∀ i, i < Gamma.length → safe i = false →
      left.at i = true → right.at i = false) :
    familyActivity w (selectByBits Gamma (routedBackground safe left)) label *
        familyActivity w
          (selectByBits Gamma (routedExternal safe left right)) label ≈
      familyActivity w (selectByBits Gamma left) label *
        familyActivity w (selectByBits Gamma right) label := by
  have hout := routedMaskWeight_preserved_of_unsafe_exclusive
    w Gamma label safe left right hunsafeExclusive
  have hbg := maskWeight_eqv_familyActivity w Gamma label
    (bitMask (routedBackground safe left))
  have hext := maskWeight_eqv_familyActivity w Gamma label
    (bitMask (routedExternal safe left right))
  have hleft := maskWeight_eqv_familyActivity w Gamma label (bitMask left)
  have hright := maskWeight_eqv_familyActivity w Gamma label (bitMask right)
  rw [maskFamily_toMask_eq_selectByBits] at hbg hext hleft hright
  exact Q'.eqv_trans _ _ _
    (mul_eqv_congr_both (Q'.eqv_symm hbg) (Q'.eqv_symm hext))
    (Q'.eqv_trans _ _ _ hout (mul_eqv_congr_both hleft hright))

/-! ## 2. Checkable target-validity package -/

structure PathSafeRoutedFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Type where
  backgroundCompatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    familyCompatibleB (selectByBits Gamma
      (routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual)) = true
  backgroundQ :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    (selectByBits Gamma
      (routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual)).all qP = true
  backgroundPath :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    ∀ X, X ∈ path.polymerWalk.vertices →
      ∀ T, T ∈ selectByBits Gamma
        (routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
          leftResidual) → compatibleB X T = true
  externalCompatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    familyCompatibleB (selectByBits Gamma
      (routedExternal (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual rightResidual)) = true
  externalQ :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    (selectByBits Gamma
      (routedExternal (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual rightResidual)).all qP = true

private theorem residual_maskWeight_eq
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (path bits : OccBitVec Gamma.length) :
    maskWeight w Gamma label (bitMask (residualBits path bits)) =
      maskWeight w Gamma label
        (residualMask (bitMask path) (bitMask bits)) := by
  apply maskWeight_congr_on
  intro i hi
  change (residualBits path bits).at i =
    residualMask (bitMask path) (bitMask bits) i
  rw [residualBits_at path bits i hi]
  rfl

private theorem switchedCode_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem switchedCode_at_right
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem exceptionalPathSafeCarrierCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (htarget : PathSafeRoutedFacts Gamma qP b1 b2 entry) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let rightResidual := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  let background := routedBackground safe leftResidual
  let external := routedExternal safe leftResidual rightResidual
  have hunsafeExclusive : ∀ i, i < Gamma.length → safe i = false →
      leftResidual.at i = true → rightResidual.at i = false := by
    intro i hi hunsafe hleft
    cases hright : rightResidual.at i with
    | false => rfl
    | true =>
        exact False.elim (exceptional_unsafe_cross_side_impossible
          Gamma qP b1 b2 entry entry rfl i hi
          (by simpa [safe, exceptionalPathSafe] using hunsafe) hleft hright)
  have hcustom := exceptionalCustomCarrierCode_weight_eqv
    w qP b1 b2 Gamma label entry background external
    htarget.backgroundCompatible htarget.backgroundQ
    htarget.backgroundPath htarget.externalCompatible htarget.externalQ
  dsimp only at hcustom
  have hsourceEq := occurrencePairWeight_eq_source_activity_of_mem
    w qP b1 b2 Gamma label pair entry.2
  have hleftOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.1)
  have hrightOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.2)
  rw [maskFamily_toMask_eq_selectByBits] at hleftOriginal hrightOriginal
  have hsourceToOriginal :
      occurrencePairWeight w qP b1 b2 Gamma label pair ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hsourceEq)
      (mul_eqv_congr_both (Q'.eqv_symm hleftOriginal)
        (Q'.eqv_symm hrightOriginal))
  have hswitchedLeft :
      maskWeight w Gamma label (bitMask switched.1) =
        maskWeight w Gamma label
          (switchedLeft Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedCode_at_left Gamma b2 pair i hi
  have hswitchedRight :
      maskWeight w Gamma label (bitMask switched.2) =
        maskWeight w Gamma label
          (switchedRight Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedCode_at_right Gamma b2 pair i hi
  have hswitch :
      maskWeight w Gamma label (bitMask switched.1) *
          maskWeight w Gamma label (bitMask switched.2) ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) := by
    rw [hswitchedLeft, hswitchedRight]
    exact maskWeight_swap_preserved w Gamma label
      (forwardComponent Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2))
      (bitMask pair.1) (bitMask pair.2)
  have hpartition := maskWeight_path_partition w Gamma label
    (bitMask pathBits) (bitMask switched.1) (bitMask switched.2)
    (exceptional_pathBits_switched_exclusive Gamma qP b1 b2 entry)
  have hleftResidualEq := residual_maskWeight_eq w Gamma label
    pathBits switched.1
  have hrightResidualEq := residual_maskWeight_eq w Gamma label
    pathBits switched.2
  rw [← hleftResidualEq, ← hrightResidualEq] at hpartition
  have hpath := pathOccurrenceMaskWeight_eqv_walk w Gamma label path
  have hleftResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask leftResidual)
  have hrightResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask rightResidual)
  rw [maskFamily_toMask_eq_selectByBits] at hleftResidual hrightResidual
  have hrouted := routedFamilyActivity_preserved_of_unsafe_exclusive
    w Gamma label safe leftResidual rightResidual hunsafeExclusive
  have hsourceToFactor :
      occurrencePairWeight w qP b1 b2 Gamma label pair ≈
        (path.polymerWalk.activityWeight w label *
          familyActivity w (selectByBits Gamma background) label) *
          familyActivity w (selectByBits Gamma external) label := by
    refine Q'.eqv_trans _ _ _ hsourceToOriginal ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hswitch) ?_
    refine Q'.eqv_trans _ _ _ hpartition ?_
    refine Q'.eqv_trans _ _ _
      (mul_eqv_congr_both hpath
        (mul_eqv_congr_both hleftResidual hrightResidual)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrouted)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  change occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
    (exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label pair
  exact Q'.eqv_trans _ _ _ hcustom (Q'.eqv_symm hsourceToFactor)

#print axioms routedMaskWeight_preserved_of_unsafe_exclusive
#print axioms routedFamilyActivity_preserved_of_unsafe_exclusive
#print axioms exceptionalPathSafeCarrierCode_weight_eqv_source

end YMGap.Continuum.XiExceptionalPathSafeExactWeight
