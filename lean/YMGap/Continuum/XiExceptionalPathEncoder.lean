/-
# Canonical exceptional paths as occurrence carrier codes

This successor attaches the canonical reached marked path to the
occurrence-indexed target enumeration.  It proves target membership for the
path together with the two recovered exterior masks.  Branch preservation is
kept separate in `switchedBranchCode`; the remaining packing step must retain
that payload without changing this carrier weight.
-/

import YMGap.Continuum.XiExceptionalSourceCodes

namespace YMGap.Continuum.XiExceptionalPathEncoder

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

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Function masks select the same family as their finite codes -/

theorem select_bitsFromMask_eq_maskFamilyFrom :
    ∀ (Gamma : List (Polymer L)) (mask : Nat → Bool) (offset : Nat),
      selectByBits Gamma (bitsFromMask Gamma.length mask offset) =
        maskFamilyFrom Gamma mask offset
  | [], _, _ => by simp [bitsFromMask, selectByBits, maskFamilyFrom]
  | X :: Gamma, mask, offset => by
      cases hm : mask offset with
      | false =>
          simp only [List.length_cons, bitsFromMask, selectByBits, hm,
            Bool.false_eq_true, ↓reduceIte, maskFamilyFrom]
          exact select_bitsFromMask_eq_maskFamilyFrom Gamma mask (offset + 1)
      | true =>
          simp only [List.length_cons, bitsFromMask, selectByBits, hm,
            ↓reduceIte, maskFamilyFrom]
          rw [select_bitsFromMask_eq_maskFamilyFrom Gamma mask (offset + 1)]

theorem select_bitsFromMask_eq_maskFamily
    (Gamma : List (Polymer L)) (mask : Nat → Bool) :
    selectByBits Gamma (bitsFromMask Gamma.length mask 0) =
      maskFamily Gamma mask :=
  select_bitsFromMask_eq_maskFamilyFrom Gamma mask 0

/-! ## 2. Encode a cons-form occurrence walk -/

def occurrenceChainCodeOfWalk {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec n) : OccChainCode n :=
  match walk with
  | .single _ => .terminal background
  | .cons _ rest => .step rest.start
      (occurrenceChainCodeOfWalk rest background)

theorem terminal_occurrence_code_mem
    (Gamma : List (Polymer L)) (background : OccBitVec Gamma.length) :
    ∀ fuel : Nat,
      OccChainCode.terminal background ∈ occurrenceChainCodes Gamma fuel
  | 0 => by
      unfold occurrenceChainCodes occurrenceTerminalCodes
      exact List.mem_map.mpr ⟨background, bitVectors_complete background, rfl⟩
  | fuel + 1 => by
      unfold occurrenceChainCodes
      apply List.mem_append_left
      unfold occurrenceTerminalCodes
      exact List.mem_map.mpr ⟨background, bitVectors_complete background, rfl⟩

theorem occurrenceChainCodeOfWalk_mem
    (Gamma : List (Polymer L)) (background : OccBitVec Gamma.length) :
    ∀ {edge : Nat → Nat → Bool} {i j : Nat}
      (walk : CWalk edge i j) (fuel : Nat),
      walk.vertices.length ≤ fuel →
      (∀ k, k ∈ walk.vertices → k < Gamma.length) →
      occurrenceChainCodeOfWalk walk background ∈
        occurrenceChainCodes Gamma fuel
  | _, _, _, .single _, fuel, _, _ =>
      terminal_occurrence_code_mem Gamma background fuel
  | edge, i, j, .cons hedge rest, 0, hlen, _ => by
      simp [CWalk.vertices] at hlen
  | edge, i, j, .cons hedge rest, fuel + 1, hlen, hbounds => by
      unfold occurrenceChainCodeOfWalk occurrenceChainCodes
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      have hnext : rest.start < Gamma.length :=
        hbounds rest.start (List.mem_cons_of_mem i (CWalk.start_mem_vertices rest))
      refine ⟨rest.start, occurrenceIndices_complete hnext, ?_⟩
      apply List.mem_map.mpr
      refine ⟨occurrenceChainCodeOfWalk rest background, ?_, rfl⟩
      apply occurrenceChainCodeOfWalk_mem Gamma background rest fuel
      · simpa [CWalk.vertices] using hlen
      · intro k hk
        exact hbounds k (List.mem_cons_of_mem i hk)

/-! ## 3. The canonical reached path code -/

def sourceExceptionalPath
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : ExceptionalSourceFacts Gamma qP b1 b2 pair) :=
  distinctExceptionalPolymerPathOfReach Gamma qP b2
    (bitMask pair.1) (bitMask pair.2)
    (exceptionalMarkedIndex Gamma b1 b2 pair)
    facts.left_q facts.right_q facts.marked_reached

def sourcePathCarrierXiCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : ExceptionalSourceFacts Gamma qP b1 b2 pair) :
    OccCarrierXiCodeAt Gamma :=
  let cut := forwardComponent Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
  let background := bitsFromMask Gamma.length
    (outsideMask cut (bitMask pair.1)) 0
  let external := bitsFromMask Gamma.length
    (outsideMask cut (bitMask pair.2)) 0
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  { carrier :=
      { start := exceptionalMarkedIndex Gamma b1 b2 pair
        chain := occurrenceChainCodeOfWalk path.indexWalk background }
    external := external }

theorem sourcePathCarrierXiCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : ExceptionalSourceFacts Gamma qP b1 b2 pair) :
    sourcePathCarrierXiCode Gamma qP b1 b2 pair facts ∈
      occurrenceCarrierXiCodes Gamma := by
  let cut := forwardComponent Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
  let background := bitsFromMask Gamma.length
    (outsideMask cut (bitMask pair.1)) 0
  let external := bitsFromMask Gamma.length
    (outsideMask cut (bitMask pair.2)) 0
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  unfold occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨external, bitVectors_complete external, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(sourcePathCarrierXiCode Gamma qP b1 b2 pair facts).carrier,
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨exceptionalMarkedIndex Gamma b1 b2 pair,
    occurrenceIndices_complete facts.marked_lt, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk path.indexWalk background, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma background path.indexWalk Gamma.length
  · have hlen := path.length_le
    rw [path.polymer_vertices, List.length_map] at hlen
    exact hlen
  · intro k hk
    have hseedN := (forwardSeed_parts Gamma.length
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
      path.seed_true).1
    exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) path.indexWalk hseedN k hk

#print axioms select_bitsFromMask_eq_maskFamily
#print axioms occurrenceChainCodeOfWalk_mem
#print axioms sourcePathCarrierXiCode_mem

end YMGap.Continuum.XiExceptionalPathEncoder
