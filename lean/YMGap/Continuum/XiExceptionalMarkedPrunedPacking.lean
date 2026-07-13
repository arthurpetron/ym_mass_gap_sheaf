/-
# Mark-pruned branch-preserving carrier packing

The first full branch packing failed because its terminal background retained
the marked start itself.  This successor clears exactly that known bit.  The
cleared bit costs no information: the carrier start recovers its index and an
exceptional switched-left mask is known to contain it.  Thus the modified
code is still injective on exceptional sources while avoiding the immediate
self-incompatibility fence.
-/

import YMGap.Continuum.XiExceptionalSafeFiberFence

namespace YMGap.Continuum.XiExceptionalMarkedPrunedPacking

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Clear one recoverable occurrence bit -/

def clearOccurrenceBit (bits : OccBitVec n) (marked : Nat) : OccBitVec n :=
  bitsFromMask n (fun i => decide (i ≠ marked) && bits.at i) 0

theorem clearOccurrenceBit_at_of_lt (bits : OccBitVec n)
    (marked i : Nat) (hi : i < n) :
    (clearOccurrenceBit bits marked).at i =
      (decide (i ≠ marked) && bits.at i) := by
  unfold clearOccurrenceBit
  simpa using bitsFromMask_at n
    (fun j => decide (j ≠ marked) && bits.at j) 0 i hi

theorem clearOccurrenceBit_recovers
    (left right : OccBitVec n) (markedLeft markedRight : Nat)
    (hmarked : markedLeft = markedRight)
    (hleftMarked : left.at markedLeft = true)
    (hrightMarked : right.at markedRight = true)
    (hclear : clearOccurrenceBit left markedLeft =
      clearOccurrenceBit right markedRight) :
    left = right := by
  apply BitVec.ext
  intro i
  by_cases hi : i < n
  · have hat := congrArg (fun bits => bits.at i) hclear
    change (clearOccurrenceBit left markedLeft).at i =
      (clearOccurrenceBit right markedRight).at i at hat
    rw [clearOccurrenceBit_at_of_lt left markedLeft i hi,
      clearOccurrenceBit_at_of_lt right markedRight i hi] at hat
    by_cases him : i = markedLeft
    · subst i
      rw [← hmarked] at hrightMarked
      exact hleftMarked.trans hrightMarked.symm
    · have hir : i ≠ markedRight := by
        intro hir
        apply him
        exact hir.trans hmarked.symm
      simpa [him, hir] using hat
  · have hge : n ≤ i := by omega
    exact (bitVec_at_false_of_ge left i hge).trans
      (bitVec_at_false_of_ge right i hge).symm

/-! ## 2. The modified branch carrier -/

def exceptionalMarkedPrunedCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let switched := switchedBranchCode Gamma b2 pair
  let marked := exceptionalMarkedIndex Gamma b1 b2 pair
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  { carrier :=
      { start := marked
        chain := occurrenceChainCodeOfWalk path.indexWalk
          (clearOccurrenceBit switched.1 marked) }
    external := switched.2 }

theorem exceptionalMarkedPrunedCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exceptionalMarkedPrunedCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let switched := switchedBranchCode Gamma b2 pair
  let marked := exceptionalMarkedIndex Gamma b1 b2 pair
  let background := clearOccurrenceBit switched.1 marked
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  unfold occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨switched.2, bitVectors_complete switched.2, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(exceptionalMarkedPrunedCarrierCode Gamma qP b1 b2 entry).carrier,
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨marked, occurrenceIndices_complete facts.marked_lt, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk path.indexWalk background, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma background path.indexWalk
    Gamma.length
  · have hlen := path.length_le
    rw [path.polymer_vertices, List.length_map] at hlen
    exact hlen
  · intro k hk
    have hseedN := (forwardSeed_parts Gamma.length
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
      path.seed_true).1
    exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) path.indexWalk hseedN k hk

/-! ## 3. Recovery and injectivity -/

theorem switchedBranchCode_left_marked
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (switchedBranchCode Gamma b2 entry.1).1.at
      (exceptionalMarkedIndex Gamma b1 b2 entry.1) = true := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  unfold switchedBranchCode
  rw [bitsFromMask_at Gamma.length _ 0
    (exceptionalMarkedIndex Gamma b1 b2 pair) facts.marked_lt]
  simp only [Nat.zero_add]
  unfold switchedLeft swapLeftMask
  rw [facts.marked_reached]
  exact facts.marked_right_true

theorem exceptionalMarkedPrunedCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : exceptionalMarkedPrunedCarrierCode Gamma qP b1 b2 entry1 =
      exceptionalMarkedPrunedCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have hmarked : exceptionalMarkedIndex Gamma b1 b2 entry1.1 =
      exceptionalMarkedIndex Gamma b1 b2 entry2.1 :=
    congrArg (fun code => code.carrier.start) hcode
  have hclearedRaw := congrArg
    (fun code => terminalBackground code.carrier.chain) hcode
  have hcleared :
      clearOccurrenceBit (switchedBranchCode Gamma b2 entry1.1).1
          (exceptionalMarkedIndex Gamma b1 b2 entry1.1) =
        clearOccurrenceBit (switchedBranchCode Gamma b2 entry2.1).1
          (exceptionalMarkedIndex Gamma b1 b2 entry2.1) := by
    simpa [exceptionalMarkedPrunedCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using hclearedRaw
  have hleft : (switchedBranchCode Gamma b2 entry1.1).1 =
      (switchedBranchCode Gamma b2 entry2.1).1 :=
    clearOccurrenceBit_recovers _ _ _ _ hmarked
      (switchedBranchCode_left_marked Gamma qP b1 b2 entry1)
      (switchedBranchCode_left_marked Gamma qP b1 b2 entry2) hcleared
  have hright : (switchedBranchCode Gamma b2 entry1.1).2 =
      (switchedBranchCode Gamma b2 entry2.1).2 := by
    simpa [exceptionalMarkedPrunedCarrierCode] using
      congrArg (fun code => code.external) hcode
  have hswitch : switchedBranchCode Gamma b2 entry1.1 =
      switchedBranchCode Gamma b2 entry2.1 := by
    apply Prod.ext
    · exact hleft
    · exact hright
  have hpairs := switchedBranchCode_injective_on_source Gamma qP b1 b2
    entry1.1 entry2.1 entry1.2 entry2.2 hswitch
  exact Subtype.ext hpairs

#print axioms clearOccurrenceBit_recovers
#print axioms exceptionalMarkedPrunedCarrierCode_mem
#print axioms switchedBranchCode_left_marked
#print axioms exceptionalMarkedPrunedCarrierCode_injective

end YMGap.Continuum.XiExceptionalMarkedPrunedPacking
