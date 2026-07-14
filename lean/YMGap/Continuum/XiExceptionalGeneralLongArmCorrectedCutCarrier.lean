/-
# Corrected cut carrier on the actual long-arm geometry

The cut cannot be the carrier start: the start is the marked endpoint of the
short ear.  The corrected construction is the adaptive C12 carrier already
proved in the concrete long-arm geometry.  Its start is always `V0`, its
step word is always `V1,V2,V3`, and the first cut is encoded only by the
terminal/external masks.

This file packages that construction by a source-parameter record and
reproves the properties needed by the parametric route: mask ownership,
carrier injectivity, pairwise disjointness, exact weight normalization,
separation from the canonical full-pattern block, and complete partial/full
coverage.  It contains no new truth-table enumeration.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmCutStartWeightFence

namespace YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned

local infix:50 " ≈ " => Q'.eqv

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

structure CorrectedCutBits where
  x4 : Bool
  x5 : Bool
  x6 : Bool
  x7 : Bool
  x8 : Bool
  x9 : Bool
  x10 : Bool
  x11 : Bool
deriving DecidableEq

def CorrectedCutBits.entry (bits : CorrectedCutBits) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  adaptiveEntry bits.x4 bits.x5 bits.x6 bits.x7 bits.x8 bits.x9
    bits.x10 bits.x11

def CorrectedCutBits.carrier (bits : CorrectedCutBits) :
    OccCarrierXiCodeAt G :=
  adaptiveCarrierCode bits.x4 bits.x5 bits.x6 bits.x7 bits.x8 bits.x9
    bits.x10 bits.x11

def CorrectedCutBits.isFull (bits : CorrectedCutBits) : Bool :=
  fullPattern bits.x4 bits.x5 bits.x6 bits.x7 bits.x8 bits.x9 bits.x10
    bits.x11

/-- The marked carrier start is independent of the cut. -/
theorem correctedCut_start (bits : CorrectedCutBits) :
    bits.carrier.carrier.start = 0 := by rfl

/-- The marked-to-bad step word is independent of the cut; only its terminal
background varies. -/
theorem correctedCut_chain (bits : CorrectedCutBits) :
    bits.carrier.carrier.chain =
      chainFromIndices
        (adaptiveTerminalBits bits.x4 bits.x5 bits.x6 bits.x7 bits.x8
          bits.x9 bits.x10 bits.x11) shortEarTail := by
  rfl

/-- Terminal plus external masks recover the complete source entry. -/
theorem correctedCut_owner (bits : CorrectedCutBits) :
    adaptivePartialOwner bits.carrier = bits.entry := by
  exact adaptivePartialOwner_carrier bits.x4 bits.x5 bits.x6 bits.x7
    bits.x8 bits.x9 bits.x10 bits.x11

/-- The corrected occurrence code is injective although its marked start and
short chain are fixed: equality of codes forces equality of owned source
entries. -/
theorem correctedCut_source_injective {a b : CorrectedCutBits}
    (h : a.carrier = b.carrier) : a.entry = b.entry := by
  rw [← correctedCut_owner a, ← correctedCut_owner b, h]

theorem correctedCut_carriers_ne {a b : CorrectedCutBits}
    (h : a.entry ≠ b.entry) :
    a.carrier ≠ b.carrier := by
  intro hc
  exact h (correctedCut_source_injective hc)

/-- Exact actual-weight normalization on every non-full source. -/
theorem correctedCut_weight_eqv_source (bits : CorrectedCutBits)
    (hpartial : bits.isFull = false)
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        bits.carrier ≈
      occurrencePairWeight w qAll markV0 badV3 G label bits.entry.1 := by
  exact adaptiveCarrierCode_weight_eqv_source bits.x4 bits.x5 bits.x6
    bits.x7 bits.x8 bits.x9 bits.x10 bits.x11 hpartial w label

def CorrectedCutBits.paidBlock (bits : CorrectedCutBits)
    (hpartial : bits.isFull = false) :
    PaidResidualBlock qAll markV0 badV3 G bits.entry :=
  adaptivePaidBlock bits.x4 bits.x5 bits.x6 bits.x7 bits.x8 bits.x9
    bits.x10 bits.x11 hpartial

/-- Partial singleton codes cannot collide with the canonical nine-code
full-pattern payer. -/
theorem correctedCut_not_mem_canonical (bits : CorrectedCutBits)
    (hpartial : bits.isFull = false) :
    bits.carrier ∉ canonicalRepairBlock := by
  exact adaptiveCarrierCode_not_mem_canonical bits.x4 bits.x5 bits.x6
    bits.x7 bits.x8 bits.x9 bits.x10 bits.x11 hpartial

def allPresent : CorrectedCutBits :=
  ⟨true, true, true, true, true, true, true, true⟩

theorem allPresent_entry : allPresent.entry = entry := by rfl

theorem full_eq_allPresent {bits : CorrectedCutBits}
    (hfull : bits.isFull = true) : bits = allPresent := by
  unfold CorrectedCutBits.isFull fullPattern prefix10 prefix9 prefix8
    prefix7 prefix6 prefix5 prefix4 at hfull
  simp only [Bool.and_eq_true] at hfull
  rcases hfull with ⟨⟨⟨⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
  cases bits with
  | mk x4 x5 x6 x7 x8 x9 x10 x11 =>
      simp only at h4 h5 h6 h7 h8 h9 h10 h11
      subst x4
      subst x5
      subst x6
      subst x7
      subst x8
      subst x9
      subst x10
      subst x11
      rfl

/-- The pre-existing complete owner accepts every non-full corrected source. -/
theorem correctedComplete_accepts_nonfull (bits : CorrectedCutBits)
    (hpartial : bits.isFull = false) :
    adaptiveCompleteOwnedFamily.test bits.entry = true := by
  exact adaptiveComplete_accepts_partial bits.x4 bits.x5 bits.x6 bits.x7
    bits.x8 bits.x9 bits.x10 bits.x11 hpartial

/-- The unique full source is routed to the canonical multi-code payer. -/
theorem correctedComplete_accepts_full (bits : CorrectedCutBits)
    (hfull : bits.isFull = true) :
    adaptiveCompleteOwnedFamily.test bits.entry = true := by
  rw [full_eq_allPresent hfull, allPresent_entry]
  exact adaptiveComplete_accepts_canonical

/-- Every source parameter is covered by exactly the appropriate branch. -/
theorem correctedComplete_accepts (bits : CorrectedCutBits) :
    adaptiveCompleteOwnedFamily.test bits.entry = true := by
  cases h : bits.isFull
  · exact correctedComplete_accepts_nonfull bits h
  · exact correctedComplete_accepts_full bits h

def correctedCompleteGlobalFamily :
    GlobalPaidResidualFamily qAll markV0 badV3 G :=
  adaptiveCompleteOwnedFamily.toGlobal

def correctedCompleteAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  adaptiveCompleteOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedCut_owner
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedCut_source_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedCut_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedCut_not_mem_canonical
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedComplete_accepts_nonfull
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedComplete_accepts_full
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedComplete_accepts
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmCorrectedCutCarrier.correctedCompleteAllocator
