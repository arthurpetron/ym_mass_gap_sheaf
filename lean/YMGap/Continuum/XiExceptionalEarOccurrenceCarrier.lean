/-
# Pair-bounced ears as occurrence target codes

The square identity for a paired open ear is useful only when its bounced
walk is one of the finite occurrence-indexed target codes.  This file makes
that lifting explicit.  The hypotheses expose exactly the two finite checks:
the bounced length fits the target fuel and every visited occurrence is in
range.  Target duplicate-freedom is inherited from the complete occurrence
enumeration, not postulated for the new codes.
-/

import YMGap.Continuum.XiExceptionalEarPairBounce
import YMGap.Continuum.XiExceptionalPathEncoder
import YMGap.Continuum.XiExceptionalTargetNodup

namespace YMGap.Continuum.XiExceptionalEarOccurrenceCarrier

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalTargetNodup
open YMGap.Continuum.XiExceptionalEarPairBounce

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-- The occurrence target obtained by putting a pair-bounced ear in the
carrier chain.  Background and external masks remain available for branch
payloads. -/
def pairedBounceCarrierCode (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j : Nat}
    (path : PairedPath edge i j)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := i
        chain := occurrenceChainCodeOfWalk (path.bounceWalk hsymm) background }
    external := external }

/-- A bounced ear belongs to the actual finite target enumeration whenever
its explicit length and occurrence bounds fit that enumeration. -/
theorem pairedBounceCarrierCode_mem (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j : Nat}
    (path : PairedPath edge i j)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length)
    (hi : i < Gamma.length)
    (hfuel : 2 + 4 * path.pairCount ≤ Gamma.length)
    (hbound : ∀ k, k ∈ (path.bounceWalk hsymm).vertices →
      k < Gamma.length) :
    pairedBounceCarrierCode Gamma path hsymm background external ∈
      occurrenceCarrierXiCodes Gamma := by
  unfold pairedBounceCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨external, bitVectors_complete external, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨i, occurrenceChainCodeOfWalk (path.bounceWalk hsymm) background⟩,
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨i, occurrenceIndices_complete hi, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk (path.bounceWalk hsymm) background,
    ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma background
    (path.bounceWalk hsymm) Gamma.length
  · rw [PairedPath.bounceWalk_length hsymm path]
    exact hfuel
  · exact hbound

/-- The finite target remains duplicate-free after including every bounced
ear through the same occurrence enumeration. -/
theorem pairedBounce_target_nodup (Gamma : List (Polymer L)) :
    (occurrenceCarrierXiCodes Gamma).Nodup :=
  occurrenceCarrierXiCodes_nodup Gamma

#print axioms pairedBounceCarrierCode_mem
#print axioms pairedBounce_target_nodup

end YMGap.Continuum.XiExceptionalEarOccurrenceCarrier
