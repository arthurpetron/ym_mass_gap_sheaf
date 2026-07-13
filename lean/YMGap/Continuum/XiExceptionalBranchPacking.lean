/-
# Branch-preserving exceptional carrier packing

The canonical exceptional path alone does not retain off-path component
branches.  This file places the already-injective switched occurrence masks
in the two finite mask fields of an actual occurrence carrier code: the first
mask is the terminal background and the second is the external family.  A
recursive terminal projection recovers the first mask from the chain code,
so equality of packed carrier codes recovers the complete switched pair and
hence the original exceptional source.

This is the structural half of the final weighted injection.  The remaining
term lemma must compare the source activity with the weight of this concrete
packed code (or a compatibility-preserving refinement of it).
-/

import YMGap.Continuum.XiExceptionalSourceWeight

namespace YMGap.Continuum.XiExceptionalBranchPacking

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Terminal-background recovery -/

def terminalBackground : OccChainCode n → OccBitVec n
  | .terminal background => background
  | .step _ rest => terminalBackground rest

theorem terminalBackground_occurrenceChainCodeOfWalk
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec n) :
    terminalBackground (occurrenceChainCodeOfWalk walk background) =
      background := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih => exact ih

/-! ## 2. Exceptional source entries and their packed target code -/

abbrev ExceptionalSourceEntry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  { pair // pair ∈ exceptionalSourceCodes Gamma qP b1 b2 }

def exceptionalBranchCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let switched := switchedBranchCode Gamma b2 pair
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  { carrier :=
      { start := exceptionalMarkedIndex Gamma b1 b2 pair
        chain := occurrenceChainCodeOfWalk path.indexWalk switched.1 }
    external := switched.2 }

theorem exceptionalBranchCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exceptionalBranchCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let switched := switchedBranchCode Gamma b2 pair
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  unfold occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨switched.2, bitVectors_complete switched.2, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(exceptionalBranchCarrierCode Gamma qP b1 b2 entry).carrier,
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨exceptionalMarkedIndex Gamma b1 b2 pair,
    occurrenceIndices_complete facts.marked_lt, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk path.indexWalk switched.1, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma switched.1 path.indexWalk
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

/-! ## 3. Packed-code injectivity -/

theorem exceptionalBranchCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : exceptionalBranchCarrierCode Gamma qP b1 b2 entry1 =
      exceptionalBranchCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have hleft := congrArg
    (fun code => terminalBackground code.carrier.chain) hcode
  have hright := congrArg (fun code => code.external) hcode
  have hleft' :
      (switchedBranchCode Gamma b2 entry1.1).1 =
        (switchedBranchCode Gamma b2 entry2.1).1 := by
    simpa [exceptionalBranchCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using hleft
  have hright' :
      (switchedBranchCode Gamma b2 entry1.1).2 =
        (switchedBranchCode Gamma b2 entry2.1).2 := by
    simpa [exceptionalBranchCarrierCode] using hright
  have hpairCode : switchedBranchCode Gamma b2 entry1.1 =
      switchedBranchCode Gamma b2 entry2.1 := by
    apply Prod.ext
    · exact hleft'
    · exact hright'
  have hpairs := switchedBranchCode_injective_on_source Gamma qP b1 b2
    entry1.1 entry2.1 entry1.2 entry2.2 hpairCode
  exact Subtype.ext hpairs

#print axioms terminalBackground_occurrenceChainCodeOfWalk
#print axioms exceptionalBranchCarrierCode_mem
#print axioms exceptionalBranchCarrierCode_injective

end YMGap.Continuum.XiExceptionalBranchPacking
