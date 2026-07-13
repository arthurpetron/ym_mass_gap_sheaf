/-
# Unequal-ear occurrence-fuel fence

The pair-bounce square code for a three-edge arm has five chain steps.  If
its alternative arm is a single edge, the whole two-arm block has only four
distinct occurrences.  The occurrence target at fuel four contains chains
with at most four steps, so the long-arm square code is absent.

This is the minimal unequal-arm capacity obstruction behind the sharp
selected-versus-reserve invariant.  It prevents a later allocator from
silently applying the balanced six-cycle construction to unequal ears.
-/

import YMGap.Continuum.XiExceptionalBlockCutFuel

namespace YMGap.Continuum.XiExceptionalUnequalEarFuelFence

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalEarOccurrenceCarrier
open YMGap.Continuum.XiExceptionalBlockCutFuel

/-! ## Exact depth of the finite occurrence-chain enumeration -/

def chainSteps {n : Nat} : OccChainCode n → Nat
  | .terminal _ => 0
  | .step _ rest => chainSteps rest + 1

theorem chainSteps_le_fuel_of_mem {L : Lattice}
    [DecidableEq L.Plaquette] (Gamma : List (Polymer L)) :
    ∀ (fuel : Nat) (code : OccChainCode Gamma.length),
      code ∈ occurrenceChainCodes Gamma fuel → chainSteps code ≤ fuel
  | 0, code, hmem => by
      unfold occurrenceChainCodes occurrenceTerminalCodes at hmem
      obtain ⟨background, _, hcode⟩ := List.mem_map.mp hmem
      rw [← hcode]
      exact Nat.zero_le _
  | fuel + 1, code, hmem => by
      unfold occurrenceChainCodes at hmem
      rcases List.mem_append.mp hmem with hterminal | hstep
      · unfold occurrenceTerminalCodes at hterminal
        obtain ⟨background, _, hcode⟩ := List.mem_map.mp hterminal
        rw [← hcode]
        exact Nat.zero_le _
      · obtain ⟨next, _, hblock⟩ := List.mem_flatMap.mp hstep
        obtain ⟨rest, hrest, hcode⟩ := List.mem_map.mp hblock
        rw [← hcode]
        simp only [chainSteps]
        have ih := chainSteps_le_fuel_of_mem Gamma fuel rest hrest
        omega

theorem occurrenceChainCodeOfWalk_steps :
    ∀ {edge : Nat → Nat → Bool} {i j : Nat}
      (walk : CWalk edge i j) {n : Nat} (background : OccBitVec n),
      chainSteps (occurrenceChainCodeOfWalk walk background) + 1 =
        walk.vertices.length
  | _, _, _, .single _, _, _ => rfl
  | _, _, _, .cons _ rest, _, background => by
      simp only [occurrenceChainCodeOfWalk, chainSteps, CWalk.vertices,
        List.length_cons]
      rw [occurrenceChainCodeOfWalk_steps rest background]

theorem occurrenceChainCodeOfWalk_not_mem_of_overflow {L : Lattice}
    [DecidableEq L.Plaquette] (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec Gamma.length)
    (hoverflow : Gamma.length + 1 < walk.vertices.length) :
    occurrenceChainCodeOfWalk walk background ∉
      occurrenceChainCodes Gamma Gamma.length := by
  intro hmem
  have hsteps := chainSteps_le_fuel_of_mem Gamma Gamma.length
    (occurrenceChainCodeOfWalk walk background) hmem
  have hexact := occurrenceChainCodeOfWalk_steps walk background
  omega

/-! ## The four-occurrence unequal-ear witness -/

def lineEdge (x y : Nat) : Bool :=
  (x + 1 == y) || (y + 1 == x)

theorem lineEdge_symm (x y : Nat) :
    lineEdge x y = true → lineEdge y x = true := by
  unfold lineEdge
  rw [Bool.or_comm]
  exact id

def longArm : PairedPath lineEdge 0 3 :=
  .pair (x := 0) (y := 1) (z := 2) (t := 3)
    (by rfl) (by rfl) (.last (by rfl))

theorem longArm_pairCount : longArm.pairCount = 1 := by
  simp [longArm, PairedPath.pairCount]

theorem longArm_bounce_length :
    (longArm.bounceWalk lineEdge_symm).vertices.length = 6 := by
  rw [PairedPath.bounceWalk_length lineEdge_symm longArm]
  rw [longArm_pairCount]

theorem unequal_block_long_arm_overflows :
    ¬ (BlockCutFuel.leaf 1 0).bouncedVertexLength ≤
      (BlockCutFuel.leaf 1 0).availableOccurrenceCount := by
  intro hfit
  have hpairs :=
    (BlockCutFuel.global_occurrence_budget_iff (.leaf 1 0)).mp hfit
  exact (by simpa [BlockCutFuel.selectedPairs,
    BlockCutFuel.reservePairs] using hpairs)

theorem longArm_chain_not_mem {L : Lattice}
    [DecidableEq L.Plaquette] (Gamma : List (Polymer L))
    (background : OccBitVec Gamma.length)
    (hcount : Gamma.length = 4) :
    occurrenceChainCodeOfWalk (longArm.bounceWalk lineEdge_symm) background ∉
      occurrenceChainCodes Gamma Gamma.length := by
  apply occurrenceChainCodeOfWalk_not_mem_of_overflow Gamma
  rw [longArm_bounce_length, hcount]
  omega

/-- The concrete long-arm carrier is absent from the complete target, not
merely outside the sufficient hypotheses of its membership constructor. -/
theorem longArm_carrier_not_mem {L : Lattice}
    [DecidableEq L.Plaquette] (Gamma : List (Polymer L))
    (background external : OccBitVec Gamma.length)
    (hcount : Gamma.length = 4) :
    pairedBounceCarrierCode Gamma longArm lineEdge_symm background external ∉
      occurrenceCarrierXiCodes Gamma := by
  intro hmem
  unfold occurrenceCarrierXiCodes at hmem
  obtain ⟨external', _, hcarrierBlock⟩ := List.mem_flatMap.mp hmem
  obtain ⟨carrier', hcarrierMem, hcodeEq⟩ := List.mem_map.mp hcarrierBlock
  have hcarrierEq := congrArg OccCarrierXiCodeAt.carrier hcodeEq
  unfold pairedBounceCarrierCode at hcarrierEq
  have hchainEq := congrArg OccCarrierCodeAt.chain hcarrierEq
  unfold occurrenceCarrierCodes at hcarrierMem
  obtain ⟨start, _, hchainBlock⟩ := List.mem_flatMap.mp hcarrierMem
  obtain ⟨chain, hchainMem, hcarrierCodeEq⟩ := List.mem_map.mp hchainBlock
  have hlistedChainEq := congrArg OccCarrierCodeAt.chain hcarrierCodeEq
  change carrier'.chain =
    occurrenceChainCodeOfWalk (longArm.bounceWalk lineEdge_symm) background
      at hchainEq
  change chain = carrier'.chain at hlistedChainEq
  apply longArm_chain_not_mem Gamma background hcount
  rw [← hchainEq, ← hlistedChainEq]
  exact hchainMem

#print axioms chainSteps_le_fuel_of_mem
#print axioms occurrenceChainCodeOfWalk_steps
#print axioms occurrenceChainCodeOfWalk_not_mem_of_overflow
#print axioms longArm_bounce_length
#print axioms unequal_block_long_arm_overflows
#print axioms longArm_chain_not_mem
#print axioms longArm_carrier_not_mem

end YMGap.Continuum.XiExceptionalUnequalEarFuelFence
