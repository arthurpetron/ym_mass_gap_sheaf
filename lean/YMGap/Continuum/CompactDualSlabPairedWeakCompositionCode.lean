/-
# An asymmetric weak-composition compiler for paired physical values

The one-component compiler uses the same budget for word length and l1 mass,
giving a `4^M` carrier.  A two-replica support word has a different geometry:
at total physical mass `M`, it has at most `2*M` coordinates but l1 mass at
most `M`.

Padding the same unary-separated word to `lengthBudget + massBudget` preserves
the existing literal decoder.  At `(2*M, M)` this gives exactly `3*M` bits and
an `8^M` carrier, rather than the wasteful `16^M` obtained by forcing both
bounds into the larger budget.

Constructive contract: structural list recursion and exact natural-number
arithmetic only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode

namespace YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Separate length and mass budgets -/

/-- Pad the unary-separated source word to the sum of independent coordinate
and l1 budgets. -/
def asymmetricWeakCompositionBinaryCode
    (lengthBudget massBudget : Nat) (values : List Nat) : List Nat :=
  unarySeparatedNatWord values ++
    List.replicate
      (lengthBudget + massBudget -
        (unarySeparatedNatWord values).length) 1

/-- The old completed-run decoder remains a literal left inverse. -/
theorem asymmetricWeakCompositionBinaryDecode_code
    (lengthBudget massBudget : Nat) (values : List Nat) :
    weakCompositionBinaryDecode
        (asymmetricWeakCompositionBinaryCode
          lengthBudget massBudget values) = values := by
  unfold weakCompositionBinaryDecode
    asymmetricWeakCompositionBinaryCode
  exact decodeCompletedUnary_unarySeparated_append_replicate_one values _

/-- The asymmetric compiler is injective even between words of different
lengths. -/
theorem asymmetricWeakCompositionBinaryCode_injective
    (lengthBudget massBudget : Nat) : ∀ left right : List Nat,
    asymmetricWeakCompositionBinaryCode lengthBudget massBudget left =
        asymmetricWeakCompositionBinaryCode lengthBudget massBudget right →
      left = right := by
  intro left right hcode
  have hdecoded := congrArg weakCompositionBinaryDecode hcode
  rw [asymmetricWeakCompositionBinaryDecode_code
      lengthBudget massBudget left,
    asymmetricWeakCompositionBinaryDecode_code
      lengthBudget massBudget right] at hdecoded
  exact hdecoded

/-- Independent coordinate and l1 bounds give the exact common code length
`lengthBudget + massBudget`. -/
theorem asymmetricWeakCompositionBinaryCode_length
    (lengthBudget massBudget : Nat) (values : List Nat)
    (hlength : values.length ≤ lengthBudget)
    (hmass : natListSum values ≤ massBudget) :
    (asymmetricWeakCompositionBinaryCode
      lengthBudget massBudget values).length =
        lengthBudget + massBudget := by
  have hraw : (unarySeparatedNatWord values).length ≤
      lengthBudget + massBudget := by
    rw [unarySeparatedNatWord_length]
    omega
  unfold asymmetricWeakCompositionBinaryCode
  simp only [List.length_append, List.length_replicate]
  omega

/-- Every emitted or padding symbol remains binary. -/
theorem asymmetricWeakCompositionBinaryCode_entry_lt_two
    (lengthBudget massBudget : Nat) (values : List Nat) (bit : Nat)
    (hmem : bit ∈ asymmetricWeakCompositionBinaryCode
      lengthBudget massBudget values) :
    bit < 2 := by
  rcases List.mem_append.mp hmem with hraw | hpadding
  · exact unarySeparatedNatWord_entry_lt_two values bit hraw
  · have hbit : bit = 1 := List.eq_of_mem_replicate hpadding
    omega

/-- Every separately bounded word lands in the explicit binary carrier of
the summed budget. -/
theorem asymmetricWeakCompositionBinaryCode_mem_allSeqs
    (lengthBudget massBudget : Nat) (values : List Nat)
    (hlength : values.length ≤ lengthBudget)
    (hmass : natListSum values ≤ massBudget) :
    asymmetricWeakCompositionBinaryCode
        lengthBudget massBudget values ∈
      allSeqs 2 (lengthBudget + massBudget) := by
  apply mem_allSeqs 2 (lengthBudget + massBudget)
  · exact asymmetricWeakCompositionBinaryCode_length
      lengthBudget massBudget values hlength hmass
  · intro bit hbit
    exact asymmetricWeakCompositionBinaryCode_entry_lt_two
      lengthBudget massBudget values bit hbit

/-! ## 2. The paired `8^M` specialization -/

/-- Two coordinates per support site and one unit of total l1 mass per unit
of physical mass produce a fixed `3*M`-bit carrier. -/
def pairedPhysicalValueCarrier (mass : Nat) : List (List Nat) :=
  allSeqs 2 (3 * mass)

theorem pairedPhysicalValueCarrier_length (mass : Nat) :
    (pairedPhysicalValueCarrier mass).length = 8 ^ mass := by
  unfold pairedPhysicalValueCarrier
  rw [length_allSeqs]
  change 2 ^ (3 * mass) = 8 ^ mass
  rw [Nat.pow_mul]

/-- Any natural word with at most `2*M` coordinates and total mass at most
`M` has its asymmetric code in the paired `8^M` carrier. -/
theorem asymmetricWeakCompositionBinaryCode_mem_pairedCarrier
    (mass : Nat) (values : List Nat)
    (hlength : values.length ≤ 2 * mass)
    (hmass : natListSum values ≤ mass) :
    asymmetricWeakCompositionBinaryCode (2 * mass) mass values ∈
      pairedPhysicalValueCarrier mass := by
  unfold pairedPhysicalValueCarrier
  have hmem := asymmetricWeakCompositionBinaryCode_mem_allSeqs
    (2 * mass) mass values hlength hmass
  have hsum : 2 * mass + mass = 3 * mass := by omega
  rw [hsum] at hmem
  exact hmem

end YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode

#print axioms YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode.asymmetricWeakCompositionBinaryDecode_code
#print axioms YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode.asymmetricWeakCompositionBinaryCode_injective
#print axioms YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode.asymmetricWeakCompositionBinaryCode_mem_allSeqs
#print axioms YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode.pairedPhysicalValueCarrier_length
#print axioms YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode.asymmetricWeakCompositionBinaryCode_mem_pairedCarrier
