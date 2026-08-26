/-
# A constructive binary compiler for bounded weak compositions

The component drop code stores natural-valued auxiliary words.  Bounding each
coordinate separately would leave a superexponential box.  The relevant
invariant is instead the sum of all coordinates.  This module gives the finite
compiler needed to exploit that invariant.

For a word `values`, write each value in unary and terminate it by zero.  If
both the word length and its l1 mass are at most `budget`, the resulting word
has length at most `2 * budget`.  Pad the remaining suffix with ones.  A decoder
returns precisely the zero-terminated unary runs and ignores the final
unterminated run of padding ones.  Consequently the compiler is injective even
when source words have different lengths, and its fixed carrier has exactly
`2 ^ (2 * budget) = 4 ^ budget` elements.

Constructive contract: structural list recursion and natural arithmetic only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Unary separators -/

/-- Unary values separated and terminated by zero bits. -/
def unarySeparatedNatWord : List Nat -> List Nat
  | [] => []
  | value :: values =>
      List.replicate value 1 ++ 0 :: unarySeparatedNatWord values

/-- The unary-separated word spends one bit per unit of mass and one separator
per source coordinate. -/
theorem unarySeparatedNatWord_length : forall values : List Nat,
    (unarySeparatedNatWord values).length =
      natListSum values + values.length
  | [] => rfl
  | value :: values => by
      simp only [unarySeparatedNatWord, List.length_append,
        List.length_replicate, List.length_cons, natListSum,
        unarySeparatedNatWord_length values]
      omega

/-- Every symbol emitted by the unary compiler is a binary digit. -/
theorem unarySeparatedNatWord_entry_lt_two : forall values : List Nat,
    forall bit : Nat, bit ∈ unarySeparatedNatWord values -> bit < 2
  | [], bit, hmem => by
      exact absurd hmem List.not_mem_nil
  | value :: values, bit, hmem => by
      have hparts := List.mem_append.mp hmem
      cases hparts with
      | inl hreplicate =>
          have hbit : bit = 1 := List.eq_of_mem_replicate hreplicate
          omega
      | inr htail =>
          have hcons := List.mem_cons.mp htail
          cases hcons with
          | inl hzero => omega
          | inr hrest =>
              exact unarySeparatedNatWord_entry_lt_two values bit hrest

/-! ## 2. A decoder which ignores an unterminated final run -/

/-- Decode completed unary runs.  `run` is the number of ones seen since the
last zero.  A final run not terminated by zero is deliberately ignored. -/
def decodeCompletedUnary : Nat -> List Nat -> List Nat
  | _, [] => []
  | run, bit :: bits =>
      if bit = 1 then
        decodeCompletedUnary (run + 1) bits
      else
        run :: decodeCompletedUnary 0 bits

/-- A word consisting only of ones contains no completed unary run. -/
theorem decodeCompletedUnary_replicate_one : forall run count : Nat,
    decodeCompletedUnary run (List.replicate count 1) = []
  | _, 0 => rfl
  | run, count + 1 => by
      simp only [List.replicate_succ, decodeCompletedUnary, ↓reduceIte]
      exact decodeCompletedUnary_replicate_one (run + 1) count

/-- A zero after `value` ones completes one run of size `run + value`. -/
theorem decodeCompletedUnary_replicate_one_zero : forall
    (run value : Nat) (rest : List Nat),
    decodeCompletedUnary run
        (List.replicate value 1 ++ 0 :: rest) =
      (run + value) :: decodeCompletedUnary 0 rest
  | run, 0, rest => by
      simp [decodeCompletedUnary]
  | run, value + 1, rest => by
      simp only [List.replicate_succ, List.cons_append,
        decodeCompletedUnary, ↓reduceIte]
      rw [decodeCompletedUnary_replicate_one_zero (run + 1) value rest]
      congr 1
      omega

/-- Appending any number of padding ones to a complete unary-separated source
does not change its decoded value word. -/
theorem decodeCompletedUnary_unarySeparated_append_replicate_one : forall
    (values : List Nat) (padding : Nat),
    decodeCompletedUnary 0
        (unarySeparatedNatWord values ++ List.replicate padding 1) = values
  | [], padding => by
      exact decodeCompletedUnary_replicate_one 0 padding
  | value :: values, padding => by
      simp only [unarySeparatedNatWord, List.cons_append,
        List.append_assoc]
      rw [decodeCompletedUnary_replicate_one_zero 0 value
        (unarySeparatedNatWord values ++ List.replicate padding 1)]
      simp only [Nat.zero_add]
      rw [decodeCompletedUnary_unarySeparated_append_replicate_one
        values padding]

/-! ## 3. The fixed binary carrier -/

/-- Pad a unary-separated source with ones to the fixed length
`2 * budget`.  Under the advertised length and l1 hypotheses, subtraction is
exact. -/
def weakCompositionBinaryCode (budget : Nat) (values : List Nat) : List Nat :=
  unarySeparatedNatWord values ++
    List.replicate
      (2 * budget - (unarySeparatedNatWord values).length) 1

/-- Decode a fixed binary weak-composition code. -/
def weakCompositionBinaryDecode (bits : List Nat) : List Nat :=
  decodeCompletedUnary 0 bits

/-- The decoder is a literal left inverse of the compiler.  This equality does
not need the size hypotheses; those are needed only to land at fixed length. -/
theorem weakCompositionBinaryDecode_code (budget : Nat) (values : List Nat) :
    weakCompositionBinaryDecode
        (weakCompositionBinaryCode budget values) = values := by
  unfold weakCompositionBinaryDecode weakCompositionBinaryCode
  exact decodeCompletedUnary_unarySeparated_append_replicate_one values _

/-- The weak-composition binary compiler is injective, including between words
of different lengths. -/
theorem weakCompositionBinaryCode_injective (budget : Nat) :
    forall left right : List Nat,
      weakCompositionBinaryCode budget left =
        weakCompositionBinaryCode budget right ->
      left = right := by
  intro left right heq
  have hdecoded := congrArg weakCompositionBinaryDecode heq
  rw [weakCompositionBinaryDecode_code budget left,
    weakCompositionBinaryDecode_code budget right] at hdecoded
  exact hdecoded

/-- If length and l1 mass are both bounded by `budget`, the code has the fixed
length `2 * budget`. -/
theorem weakCompositionBinaryCode_length
    (budget : Nat) (values : List Nat)
    (hlength : values.length <= budget)
    (hmass : natListSum values <= budget) :
    (weakCompositionBinaryCode budget values).length = 2 * budget := by
  have hraw : (unarySeparatedNatWord values).length <= 2 * budget := by
    rw [unarySeparatedNatWord_length]
    omega
  unfold weakCompositionBinaryCode
  simp only [List.length_append, List.length_replicate]
  omega

/-- Every symbol in the padded code is a binary digit. -/
theorem weakCompositionBinaryCode_entry_lt_two
    (budget : Nat) (values : List Nat) (bit : Nat)
    (hmem : bit ∈ weakCompositionBinaryCode budget values) :
    bit < 2 := by
  have hparts := List.mem_append.mp hmem
  cases hparts with
  | inl hraw =>
      exact unarySeparatedNatWord_entry_lt_two values bit hraw
  | inr hpadding =>
      have hbit : bit = 1 := List.eq_of_mem_replicate hpadding
      omega

/-- Every bounded weak composition lands in the explicit enumeration of all
length-`2 * budget` binary words. -/
theorem weakCompositionBinaryCode_mem_allSeqs
    (budget : Nat) (values : List Nat)
    (hlength : values.length <= budget)
    (hmass : natListSum values <= budget) :
    weakCompositionBinaryCode budget values ∈
      allSeqs 2 (2 * budget) := by
  apply mem_allSeqs 2 (2 * budget)
  · exact weakCompositionBinaryCode_length budget values hlength hmass
  · intro bit hbit
    exact weakCompositionBinaryCode_entry_lt_two budget values bit hbit

/-- The explicit binary carrier has `2 ^ (2 * budget)` words. -/
theorem weakCompositionBinaryCarrier_length (budget : Nat) :
    (allSeqs 2 (2 * budget)).length = 2 ^ (2 * budget) := by
  exact length_allSeqs 2 (2 * budget)

/-- Re-express the carrier cardinality as a fixed base to the l1 budget. -/
theorem two_pow_two_mul_eq_four_pow (budget : Nat) :
    2 ^ (2 * budget) = 4 ^ budget := by
  rw [Nat.pow_mul]

/-! ## 4. Finite-list counting consequence -/

/-- A duplicate-free finite family of natural words with length and l1 mass at
most `budget` has at most `4 ^ budget` members. -/
theorem boundedNatWordList_length_le_four_pow
    (budget : Nat) (words : List (List Nat))
    (hnodup : words.Nodup)
    (hlength : forall word, word ∈ words -> word.length <= budget)
    (hmass : forall word, word ∈ words -> natListSum word <= budget) :
    words.length <= 4 ^ budget := by
  let encode : List Nat -> List Nat := weakCompositionBinaryCode budget
  have hencodedNodup : (words.map encode).Nodup := by
    apply nodup_map_of_injOn encode words hnodup
    intro left _ right _ heq
    exact weakCompositionBinaryCode_injective budget left right heq
  have hsubset : forall code,
      code ∈ words.map encode -> code ∈ allSeqs 2 (2 * budget) := by
    intro code hcode
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hcode
    exact weakCompositionBinaryCode_mem_allSeqs budget word
      (hlength word hword) (hmass word hword)
  have hbound := nodup_subset_length_le
    (words.map encode) (allSeqs 2 (2 * budget)) hencodedNodup hsubset
  rw [List.length_map, weakCompositionBinaryCarrier_length,
    two_pow_two_mul_eq_four_pow] at hbound
  exact hbound

/-! ## 5. Specialization to the sparse slab-component auxiliary table -/

/-- Forget row keys and boundaries, retaining the natural values in row order.
The row skeleton remains a separate part of the complete component code. -/
def auxiliaryWordTableValues
    (entries : List (SlabLink × List Nat)) : List Nat :=
  entries.flatMap fun entry => entry.2

/-- Flattening the value rows preserves their total l1 mass exactly. -/
theorem auxiliaryWordTableValues_l1 : forall
    entries : List (SlabLink × List Nat),
    natListSum (auxiliaryWordTableValues entries) =
      auxiliaryWordTableL1 entries
  | [] => rfl
  | entry :: entries => by
      simp only [auxiliaryWordTableValues, List.flatMap_cons,
        auxiliaryWordTableL1]
      rw [natListSum_append]
      change natListSum entry.2 + natListSum (auxiliaryWordTableValues entries) =
        natListSum entry.2 + auxiliaryWordTableL1 entries
      rw [auxiliaryWordTableValues_l1 entries]

/-- If every row has at most three coordinates, the flattened value word has
at most three coordinates per row. -/
theorem auxiliaryWordTableValues_length_le_three_mul : forall
    entries : List (SlabLink × List Nat),
    (forall entry, entry ∈ entries -> entry.2.length <= 3) ->
    (auxiliaryWordTableValues entries).length <= 3 * entries.length
  | [], _ => Nat.le_refl 0
  | entry :: entries, hrow => by
      have hhead : entry.2.length <= 3 := hrow entry List.mem_cons_self
      have htail := auxiliaryWordTableValues_length_le_three_mul entries
        (fun next hnext => hrow next (List.mem_cons_of_mem entry hnext))
      simp only [auxiliaryWordTableValues, List.flatMap_cons,
        List.length_append, List.length_cons]
      change entry.2.length + (auxiliaryWordTableValues entries).length <=
        3 * (entries.length + 1)
      omega

/-- The flattened natural-valued auxiliary part of one sparse rooted-component
code. -/
def SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : List Nat :=
  auxiliaryWordTableValues
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords

/-- Every row of the sparse component code inherits the universal three-slot
resolver bound. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_row_length_le_three
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords) :
    entry.2.length <= 3 := by
  have hword := sparseAuxiliaryDropRow_word_eq
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    links entry (by
      unfold SlabFusionWitnessFaceStrandSeed.sparseDropCode at hentry
      exact hentry)
  rw [hword]
  exact SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_length_le_three
    seed entry.1

/-- For the production complete-slab carrier, the flattened auxiliary word has
at most twelve coordinates per physical peel entry. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord_length_le_twelve_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord seed).length <=
      12 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  have hflatten := auxiliaryWordTableValues_length_le_three_mul
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords
    (fun entry hentry =>
      SlabFusionWitnessFaceStrandSeed.sparseDropCode_row_length_le_three
        seed entry hentry)
  have hrows :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le_four_mul_peelFaces
      seed (boundaryCompleteSlabLinks_nodup extent)
  unfold SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord
  omega

/-- For the production complete-slab carrier, the flattened auxiliary word's
l1 mass is at most twelve per physical peel entry. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord_l1_le_twelve_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    natListSum
        (SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord seed) <=
      12 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord
  rw [auxiliaryWordTableValues_l1]
  exact
    SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWordTableL1_le_twelve_mul_peelFaces
      seed

/-- Compile the complete-slab auxiliary values into a fixed binary word with
budget `12 * peelFaces.length`. -/
def SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List Nat :=
  weakCompositionBinaryCode
    (12 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length)
    (SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord seed)

/-- The production auxiliary-value compiler is exactly decodable. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryDecode
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    weakCompositionBinaryDecode
        (SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode seed) =
      SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord seed := by
  unfold SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode
  exact weakCompositionBinaryDecode_code _ _

/-- The production auxiliary-value code lands in a finite carrier depending
only on the physical peel length, not on the spin cutoff or slab extent. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode seed ∈
      allSeqs 2
        (2 * (12 *
          (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length)) := by
  unfold SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode
  apply weakCompositionBinaryCode_mem_allSeqs
  · exact
      SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord_length_le_twelve_mul_peelFaces
        seed
  · exact
      SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord_l1_le_twelve_mul_peelFaces
        seed

/-- The complete-slab auxiliary-value carrier is a fixed exponential in the
physical peel length: `(4 ^ 12) ^ peelFaces.length`. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCarrier_length
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (allSeqs 2
        (2 * (12 *
          (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length))).length =
      (4 ^ 12) ^
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  rw [weakCompositionBinaryCarrier_length,
    two_pow_two_mul_eq_four_pow, Nat.pow_mul]

#print axioms unarySeparatedNatWord
#print axioms unarySeparatedNatWord_length
#print axioms unarySeparatedNatWord_entry_lt_two
#print axioms decodeCompletedUnary
#print axioms decodeCompletedUnary_replicate_one
#print axioms decodeCompletedUnary_replicate_one_zero
#print axioms decodeCompletedUnary_unarySeparated_append_replicate_one
#print axioms weakCompositionBinaryCode
#print axioms weakCompositionBinaryDecode
#print axioms weakCompositionBinaryDecode_code
#print axioms weakCompositionBinaryCode_injective
#print axioms weakCompositionBinaryCode_length
#print axioms weakCompositionBinaryCode_entry_lt_two
#print axioms weakCompositionBinaryCode_mem_allSeqs
#print axioms weakCompositionBinaryCarrier_length
#print axioms two_pow_two_mul_eq_four_pow
#print axioms boundedNatWordList_length_le_four_pow
#print axioms auxiliaryWordTableValues
#print axioms auxiliaryWordTableValues_l1
#print axioms auxiliaryWordTableValues_length_le_three_mul
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_row_length_le_three
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord_length_le_twelve_mul_peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueWord_l1_le_twelve_mul_peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryDecode
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode_mem_carrier
#print axioms SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCarrier_length

end YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
