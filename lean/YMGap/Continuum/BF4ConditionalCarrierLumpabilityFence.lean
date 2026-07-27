/-
# Conditional-carrier Markov lumpability: exact theorem and finite fence

The BF4 U(1) files prove exact full-carrier reindexing and locality of the
deterministic four-face block on lower/reflected-upper observables.  They do
not define a nine-loop or five-holonomy terminal-normalized physical kernel.
Consequently those theorems alone cannot establish Markov lumpability of the
smaller carrier.

This module tests the missing implication on an actual conditionally
integrated kernel already present in the tree:
`Z4ThreeBlockFiberConditionalKernel.threeBlockFiberConditionalKernel`.
That kernel is nonnegative, row-normalized, pushforward-exact, and obtained
by exact division by the target fiber mass.

There are two complementary results.

1. The complete three-bit pattern is genuinely Markov-lumpable after
   multiplication by an arbitrary terminal message and row normalization.
   The proof is terminal-independent: equal raw rows give equal terminal
   denominators and equal normalized rows.

2. A smaller retained carrier that forgets the left bit is not lumpable,
   even for the unit terminal message.  Two explicit source states collide
   under that projection but their normalized conditional rows differ at an
   explicit target.

Thus conditional integration can prove lumpability when the retained
carrier captures the complete source pattern, but conditional integration
alone does not prove that a proposed smaller carrier is sufficient.  This
is a finite exact fence for the corresponding nine-loop/five-holonomy
inference; it is not a counterexample to the actual Yang--Mills kernel.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or
placeholder.
-/

import YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Terminal-message Markovization -/

/-- Denominator of a finite backward-message row. -/
def terminalWeightedDenominator
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (source : Source) : Q' :=
  listQSum
    (fun target => kernel source target * terminal target)
    targetStates

/-- A finite raw kernel multiplied by a terminal message and normalized in
each source row. -/
def terminalNormalizedKernel
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (source : Source) (target : Target) : Q' :=
  Q'.divPos
    (kernel source target * terminal target)
    (terminalWeightedDenominator
      targetStates kernel terminal source)
    (denominator_pos source)

/-- Terminal normalization preserves nonnegativity. -/
theorem terminalNormalizedKernel_nonnegative
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (kernel_nonnegative :
      ∀ source target, (0 : Q') ≤ kernel source target)
    (terminal_nonnegative :
      ∀ target, (0 : Q') ≤ terminal target)
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (source : Source) (target : Target) :
    (0 : Q') ≤
      terminalNormalizedKernel
        targetStates kernel terminal
        denominator_pos source target := by
  unfold terminalNormalizedKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (kernel_nonnegative source target)
      (terminal_nonnegative target))
    (Q'.le_of_lt
      (Q'.recipPos_pos _ (denominator_pos source)))

/-- Terminal normalization produces exact stochastic rows. -/
theorem terminalNormalizedKernel_row_normalized
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (source : Source) :
    listQSum
        (terminalNormalizedKernel
          targetStates kernel terminal
          denominator_pos source)
        targetStates ≈ 1 := by
  unfold terminalNormalizedKernel
  let denominator :=
    terminalWeightedDenominator
      targetStates kernel terminal source
  let reciprocal :=
    Q'.recipPos denominator (denominator_pos source)
  change
    listQSum
        (fun target =>
          (kernel source target * terminal target) *
            reciprocal)
        targetStates ≈ 1
  refine Q'.eqv_trans _
    (listQSum
        (fun target =>
          kernel source target * terminal target)
        targetStates * reciprocal) _ ?_ ?_
  · exact listQSum_mul_right
      (fun target =>
        kernel source target * terminal target)
      reciprocal targetStates
  · change denominator * reciprocal ≈ 1
    exact Q'.mul_recipPos_eqv
      denominator (denominator_pos source)

private theorem qeqv_of_le_of_ge_local {left right : Q'}
    (left_le_right : left ≤ right)
    (right_le_left : right ≤ left) :
    left ≈ right := by
  show
    left.num * (right.den : Int) =
      right.num * (left.den : Int)
  exact Int.le_antisymm left_le_right right_le_left

private theorem divPos_eqv_congr_local
    {numerator numerator' denominator denominator' : Q'}
    (denominator_pos : (0 : Q') < denominator)
    (denominator'_pos : (0 : Q') < denominator')
    (numerator_eqv : numerator ≈ numerator')
    (denominator_eqv : denominator ≈ denominator') :
    Q'.divPos numerator denominator denominator_pos ≈
      Q'.divPos numerator' denominator' denominator'_pos := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le
      numerator' denominator' denominator'_pos
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator denominator_pos)
          denominator' denominator
          (Q'.eqv_symm denominator_eqv))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator denominator denominator_pos)
          numerator_eqv))
  · apply Q'.le_divPos_of_mul_le
      numerator denominator denominator_pos
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator' denominator'
            denominator'_pos)
          denominator denominator' denominator_eqv)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator' denominator' denominator'_pos)
          (Q'.eqv_symm numerator_eqv)))

/-- Pointwise equality of two raw rows forces equality of their terminal
denominators for every terminal message. -/
theorem terminalWeightedDenominator_eqv_of_rows
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (first second : Source)
    (rows_eqv :
      ∀ target, target ∈ targetStates →
        kernel first target ≈ kernel second target) :
    terminalWeightedDenominator
        targetStates kernel terminal first ≈
      terminalWeightedDenominator
        targetStates kernel terminal second := by
  unfold terminalWeightedDenominator
  apply listQSum_congr_on
  intro target htarget
  exact Q'.mul_eqv_congr_right
    (kernel first target)
    (kernel second target)
    (terminal target)
    (rows_eqv target htarget)

/-- **Terminal-independent Markov lumpability.**  Any source projection that
determines the entire raw row also determines every terminal-normalized row.
-/
theorem terminalNormalizedKernel_eqv_of_rows
    {Source Target : Type}
    (targetStates : List Target)
    (kernel : Source → Target → Q')
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetStates kernel terminal source)
    (first second : Source)
    (rows_eqv :
      ∀ target, target ∈ targetStates →
        kernel first target ≈ kernel second target)
    (target : Target) (htarget : target ∈ targetStates) :
    terminalNormalizedKernel
        targetStates kernel terminal
        denominator_pos first target ≈
      terminalNormalizedKernel
        targetStates kernel terminal
        denominator_pos second target := by
  exact divPos_eqv_congr_local
    (denominator_pos first)
    (denominator_pos second)
    (Q'.mul_eqv_congr_right
      (kernel first target)
      (kernel second target)
      (terminal target)
      (rows_eqv target htarget))
    (terminalWeightedDenominator_eqv_of_rows
      targetStates kernel terminal first second rows_eqv)

/-! ## 2. Genuine lumpability of the complete conditional pattern -/

/-- The actual three-block fiber-conditional kernel remains lumpable on the
complete three-bit source pattern after every admissible terminal message. -/
theorem threeBlockFiberTerminalKernel_source_pattern_lumpable
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (targetPattern_pos :
      ∀ pattern,
        (0 : Q') <
          threeBlockPatternMass targetLaw pattern)
    (terminal : Target → Q')
    (denominator_pos :
      ∀ source,
        (0 : Q') <
          terminalWeightedDenominator
            targetLaw.states
            (threeBlockFiberConditionalKernel
              sourceLaw targetLaw targetPattern_pos)
            terminal source)
    (first second : Source)
    (samePattern :
      threeBlockPattern sourceLaw first =
        threeBlockPattern sourceLaw second)
    (target : Target) (htarget : target ∈ targetLaw.states) :
    terminalNormalizedKernel
        targetLaw.states
        (threeBlockFiberConditionalKernel
          sourceLaw targetLaw targetPattern_pos)
        terminal denominator_pos first target ≈
      terminalNormalizedKernel
        targetLaw.states
        (threeBlockFiberConditionalKernel
          sourceLaw targetLaw targetPattern_pos)
        terminal denominator_pos second target := by
  apply terminalNormalizedKernel_eqv_of_rows
  · intro candidate _
    exact
      threeBlockFiberConditionalKernel_source_pattern_local
        sourceLaw targetLaw targetPattern_pos
        first second samePattern candidate
  · exact htarget

/-! ## 3. Concrete reduced-carrier failure -/

/-- The concrete, exactly integrated minimal conditional kernel. -/
def minimalFiberKernel
    (source target : MinimalParityState) : Q' :=
  threeBlockFiberConditionalKernel
    minimalUniformThreeBitLaw
    minimalUniformThreeBitLaw
    minimalUniformThreeBit_patternMass_pos
    source target

/-- Unit terminal message. -/
def unitTerminal (_target : MinimalParityState) : Q' := 1

theorem minimalFiberUnitDenominator_eqv_one
    (source : MinimalParityState) :
    terminalWeightedDenominator
        minimalParityStateSpace
        minimalFiberKernel unitTerminal source ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (minimalFiberKernel source)
      minimalParityStateSpace) _ ?_ ?_
  · unfold terminalWeightedDenominator unitTerminal
    apply listQSum_congr_on
    intro target _
    exact Q'.mul_one_eqv _
  · unfold minimalFiberKernel
    exact
      threeBlockFiberConditionalKernel_row_normalized
        minimalUniformThreeBitLaw
        minimalUniformThreeBitLaw
        minimalUniformThreeBit_patternMass_pos
        source

theorem minimalFiberUnitDenominator_pos
    (source : MinimalParityState) :
    (0 : Q') <
      terminalWeightedDenominator
        minimalParityStateSpace
        minimalFiberKernel unitTerminal source :=
  Q'.pos_of_lt_of_le
    (by decide)
    (Q'.ge_of_eqv
      (minimalFiberUnitDenominator_eqv_one source))

/-- The unit-terminal normalized conditional kernel. -/
def minimalFiberUnitMarkovKernel
    (source target : MinimalParityState) : Q' :=
  terminalNormalizedKernel
    minimalParityStateSpace
    minimalFiberKernel unitTerminal
    minimalFiberUnitDenominator_pos
    source target

/-- With the unit terminal message, Markovization returns the already
row-normalized fiber kernel. -/
theorem minimalFiberUnitMarkovKernel_eqv_raw
    (source target : MinimalParityState) :
    minimalFiberUnitMarkovKernel source target ≈
      minimalFiberKernel source target := by
  unfold minimalFiberUnitMarkovKernel
  refine Q'.eqv_trans _
    (Q'.divPos
      (minimalFiberKernel source target)
      1 (by decide)) _ ?_ ?_
  · exact divPos_eqv_congr_local
      (minimalFiberUnitDenominator_pos source)
      (by decide)
      (Q'.mul_one_eqv _)
      (minimalFiberUnitDenominator_eqv_one source)
  · unfold Q'.divPos
    change minimalFiberKernel source target * 1 ≈
      minimalFiberKernel source target
    exact Q'.mul_one_eqv _

/-- A deliberately incomplete retained carrier: it forgets the left block
bit and keeps only the shared/right pair. -/
def incompleteRetainedPair
    (state : MinimalParityState) : Bool × Bool :=
  (state.2.1, state.2.2)

/-- Exact finite Markov-lumpability predicate on a selected carrier. -/
def MarkovLumpableOnProjection
    {State Retained : Type}
    (states : List State)
    (projection : State → Retained)
    (kernel : State → State → Q') : Prop :=
  ∀ first, first ∈ states →
    ∀ second, second ∈ states →
      projection first = projection second →
        ∀ target, target ∈ states →
          kernel first target ≈ kernel second target

/-- The two witness sources collide under the incomplete retained carrier. -/
theorem incompleteRetainedPair_witness_collision :
    incompleteRetainedPair (false, false, false) =
      incompleteRetainedPair (true, false, false) :=
  rfl

/-- Their unit-terminal normalized rows nevertheless differ at the displayed
target. -/
theorem minimalFiberUnitMarkovKernel_witness_row_failure :
    ¬ minimalFiberUnitMarkovKernel
          (false, false, false) (false, false, false) ≈
        minimalFiberUnitMarkovKernel
          (true, false, false) (false, false, false) := by
  intro hnormalized
  have hraw :
      minimalFiberKernel
          (false, false, false) (false, false, false) ≈
        minimalFiberKernel
          (true, false, false) (false, false, false) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (minimalFiberUnitMarkovKernel_eqv_raw
          (false, false, false) (false, false, false)))
      (Q'.eqv_trans _ _ _ hnormalized
        (minimalFiberUnitMarkovKernel_eqv_raw
          (true, false, false) (false, false, false)))
  exact
    minimalUniformThreeBitFiberKernel_source_dependent
      hraw

/-- **Concrete conditional-integration fence.**  Forgetting one source
coordinate destroys Markov lumpability even though the underlying kernel is
an exact nonnegative, row-normalized, pushforward-exact fiber conditional
kernel and the terminal message is the positive constant one. -/
theorem minimalFiberUnitMarkovKernel_not_lumpable_on_incompleteRetainedPair :
    ¬ MarkovLumpableOnProjection
      minimalParityStateSpace
      incompleteRetainedPair
      minimalFiberUnitMarkovKernel := by
  intro hlumpable
  have heq :=
    hlumpable
      (false, false, false) (by decide)
      (true, false, false) (by decide)
      incompleteRetainedPair_witness_collision
      (false, false, false) (by decide)
  exact
    minimalFiberUnitMarkovKernel_witness_row_failure heq

/-- Bundled machine-checkable conclusion: the concrete sources have the same
reduced carrier value but different terminal-normalized conditional rows. -/
theorem conditional_integration_does_not_imply_reduced_carrier_lumpability :
    incompleteRetainedPair (false, false, false) =
        incompleteRetainedPair (true, false, false) ∧
      ¬ minimalFiberUnitMarkovKernel
          (false, false, false) (false, false, false) ≈
        minimalFiberUnitMarkovKernel
          (true, false, false) (false, false, false) :=
  ⟨incompleteRetainedPair_witness_collision,
    minimalFiberUnitMarkovKernel_witness_row_failure⟩

end YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.terminalNormalizedKernel_row_normalized
#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.terminalNormalizedKernel_eqv_of_rows
#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.threeBlockFiberTerminalKernel_source_pattern_lumpable
#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.minimalFiberUnitMarkovKernel_eqv_raw
#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.minimalFiberUnitMarkovKernel_witness_row_failure
#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.minimalFiberUnitMarkovKernel_not_lumpable_on_incompleteRetainedPair
#print axioms YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence.conditional_integration_does_not_imply_reduced_carrier_lumpability
