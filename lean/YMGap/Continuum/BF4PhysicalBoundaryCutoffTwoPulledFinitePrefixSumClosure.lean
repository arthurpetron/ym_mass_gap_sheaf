/-
# A one-two-hundredth finite-prefix sum closes the BF4 limit gap

The preceding module constructs every individual consecutive prefix error.
This module identifies one simple exact budget that makes the recursive rate
strict after composition with the proved tail stability:

  sum eta <= 1/200
  qPrefix <= 49/50 + 2/200 = 99/100
  qFinal  <= (99/100)(1 + 1/200) + 1/200 = 19999/20000 < 1.

Thus the remaining quantitative question is no longer an opaque recursive
rate calculation.  It is the single finite total-variation inequality
`finSum eta <= 1/200`, aligned with a tail-stability start.  A named exact
recode still connects the compact Bishop-real aliases to the displayed
physical forms, as recorded in the imported increment-existence module.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

/-! ## 1. Exact slack arithmetic -/

/-- The entire finite prefix is allocated one two-hundredth of relative
variation. -/
def cutoffTwoFinitePrefixTotalErrorBudget : Q' :=
  cutoffTwoTailSeedRelativeError

/-- The additive prefix envelope is at most `99/100`. -/
theorem cutoffTwoFinitePrefixEnvelopeAtBudget_le_one :
    cutoffTwoAnchorRate +
        (((1 : Q') + 1) * cutoffTwoFinitePrefixTotalErrorBudget) ≤
      (1 : Q') := by
  decide

/-- After the separate `1/200` tail error, the closed rate is exactly below
one (numerically `19999/20000`). -/
theorem cutoffTwoFinitePrefixBudgetClosedTailRate_lt_one :
    (cutoffTwoAnchorRate +
        (((1 : Q') + 1) * cutoffTwoFinitePrefixTotalErrorBudget)) *
          ((1 : Q') + cutoffTwoTailSeedRelativeError) +
        cutoffTwoTailSeedRelativeError <
      (1 : Q') := by
  decide

/-- A single monotone partial-sum bound supplies both premises of the generic
prefix-rate theorem. -/
theorem prefixTailRate_lt_one_of_finSum_le_totalErrorBudget
    {coefficient : Nat → Q'} {length : Nat}
    (control : CutoffTwoPulledFinitePrefixIncrementControl
      coefficient length)
    (hsum : ∀ stage, stage ≤ length →
      finSum control.error stage ≤
        cutoffTwoFinitePrefixTotalErrorBudget) :
    cutoffTwoPrefixTailRate control.error length < (1 : Q') := by
  have hfactor : (0 : Q') ≤ (1 : Q') + 1 := by decide
  have hbudget : ∀ stage, stage ≤ length →
      cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error stage) ≤
        (1 : Q') := by
    intro stage hstage
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
      (hsum stage hstage) hfactor
    have hadd := Q'.add_le_add_left cutoffTwoAnchorRate _ _ hscaled
    exact Q'.le_trans' _ _ _ hadd
      cutoffTwoFinitePrefixEnvelopeAtBudget_le_one
  have henvelope :
      cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error length) ≤
        cutoffTwoAnchorRate +
          (((1 : Q') + 1) * cutoffTwoFinitePrefixTotalErrorBudget) := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
      (hsum length (Nat.le_refl _)) hfactor
    exact Q'.add_le_add_left cutoffTwoAnchorRate _ _ hscaled
  have htailFactor :
      (0 : Q') ≤ (1 : Q') + cutoffTwoTailSeedRelativeError := by
    exact Q'.zero_le_add _ _ (by decide)
      (Q'.le_of_lt cutoffTwoTailSeedRelativeError_pos)
  have hscaledTail := Q'.mul_le_mul_of_nonneg_right _ _ _
    henvelope htailFactor
  have haddTail := Q'.add_le_add_right _ _
    cutoffTwoTailSeedRelativeError hscaledTail
  have hstrict :
      (cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error length)) *
            ((1 : Q') + cutoffTwoTailSeedRelativeError) +
          cutoffTwoTailSeedRelativeError <
        (1 : Q') :=
    Q'.lt_of_le_of_lt haddTail
      cutoffTwoFinitePrefixBudgetClosedTailRate_lt_one
  exact control.prefixTailRate_lt_one_of_sumBudget hbudget hstrict

/-! ## 2. The remaining data and its contraction -/

def cutoffTwoConstructedFinitePrefixControl
    (coefficient : Nat → Q')
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (length : Nat) :
    CutoffTwoPulledFinitePrefixIncrementControl coefficient length :=
  finitePrefixIncrementControlForEveryCoefficient coefficient recode length

/-- Exact remaining fixed-carrier data after qualitative increment existence:
one tail-aligned endpoint and one `1/200` total prefix-variation bound. -/
structure CutoffTwoPulledFinitePrefixSumClosure
    (coefficient : Nat → Q') : Type 1 where
  recode : CutoffTwoActualMovingFormRecode coefficient
  length : Nat
  tail_stability : ∀ later,
    cutoffTwoPrefixCutoff length ≤ later →
    Q'.abs
        (cutoffTwoActualMovingMatrixAt
            (cutoffTwoPrefixCutoff length) coefficient +
          (-cutoffTwoActualMovingMatrixAt later coefficient)) ≤
        cutoffTwoTailSeedRelativeError *
          cutoffTwoActualMovingDiagonalAt later coefficient ∧
      Q'.abs
        (cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff length) coefficient +
          (-cutoffTwoActualMovingDiagonalAt later coefficient)) ≤
        cutoffTwoTailSeedRelativeError *
          cutoffTwoActualMovingDiagonalAt later coefficient
  prefix_sum_budget : ∀ stage, stage ≤ length →
    finSum
        (cutoffTwoConstructedFinitePrefixControl
          coefficient recode length).error stage ≤
      cutoffTwoFinitePrefixTotalErrorBudget

namespace CutoffTwoPulledFinitePrefixSumClosure

/-- The simple sum closure constructs the complete prefix-to-tail gap
certificate; no recursive-rate field remains. -/
def toFinitePrefixToTailGap
    {coefficient : Nat → Q'}
    (closure : CutoffTwoPulledFinitePrefixSumClosure coefficient) :
    CutoffTwoPulledFinitePrefixToTailGap coefficient where
  length := closure.length
  incrementControl := cutoffTwoConstructedFinitePrefixControl
    coefficient closure.recode closure.length
  tail_stability := closure.tail_stability
  final_rate_lt_one :=
    prefixTailRate_lt_one_of_finSum_le_totalErrorBudget
      (cutoffTwoConstructedFinitePrefixControl
        coefficient closure.recode closure.length)
      closure.prefix_sum_budget

/-- The remaining finite sum closure contracts to the literal same-object
moving Bishop-real form gap at its computed strict rate. -/
theorem centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal
    {coefficient : Nat → Q'}
    (closure : CutoffTwoPulledFinitePrefixSumClosure coefficient) :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ'
          (cutoffTwoPrefixTailRate
            (cutoffTwoConstructedFinitePrefixControl
              coefficient closure.recode closure.length).error
            closure.length))
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  exact
    CutoffTwoPulledFinitePrefixToTailGap.centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal
      closure.toFinitePrefixToTailGap

end CutoffTwoPulledFinitePrefixSumClosure

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure.cutoffTwoFinitePrefixEnvelopeAtBudget_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure.cutoffTwoFinitePrefixBudgetClosedTailRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure.prefixTailRate_lt_one_of_finSum_le_totalErrorBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure.CutoffTwoPulledFinitePrefixSumClosure.toFinitePrefixToTailGap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure.CutoffTwoPulledFinitePrefixSumClosure.centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal
