/-
# Finite incremental bridge from cutoff two to the stable tail

The exact cutoff-two gap and the full late-pair stability theorem leave a
finite prefix between them.  This module gives that prefix its causal form.
A finite certificate records relative moving-matrix and moving-diagonal
errors for each consecutive cutoff.  The gap rate is propagated recursively
from the verified `49/50` anchor.  If the final prefix cutoff is also a start
of the verified tail and the composed rate is still below one, the same
strict rate reaches the moving Bishop-real forms.

No increment estimate or budget is postulated silently: they are explicit
fields of the remaining certificate.  The module does not inhabit those
fields.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. The rate recurrence forced by one relative moving-form step -/

def cutoffTwoPrefixCutoff (stage : Nat) : Nat := 2 + stage

def cutoffTwoPrefixRate (error : Nat → Q') : Nat → Q'
  | 0 => cutoffTwoAnchorRate
  | stage + 1 =>
      cutoffTwoPrefixRate error stage * ((1 : Q') + error stage) +
        error stage

def cutoffTwoPrefixTailRate
    (error : Nat → Q') (length : Nat) : Q' :=
  cutoffTwoPrefixRate error length *
      ((1 : Q') + cutoffTwoTailSeedRelativeError) +
    cutoffTwoTailSeedRelativeError

/-- Abstract one-step propagation.  Matrix drift adds `error`; diagonal drift
inflates the old norm by `1 + error`. -/
theorem moving_abs_gap_step
    {firstMatrix laterMatrix firstDiagonal laterDiagonal rate error : Q'}
    (hrate : (0 : Q') ≤ rate)
    (hgap : Q'.abs firstMatrix ≤ rate * firstDiagonal)
    (hmatrix : Q'.abs (firstMatrix + (-laterMatrix)) ≤
      error * laterDiagonal)
    (hdiagonal : Q'.abs (firstDiagonal + (-laterDiagonal)) ≤
      error * laterDiagonal) :
    Q'.abs laterMatrix ≤
      (rate * ((1 : Q') + error) + error) * laterDiagonal := by
  have hdiagonalInflation : firstDiagonal ≤
      ((1 : Q') + error) * laterDiagonal := by
    have hadd := ExpNeg.le_add_of_abs_sub_le hdiagonal
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (Q'.eqv_trans _
          ((1 : Q') * laterDiagonal + error * laterDiagonal) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.eqv_symm (Q'.one_mul_eqv laterDiagonal)))
          (Q'.eqv_symm (Q'.add_mul_eqv (1 : Q') error laterDiagonal))))
  have hscaled : rate * firstDiagonal ≤
      rate * (((1 : Q') + error) * laterDiagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalInflation hrate
  have hcommuted : Q'.abs (laterMatrix + (-firstMatrix)) ≤
      error * laterDiagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          laterMatrix firstMatrix)) hmatrix
  have htriangle := Q'.abs_le_abs_add_abs_sub laterMatrix firstMatrix
  have hsum : Q'.abs firstMatrix +
        Q'.abs (laterMatrix + (-firstMatrix)) ≤
      rate * (((1 : Q') + error) * laterDiagonal) +
        error * laterDiagonal :=
    Q'.add_le_add (Q'.le_trans' _ _ _ hgap hscaled) hcommuted
  refine Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ hsum ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      ((rate * ((1 : Q') + error)) * laterDiagonal +
        error * laterDiagonal) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv rate ((1 : Q') + error) laterDiagonal)))
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (rate * ((1 : Q') + error)) error laterDiagonal)))

/-! ## 2. A finite sequence of physical moving-form increments -/

structure CutoffTwoPulledFinitePrefixIncrementControl
    (coefficient : Nat → Q') (length : Nat) : Type 1 where
  error : Nat → Q'
  anchor_gap :
    Q'.abs
        (cutoffTwoActualMovingMatrixAt
          (cutoffTwoPrefixCutoff 0) coefficient) ≤
      cutoffTwoAnchorRate *
        cutoffTwoActualMovingDiagonalAt
          (cutoffTwoPrefixCutoff 0) coefficient
  error_nonnegative : ∀ stage, stage < length → (0 : Q') ≤ error stage
  moving_error : ∀ stage, stage < length →
    Q'.abs
        (cutoffTwoActualMovingMatrixAt
            (cutoffTwoPrefixCutoff stage) coefficient +
          (-cutoffTwoActualMovingMatrixAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient)) ≤
        error stage *
          cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient ∧
      Q'.abs
        (cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff stage) coefficient +
          (-cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient)) ≤
        error stage *
          cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient

namespace CutoffTwoPulledFinitePrefixIncrementControl

theorem prefixRate_nonnegative
    {coefficient : Nat → Q'} {length : Nat}
    (control : CutoffTwoPulledFinitePrefixIncrementControl
      coefficient length) :
    ∀ stage, stage ≤ length →
      (0 : Q') ≤ cutoffTwoPrefixRate control.error stage
  | 0, _ => cutoffTwoSectorRate49Over50_nonnegative
  | stage + 1, hstage => by
      have hprevious : stage ≤ length := Nat.le_trans
        (Nat.le_succ stage) hstage
      have hstageLt : stage < length := Nat.lt_of_succ_le hstage
      have hrate := control.prefixRate_nonnegative stage hprevious
      have herror := control.error_nonnegative stage hstageLt
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ hrate
          (Q'.zero_le_add _ _ (by decide) herror)) herror

/-- Induction along the certified finite prefix propagates the exact
cutoff-two gap to every certified stage. -/
theorem abs_gap_at_stage
    {coefficient : Nat → Q'} {length : Nat}
    (control : CutoffTwoPulledFinitePrefixIncrementControl
      coefficient length) :
    ∀ stage, stage ≤ length →
      Q'.abs
          (cutoffTwoActualMovingMatrixAt
            (cutoffTwoPrefixCutoff stage) coefficient) ≤
        cutoffTwoPrefixRate control.error stage *
          cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff stage) coefficient
  | 0, _ => by
      exact control.anchor_gap
  | stage + 1, hstage => by
      have hprevious : stage ≤ length := Nat.le_trans
        (Nat.le_succ stage) hstage
      have hstageLt : stage < length := Nat.lt_of_succ_le hstage
      have hgap := control.abs_gap_at_stage stage hprevious
      have hstep := control.moving_error stage hstageLt
      exact moving_abs_gap_step
        (control.prefixRate_nonnegative stage hprevious)
        hgap hstep.1 hstep.2

private theorem prefixRate_step_expansion_eqv (rate error : Q') :
    rate * ((1 : Q') + error) + error ≈
      rate + (rate * error + error) := by
  ring_qeqv

private theorem sumEnvelope_step_eqv
    (anchor accumulated error : Q') :
    (anchor + (((1 : Q') + 1) * accumulated)) + (error + error) ≈
      anchor + (((1 : Q') + 1) * (accumulated + error)) := by
  ring_qeqv

/-- Before the rate reaches one, the nonlinear recurrence loses at most
twice the accumulated relative increment.  This turns a very long finite
prefix into one rational partial-sum budget. -/
theorem prefixRate_le_anchor_add_twice_finSum
    {coefficient : Nat → Q'} {length : Nat}
    (control : CutoffTwoPulledFinitePrefixIncrementControl
      coefficient length)
    (hbudget : ∀ stage, stage ≤ length →
      cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error stage) ≤
        (1 : Q')) :
    ∀ stage, stage ≤ length →
      cutoffTwoPrefixRate control.error stage ≤
        cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error stage)
  | 0, _ => by
      exact Q'.le_of_eqv (by ring_qeqv)
  | stage + 1, hstage => by
      have hprevious : stage ≤ length := Nat.le_trans
        (Nat.le_succ stage) hstage
      have hstageLt : stage < length := Nat.lt_of_succ_le hstage
      have hinduction := control.prefixRate_le_anchor_add_twice_finSum
        hbudget stage hprevious
      have hrateOne : cutoffTwoPrefixRate control.error stage ≤ (1 : Q') :=
        Q'.le_trans' _ _ _ hinduction (hbudget stage hprevious)
      have herror := control.error_nonnegative stage hstageLt
      have hproduct : cutoffTwoPrefixRate control.error stage *
          control.error stage ≤ control.error stage := by
        exact Q'.le_trans' _ ((1 : Q') * control.error stage) _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hrateOne herror)
          (Q'.le_of_eqv (Q'.one_mul_eqv _))
      have hinside :
          cutoffTwoPrefixRate control.error stage * control.error stage +
              control.error stage ≤
            control.error stage + control.error stage :=
        Q'.add_le_add_right _ _ (control.error stage) hproduct
      have hrecurrence : cutoffTwoPrefixRate control.error (stage + 1) ≤
          cutoffTwoPrefixRate control.error stage +
            (control.error stage + control.error stage) := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (prefixRate_step_expansion_eqv
              (cutoffTwoPrefixRate control.error stage)
              (control.error stage)))
          (Q'.add_le_add (Q'.le_refl' _) hinside)
      have henvelopeStep :
          cutoffTwoPrefixRate control.error stage +
              (control.error stage + control.error stage) ≤
            (cutoffTwoAnchorRate +
                (((1 : Q') + 1) * finSum control.error stage)) +
              (control.error stage + control.error stage) :=
        Q'.add_le_add_right _ _ _ hinduction
      refine Q'.le_trans' _ _ _ hrecurrence
        (Q'.le_trans' _ _ _ henvelopeStep ?_)
      exact Q'.le_of_eqv
        (sumEnvelope_step_eqv cutoffTwoAnchorRate
          (finSum control.error stage) (control.error stage))

/-- A closed partial-sum inequality discharges the recursive final-rate
field.  Thus a long prefix needs one uniform sum budget, not a normalization
of tens of thousands of individual recurrence expressions. -/
theorem prefixTailRate_lt_one_of_sumBudget
    {coefficient : Nat → Q'} {length : Nat}
    (control : CutoffTwoPulledFinitePrefixIncrementControl
      coefficient length)
    (hbudget : ∀ stage, stage ≤ length →
      cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error stage) ≤
        (1 : Q'))
    (hstrict :
      (cutoffTwoAnchorRate +
          (((1 : Q') + 1) * finSum control.error length)) *
            ((1 : Q') + cutoffTwoTailSeedRelativeError) +
          cutoffTwoTailSeedRelativeError <
        (1 : Q')) :
    cutoffTwoPrefixTailRate control.error length < (1 : Q') := by
  have hprefix := control.prefixRate_le_anchor_add_twice_finSum
    hbudget length (Nat.le_refl _)
  have htail0 : (0 : Q') ≤ cutoffTwoTailSeedRelativeError :=
    Q'.le_of_lt cutoffTwoTailSeedRelativeError_pos
  have hfactor0 : (0 : Q') ≤
      (1 : Q') + cutoffTwoTailSeedRelativeError :=
    Q'.zero_le_add _ _ (by decide) htail0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hprefix hfactor0
  have hadd := Q'.add_le_add_right _ _
    cutoffTwoTailSeedRelativeError hscaled
  exact Q'.lt_of_le_of_lt hadd hstrict

end CutoffTwoPulledFinitePrefixIncrementControl

/-! ## 3. Alignment of the finite prefix with the proved tail -/

/-- Exact finite-prefix-to-tail certificate.  The incremental controls start
at cutoff two; their endpoint is required to be a stability start, and the
explicit composed rate must retain strict slack below one. -/
structure CutoffTwoPulledFinitePrefixToTailGap
    (coefficient : Nat → Q') : Type 1 where
  length : Nat
  incrementControl :
    CutoffTwoPulledFinitePrefixIncrementControl coefficient length
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
  final_rate_lt_one :
    cutoffTwoPrefixTailRate incrementControl.error length < (1 : Q')

namespace CutoffTwoPulledFinitePrefixToTailGap

theorem final_rate_nonnegative
    {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledFinitePrefixToTailGap coefficient) :
    (0 : Q') ≤
      cutoffTwoPrefixTailRate
        certificate.incrementControl.error certificate.length := by
  unfold cutoffTwoPrefixTailRate
  have hprefix := certificate.incrementControl.prefixRate_nonnegative
    certificate.length (Nat.le_refl _)
  have htail0 : (0 : Q') ≤ cutoffTwoTailSeedRelativeError :=
    Q'.le_of_lt cutoffTwoTailSeedRelativeError_pos
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hprefix
      (Q'.zero_le_add _ _ (by decide) htail0)) htail0

/-- The finite incremental bridge and the aligned tail stability propagate a
strict gap from cutoff two to every cutoff beyond the prefix. -/
theorem later_abs_gap
    {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledFinitePrefixToTailGap coefficient)
    (later : Nat)
    (hlater : cutoffTwoPrefixCutoff certificate.length ≤ later) :
    Q'.abs (cutoffTwoActualMovingMatrixAt later coefficient) ≤
      cutoffTwoPrefixTailRate
          certificate.incrementControl.error certificate.length *
        cutoffTwoActualMovingDiagonalAt later coefficient := by
  have hseedGap := certificate.incrementControl.abs_gap_at_stage
    certificate.length (Nat.le_refl _)
  have htail := certificate.tail_stability later hlater
  exact moving_abs_gap_step
    (certificate.incrementControl.prefixRate_nonnegative
      certificate.length (Nat.le_refl _))
    hseedGap htail.1 htail.2

private theorem cReal_leEv_of_eventual_abs_gap
    (matrix diagonal : CReal) (rate : Q')
    (hrate0 : (0 : Q') ≤ rate) (hrate1 : rate < (1 : Q'))
    (gapAnchor : Nat)
    (hgap : ∀ stage, gapAnchor ≤ stage →
      Q'.abs (matrix.approx stage) ≤ rate * diagonal.approx stage) :
    CReal.leEv matrix (CReal.mul (CReal.ofQ' rate) diagonal) := by
  intro tolerance htolerance
  let delta := HalfPow.half * tolerance
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos tolerance htolerance
  obtain ⟨matrixCutoff, hmatrix⟩ := matrix.cauchy delta hdelta
  obtain ⟨diagonalCutoff, hdiagonal⟩ := diagonal.cauchy delta hdelta
  let threshold := max matrixCutoff diagonalCutoff
  let anchor := max gapAnchor threshold
  have hgapAnchor : gapAnchor ≤ anchor := Nat.le_max_left _ _
  have hthresholdAnchor : threshold ≤ anchor := Nat.le_max_right _ _
  have hmatrixAnchor : matrixCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_left _ _) hthresholdAnchor
  have hdiagonalAnchor : diagonalCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_right _ _) hthresholdAnchor
  refine ⟨threshold, ?_⟩
  intro later hlater
  have hmatrixLater : matrixCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hdiagonalLater : diagonalCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  have hmatrixToAnchor : matrix.approx later ≤
      matrix.approx anchor + delta :=
    (hmatrix later anchor hmatrixLater hmatrixAnchor).1
  have hdiagonalFromAnchor : diagonal.approx anchor ≤
      diagonal.approx later + delta :=
    (hdiagonal anchor later hdiagonalAnchor hdiagonalLater).1
  have hanchorGap : matrix.approx anchor ≤
      rate * diagonal.approx anchor := by
    exact Q'.le_trans' _ (Q'.abs (matrix.approx anchor)) _
      (Q'.le_abs_self _) (hgap anchor hgapAnchor)
  have hscaledDiagonal : rate * diagonal.approx anchor ≤
      rate * (diagonal.approx later + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalFromAnchor hrate0
  have hscaleDelta : rate * delta ≤ delta :=
    Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt hrate1) (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : rate * delta + delta ≤ tolerance :=
    Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves tolerance))
  refine Q'.le_trans' _ _ _ hmatrixToAnchor ?_
  refine Q'.le_trans' _ (rate * diagonal.approx anchor + delta) _
    (Q'.add_le_add_right _ _ delta hanchorGap) ?_
  refine Q'.le_trans' _
    (rate * (diagonal.approx later + delta) + delta) _
    (Q'.add_le_add_right _ _ delta hscaledDiagonal) ?_
  refine Q'.le_trans' _
    (rate * diagonal.approx later + (rate * delta + delta)) _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((rate * diagonal.approx later + rate * delta) + delta) _
        (Q'.add_eqv_congr_right _ _ delta
          (Q'.mul_add_eqv rate (diagonal.approx later) delta))
        (Q'.add_assoc_eqv
          (rate * diagonal.approx later) (rate * delta) delta))) ?_
  exact Q'.add_le_add_left
    (rate * diagonal.approx later) (rate * delta + delta)
    tolerance herror

/-- A successful finite-prefix certificate reaches the literal same-object
moving Bishop-real forms at its explicitly computed strict rate. -/
theorem centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal
    {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledFinitePrefixToTailGap coefficient) :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ'
          (cutoffTwoPrefixTailRate
            certificate.incrementControl.error certificate.length))
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  apply cReal_leEv_of_eventual_abs_gap
    (cutoffTwoMovingMatrixLimit coefficient)
    (cutoffTwoMovingDiagonalLimit coefficient)
    (cutoffTwoPrefixTailRate
      certificate.incrementControl.error certificate.length)
    certificate.final_rate_nonnegative certificate.final_rate_lt_one
    (cutoffTwoPrefixCutoff certificate.length)
  intro later hlater
  exact certificate.later_abs_gap later hlater

end CutoffTwoPulledFinitePrefixToTailGap

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.moving_abs_gap_step
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.CutoffTwoPulledFinitePrefixIncrementControl.abs_gap_at_stage
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.CutoffTwoPulledFinitePrefixIncrementControl.prefixRate_le_anchor_add_twice_finSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.CutoffTwoPulledFinitePrefixIncrementControl.prefixTailRate_lt_one_of_sumBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.CutoffTwoPulledFinitePrefixToTailGap.later_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.CutoffTwoPulledFinitePrefixToTailGap.centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal
