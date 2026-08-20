/-
# Division-free cross-tail refresh comparison

For a scale-dependent defect ratio `numerator / denominator`, monotonicity on
the infinite tail follows from the division-free inequality

  numerator (k+1) * denominator k
    <= numerator k * denominator (k+1).

This module converts exact finite prefix bounds and that cross-product tail
into the uniform finite refresh-comparison family.  It is designed as the
Lean trust boundary for generated rational certificates, verified interval
arithmetic, and formal finite-system probability bounds.

No physical BF4 estimate is postulated here.  Supplying the numerator,
positive denominator, row-defect majorization, and tail cross inequality
remains the mathematical/computational obligation.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail
import YMGap.Continuum.FusionMarginMono

namespace YMGap.Continuum.FiniteRefreshSpectralComparisonCrossTail

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRefreshSpectralComparison
open YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive quotient and cross-product tail -/

def quotientError
    (numerator denominator : Nat → Q')
    (denominator_pos : ∀ stage, (0 : Q') < denominator stage)
    (stage : Nat) : Q' :=
  Q'.divPos
    (numerator stage) (denominator stage) (denominator_pos stage)

/-- A strict quotient bound from exact prefix checks and a division-free
tail comparison. -/
structure StrictCrossProductErrorTail
    (numerator denominator : Nat → Q') : Type where
  tolerance : Q'
  tolerance_nonnegative : (0 : Q') ≤ tolerance
  tolerance_lt_one : tolerance < (1 : Q')
  threshold : Nat
  denominator_pos : ∀ stage, (0 : Q') < denominator stage
  prefix_bound : ∀ stage, stage < threshold →
    numerator stage ≤ tolerance * denominator stage
  threshold_bound :
    numerator threshold ≤ tolerance * denominator threshold
  tail_cross : ∀ stage, threshold ≤ stage →
    numerator (stage + 1) * denominator stage ≤
      numerator stage * denominator (stage + 1)

namespace StrictCrossProductErrorTail

theorem quotient_tail_step
    {numerator denominator : Nat → Q'}
    (certificate :
      StrictCrossProductErrorTail numerator denominator)
    (stage : Nat) (hstage : certificate.threshold ≤ stage) :
    quotientError numerator denominator certificate.denominator_pos
        (stage + 1) ≤
      quotientError numerator denominator certificate.denominator_pos
        stage := by
  exact YMGap.Continuum.FusionMarginMono.divPos_le_divPos_of_cross
    (numerator (stage + 1)) (denominator (stage + 1))
    (numerator stage) (denominator stage)
    (certificate.denominator_pos (stage + 1))
    (certificate.denominator_pos stage)
    (certificate.tail_cross stage hstage)

/-- Convert the division-free input into the generic strict prefix/tail
budget. -/
def toStrictErrorPrefixTail
    {numerator denominator : Nat → Q'}
    (certificate :
      StrictCrossProductErrorTail numerator denominator) :
    StrictErrorPrefixTail
      (quotientError numerator denominator certificate.denominator_pos) where
  tolerance := certificate.tolerance
  tolerance_nonnegative := certificate.tolerance_nonnegative
  tolerance_lt_one := certificate.tolerance_lt_one
  threshold := certificate.threshold
  prefix_bound := by
    intro stage hstage
    exact Q'.divPos_le_of_le_mul
      (numerator stage) (denominator stage)
      (certificate.denominator_pos stage)
      (certificate.prefix_bound stage hstage)
  threshold_bound := by
    exact Q'.divPos_le_of_le_mul
      (numerator certificate.threshold)
      (denominator certificate.threshold)
      (certificate.denominator_pos certificate.threshold)
      certificate.threshold_bound
  tail_step := certificate.quotient_tail_step

theorem quotient_bound_all
    {numerator denominator : Nat → Q'}
    (certificate :
      StrictCrossProductErrorTail numerator denominator)
    (stage : Nat) :
    quotientError numerator denominator certificate.denominator_pos stage ≤
      certificate.tolerance :=
  certificate.toStrictErrorPrefixTail.bound_all stage

end StrictCrossProductErrorTail

/-! ## 2. Indexed Markov-family adapter -/

/-- An indexed finite refresh comparison whose scalar row-defect majorant is
a positive quotient with a division-free cross-tail certificate. -/
structure FiniteRefreshComparisonCrossTailFamily
    (State : Nat → Type)
    (states : ∀ stage, List (State stage))
    (kernel reference :
      ∀ stage, State stage → State stage → Q') : Type where
  numerator : Nat → Q'
  denominator : Nat → Q'
  errorTail : StrictCrossProductErrorTail numerator denominator
  kernel_nonnegative :
    ∀ stage source, source ∈ states stage →
      ∀ target, target ∈ states stage →
        (0 : Q') ≤ kernel stage source target
  kernel_row_normalized :
    ∀ stage source, source ∈ states stage →
      listQSum (kernel stage source) (states stage) ≈ 1
  reference_nonnegative :
    ∀ stage source, source ∈ states stage →
      ∀ target, target ∈ states stage →
        (0 : Q') ≤ reference stage source target
  reference_row_normalized :
    ∀ stage source, source ∈ states stage →
      listQSum (reference stage source) (states stage) ≈ 1
  row_defect_le_quotient :
    ∀ stage source, source ∈ states stage →
      finiteRowL1Defect (states stage)
          (kernel stage) (reference stage) source ≤
        quotientError numerator denominator errorTail.denominator_pos stage

namespace FiniteRefreshComparisonCrossTailFamily

def toPrefixTailFamily
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonCrossTailFamily
        State states kernel reference) :
    FiniteRefreshComparisonPrefixTailFamily
      State states kernel reference where
  error := quotientError family.numerator family.denominator
    family.errorTail.denominator_pos
  errorBudget := family.errorTail.toStrictErrorPrefixTail
  kernel_nonnegative := family.kernel_nonnegative
  kernel_row_normalized := family.kernel_row_normalized
  reference_nonnegative := family.reference_nonnegative
  reference_row_normalized := family.reference_row_normalized
  row_defect_le_error := family.row_defect_le_quotient

/-- Each stage inherits the common strict tolerance as a checked comparison
certificate. -/
def toComparisonCertificate
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonCrossTailFamily
        State states kernel reference)
    (stage : Nat) :
    FiniteRefreshComparisonCertificate
      (states stage) (kernel stage) (reference stage) :=
  family.toPrefixTailFamily.toComparisonCertificate stage

theorem centeredAction_abs_le
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonCrossTailFamily
        State states kernel reference)
    (stage : Nat)
    (observable : State stage → Q') (bound : Q')
    (bound_nonnegative : (0 : Q') ≤ bound)
    (observable_bound :
      ∀ target, target ∈ states stage →
        Q'.abs (observable target) ≤ bound)
    (reference_zero :
      ∀ source, source ∈ states stage →
        finiteObservableAction (states stage)
          (reference stage) observable source ≈ 0)
    (source : State stage) (hsource : source ∈ states stage) :
    Q'.abs
        (finiteObservableAction (states stage)
          (kernel stage) observable source) ≤
      family.errorTail.tolerance * bound := by
  exact family.toPrefixTailFamily.centeredAction_abs_le
    stage observable bound bound_nonnegative observable_bound
    reference_zero source hsource

theorem uniformMargin_pos
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonCrossTailFamily
        State states kernel reference) :
    (0 : Q') <
      (1 : Q') - family.errorTail.tolerance := by
  exact one_sub_pos_of_lt_one family.errorTail.tolerance_lt_one

end FiniteRefreshComparisonCrossTailFamily

end YMGap.Continuum.FiniteRefreshSpectralComparisonCrossTail

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonCrossTail.StrictCrossProductErrorTail.quotient_tail_step
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonCrossTail.StrictCrossProductErrorTail.quotient_bound_all
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonCrossTail.FiniteRefreshComparisonCrossTailFamily.toComparisonCertificate
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonCrossTail.FiniteRefreshComparisonCrossTailFamily.centeredAction_abs_le
