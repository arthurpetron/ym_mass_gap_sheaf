/-
# Finite-prefix and analytic-tail refresh comparison

This module lifts the finite `L1` refresh-comparison theorem to an indexed
family of finite state spaces.  A uniform strict defect tolerance is obtained
from finitely checked prefix values and an antitone analytic tail.  Each
stage then receives a kernel-checked `FiniteRefreshComparisonCertificate`
with the same positive contraction margin.

External exact arithmetic, verified interval computation, or a finite
statistical argument with a formal deterministic coverage theorem may fill
the prefix fields.  Lean checks every emitted inequality and the induction
covering the infinite tail.  Uncertified random sampling cannot fill this
interface.

The conclusion remains an indexed family of finite contraction estimates.
It does not construct a continuum limit or identify a physical Hamiltonian.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRefreshSpectralComparison

namespace YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRefreshSpectralComparison
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic strict prefix/tail scalar budget -/

/-- A proof-carrying uniform strict bound assembled from finite prefix checks
and a monotone tail theorem. -/
structure StrictErrorPrefixTail (error : Nat → Q') : Type where
  tolerance : Q'
  tolerance_nonnegative : (0 : Q') ≤ tolerance
  tolerance_lt_one : tolerance < (1 : Q')
  threshold : Nat
  prefix_bound : ∀ stage, stage < threshold → error stage ≤ tolerance
  threshold_bound : error threshold ≤ tolerance
  tail_step : ∀ stage, threshold ≤ stage →
    error (stage + 1) ≤ error stage

namespace StrictErrorPrefixTail

/-- Every point later than a tail start is bounded by that start. -/
theorem tail_antitone_add
    {error : Nat → Q'}
    (budget : StrictErrorPrefixTail error)
    (start : Nat) (hstart : budget.threshold ≤ start) :
    ∀ offset, error (start + offset) ≤ error start
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      refine Q'.le_trans' _ _ _ ?_
        (budget.tail_antitone_add start hstart offset)
      rw [show start + (offset + 1) = (start + offset) + 1 by omega]
      exact budget.tail_step (start + offset)
        (Nat.le_trans hstart (Nat.le_add_right start offset))

/-- The checked prefix and analytic tail cover every natural stage. -/
theorem bound_all
    {error : Nat → Q'}
    (budget : StrictErrorPrefixTail error)
    (stage : Nat) :
    error stage ≤ budget.tolerance := by
  rcases Nat.lt_or_ge stage budget.threshold with hprefix | htail
  · exact budget.prefix_bound stage hprefix
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le htail
    exact Q'.le_trans' _ _ _
      (budget.tail_antitone_add budget.threshold
        (Nat.le_refl _) offset)
      budget.threshold_bound

/-- The common margin supplied by the strict tolerance. -/
def uniformMargin
    {error : Nat → Q'}
    (budget : StrictErrorPrefixTail error) : Q' :=
  (1 : Q') - budget.tolerance

theorem uniformMargin_pos
    {error : Nat → Q'}
    (budget : StrictErrorPrefixTail error) :
    (0 : Q') < budget.uniformMargin := by
  exact one_sub_pos_of_lt_one budget.tolerance_lt_one

end StrictErrorPrefixTail

/-! ## 2. Indexed finite Markov comparison family -/

/-- An indexed family of finite kernels whose row defects are controlled by
one prefix/tail scalar budget. -/
structure FiniteRefreshComparisonPrefixTailFamily
    (State : Nat → Type)
    (states : ∀ stage, List (State stage))
    (kernel reference :
      ∀ stage, State stage → State stage → Q') : Type where
  error : Nat → Q'
  errorBudget : StrictErrorPrefixTail error
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
  row_defect_le_error :
    ∀ stage source, source ∈ states stage →
      finiteRowL1Defect (states stage)
        (kernel stage) (reference stage) source ≤ error stage

namespace FiniteRefreshComparisonPrefixTailFamily

/-- Every stage receives the same strict tolerance as its checked comparison
parameter; the prefix/tail argument supplies its row-defect bound. -/
def toComparisonCertificate
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonPrefixTailFamily
        State states kernel reference)
    (stage : Nat) :
    FiniteRefreshComparisonCertificate
      (states stage) (kernel stage) (reference stage) where
  epsilon := family.errorBudget.tolerance
  epsilon_nonnegative := family.errorBudget.tolerance_nonnegative
  epsilon_lt_one := family.errorBudget.tolerance_lt_one
  kernel_nonnegative := family.kernel_nonnegative stage
  kernel_row_normalized := family.kernel_row_normalized stage
  reference_nonnegative := family.reference_nonnegative stage
  reference_row_normalized := family.reference_row_normalized stage
  row_defect_le := by
    intro source hsource
    exact Q'.le_trans' _ _ _
      (family.row_defect_le_error stage source hsource)
      (family.errorBudget.bound_all stage)

/-- Uniform checked action estimate on every finite stage and every
reference-centered bounded observable. -/
theorem centeredAction_abs_le
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonPrefixTailFamily
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
      family.errorBudget.tolerance * bound := by
  exact
    (family.toComparisonCertificate stage).centeredAction_abs_le
      observable bound bound_nonnegative observable_bound
      reference_zero source hsource

theorem uniformMargin_pos
    {State : Nat → Type}
    {states : ∀ stage, List (State stage)}
    {kernel reference :
      ∀ stage, State stage → State stage → Q'}
    (family :
      FiniteRefreshComparisonPrefixTailFamily
        State states kernel reference) :
    (0 : Q') < family.errorBudget.uniformMargin :=
  family.errorBudget.uniformMargin_pos

end FiniteRefreshComparisonPrefixTailFamily

end YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail.StrictErrorPrefixTail.bound_all
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail.StrictErrorPrefixTail.uniformMargin_pos
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail.FiniteRefreshComparisonPrefixTailFamily.toComparisonCertificate
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparisonPrefixTail.FiniteRefreshComparisonPrefixTailFamily.centeredAction_abs_le
