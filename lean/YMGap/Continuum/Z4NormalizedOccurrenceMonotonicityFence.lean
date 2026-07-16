/-
# Normalized occurrence is not implied monotone by termwise monotonicity

Every fixed-cutoff physical spin-foam summand is a nonnegative monomial in
the coupling (times a coupling-independent multiplicity).  Consequently its
event numerator and full partition are both termwise nondecreasing.  This
does *not* imply that their normalized ratio is nondecreasing.

The exact three-state hard-core gas below is the minimal obstruction.  Its
states are the vacuum, a marked root of activity `w`, and an incompatible
blocker of activity `w^3`.  All three state weights, the root numerator, and
the partition increase from `w = 3/4` to `w = 1`, but the normalized root
occurrence decreases from `48/139` to `1/3`.

This fence does not claim a counterexample for the particular four-
dimensional finite law.  It proves that raw termwise coupling monotonicity is
insufficient there: a proof of normalized root/block monotonicity needs an
additional event-versus-energy likelihood-ratio (TP2/MLR) inequality.
-/

import YMGap.Continuum.CrossRatioMonotone
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.RGTransport

namespace YMGap.Continuum.Z4NormalizedOccurrenceMonotonicityFence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CrossRatioMonotone
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

def lowerCoupling : Q' := Q'.mkPos 3 4 (by decide)

def upperCoupling : Q' := 1

/-- Weight of the marked root state. -/
def rootWeight (w : Q') : Q' := qpow w 1

/-- Weight of an incompatible state whose energy is three times larger. -/
def blockerWeight (w : Q') : Q' := qpow w 3

/-- Partition of the three compatible alternatives: vacuum, root, blocker. -/
def toyPartition (w : Q') : Q' :=
  1 + (rootWeight w + blockerWeight w)

theorem lowerCoupling_nonnegative : (0 : Q') ≤ lowerCoupling := by decide

theorem lower_le_upper : lowerCoupling ≤ upperCoupling := by decide

/-- Every individual state weight is nondecreasing across the test window. -/
theorem all_state_weights_termwise_mono :
    (1 : Q') ≤ 1 ∧
      rootWeight lowerCoupling ≤ rootWeight upperCoupling ∧
        blockerWeight lowerCoupling ≤ blockerWeight upperCoupling := by
  decide

theorem root_numerator_mono :
    rootWeight lowerCoupling ≤ rootWeight upperCoupling := by
  decide

theorem partition_mono :
    toyPartition lowerCoupling ≤ toyPartition upperCoupling := by
  decide

theorem toyPartition_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < toyPartition w := by
  unfold toyPartition
  have hroot : (0 : Q') ≤ rootWeight w := qpow_nonneg w hw 1
  have hblocker : (0 : Q') ≤ blockerWeight w := qpow_nonneg w hw 3
  exact YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (show (0 : Q') < 1 by decide)
    (Q'.add_le_self_of_nonneg 1 (rootWeight w + blockerWeight w)
      (Q'.zero_le_add _ _ hroot hblocker))

/-- Normalized probability that the marked root, rather than the vacuum or
the incompatible blocker, occurs. -/
def toyRootOccurrenceProbability
    (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos (rootWeight w) (toyPartition w) (toyPartition_pos w hw)

theorem lower_probability_eqv :
    toyRootOccurrenceProbability lowerCoupling lowerCoupling_nonnegative ≈
      Q'.mkPos 48 139 (by decide) := by
  decide

theorem upper_probability_eqv :
    toyRootOccurrenceProbability upperCoupling (by decide) ≈
      Q'.mkPos 1 3 (by decide) := by
  decide

/-- Exact rational fence: despite pointwise growth of every state weight and
growth of both unnormalized sums, the normalized marked-root occurrence is
strictly smaller at the larger coupling. -/
theorem normalized_root_occurrence_strictly_decreases :
    toyRootOccurrenceProbability upperCoupling (by decide) <
      toyRootOccurrenceProbability lowerCoupling
        lowerCoupling_nonnegative := by
  decide

/-- The corresponding non-monotonicity statement in the direction that a
naive termwise-normalization argument would try to prove. -/
theorem termwise_mono_does_not_normalize :
    ¬ toyRootOccurrenceProbability lowerCoupling
        lowerCoupling_nonnegative ≤
      toyRootOccurrenceProbability upperCoupling (by decide) := by
  decide

/-! The precise missing structure: event-versus-total MLR -/

/-- Coefficients of the marked event on the exponent grid `0,1,3`. -/
def eventCoefficient : Nat → Q'
  | 1 => 1
  | _ => 0

/-- Coefficients of the full three-state partition on the same grid. -/
def totalCoefficient : Nat → Q'
  | 0 | 1 | 2 => 1
  | _ => 0

def toyExponent : Nat → Nat
  | 0 => 0
  | 1 => 1
  | _ => 3

/-- The high-energy blocker produces the failed MLR minor `1 ≤ 0` between
exponents one and three.  Thus the exact hypothesis consumed by
`CrossRatioMonotone.crossTP2` is genuinely absent in the fence. -/
theorem toy_event_total_arrayMLR_fails
    (H : ArrayMLR eventCoefficient totalCoefficient toyExponent) : False := by
  have hbad := H.mlr 2 1 (by decide)
  change (1 : Q') ≤ 0 at hbad
  exact (by decide : ¬ (1 : Q') ≤ 0) hbad

#print axioms all_state_weights_termwise_mono
#print axioms root_numerator_mono
#print axioms partition_mono
#print axioms toyPartition_pos
#print axioms lower_probability_eqv
#print axioms upper_probability_eqv
#print axioms normalized_root_occurrence_strictly_decreases
#print axioms termwise_mono_does_not_normalize
#print axioms toy_event_total_arrayMLR_fails

end YMGap.Continuum.Z4NormalizedOccurrenceMonotonicityFence
