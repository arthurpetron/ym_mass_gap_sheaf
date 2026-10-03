/-
# Finite ORIGINAL root/log comparison in squared norm

The checked original S/F forms and retained tail give the two diagonal
estimates.  Symmetry of the literal logPartial and differenceQuotient maps
gives additivity and subtraction, then rational polarization gives the
squared-distance bound.  No caller-supplied linearity or norm premise is
used.  This finite comparison does not identify the limiting maps or supply
a changing-family/physical scaling estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootLogFormComparison
import YMGap.Continuum.BF4WilsonAllNomeSymmetricFormNorm
import YMGap.Continuum.BF4WilsonAllNomeLogPartialAlgebra
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.BF4WilsonAllNomeRootLogNormComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedSub)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (differenceQuotient)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (quotient_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeLogPartial (logPartial)
open YMGap.Continuum.BF4WilsonAllNomeLogPartialAlgebra (logPartial_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeRootLogFormComparison
  (diagonalError diagonalError_upper diagonalError_lower)
open YMGap.Continuum.BF4WilsonAllNomeSymmetricFormNorm (symmetric_form_norm_bound)
open YMGap.Continuum.RCSignedPairBudget (neg_mono)

/-- The actual rational error budget, with independent root/log cutoffs. -/
def errorCoefficient (d m : Nat) : Q' := 2*half^d + Q'.invSucc m

private theorem half_power_positive (d : Nat) : (0 : Q') < half^d := by
  induction d with
  | zero =>
      exact (by decide : (0 : Q') < 1)
  | succ d ih =>
      rw [Q'.pow_succ]
      exact Q'.mul_pos (by decide : (0 : Q') < half) ih

theorem errorCoefficient_positive (d m : Nat) :
    (0 : Q') < errorCoefficient d m :=
  Q'.add_pos (Q'.mul_pos (by decide : (0 : Q') < 2) (half_power_positive d))
    (Q'.invSucc_pos m)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "D" => completedSub hw0 hw1

/-- The difference of the two EXISTING maps on the SAME completion. -/
def finiteDifference (d m : Nat) (x : V) : V :=
  D (logPartial hw0 hw1 m x) (differenceQuotient hw0 hw1 (d+2) x)

theorem finiteDifference_symmetric (d m : Nat) (x y : V) :
    B (finiteDifference hw0 hw1 d m x) y =
      B x (finiteDifference hw0 hw1 d m y) := by
  unfold finiteDifference
  rw [completedInner_sub_left, completedInner_sub_right,
    logPartial_symmetric, quotient_symmetric]

private theorem finiteDifference_add (d m : Nat) (x y : V) :
    finiteDifference hw0 hw1 d m (A x y) =
      A (finiteDifference hw0 hw1 d m x) (finiteDifference hw0 hw1 d m y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [finiteDifference_symmetric, completedInner_add_left,
    completedInner_add_left, finiteDifference_symmetric, finiteDifference_symmetric]

private theorem finiteDifference_sub (d m : Nat) (x y : V) :
    finiteDifference hw0 hw1 d m (D x y) =
      D (finiteDifference hw0 hw1 d m x) (finiteDifference hw0 hw1 d m y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [finiteDifference_symmetric, completedInner_sub_left,
    completedInner_sub_left, finiteDifference_symmetric, finiteDifference_symmetric]

/-- Constructed squared-norm comparison, retaining the original boundary
kernel and every state; only the finite log cutoff must be positive. -/
theorem root_log_norm_bound (d : Nat) (x : V) (m : Nat) (hm : 0 < m) :
    RCle (completedDist hw0 hw1 (logPartial hw0 hw1 m x)
      (differenceQuotient hw0 hw1 (d+2) x))
      (RCscale (errorCoefficient d m * errorCoefficient d m) (B x x)) := by
  have hroot0 : (0 : Q') ≤ 2*half^d :=
    Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
      (Q'.pow_nonneg half half_nonneg d)
  have hroot : 2*half^d ≤ errorCoefficient d m :=
    Q'.add_le_self_of_nonneg _ _ (Q'.invSucc_nonneg m)
  have hlog : Q'.invSucc m ≤ errorCoefficient d m :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hroot0)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hupper : ∀ z : V,
      RCle (B z (finiteDifference hw0 hw1 d m z))
        (RCscale (errorCoefficient d m) (B z z)) := by
    intro z
    have h := diagonalError_upper hw0 hw1 d z m hm
    change RCle (B z (finiteDifference hw0 hw1 d m z))
      (RCscale (2*half^d) (B z z)) at h
    exact RCle_trans h (RCscale_scalar_mono hroot (completedInner_nonnegative hw0 hw1 z))
  have hlower : ∀ z : V,
      RCle (RCneg (RCscale (errorCoefficient d m) (B z z)))
        (B z (finiteDifference hw0 hw1 d m z)) := by
    intro z
    have h := diagonalError_lower hw0 hw1 (d+2) z m hm
    change RCle (RCneg (RCscale (Q'.invSucc m) (B z z)))
      (B z (finiteDifference hw0 hw1 d m z)) at h
    exact RCle_trans (neg_mono
      (RCscale_scalar_mono hlog (completedInner_nonnegative hw0 hw1 z))) h
  have h := symmetric_form_norm_bound hw0 hw1 (finiteDifference hw0 hw1 d m)
    (finiteDifference_add hw0 hw1 d m) (finiteDifference_sub hw0 hw1 d m)
    (finiteDifference_symmetric hw0 hw1 d m) (errorCoefficient d m)
    (errorCoefficient_positive d m) hupper hlower x
  simpa only [completedDist, finiteDifference] using h

#print axioms errorCoefficient
#print axioms errorCoefficient_positive
#print axioms finiteDifference
#print axioms finiteDifference_symmetric
#print axioms root_log_norm_bound

end YMGap.Continuum.BF4WilsonAllNomeRootLogNormComparison
