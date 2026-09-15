/-
# Exact finite range approximation for the ORIGINAL transfer

For the existing T2 and D=I-T2, the explicitly computed sum
P_n x = x + D x + ... + D^(n-1) x satisfies
  T2(P_n x) + D^n x = x.
Its ORIGINAL squared approximation error is exactly m_x(0,2n), an
already constructed mixed moment with a CReal representative and modulus.
No inverse, density theorem, spectral model or representative selection
is used. On a possible T2-kernel vector the residual stays equal to x:
the identity exposes that obstruction instead of silently removing it.

This is finite operator algebra at fixed SU(2) nome and spacing. Decay
of these residuals on EVERY original state, full-space time-zero
continuity, physical Hamiltonian identification and continuum/Clay remain
open. In particular, this module does not assert successful approximation
at arbitrarily small tolerances for every original vector.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedSub_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicResolvent (defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (sub_add_left_cancel)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem defectPower_add (s t : Nat) (x : Completion) :
    defectPower s (defectPower t x) = defectPower (s+t) x := by
  induction s with
  | zero => rw [Nat.zero_add]; rfl
  | succ s ih =>
      change defect (defectPower s (defectPower t x)) = defectPower (s+1+t) x
      rw [ih, show s+1+t=(s+t)+1 by omega]
      rfl

/-- A finite candidate preimage, not an inverse of T2. -/
def partialPreimage : Nat → Completion → Completion
  | 0, _ => completedZero
  | n+1, x => completedAdd (partialPreimage n x) (defectPower n x)

theorem transfer_residual_split (x : Completion) :
    completedAdd (twoStepTransfer x) (defect x) = x := by
  rw [completedAdd_comm]
  exact completedSub_add_cancel x (twoStepTransfer x)

theorem partialPreimage_identity (n : Nat) (x : Completion) :
    completedAdd (twoStepTransfer (partialPreimage n x)) (defectPower n x) = x := by
  induction n with
  | zero =>
      change completedAdd (completedTime 2 completedZero) x = x
      rw [completedTime_zeroState, completedZero_add]
  | succ n ih =>
      change completedAdd (completedTime 2 (completedAdd (partialPreimage n x) (defectPower n x)))
        (defect (defectPower n x)) = x
      rw [completedTime_add, completedAdd_assoc]
      change completedAdd (twoStepTransfer (partialPreimage n x))
        (completedAdd (twoStepTransfer (defectPower n x)) (defect (defectPower n x))) = x
      rw [transfer_residual_split]
      exact ih

theorem partialPreimage_residual (n : Nat) (x : Completion) :
    completedSub x (twoStepTransfer (partialPreimage n x)) = defectPower n x := by
  have h := congrArg (fun y => completedSub y (twoStepTransfer (partialPreimage n x)))
    (partialPreimage_identity n x)
  dsimp only at h
  rw [sub_add_left_cancel] at h
  exact h.symm

theorem residual_norm_moment (n : Nat) (x : Completion) :
    B (defectPower n x) (defectPower n x) = mixedMoment x 0 (n+n) := by
  rw [defectPower_symmetric, defectPower_add]
  unfold mixedMoment
  rw [completedTime_zero]

theorem partialPreimage_distance (n : Nat) (x : Completion) :
    completedDist x (twoStepTransfer (partialPreimage n x)) = mixedMoment x 0 (n+n) := by
  unfold completedDist
  rw [partialPreimage_residual, residual_norm_moment]

def partialPreimageCauchy : Nat → seminorm.Cauchy → seminorm.Cauchy
  | 0, X => (scalarContinuous 0).mapCauchy X
  | n+1, X => addition.mapCauchy (partialPreimageCauchy n X) (defectPowerCauchy n X)

theorem partialPreimageCauchy_pin (n : Nat) (X : seminorm.Cauchy) :
    (point (partialPreimageCauchy n X)) = partialPreimage n (point X) := by
  induction n with
  | zero => exact completedSmul_zero (point X)
  | succ n ih =>
      change completedAdd (point (partialPreimageCauchy n X)) (point (defectPowerCauchy n X)) =
        completedAdd (partialPreimage n (point X)) (defectPower n (point X))
      rw [ih, ← defectPower_mk]

/-- The preimage, residual real and all original Cauchy data are computed. -/
def approximationCertificate (n : Nat) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy, Σ' r : CReal,
      QCauchy r.approx ×'
      ((point Y) = partialPreimage n (point X)) ×'
      (completedDist (point X) (twoStepTransfer (point Y)) = Quotient.mk crealSetoid r) :=
  ⟨partialPreimageCauchy n X, momentRepresentative X 0 (n+n), momentCauchy X 0 (n+n),
    partialPreimageCauchy_pin n X, by rw [partialPreimageCauchy_pin, partialPreimage_distance, moment_pin]⟩

theorem kernel_residual_fixed (n : Nat) (x : Completion)
    (hx : twoStepTransfer x = completedZero) : defectPower n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect (defectPower n x) = x
      rw [ih]
      unfold defect
      rw [hx, completedSub_zero]

theorem kernel_residual_moment (n : Nat) (x : Completion)
    (hx : twoStepTransfer x = completedZero) : mixedMoment x 0 (n+n) = B x x := by
  rw [← residual_norm_moment, kernel_residual_fixed n x hx]

end YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.defectPower_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.partialPreimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.transfer_residual_split
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.partialPreimage_identity
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.partialPreimage_residual
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.residual_norm_moment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.partialPreimage_distance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.partialPreimageCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.partialPreimageCauchy_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.approximationCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.kernel_residual_fixed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation.kernel_residual_moment
