/-
# Computed ORIGINAL transfer residual decay for every dense presentation

Let D=I-T2, f be an original embedded presentation, and C its existing
square cap. The new original test estimate bounds B(f,D^n f)^2 by
C*B(T1 D^n f,D^n f). Original Cauchy--Schwarz makes that last pairing
small using the already quantified geometric-T1 residual energy.
Finally ||D^n f||^2=m_f(0,2n)<=m_f(0,n)=B(f,D^n f).

Two applications of the existing rational smallTolerance give the degree
as data, without square roots, division by C, an inverse, or a supplied
density hypothesis. The bound holds at every larger degree. Its concrete
consumer is the OLD partialPreimageCauchy on the SAME original completion.

SU(2), nome 1/1024, fixed spacing. This test-dependent residual rate is
not a uniform inverse or a physical Hamiltonian mass gap. Arbitrary-state
extension and full-space time zero are downstream, not premises here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound
import YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation (Presentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy (residualDegree)
open YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicTransferTestBound (completed_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity (pairing_small small_of_square)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (smallTolerance smallTolerance_pos smallTolerance_budget)
open YMGap.Continuum.ScaledGNSCompletionEstimates (mul_mono_left)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

/-- Source cap and requested squared error determine both rational tolerances. -/
def responseTolerance (f : Presentation) (epsilon : Q') : Q' :=
  smallTolerance (diagonalCeiling f) (diagonalCeiling_nonnegative f)
    (smallTolerance (diagonalCeiling f) (diagonalCeiling_nonnegative f) epsilon)

theorem responseTolerance_positive (f : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < responseTolerance f epsilon :=
  smallTolerance_pos _ _ (smallTolerance_pos _ _ he)

/-- A computed degree, not a successful-search assumption or a chosen inverse. -/
def denseDegree (f : Presentation) (epsilon : Q') : Nat :=
  residualDegree (seminorm.constant f) (responseTolerance f epsilon)

theorem response_norm_small (f : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : denseDegree f epsilon ≤ n) :
    RCle (B (completedTime 1 (defectPower n (embedPresentation f)))
      (completedTime 1 (defectPower n (embedPresentation f)))) (rat (responseTolerance f epsilon)) := by
  rw [time_defectPower, residual_norm_moment]
  exact RCle_trans (moment_defect_antitone _ 0 (show
    denseDegree f epsilon + denseDegree f epsilon ≤ n+n by omega))
    (oneStep_residual_small (seminorm.constant f) (responseTolerance f epsilon)
      (responseTolerance_positive f epsilon he))

private theorem defect_norm_cap (f : Presentation) (n : Nat) :
    RCle (B (defectPower n (embedPresentation f)) (defectPower n (embedPresentation f)))
      (rat (diagonalCeiling f)) := by
  rw [residual_norm_moment]
  have h := moment_defect_antitone (embedPresentation f) 0 (Nat.zero_le (n+n))
  rw [mixedMoment_zero, completedInner_embedPresentation] at h
  exact RCle_trans h (diagonal_le_ceiling f)

/-- Actual squared error at EVERY degree above the computed threshold. -/
theorem dense_residual_small (f : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : denseDegree f epsilon ≤ n) :
    RCle (mixedMoment (embedPresentation f) 0 (n+n)) (rat epsilon) := by
  let C := diagonalCeiling f
  let hC := diagonalCeiling_nonnegative f
  let delta := smallTolerance C hC epsilon
  have hd : (0 : Q') < delta := smallTolerance_pos C hC he
  let y := defectPower n (embedPresentation f)
  have ha : RCle (B (completedTime 1 y) y) (rat delta) :=
    (pairing_small (completedTime 1 y) y C hC delta hd
      (response_norm_small f epsilon he n hn) (defect_norm_cap f n)).1
  have hCrat : RCnonneg (rat C) := leEv_ofQ'_of_approx_ge (fun _ => hC)
  have hbudget : RCle (RCmul (rat C) (rat delta)) (rat (HalfPow.half * (epsilon*epsilon))) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) (smallTolerance_budget C hC he))
  have hs := (small_of_square (B (embedPresentation f) y) epsilon he
    (RCle_trans (completed_bound y f) (RCle_trans (mul_mono_left hCrat ha) hbudget))).1
  have hr := moment_defect_antitone (embedPresentation f) 0 (Nat.le_add_right n n)
  simp only [mixedMoment, Nat.zero_add, completedTime_zero] at hr
  simpa only [mixedMoment, Nat.zero_add, completedTime_zero] using (RCle_trans hr hs)

/-- The old finite sum now has a proved sufficient degree on each dense test. -/
def densePreimage (f : Presentation) (epsilon : Q') : seminorm.Cauchy :=
  partialPreimageCauchy (denseDegree f epsilon) (seminorm.constant f)

theorem densePreimage_bound (f : Presentation) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist (embedPresentation f) (twoStepTransfer (point (densePreimage f epsilon))))
      (rat epsilon) := by
  rw [densePreimage, partialPreimageCauchy_pin]
  change RCle (completedDist (embedPresentation f)
    (twoStepTransfer (partialPreimage (denseDegree f epsilon) (embedPresentation f)))) (rat epsilon)
  rw [partialPreimage_distance]
  exact dense_residual_small f epsilon he _ (Nat.le_refl _)

end YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.responseTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.responseTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.denseDegree
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.response_norm_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.dense_residual_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.densePreimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay.densePreimage_bound
