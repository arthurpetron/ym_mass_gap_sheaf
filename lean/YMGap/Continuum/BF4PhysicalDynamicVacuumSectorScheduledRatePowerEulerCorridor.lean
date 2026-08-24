/-
# Euler corridor for the actual scheduled squared transfer rate

The normalized moving-cube decay theorem contains the literal rational stream

    ((q_j * q_j) ^ floor(t / a_j)).

`RationalEulerPowerSandwich` supplies a finite exponential corridor for any
positive subunit rational base.  This module specializes that theorem without
changing the completed family, rate, or sampling schedule.  It also proves
that the adaptive transition-product producer supplies strict positivity of
its completed rate definitionally: the rate is the positive reciprocal of
`1 + strength`.

For the squared rate `r_j = q_j^2`, the resulting exponents are

    ((1-r_j)/r_j) * floor(t/a_j)   and
    (1-r_j) * floor(t/a_j).

Both still need a cross-scale convergence proof to a common physical
exponent.  This module does not inhabit a variation certificate, identify a
continuum exponential, construct a projective measure or OS Hilbert space, or
prove continuum Yang--Mills or the Clay mass gap.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
import YMGap.Continuum.RationalEulerPowerSandwich

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.RationalEulerPowerSandwich

/-! ## 1. The squared completed rate -/

/-- The exact squared rate occurring in the normalized moving-cube estimate. -/
def completedSquaredRate
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) : Q' :=
  (family.completedGap scale).rate *
    (family.completedGap scale).rate

/-- Strict positivity of the squared rate needs only strict positivity of the
actual completed rate. -/
theorem completedSquaredRate_pos
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale, (0 : Q') < (family.completedGap scale).rate)
    (scale : Nat) :
    (0 : Q') < completedSquaredRate family scale :=
  Q'.mul_pos (rate_pos scale) (rate_pos scale)

/-- The squared completed rate is at most one. -/
theorem completedSquaredRate_le_one
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    completedSquaredRate family scale <= (1 : Q') := by
  let rate := (family.completedGap scale).rate
  have hrate0 : (0 : Q') <= rate :=
    (family.completedGap scale).rate_nonnegative
  have hrate1 : rate <= (1 : Q') :=
    Q'.le_of_lt (family.completedGap scale).rate_lt_one
  have hscaled : rate * rate <= rate * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left rate 1 rate hrate1 hrate0
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv rate)) hrate1)

/-! ## 2. The two scheduled Euler exponents -/

/-- A positive rational lies strictly below one after subtraction from one. -/
theorem one_sub_lt_one_of_pos {q : Q'} (hq0 : (0 : Q') < q) :
    (1 : Q') + -q < (1 : Q') := by
  show ((1 : Q') + -q).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -q).den : Int)
  have hnum : (0 : Int) < q.num := Q'.num_pos_of_pos hq0
  change
    (((1 : Int) * (q.den : Int) + (-q.num) * (1 : Int)) * (1 : Int)) <
      ((1 : Int) * (((1 : Nat) * q.den : Nat) : Int))
  push_cast
  omega

/-- The upper Euler exponent `(1-q_j^2) floor(t/a_j)`. -/
def scheduledSquaredRateUpperExponent
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) : Q' :=
  ((1 : Q') + -completedSquaredRate family scale) *
    Q'.ofNat (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- The odds-corrected lower Euler exponent
`((1-q_j^2)/q_j^2) floor(t/a_j)`. -/
def scheduledSquaredRateLowerExponent
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale, (0 : Q') < (family.completedGap scale).rate)
    (scale time : Nat) : Q' :=
  eulerOdds
      ((1 : Q') + -completedSquaredRate family scale)
      (one_sub_lt_one_of_pos
        (completedSquaredRate_pos family rate_pos scale)) *
    Q'.ofNat (centralPhysicalDynamicRCLatticeSteps family scale time)

theorem scheduledSquaredRateUpperExponent_nonnegative
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    (0 : Q') <= scheduledSquaredRateUpperExponent family scale time :=
  Q'.mul_nonneg _ _
    (Q'.sub_nonneg_of_le (completedSquaredRate_le_one family scale))
    (ofNat_nonneg _)

theorem scheduledSquaredRateLowerExponent_nonnegative
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale, (0 : Q') < (family.completedGap scale).rate)
    (scale time : Nat) :
    (0 : Q') <=
      scheduledSquaredRateLowerExponent family rate_pos scale time :=
  Q'.mul_nonneg _ _
    (eulerOdds_nonnegative
      (Q'.sub_nonneg_of_le (completedSquaredRate_le_one family scale))
      (one_sub_lt_one_of_pos
        (completedSquaredRate_pos family rate_pos scale)))
    (ofNat_nonneg _)

/-! ## 3. The literal scheduled-power corridor -/

/-- At every finite scale and physical time, the exact rational rate factor
used by the normalized same-object decay theorem lies between the two
constructive exponentials above. -/
theorem normalizedMovingCubeSampledRatePower_euler_sandwich
    (family : DynamicVacuumSectorCompletedFamily 0)
    (rate_pos : forall scale, (0 : Q') < (family.completedGap scale).rate)
    (scale time : Nat) :
    CReal.leEv
        (ExpNeg.expNeg
          (scheduledSquaredRateLowerExponent family rate_pos scale time)
          (scheduledSquaredRateLowerExponent_nonnegative
            family rate_pos scale time))
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower family scale time))
      /\
    CReal.leEv
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower family scale time))
        (ExpNeg.expNeg
          (scheduledSquaredRateUpperExponent family scale time)
          (scheduledSquaredRateUpperExponent_nonnegative
            family scale time)) := by
  have hsandwich := rationalRatePower_sandwich
    (completedSquaredRate_pos family rate_pos scale)
    (completedSquaredRate_le_one family scale)
    (centralPhysicalDynamicRCLatticeSteps family scale time)
  simpa [completedSquaredRate, scheduledSquaredRateLowerExponent,
    scheduledSquaredRateUpperExponent,
    normalizedMovingCubeSampledRatePower] using hsandwich

/-! ## 4. The adaptive producer supplies rate positivity -/

namespace DynamicSpinCubeOffRayResidualCoercivityFamily

/-- The completed rate produced from residual coercivity is strictly positive,
because it is a positive rational reciprocal with numerator one. -/
theorem completedRate_pos
    (family : DynamicSpinCubeOffRayResidualCoercivityFamily)
    (scale : Nat) :
    (0 : Q') < (family.toCompletedFamily.completedGap scale).rate := by
  change (0 : Q') < (family.completedGapAt scale).rate
  rw [family.completedGapAt_rate_eq scale]
  unfold cutoffTwoDirichletGluingRate
  exact Q'.divPos_pos _ _
    (cutoffTwoDirichletGluingDenominator_pos
      (FixedNomeCofinalSpinCubeOffRayResidualCoercivity.sharedFloor_pos
        (family.residualCoercivity scale))
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
        (family.nome scale)
        (Q'.le_of_lt (family.nome_pos scale)) 0))
    (by decide)

end DynamicSpinCubeOffRayResidualCoercivityFamily

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- The adaptive transition-product family inherits strict rate positivity
through its lossless residual-coercivity projection. -/
theorem completedRate_pos
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :
    (0 : Q') < (family.toCompletedFamily.completedGap scale).rate :=
  BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayResidualCoercivityFamily.completedRate_pos
    family.toResidualCoercivityFamily scale

/-- The finite scheduled Euler corridor specialized all the way to one
adaptive transition-product producer. -/
theorem normalizedMovingCubeSampledRatePower_euler_sandwich
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) :
    CReal.leEv
        (ExpNeg.expNeg
          (scheduledSquaredRateLowerExponent family.toCompletedFamily
            (completedRate_pos family) scale time)
          (scheduledSquaredRateLowerExponent_nonnegative
            family.toCompletedFamily (completedRate_pos family) scale time))
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower
            family.toCompletedFamily scale time))
      /\
    CReal.leEv
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower
            family.toCompletedFamily scale time))
        (ExpNeg.expNeg
          (scheduledSquaredRateUpperExponent
            family.toCompletedFamily scale time)
          (scheduledSquaredRateUpperExponent_nonnegative
            family.toCompletedFamily scale time)) :=
  BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.normalizedMovingCubeSampledRatePower_euler_sandwich
    family.toCompletedFamily (completedRate_pos family) scale time

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.completedSquaredRate_pos
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.completedSquaredRate_le_one
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.normalizedMovingCubeSampledRatePower_euler_sandwich
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayResidualCoercivityFamily.completedRate_pos
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
#print axioms YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledRatePower_euler_sandwich
