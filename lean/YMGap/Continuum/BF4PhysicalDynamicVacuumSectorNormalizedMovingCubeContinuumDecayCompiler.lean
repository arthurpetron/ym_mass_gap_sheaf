/-
# Pass the normalized moving-cube decay estimate through cutoff removal

The normalized moving-cube cutoff limit already absorbs the reciprocal-square
observable rescaling into the same representative sequence.  Therefore the
finite squared-decay estimate can pass to the continuum once one additional
analytic input is supplied: constructive convergence of the exact scheduled
rate-power sequence

    ((q_j * q_j) ^ floor(t / a_j)).

This file proves that passage directly at the representative level and then
descends it to `RC`.  No fourth-power normalization-debt limit is separately
postulated; its finite algebra has already been incorporated into the actual
normalized matrix coefficient and norm.

No scheduled rate-power limit, normalized correlation limit, adaptive
producer, identification with a physical exponential, projective measure, OS
reconstruction, continuum Yang--Mills theory, or Clay conclusion is inhabited
here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

/-! ## 1. The exact scheduled rate-power limit input -/

/-- The exact rational rate factor occurring in the proved normalized squared
correlation estimate at one scale and physical time. -/
def normalizedMovingCubeSampledRatePower
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) : Q' :=
  (((family.completedGap scale).rate *
      (family.completedGap scale).rate) ^
    (centralPhysicalDynamicRCLatticeSteps family scale time))

/-- Explicit constructive convergence of the exact scheduled rate factors.
Identifying the limit with a physical exponential is a later theorem, not a
field hidden in this interface. -/
structure NormalizedMovingCubeSampledRatePowerLimit
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 where
  limitRepresentative : Nat -> CReal
  converges : forall time,
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (normalizedMovingCubeSampledRatePower family scale time))
      (limitRepresentative time)

/-! ## 2. Termwise representative decay -/

/-- The finite `RC` decay theorem is exactly the eventual-order inequality on
the representatives selected by the same normalized cutoff-limit record. -/
theorem normalizedMovingCubeLimitRepresentativeSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (limit : NormalizedMovingCubeScheduledRCContinuumLimit family)
    (scale time : Nat) :
    CReal.leEv
      (CReal.mul
        (limit.representative time scale)
        (limit.representative time scale))
      (CReal.mul
        (CReal.mul
          (CReal.ofQ'
            (normalizedMovingCubeSampledRatePower family scale time))
          (limit.representative 0 scale))
        (limit.representative 0 scale)) := by
  have hdecay :=
    normalizedMovingCubeSampledConnectedAutocorrelationSq_decay
      family scale time
  have hrc : CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.mul
          (limit.representative time scale)
          (limit.representative time scale)))
      (Quotient.mk CReal.crealSetoid
        (CReal.mul
          (CReal.mul
            (CReal.ofQ'
              (normalizedMovingCubeSampledRatePower family scale time))
            (limit.representative 0 scale))
          (limit.representative 0 scale))) := by
    rw [← CReal.RCmul_mk, ← CReal.RCmul_mk, ← CReal.RCscale_mk]
    rw [limit.represents time scale, limit.represents 0 scale,
      normalizedMovingCubeSampledConnectedAutocorrelation_zero_eq_normSq]
    simpa [normalizedMovingCubeSampledConnectedAutocorrelationSq,
      normalizedMovingCubeSampledRatePower] using hdecay
  exact hrc

/-! ## 3. Continuum decay for the same observable -/

/-- The normalized continuum representative satisfies the limit of the exact
finite scheduled decay bound. -/
theorem normalizedMovingCubeContinuumRepresentativeSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (limit : NormalizedMovingCubeScheduledRCContinuumLimit family)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family)
    (time : Nat) :
    CReal.leEv
      (CReal.mul
        (limit.limitRepresentative time)
        (limit.limitRepresentative time))
      (CReal.mul
        (CReal.mul
          (ratePower.limitRepresentative time)
          (limit.limitRepresentative 0))
        (limit.limitRepresentative 0)) := by
  have hleft : CReal.ConvergesTo
      (fun scale => CReal.mul
        (limit.representative time scale)
        (limit.representative time scale))
      (CReal.mul
        (limit.limitRepresentative time)
        (limit.limitRepresentative time)) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (limit.converges time) (limit.converges time)
  have hscaled : CReal.ConvergesTo
      (fun scale => CReal.mul
        (CReal.ofQ' (normalizedMovingCubeSampledRatePower family scale time))
        (limit.representative 0 scale))
      (CReal.mul
        (ratePower.limitRepresentative time)
        (limit.limitRepresentative 0)) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (ratePower.converges time) (limit.converges 0)
  have hright : CReal.ConvergesTo
      (fun scale => CReal.mul
        (CReal.mul
          (CReal.ofQ' (normalizedMovingCubeSampledRatePower family scale time))
          (limit.representative 0 scale))
        (limit.representative 0 scale))
      (CReal.mul
        (CReal.mul
          (ratePower.limitRepresentative time)
          (limit.limitRepresentative 0))
        (limit.limitRepresentative 0)) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      hscaled (limit.converges 0)
  apply CReal.leEv_of_convergesTo_le hleft hright
  intro scale
  exact normalizedMovingCubeLimitRepresentativeSq_decay
    family limit scale time

/-- The quotient-real version of the same continuum squared-decay theorem. -/
theorem normalizedMovingCubeContinuumConnectedAutocorrelationSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (limit : NormalizedMovingCubeScheduledRCContinuumLimit family)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          limit time)
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          limit time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (ratePower.limitRepresentative time))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            limit 0))
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          limit 0)) := by
  exact normalizedMovingCubeContinuumRepresentativeSq_decay
    family limit ratePower time

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler.normalizedMovingCubeLimitRepresentativeSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler.normalizedMovingCubeContinuumRepresentativeSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler.normalizedMovingCubeContinuumConnectedAutocorrelationSq_decay
