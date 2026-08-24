/-
# Raw moving-cube continuum decay without normalization debt

The normalized continuum route rescales the moving cube by the reciprocal of
a cutoff-dependent rational norm floor.  That guarantees a unit lower bound
at time zero, but creates an additional scale-variation problem for the
normalization debt.

This file records the alternative observable-connected route.  It keeps the
literal unnormalized moving-cube vector and passes its finite squared-decay
estimate through cutoff removal.  The analytic convergence tributaries are
then only

1. the raw same-object moment representatives; and
2. the exact scheduled squared-rate powers.

Nontriviality is stated separately as positivity of the zero-time limit of
that exact raw representative family.  It is a one-value certificate, not a
third sequence-convergence obligation.  The final theorem rejoins the two
limits and this certificate on the definitionally same observable.

No raw variation, zero-time nontriviality certificate, scheduled rate-power
variation, adaptive producer, projective measure, OS reconstruction,
continuum Yang--Mills theory, or Clay conclusion is inhabited here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.RCStrictPositivity

/-! ## 1. The literal raw continuum observable -/

/-- The raw moving-cube limit selected by the summable variation of the
literal sampled same-object representatives. -/
def rawMovingCubeContinuumLimitOfVariation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family) :
    ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family) :=
  raw.toScheduledRCContinuumLimit

/-- Nontriviality data for the exact raw continuum observable selected by
`raw`.  Unlike reciprocal normalization, this asks only for positivity of the
one zero-time limit that is actually used as the decay amplitude. -/
structure MovingCubeRawContinuumNontriviality
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family) : Type 1 where
  zero_isPositive :
    RCIsPositive
      (ScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (rawMovingCubeContinuumLimitOfVariation family raw) 0)

/-! ## 2. Pass the finite raw estimate to representatives -/

/-- The finite raw same-object decay theorem is exactly the eventual-order
inequality on the representatives selected by its scheduled continuum limit.
No normalization factor occurs. -/
theorem rawMovingCubeLimitRepresentativeSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (limit : ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family))
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
    sampledConnectedAutocorrelationSq_decay
      (centralPhysicalDynamicMovingCubeRCChannel family) scale time
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
      sampledConnectedAutocorrelation_zero_eq_normSq]
    simpa [sampledConnectedAutocorrelationSq,
      normalizedMovingCubeSampledRatePower] using hdecay
  exact hrc

/-! ## 3. The raw continuum decay and its causal join -/

/-- Raw-moment convergence and scheduled-power convergence pass the literal
finite same-object estimate to their exact constructive-real limits. -/
theorem rawMovingCubeContinuumRepresentativeSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (limit : ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family))
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
  exact rawMovingCubeLimitRepresentativeSq_decay
    family limit scale time

/-- The quotient-real form of the unnormalized same-observable continuum
decay.  Its amplitude is the actual zero-time raw limit, not a replacement
normalization constant. -/
theorem rawMovingCubeContinuumConnectedAutocorrelationSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (limit : ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (limit.continuumConnectedAutocorrelation time)
        (limit.continuumConnectedAutocorrelation time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (ratePower.limitRepresentative time))
          (limit.continuumConnectedAutocorrelation 0))
        (limit.continuumConnectedAutocorrelation 0)) :=
  rawMovingCubeContinuumRepresentativeSq_decay
    family limit ratePower time

/-- The smaller raw route rejoins its two convergence tributaries and the
single nontriviality certificate on one definitionally fixed observable. -/
theorem rawMovingCubeObservableConnectedContinuumPath
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (nontrivial : MovingCubeRawContinuumNontriviality family raw)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family)
    (time : Nat) :
    RCIsPositive
        ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
          0) /\
      CReal.RCle
        (CReal.RCmul
          ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
            time)
          ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
            time))
        (CReal.RCmul
          (CReal.RCmul
            (Quotient.mk CReal.crealSetoid
              (ratePower.limitRepresentative time))
            ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
              0))
          ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
            0)) :=
  ⟨nontrivial.zero_isPositive,
    rawMovingCubeContinuumConnectedAutocorrelationSq_decay
      family (rawMovingCubeContinuumLimitOfVariation family raw)
      ratePower time⟩

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.rawMovingCubeContinuumLimitOfVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.rawMovingCubeLimitRepresentativeSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.rawMovingCubeContinuumRepresentativeSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.rawMovingCubeContinuumConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.rawMovingCubeObservableConnectedContinuumPath
