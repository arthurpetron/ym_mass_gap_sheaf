/-
# Compile raw correlation and normalization-debt limits

Reciprocal normalization moved finite-scale nondegeneracy into an explicit
scale-dependent debt.  This file decomposes the resulting cutoff-limit
obligation.  A normalized same-observable limit is constructed from:

* an explicit representative-level limit of the raw sampled moving-cube
  correlation; and
* an explicit constructive-real limit of the reciprocal-square norm debt.

The product convergence theorem then supplies the normalized representative
modulus.  The resulting continuum correlation is definitionally the product
of the debt limit and the raw same-observable correlation limit.

Neither input limit is inhabited here.  In particular, no convergence or
boundedness of the reciprocal-square or reciprocal-fourth-power debt, no
adaptive producer, projective measure, OS reconstruction, continuum
Yang--Mills theory, or Clay conclusion is proved.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

/-! ## 1. Split the normalized cutoff obligation into two exact inputs -/

/-- Constructive convergence of the reciprocal-square normalization debt.
The sequence is the actual rational debt embedded in `CReal`; no unrelated
majorant may replace it. -/
structure MovingCubeNormalizationNormDebtLimit
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 where
  limitRepresentative : CReal
  converges : CReal.ConvergesTo
    (fun scale => CReal.ofQ'
      (movingCubeNormalizationNormDebt family scale))
    limitRepresentative

/-- At every scale and physical time, the normalized sampled moment is exactly
the reciprocal-square scaling of the raw sampled moment of the same moving
cube and completed transfer. -/
theorem normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    normalizedMovingCubeSampledConnectedAutocorrelation family scale time =
      CReal.RCscale (movingCubeNormalizationNormDebt family scale)
        (sampledConnectedAutocorrelation
          (centralPhysicalDynamicMovingCubeRCChannel family) scale time) := by
  exact normalizedMovingCubeConnectedAutocorrelation_eq_scaled
    family scale (centralPhysicalDynamicRCLatticeSteps family scale time)

/-! ## 2. Product-limit compiler -/

/-- Raw same-observable cutoff convergence plus convergence of the exact
reciprocal-square debt constructs cutoff convergence of the literal normalized
sampled correlation. -/
def compileNormalizedMovingCubeScheduledRCContinuumLimit
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (debt : MovingCubeNormalizationNormDebtLimit family) :
    NormalizedMovingCubeScheduledRCContinuumLimit family where
  representative := fun time scale =>
    CReal.mul
      (CReal.ofQ' (movingCubeNormalizationNormDebt family scale))
      (raw.representative time scale)
  represents := by
    intro time scale
    rw [← CReal.RCscale_mk]
    rw [raw.represents time scale]
    exact Eq.symm
      (normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw
        family scale time)
  limitRepresentative := fun time =>
    CReal.mul debt.limitRepresentative (raw.limitRepresentative time)
  converges := by
    intro time
    exact
      YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        debt.converges (raw.converges time)

/-- The continuum output of the compiler is the quotient-real product of the
debt limit and the raw same-observable continuum correlation. -/
theorem compileNormalizedMovingCube_continuum_eq_product
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (debt : MovingCubeNormalizationNormDebtLimit family)
    (time : Nat) :
    NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (compileNormalizedMovingCubeScheduledRCContinuumLimit
          family raw debt) time =
      CReal.RCmul
        (Quotient.mk CReal.crealSetoid debt.limitRepresentative)
        (ScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          raw time) := by
  rfl

/-- The compiled normalized continuum channel is automatically nonzero at
zero time, while all analytic work remains localized in the two supplied
limit inputs. -/
theorem compileNormalizedMovingCube_continuum_zero_isPositive
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (debt : MovingCubeNormalizationNormDebtLimit family) :
    RCStrictPositivity.RCIsPositive
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (compileNormalizedMovingCubeScheduledRCContinuumLimit
          family raw debt) 0) :=
  NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive
    (compileNormalizedMovingCubeScheduledRCContinuumLimit family raw debt)

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler.normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler.compileNormalizedMovingCubeScheduledRCContinuumLimit
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler.compileNormalizedMovingCube_continuum_eq_product
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler.compileNormalizedMovingCube_continuum_zero_isPositive
