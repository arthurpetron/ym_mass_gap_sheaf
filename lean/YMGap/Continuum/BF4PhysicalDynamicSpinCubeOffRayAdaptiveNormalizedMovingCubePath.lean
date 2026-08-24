/-
# Adaptive producer to the reciprocal-normalized moving-cube continuum frontier

This file specializes the explicit normalized moving-cube construction to the
completed family produced by one supplied dynamic adaptive off-ray transition-
product family.  It preserves one causal lineage: producer, completed
transfer, moving-cube vector, reciprocal rescaling, physical-time sampling,
connected matrix coefficient, completed rate, and optional physical strength
band.

The normalization is not free.  The reciprocal-square norm debt and
reciprocal-fourth-power squared-correlation debt are retained as explicit
functions of the same producer.  A continuum value is obtained only from an
explicit representative-level cutoff limit of this normalized channel.

No adaptive transition-product family, strength band, normalized cutoff-limit
inhabitant, bound on the normalization debts, projective measure, OS
reconstruction, continuum Yang--Mills theory, or Clay conclusion is produced
here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-! ## 1. The actual normalized producer-connected observable -/

/-- The reciprocal scale of the moving cube belonging to this exact adaptive
producer. -/
def normalizedMovingCubeScale
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) : Q' :=
  movingCubeNormalizationScale family.toCompletedFamily scale

/-- The reciprocal-square debt carried by the normalized norm. -/
def normalizedMovingCubeNormDebt
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) : Q' :=
  movingCubeNormalizationNormDebt family.toCompletedFamily scale

/-- The reciprocal-fourth-power debt carried while transporting a squared
correlation estimate. -/
def normalizedMovingCubeCorrelationSqDebt
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) : Q' :=
  movingCubeNormalizationCorrelationSqDebt family.toCompletedFamily scale

/-- The literal normalized global completed vacuum-complement vector selected
from this producer. -/
def normalizedMovingCubeVectorAt
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :=
  BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeGlobalVectorAt
    family.toCompletedFamily scale

/-- Its literal completed norm square. -/
def normalizedMovingCubeNormSq
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) : CReal.RC :=
  BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeNormSq
    family.toCompletedFamily scale

/-- Its literal connected matrix coefficient sampled at fixed physical time. -/
def normalizedMovingCubeSampledConnectedAutocorrelation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) : CReal.RC :=
  BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeSampledConnectedAutocorrelation
    family.toCompletedFamily scale time

/-- The square of that same sampled matrix coefficient. -/
def normalizedMovingCubeSampledConnectedAutocorrelationSq
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) : CReal.RC :=
  BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeSampledConnectedAutocorrelationSq
    family.toCompletedFamily scale time

/-- The normalized sampled channel is exactly the reciprocal-square rescaling
of the raw sampled moving-cube channel produced by the preceding compiler. -/
theorem normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) :
    normalizedMovingCubeSampledConnectedAutocorrelation family scale time =
      CReal.RCscale (normalizedMovingCubeNormDebt family scale)
        (movingCubeSampledConnectedAutocorrelation family scale time) := by
  exact normalizedMovingCubeConnectedAutocorrelation_eq_scaled
    family.toCompletedFamily scale (movingCubeLatticeSteps family scale time)

/-- The normalized correlation remains the literal global matrix coefficient
of the actual normalized vector under the completed transfer produced by the
same adaptive family. -/
theorem normalizedMovingCubeSampledConnectedAutocorrelation_eq_global
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) :
    normalizedMovingCubeSampledConnectedAutocorrelation family scale time =
      centralPhysicalCutoffCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (family.nome_pos scale) (family.nome_lt_one scale) 0
          (movingCubeLatticeSteps family scale time)
          (normalizedMovingCubeVectorAt family scale).1)
        (normalizedMovingCubeVectorAt family scale).1 := by
  rfl

/-! ## 2. The same completed and physical rates -/

/-- The producer-connected normalized observable obeys the completed-rate
decay estimate at the exact lattice power selected for physical time. -/
theorem normalizedMovingCubeSampledConnectedAutocorrelationSq_decay
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) :
    CReal.RCle
      (normalizedMovingCubeSampledConnectedAutocorrelationSq
        family scale time)
      (CReal.RCmul
        (CReal.RCscale
          (((((family.toCompletedFamily.completedGap scale).rate *
              (family.toCompletedFamily.completedGap scale).rate)) ^
            (movingCubeLatticeSteps family scale time)))
          (normalizedMovingCubeNormSq family scale))
        (normalizedMovingCubeNormSq family scale)) := by
  exact BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeSampledConnectedAutocorrelationSq_decay
    family.toCompletedFamily scale time

/-- The zero-time norm floor of the actual normalized producer-connected
observable is uniformly one. -/
theorem one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (normalizedMovingCubeSampledConnectedAutocorrelation family scale 0) := by
  exact BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero
    family.toCompletedFamily scale

/-- A supplied strength band governs the definitionally identical completed
rate in the normalized sampled decay theorem. -/
theorem normalizedMovingCube_physicalGap_twoSided
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (band : family.StrengthBand)
    (scale : Nat) :
    band.toPhysicalRateBand.floor ≤
        family.toCompletedFamily.physicalGap scale /\
      family.toCompletedFamily.physicalGap scale ≤
        band.toPhysicalRateBand.ceiling :=
  movingCube_physicalGap_twoSided band scale

/-! ## 3. The exact normalized cutoff-limit frontier -/

/-- Cutoff convergence data for the same normalized observable compiled from
this producer.  Inhabiting it must control the explicit normalization debts. -/
def NormalizedMovingCubeContinuumLimit
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  NormalizedMovingCubeScheduledRCContinuumLimit family.toCompletedFamily

/-- The continuum connected correlation selected by that same-channel limit. -/
def normalizedMovingCubeContinuumConnectedAutocorrelation
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (limit : NormalizedMovingCubeContinuumLimit family)
    (time : Nat) : CReal.RC :=
  NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
    limit time

/-- Any cutoff limit of the exact normalized producer-connected channel is
strictly positive at time zero. -/
theorem normalizedMovingCubeContinuumConnectedAutocorrelation_zero_isPositive
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (limit : NormalizedMovingCubeContinuumLimit family) :
    RCStrictPositivity.RCIsPositive
      (normalizedMovingCubeContinuumConnectedAutocorrelation limit 0) :=
  NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive
    limit

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledConnectedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCube_physicalGap_twoSided
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation_zero_isPositive
