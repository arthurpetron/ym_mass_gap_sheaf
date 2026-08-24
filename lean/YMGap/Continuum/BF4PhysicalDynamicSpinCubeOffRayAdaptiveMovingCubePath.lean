/-
# One observable-connected path from adaptive products to physical sampling

The adaptive transition-product family is the viable finite local producer.
The source-independent completed-family interface, moving cube RC channel,
and physical-time sampler are the downstream compilers.  This file composes
them without changing the nome, carrier, completed transfer, vector, moment,
sampling power, or decay rate at any join.

An optional normalized-strength band is also attached to the definitionally
same completed rate.  Its lower and upper margin estimates therefore govern
the very rate appearing in the sampled moving-cube autocorrelation theorem,
not a parallel scalar model.

No adaptive transition-product family, strength band, RC cutoff limit,
uniform observable normalization, projective measure, OS reconstruction,
continuum Yang--Mills theory, or Clay conclusion is inhabited here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.RCStrictPositivity

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-! ## 1. Direct composition of the actual producer and channel -/

/-- The exact moving-centered cube channel on the completed family produced
by this adaptive transition-product family. -/
def toMovingCubeRCChannel
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) :
    DynamicVacuumSectorSameObjectRCChannel family.toCompletedFamily :=
  centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily

/-- The canonical physical-time power selected from the same family's
spacing-to-zero data. -/
def movingCubeLatticeSteps
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) : Nat :=
  centralPhysicalDynamicRCLatticeSteps family.toCompletedFamily scale time

/-- The literal sampled moving-cube connected autocorrelation. -/
def movingCubeSampledConnectedAutocorrelation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) : CReal.RC :=
  sampledConnectedAutocorrelation (toMovingCubeRCChannel family) scale time

/-- The literal squared sampled moving-cube connected autocorrelation. -/
def movingCubeSampledConnectedAutocorrelationSq
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) : CReal.RC :=
  sampledConnectedAutocorrelationSq (toMovingCubeRCChannel family) scale time

/-- The sampled moving-cube moment obeys the contraction rate of the actual
completed transfer constructed from this same adaptive producer. -/
theorem movingCubeSampledConnectedAutocorrelationSq_decay
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) :
    CReal.RCle
      (movingCubeSampledConnectedAutocorrelationSq family scale time)
      (CReal.RCmul
        (CReal.RCscale
          (((((family.toCompletedFamily.completedGap scale).rate *
              (family.toCompletedFamily.completedGap scale).rate)) ^
            (movingCubeLatticeSteps family scale time)))
          ((toMovingCubeRCChannel family).normSq scale))
        ((toMovingCubeRCChannel family).normSq scale)) :=
  sampledConnectedAutocorrelationSq_decay
    (toMovingCubeRCChannel family) scale time

/-- The same sampled moment is exactly the global adaptive-transfer matrix
coefficient of the same moving cube vector. -/
theorem movingCubeSampledConnectedAutocorrelation_eq_global
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale time : Nat) :
    movingCubeSampledConnectedAutocorrelation family scale time =
      centralPhysicalCutoffCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (family.nome_pos scale) (family.nome_lt_one scale) 0
          (movingCubeLatticeSteps family scale time)
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            ((toMovingCubeRCChannel family).vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((toMovingCubeRCChannel family).vectorAt scale).1) :=
  sampledConnectedAutocorrelation_eq_global
    (toMovingCubeRCChannel family) scale time

/-- The producer-connected moving cube channel is non-vacuous at zero time
at every finite physical scale. -/
theorem movingCubeSampledConnectedAutocorrelation_zero_isPositive
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :
    RCIsPositive
      (movingCubeSampledConnectedAutocorrelation family scale 0) :=
  sampledConnectedAutocorrelation_zero_isPositive
    (toMovingCubeRCChannel family) scale

/-! ## 2. The optional strength band controls that identical rate -/

/-- A supplied normalized-strength band bounds the lattice margin of the
same completed rate appearing in the sampled correlation theorem. -/
theorem movingCube_completedRate_physicalBand
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (band : family.StrengthBand)
    (scale : Nat) :
    (band.toPhysicalRateBand.floor *
        family.transferSpacing.spacing scale ≤
      family.toCompletedFamily.latticeMargin scale) /\
    (family.toCompletedFamily.latticeMargin scale ≤
      band.toPhysicalRateBand.ceiling *
        family.transferSpacing.spacing scale) :=
  ⟨band.toPhysicalRateBand.lowerRate scale,
    band.toPhysicalRateBand.upperRate scale⟩

/-- The same two-sided band gives a positive physical gap floor and finite
ceiling for the exact rate in the moving-cube decay theorem. -/
theorem movingCube_physicalGap_twoSided
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (band : family.StrengthBand)
    (scale : Nat) :
    band.toPhysicalRateBand.floor ≤
        family.toCompletedFamily.physicalGap scale /\
      family.toCompletedFamily.physicalGap scale ≤
        band.toPhysicalRateBand.ceiling :=
  ⟨band.toPhysicalRateBand.floor_le_physicalGap scale,
    band.toPhysicalRateBand.physicalGap_le_ceiling scale⟩

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toMovingCubeRCChannel
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeSampledConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeSampledConnectedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeSampledConnectedAutocorrelation_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCube_physicalGap_twoSided
