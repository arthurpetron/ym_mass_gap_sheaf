/-
# Compile a uniform raw moving-cube norm floor to continuum nontriviality

The raw observable route asks only that its exact zero-time continuum limit be
strictly positive.  Finite-scale positivity does not suffice: the positive
witness may vanish along the cutoff trajectory.  A stronger but directly
finite-level sufficient input is one positive rational floor below the norm of
the same moving-cube vector at every scale.

This module performs that contraction.  The existing scheduled-channel limit
compiler passes the uniform floor through the exact representatives selected
by the raw variation.  The result is precisely
`MovingCubeRawContinuumNontriviality`, with no new limit or observable chosen.

For the adaptive producer, a transparent alias exposes the remaining scalar
frontier.  The compiler does not inhabit that uniform floor; in particular it
does not confuse the already-proved scale-dependent coordinate floors with a
cutoff-independent lower bound.

No uniform floor, raw variation, adaptive family, continuum measure, OS/GNS
semantics, continuum Yang--Mills theory, or Clay conclusion is inhabited here.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

namespace MovingCubeRawContinuumNontriviality

/-- A cutoff-independent lower norm floor for the exact moving-cube channel
passes through the raw representative limit and constructs its zero-time
nontriviality certificate. -/
def ofUniformNormFloor
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family)) :
    MovingCubeRawContinuumNontriviality family raw where
  zero_isPositive :=
    ScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive
      (rawMovingCubeContinuumLimitOfVariation family raw) uniform

end MovingCubeRawContinuumNontriviality

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- The exact cutoff-independent scalar floor sufficient to keep the adaptive
raw moving-cube observable nonzero after cutoff removal. -/
def RawMovingCubeUniformNormFloor
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  DynamicVacuumSectorUniformRCNormFloor
    (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily)

/-- The adaptive raw nontriviality certificate compiled from that one uniform
finite norm floor. -/
def rawMovingCubeContinuumNontrivialityOfUniformNormFloor
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (uniform : RawMovingCubeUniformNormFloor family) :
    RawMovingCubeContinuumNontriviality family raw :=
  MovingCubeRawContinuumNontriviality.ofUniformNormFloor uniform

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.MovingCubeRawContinuumNontriviality.ofUniformNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfUniformNormFloor
