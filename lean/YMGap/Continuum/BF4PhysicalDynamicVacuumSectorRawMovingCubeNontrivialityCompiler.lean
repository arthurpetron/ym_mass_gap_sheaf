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

It also factors the abstract floor through one sharper finite certificate: a
uniform rational ceiling on the exact reciprocal normalization scale.  The
same ceiling simultaneously supplies the raw norm floor and bounds the square
and fourth-power normalization debts.  Thus the raw and normalized routes
share one scalar obstruction instead of hiding two unrelated assumptions.

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
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel

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
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel

/-! ## 1. One finite certificate shared by the raw and normalized routes -/

/-- A cutoff-independent rational ceiling on the exact reciprocal floor used
to normalize the literal moving-cube vector.  This is stronger and more
concrete than an abstract completed-real norm floor: it refers only to the
already-constructed rational coordinate floor at each cutoff. -/
structure MovingCubeNormalizationScaleCeiling
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 where
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  scale_le : forall scale,
    movingCubeNormalizationScale family scale ≤ ceiling

namespace MovingCubeNormalizationScaleCeiling

/-- The raw rational floor recovered by reciprocating the uniform
normalization-scale ceiling. -/
def rawFloor
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family) : Q' :=
  Q'.divPos 1 bound.ceiling bound.ceiling_pos

theorem rawFloor_pos
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family) :
    (0 : Q') < bound.rawFloor := by
  unfold rawFloor
  exact Q'.divPos_pos 1 bound.ceiling bound.ceiling_pos (by decide)

/-- The reciprocal ceiling lies below the exact rational coordinate floor at
every cutoff. -/
theorem rawFloor_le_channelFloor
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family)
    (scale : Nat) :
    bound.rawFloor ≤
      (centralPhysicalDynamicMovingCubeRCChannel family).normFloor scale := by
  let channel := centralPhysicalDynamicMovingCubeRCChannel family
  let floor := channel.normFloor scale
  let normalization := movingCubeNormalizationScale family scale
  have hfloorNonneg : (0 : Q') ≤ floor :=
    Q'.le_of_lt (channel.normFloor_pos scale)
  have hnormalized : normalization * floor ≤ bound.ceiling * floor :=
    Q'.mul_le_mul_of_nonneg_right
      normalization bound.ceiling floor (bound.scale_le scale) hfloorNonneg
  have hone : (1 : Q') ≤ bound.ceiling * floor :=
    Q'.le_trans' _ (normalization * floor) _
      (Q'.ge_of_eqv
        (movingCubeNormalizationScale_mul_floor_eqv_one family scale))
      hnormalized
  unfold rawFloor
  exact Q'.divPos_le_of_le_mul 1 bound.ceiling bound.ceiling_pos
    (Q'.le_trans' _ (bound.ceiling * floor) _ hone
      (Q'.le_of_eqv (Q'.mul_comm_eqv bound.ceiling floor)))

/-- The normalization-scale ceiling constructs the raw channel's uniform
completed-real norm floor without changing its vector or observable. -/
def toUniformNormFloor
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family) :
    DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family) where
  floor := bound.rawFloor
  floor_pos := bound.rawFloor_pos
  floor_le scale := by
    refine CReal.RCle_trans ?_
      ((centralPhysicalDynamicMovingCubeRCChannel family).normFloor_le_normSq
        scale)
    rw [CReal.RCle_mk]
    exact CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ' (bound.rawFloor_le_channelFloor scale))

/-- The same scalar certificate bounds the square normalization debt. -/
theorem normDebt_le_ceiling_sq
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family)
    (scale : Nat) :
    movingCubeNormalizationNormDebt family scale ≤
      bound.ceiling * bound.ceiling := by
  unfold movingCubeNormalizationNormDebt
  exact Q'.mul_le_mul_of_nonneg
    (bound.scale_le scale) (bound.scale_le scale)
    (Q'.le_of_lt bound.ceiling_pos)
    (Q'.le_of_lt (movingCubeNormalizationScale_pos family scale))

/-- The same scalar certificate bounds the fourth-power squared-correlation
normalization debt. -/
theorem correlationSqDebt_le_ceiling_fourth
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family)
    (scale : Nat) :
    movingCubeNormalizationCorrelationSqDebt family scale ≤
      (bound.ceiling * bound.ceiling) *
        (bound.ceiling * bound.ceiling) := by
  unfold movingCubeNormalizationCorrelationSqDebt
  exact Q'.mul_le_mul_of_nonneg
    (bound.normDebt_le_ceiling_sq scale)
    (bound.normDebt_le_ceiling_sq scale)
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt bound.ceiling_pos)
      (Q'.le_of_lt bound.ceiling_pos))
    (Q'.le_of_lt (movingCubeNormalizationNormDebt_pos family scale))

end MovingCubeNormalizationScaleCeiling

/-! ## 2. Raw continuum nontriviality -/

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

/-- The adaptive raw continuum channel stays nontrivial whenever the exact
reciprocal normalization scales admit one uniform rational ceiling. -/
def rawMovingCubeContinuumNontrivialityOfNormalizationScaleCeiling
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (bound : MovingCubeNormalizationScaleCeiling family.toCompletedFamily) :
    RawMovingCubeContinuumNontriviality family raw :=
  rawMovingCubeContinuumNontrivialityOfUniformNormFloor family raw
    bound.toUniformNormFloor

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.MovingCubeRawContinuumNontriviality.ofUniformNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfUniformNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.MovingCubeNormalizationScaleCeiling.toUniformNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.MovingCubeNormalizationScaleCeiling.correlationSqDebt_le_ceiling_fourth
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfNormalizationScaleCeiling
