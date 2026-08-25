/-
# Reduce the moving-cube normalization ceiling to its asymptotic tail

The raw moving-cube route and the normalized moving-cube route share one
scalar obstruction: a uniform ceiling on the reciprocal of the exact
coordinate floor.  Asking for that ceiling at every cutoff obscures a useful
constructive fact.  Every finite prefix already has a located rational
maximum, so only the asymptotic tail requires new analytic control.

This file makes that reduction exact.  It computes the finite-prefix maximum,
glues it to one supplied tail ceiling, and recovers the existing global
`MovingCubeNormalizationScaleCeiling`.  Restricting a global ceiling to a tail
gives the converse compiler.  Thus the global and eventual formulations are
equivalent as Type-level data, up to an explicitly enlarged rational ceiling.

The resulting global certificate feeds both the raw continuum-nontriviality
compiler and the normalized reciprocal-square variation compiler without
changing the completed vector or observable.  No physical tail estimate,
dynamic adaptive family, cutoff variation, continuum carrier, Yang--Mills
theory, or Clay conclusion is inhabited here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or `noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler

set_option maxRecDepth 1000000
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
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.SummableRationalStepVariation

/-! ## 1. The finite prefix is executable -/

/-- Located maximum of the exact reciprocal normalization scales on a supplied
finite list of cutoff indices.  The empty list is seeded at zero. -/
def movingCubeNormalizationFiniteMaximum
    (family : DynamicVacuumSectorCompletedFamily 0) : List Nat -> Q'
  | [] => 0
  | scale :: rest =>
      Q'.max' (movingCubeNormalizationScale family scale)
        (movingCubeNormalizationFiniteMaximum family rest)

/-- Every listed normalization scale lies below the executable finite
maximum. -/
theorem movingCubeNormalizationScale_le_finiteMaximum
    (family : DynamicVacuumSectorCompletedFamily 0) :
    forall (items : List Nat) {scale : Nat},
      scale ∈ items ->
        movingCubeNormalizationScale family scale <=
          movingCubeNormalizationFiniteMaximum family items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, scale, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst scale
        exact Q'.le_max'_left _ _
      · exact Q'.le_trans' _ _ _
          (movingCubeNormalizationScale_le_finiteMaximum
            family tail htail)
          (Q'.le_max'_right _ _)

/-- Exact located maximum of all normalization scales with index strictly
below `start`. -/
def movingCubeNormalizationPrefixCeiling
    (family : DynamicVacuumSectorCompletedFamily 0)
    (start : Nat) : Q' :=
  movingCubeNormalizationFiniteMaximum family (List.range start)

theorem movingCubeNormalizationScale_le_prefixCeiling
    (family : DynamicVacuumSectorCompletedFamily 0)
    {scale start : Nat} (hscale : scale < start) :
    movingCubeNormalizationScale family scale <=
      movingCubeNormalizationPrefixCeiling family start := by
  exact movingCubeNormalizationScale_le_finiteMaximum
    family (List.range start) (List.mem_range.mpr hscale)

/-! ## 2. Only the asymptotic tail remains analytic -/

/-- One rational ceiling from `start` onward.  Unlike the global certificate,
this contains only the genuinely asymptotic analytic obligation; the prefix
is compiled by finite recursion above. -/
structure MovingCubeNormalizationScaleTailCeiling
    (family : DynamicVacuumSectorCompletedFamily 0)
    (start : Nat) : Type 1 where
  ceiling : Q'
  scale_le : forall scale, start <= scale ->
    movingCubeNormalizationScale family scale <= ceiling

namespace MovingCubeNormalizationScaleTailCeiling

/-- Summable two-sided variation of the reciprocal scale automatically
constructs a tail ceiling.  The canonical start asks the tail budget for
total remaining variation at most one. -/
def ofScaleVariation
    {family : DynamicVacuumSectorCompletedFamily 0}
  (variation : MovingCubeNormalizationScaleRationalVariation family) :
    MovingCubeNormalizationScaleTailCeiling family
      variation.tailCeilingStart where
  ceiling := variation.tailCeiling
  scale_le := fun _ hscale => variation.le_tailCeiling hscale

/-- The located maximum of the exact finite prefix and the supplied
asymptotic tail ceiling. -/
def globalCeiling
    {family : DynamicVacuumSectorCompletedFamily 0}
    {start : Nat}
    (tail : MovingCubeNormalizationScaleTailCeiling family start) : Q' :=
  Q'.max' (movingCubeNormalizationPrefixCeiling family start) tail.ceiling

/-- Finite-prefix/tail gluing constructs the global reciprocal-scale ceiling
consumed by both moving-cube proof routes. -/
def toGlobalCeiling
    {family : DynamicVacuumSectorCompletedFamily 0}
    {start : Nat}
    (tail : MovingCubeNormalizationScaleTailCeiling family start) :
    MovingCubeNormalizationScaleCeiling family where
  ceiling := tail.globalCeiling
  ceiling_pos := by
    have htailAtStart :
        movingCubeNormalizationScale family start <= tail.ceiling :=
      tail.scale_le start (Nat.le_refl start)
    have htailPos : (0 : Q') < tail.ceiling :=
      YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
        (movingCubeNormalizationScale_pos family start) htailAtStart
    exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      htailPos (Q'.le_max'_right _ _)
  scale_le := fun scale => by
    rcases Nat.lt_or_ge scale start with hprefix | htail
    · exact Q'.le_trans' _ _ _
        (movingCubeNormalizationScale_le_prefixCeiling family hprefix)
        (Q'.le_max'_left _ _)
    · exact Q'.le_trans' _ _ _
        (tail.scale_le scale htail)
        (Q'.le_max'_right _ _)

/-- The tail ceiling already implies a uniform raw norm floor for the same
literal moving-cube channel. -/
def toUniformNormFloor
    {family : DynamicVacuumSectorCompletedFamily 0}
    {start : Nat}
    (tail : MovingCubeNormalizationScaleTailCeiling family start) :
    DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family) :=
  tail.toGlobalCeiling.toUniformNormFloor

/-- With the normalized route's additional scale-variation input, the same
tail ceiling controls reciprocal-square normalization debt. -/
def toNormDebtRationalVariation
    {family : DynamicVacuumSectorCompletedFamily 0}
    {start : Nat}
    (tail : MovingCubeNormalizationScaleTailCeiling family start)
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation family) :
    MovingCubeNormalizationNormDebtRationalVariation family :=
  tail.toGlobalCeiling.toNormDebtRationalVariation scaleVariation

end MovingCubeNormalizationScaleTailCeiling

namespace MovingCubeNormalizationScaleCeiling

/-- Summable reciprocal-scale variation already contains the missing global
ceiling: compile its automatic tail bound and glue the finite prefix. -/
def ofScaleVariation
    {family : DynamicVacuumSectorCompletedFamily 0}
    (variation : MovingCubeNormalizationScaleRationalVariation family) :
    MovingCubeNormalizationScaleCeiling family :=
  (MovingCubeNormalizationScaleTailCeiling.ofScaleVariation
    variation).toGlobalCeiling

/-- Consequently reciprocal-scale variation alone compiles to summable
reciprocal-square debt; no independently supplied ceiling is necessary. -/
def normDebtRationalVariationOfScaleVariation
    {family : DynamicVacuumSectorCompletedFamily 0}
    (variation : MovingCubeNormalizationScaleRationalVariation family) :
    MovingCubeNormalizationNormDebtRationalVariation family :=
  (ofScaleVariation variation).toNormDebtRationalVariation variation

/-- Conversely, any global reciprocal-scale ceiling restricts to every
asymptotic tail. -/
def toTailCeiling
    {family : DynamicVacuumSectorCompletedFamily 0}
    (bound : MovingCubeNormalizationScaleCeiling family)
    (start : Nat) :
    MovingCubeNormalizationScaleTailCeiling family start where
  ceiling := bound.ceiling
  scale_le := fun scale _ => bound.scale_le scale

end MovingCubeNormalizationScaleCeiling

/-! ## 3. Direct consumers on the adaptive physical path -/

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- On the adaptive path, a tail ceiling is sufficient to keep the exact raw
moving-cube observable nonzero after cutoff removal. -/
def rawMovingCubeContinuumNontrivialityOfNormalizationScaleTailCeiling
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    {start : Nat}
    (tail : MovingCubeNormalizationScaleTailCeiling
      family.toCompletedFamily start) :
    RawMovingCubeContinuumNontriviality family raw :=
  BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfNormalizationScaleCeiling
    family raw tail.toGlobalCeiling

/-- The normalized route's reciprocal-scale variation is therefore also a
sufficient raw nontriviality producer for the exact same observable. -/
def rawMovingCubeContinuumNontrivialityOfNormalizationScaleVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (variation : MovingCubeNormalizationScaleRationalVariation
      family.toCompletedFamily) :
    RawMovingCubeContinuumNontriviality family raw :=
  rawMovingCubeContinuumNontrivialityOfNormalizationScaleTailCeiling
    family raw
      (MovingCubeNormalizationScaleTailCeiling.ofScaleVariation variation)

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.movingCubeNormalizationScale_le_prefixCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.MovingCubeNormalizationScaleTailCeiling.toGlobalCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.MovingCubeNormalizationScaleCeiling.ofScaleVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.MovingCubeNormalizationScaleCeiling.normDebtRationalVariationOfScaleVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.MovingCubeNormalizationScaleTailCeiling.toUniformNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.MovingCubeNormalizationScaleTailCeiling.toNormDebtRationalVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfNormalizationScaleTailCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfNormalizationScaleVariation
