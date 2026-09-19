/-
# Primitive variation compiler for the completed physical gap

The dynamic completed-family path defines

  `physicalGap = latticeMargin / transferSpacing`.

This module compiles two explicit primitive variation witnesses into the exact
same-family `SummableRationalStepVariation family.physicalGap`: one witness
for the dimensionless lattice margin and one for the positive spacing, with a
uniform positive spacing floor.  The reciprocal and product steps are the
generic constructive compilers; the final pointwise equality is only the
definition of `Q'.divPos`.

The result is a backward-facing mass-calibration interface.  It does not
construct either primitive variation stream, the physical rate band, a
continuum measure, or the Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
import YMGap.Continuum.SummableRationalReciprocalStepVariation
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.QuadraticRateErrorTailControl

local infix:50 " ≈ " => Q'.eqv
open YMGap.Continuum.SummableRationalReciprocalStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

/-! ## 1. Exact same-family variation -/

/-- Margin variation and positive-spacing variation meet at the exact
completed-family physical gap.  The positive spacing floor is the explicit
noncollapse witness needed by the reciprocal compiler. -/
def physicalGapVariationOfPrimitiveComponents
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (spacingVariation :
      SummableRationalStepVariation
        (fun scale => family.transferSpacing.spacing scale))
    (spacingFloor : Q')
    (spacingFloor_pos : (0 : Q') < spacingFloor)
    (spacingFloor_le :
      ∀ scale, spacingFloor ≤ family.transferSpacing.spacing scale) :
    SummableRationalStepVariation family.physicalGap := by
  let reciprocalSpacingVariation := reciprocal
    (fun scale => family.transferSpacing.spacing_pos scale)
    spacingVariation spacingFloor spacingFloor_pos spacingFloor_le
  let productVariation := mul marginVariation reciprocalSpacingVariation
    (fun scale => Q'.le_of_lt (family.latticeMargin_pos scale))
    (fun scale =>
      Q'.le_of_lt
        (Q'.recipPos_pos
          (family.transferSpacing.spacing scale)
          (family.transferSpacing.spacing_pos scale)))
  exact ofPointwiseEqv productVariation (fun scale => by
    change family.latticeMargin scale *
        Q'.recipPos
          (family.transferSpacing.spacing scale)
          (family.transferSpacing.spacing_pos scale) ≈
      family.physicalGap scale
    unfold DynamicVacuumSectorCompletedFamily.physicalGap
    exact Q'.eqv_refl _)

/-! ## 2. Explicit join to the exact-log backward target -/

/-- The primitive variation compiler feeds the existing exact-log Cauchy
compiler without changing the completed family, observable pin, or spacing
tail. -/
def exactLogRateCauchy_of_primitiveComponents
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (spacingVariation :
      SummableRationalStepVariation
        (fun scale => family.transferSpacing.spacing scale))
    (spacingFloor : Q')
    (spacingFloor_pos : (0 : Q') < spacingFloor)
    (spacingFloor_le :
      ∀ scale, spacingFloor ≤ family.transferSpacing.spacing scale)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  DynamicVacuumSectorObservablePin.exactLogRateCauchy
    pin band
    (physicalGapVariationOfPrimitiveComponents
      family marginVariation spacingVariation spacingFloor
      spacingFloor_pos spacingFloor_le)
    spacingTail

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.physicalGapVariationOfPrimitiveComponents
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.exactLogRateCauchy_of_primitiveComponents
