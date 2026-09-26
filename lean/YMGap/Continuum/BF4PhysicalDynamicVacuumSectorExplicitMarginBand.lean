/-
# Explicit denominator-level physical calibration

The completed-family interface already consumes a two-sided physical-rate band.
This file factors that input one step further: a finite analytic route may
provide an explicit positive denominator for the lattice margin, an exact
margin-to-reciprocal identity, and two rational product inequalities.  The
compiler below turns those data into the existing physical-rate band on the
definitionally same completed family.

This is a named scale-law certificate, not an inhabitant of the changing-nome
SU(2) calibration.  It exposes the remaining comparison with the spacing and
does not assert a continuum limit, an OS/GNS identification, or the Clay
theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The refined named input -/

/-- An explicit positive denominator presentation of the dimensionless lattice
margin of one completed family.  The `margin_eqv_inverse` field is the exact
algebraic bridge from the actual completed rate to the presented denominator;
it prevents a later compiler from silently replacing the rate by unrelated
data. -/
structure ExplicitMarginInverseLaw
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  denominator : Nat → Q'
  denominator_pos : ∀ scale, (0 : Q') < denominator scale
  margin_eqv_inverse : ∀ scale,
    family.latticeMargin scale ≈
      Q'.divPos 1 (denominator scale) (denominator_pos scale)

/-- A two-sided scale law written before division by the explicit denominator.
The inequalities are the exact raw obligations needed by the rate-band
compiler, with no hidden asymptotic or uniformity claim. -/
structure ExplicitMarginDenominatorBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (law : ExplicitMarginInverseLaw family) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerDenominator : ∀ scale,
    (floor * family.transferSpacing.spacing scale) * law.denominator scale ≤
      (1 : Q')
  upperDenominator : ∀ scale,
    (1 : Q') ≤
      (ceiling * family.transferSpacing.spacing scale) * law.denominator scale

namespace ExplicitMarginDenominatorBand

/-! ## 2. The causal compiler -/

/-- Compile the explicit denominator inequalities into the existing physical
rate band for the same completed family. -/
def toPhysicalRateBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (band : ExplicitMarginDenominatorBand law) :
    DynamicVacuumSectorPhysicalRateBand family where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  lowerRate := fun scale => by
    have hquotient := Q'.le_divPos_of_mul_le
      (1 : Q') (law.denominator scale) (law.denominator_pos scale)
      (band.lowerDenominator scale)
    exact Q'.le_trans' _ _ _ hquotient
      (Q'.le_of_eqv
        (Q'.eqv_symm (law.margin_eqv_inverse scale)))
  upperRate := fun scale => by
    have hquotient := Q'.divPos_le_of_le_mul
      (1 : Q') (law.denominator scale) (law.denominator_pos scale)
      (band.upperDenominator scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (law.margin_eqv_inverse scale)) hquotient

/-- The refined certificate reaches the existing constructive continuum-gap
interface without changing the family or its physical spacing. -/
def toContinuumGapTheorem
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : ExplicitMarginInverseLaw family}
    (band : ExplicitMarginDenominatorBand law) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  band.toPhysicalRateBand.toContinuumGapTheorem

end ExplicitMarginDenominatorBand

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExplicitMarginBand.ExplicitMarginDenominatorBand.toContinuumGapTheorem
