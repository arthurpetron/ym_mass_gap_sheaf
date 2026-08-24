/-
# The dynamic rooted strength is automatically normalized

The physical-rate compiler of
`BF4PhysicalDynamicVacuumRootStrengthPhysicalBand` asks for a finite common
cap on

  strength_j = rootCapacityDelta_j * uniformSectorMassFloor_j.

That cap is not an additional analytic hypothesis.  The uniform sector-mass
floor lies below a probability mass and is therefore at most one.  Every
cofinal root-linear ratio is also at most one: its positive delta multiplied
by a cost at least one lies below the finite edge floor, while that edge floor
is normalized by an explicit fallback candidate one.

Consequently every dynamic rooted strength is at most one.  A two-sided
spacing comparison alone now constructs the previous strength band with
`cap = 1`; positivity of the upper coefficient is also forced by the positive
strength at scale zero.

No dynamic family or spacing comparison is inhabited here.  No continuum
carrier, continuum Yang--Mills measure, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction
open YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand
open YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Each concrete factor is at most one -/

/-- The constructed uniform sector-mass floor lies below one because it lies
below the full vacuum-sector probability mass already at its own anchor. -/
theorem centralPhysicalFiniteVacuumSectorUniformMassFloor_le_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    centralPhysicalFiniteVacuumSectorUniformMassFloor
        w (Q'.le_of_lt hw0) half ≤ 1 := by
  let anchor :=
    centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w half
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_le
      hw0 hw1 half (K := anchor) (Nat.le_refl anchor))
    (centralPhysicalFiniteVacuumSectorMass_le_one
      w (Q'.le_of_lt hw0) anchor half)

/-- Any cofinal root-linear ratio is at most one.  This is a consequence of
its defining comparison, not a normalization added to the record. -/
theorem cofinalVacuumRootLinearRatio_delta_le_one
    {w : Q'} {hw0 : (0 : Q') < w} {half : Nat}
    (ratio : FixedNomeCofinalVacuumRootLinearRatio hw0 half) :
    ratio.delta ≤ 1 := by
  let cost := centralPhysicalFiniteVacuumSectorRootLinearCost
    w (Q'.le_of_lt hw0) ratio.start half
  have hcostOne : (1 : Q') ≤ cost := by
    unfold cost centralPhysicalFiniteVacuumSectorRootLinearCost
    exact Q'.add_le_self_of_nonneg 1 _
      (centralPhysicalFiniteVacuumSectorRootLinearMoment_nonnegative
        w (Q'.le_of_lt hw0) ratio.start half)
  have hscaled : ratio.delta * 1 ≤ ratio.delta * cost :=
    Q'.mul_le_mul_of_nonneg_left 1 cost ratio.delta hcostOne
      (Q'.le_of_lt ratio.delta_pos)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv ratio.delta)))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (ratio.ratio_bound ratio.start (Nat.le_refl ratio.start))
        (centralPhysicalFiniteVacuumSectorEdgeFloor_le_one
          w (Q'.le_of_lt hw0) ratio.start half)))

/-! ## 2. The dynamic rooted strength has the canonical cap one -/

/-- The exact rooted strength of every member of a dynamic completed family
is bounded by one. -/
theorem dynamicVacuumRootStrength_le_one {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) :
    dynamicVacuumRootStrength family scale ≤ 1 := by
  let delta := (family.linearRatio scale).delta
  let massFloor := centralPhysicalFiniteVacuumSectorUniformMassFloor
    (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) half
  have hdelta0 : (0 : Q') ≤ delta :=
    Q'.le_of_lt (family.linearRatio scale).delta_pos
  have hdelta1 : delta ≤ 1 :=
    cofinalVacuumRootLinearRatio_delta_le_one (family.linearRatio scale)
  have hmass0 : (0 : Q') ≤ massFloor :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
        (family.nome scale)
        (Q'.le_of_lt (family.nome_pos scale)) half)
  have hmass1 : massFloor ≤ 1 :=
    centralPhysicalFiniteVacuumSectorUniformMassFloor_le_one
      (family.nome_pos scale) (family.nome_lt_one scale) half
  have hfirst : delta * massFloor ≤ 1 * massFloor :=
    Q'.mul_le_mul_of_nonneg_right delta 1 massFloor hdelta1 hmass0
  have hsecond : 1 * massFloor ≤ 1 * 1 :=
    Q'.mul_le_mul_of_nonneg_left massFloor 1 1 hmass1
      (by decide : (0 : Q') ≤ 1)
  unfold dynamicVacuumRootStrength cutoffTwoDirichletGluingStrength
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

/-! ## 3. Only the two-sided spacing comparison remains -/

/-- The genuinely analytic physical scaling input after automatic
normalization.  The upper coefficient need not carry a separate positivity
field: positivity follows from the scale-zero estimate. -/
structure FixedHalfDynamicVacuumRootStrengthScaling
    {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half) : Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  lowerScale : ∀ scale,
    lower * family.transferSpacing.spacing scale ≤
      dynamicVacuumRootStrength family scale
  upperScale : ∀ scale,
    dynamicVacuumRootStrength family scale ≤
      upper * family.transferSpacing.spacing scale

namespace FixedHalfDynamicVacuumRootStrengthScaling

/-- The upper multiplier is forced positive by the positive strength and
positive transfer spacing at scale zero. -/
theorem upper_pos {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (scaling : FixedHalfDynamicVacuumRootStrengthScaling family) :
    (0 : Q') < scaling.upper := by
  have hquotientPos :
      (0 : Q') < Q'.divPos
        (dynamicVacuumRootStrength family 0)
        (family.transferSpacing.spacing 0)
        (family.transferSpacing.spacing_pos 0) :=
    Q'.divPos_pos _ _ (family.transferSpacing.spacing_pos 0)
      (dynamicVacuumRootStrength_pos family 0)
  have hquotientLe :
      Q'.divPos
          (dynamicVacuumRootStrength family 0)
          (family.transferSpacing.spacing 0)
          (family.transferSpacing.spacing_pos 0) ≤
        scaling.upper :=
    Q'.divPos_le_of_le_mul _ _
      (family.transferSpacing.spacing_pos 0)
      (scaling.upperScale 0)
  exact Q'.pos_of_lt_of_le hquotientPos hquotientLe

/-- The canonical cap `1` turns a two-sided strength/spacing comparison into
the full strength-band record. -/
def toStrengthBand {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (scaling : FixedHalfDynamicVacuumRootStrengthScaling family) :
    FixedHalfDynamicVacuumRootStrengthBand family where
  lower := scaling.lower
  lower_pos := scaling.lower_pos
  upper := scaling.upper
  upper_pos := scaling.upper_pos
  cap := 1
  cap_nonnegative := by decide
  lowerScale := scaling.lowerScale
  upperScale := scaling.upperScale
  strengthCap := dynamicVacuumRootStrength_le_one family

/-- The normalized scaling input reaches the same-object physical-rate band. -/
def toPhysicalRateBand {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (scaling : FixedHalfDynamicVacuumRootStrengthScaling family) :
    FixedHalfDynamicVacuumRootPhysicalRateBand family :=
  scaling.toStrengthBand.toPhysicalRateBand

/-- The normalized scaling input reaches the sharp continuum-gap interface
without a separate cap or upper-positivity hypothesis. -/
def toContinuumGapTheorem {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (scaling : FixedHalfDynamicVacuumRootStrengthScaling family) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  scaling.toStrengthBand.toContinuumGapTheorem

end FixedHalfDynamicVacuumRootStrengthScaling

end YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.centralPhysicalFiniteVacuumSectorUniformMassFloor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.cofinalVacuumRootLinearRatio_delta_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.dynamicVacuumRootStrength_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.FixedHalfDynamicVacuumRootStrengthScaling.upper_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.FixedHalfDynamicVacuumRootStrengthScaling.toStrengthBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.FixedHalfDynamicVacuumRootStrengthScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthNormalization.FixedHalfDynamicVacuumRootStrengthScaling.toContinuumGapTheorem
