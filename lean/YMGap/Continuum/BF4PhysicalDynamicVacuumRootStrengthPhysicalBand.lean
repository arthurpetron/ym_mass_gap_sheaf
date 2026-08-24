/-
# Rooted coercivity strength produces the dynamic physical-rate band

For the completed vacuum-root gap, the strict rate is not independent data:

  q = 1 / (1 + strength),
  strength = rootCapacityDelta * uniformSectorMassFloor.

This module proves the exact margin identity

  1 - q = strength / (1 + strength)

in rational equivalence and converts scale-wise analytic bounds on that
explicit strength into the honest two-sided physical-rate band of
`BF4PhysicalDynamicVacuumRootLinearPhysicalBand`.

The resulting sufficient input is geometric and scalar: a positive lower
multiple of the concrete transfer length, an upper multiple, and one global
finite cap on the rooted strength.  The output remains tied to the same
completed transfer and therefore inherits the observable-connected physical
and continuum-floor compilers.

No strength band, cofinal linear-ratio family, continuum carrier, or
Yang--Mills measure is inhabited here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem one_sub_divPos_eqv_local
    (p q : Q') (hq : (0 : Q') < q) :
    ((1 : Q') - Q'.divPos p q hq) ≈
      Q'.divPos (q - p) q hq := by
  refine Q'.eqv_symm ?_
  show ((q - p) * Q'.recipPos q hq) ≈
    ((1 : Q') - Q'.divPos p q hq)
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv q (-p) (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_recipPos_eqv q hq)
      (Q'.neg_mul_eqv p (Q'.recipPos q hq))) ?_
  exact Q'.eqv_refl _

private theorem denominator_sub_one_eqv_strength
    (floor massFloor : Q') :
    cutoffTwoDirichletGluingDenominator floor massFloor - 1 ≈
      cutoffTwoDirichletGluingStrength floor massFloor := by
  unfold cutoffTwoDirichletGluingDenominator
    cutoffTwoDirichletGluingStrength
  refine Q'.eqv_trans _
    ((1 : Q') + ((floor * massFloor) + (-1))) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    ((1 : Q') + ((-1) + (floor * massFloor))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_comm_eqv (floor * massFloor) (-1))) ?_
  refine Q'.eqv_trans _
    (((1 : Q') + (-1)) + (floor * massFloor)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (0 + (floor * massFloor)) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ ((-1) + 1) _
        (Q'.add_comm_eqv 1 (-1))
        (Q'.neg_add_self_eqv 1))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (floor * massFloor))

/-- Exact rational identity between the gluing-rate margin and the normalized
coercivity strength. -/
theorem cutoffTwoDirichletGluingMargin_eqv_strengthRatio
    (floor massFloor : Q')
    (hfloor : (0 : Q') < floor)
    (hmass : (0 : Q') < massFloor) :
    (1 - cutoffTwoDirichletGluingRate
        floor massFloor hfloor hmass) ≈
      Q'.divPos
        (cutoffTwoDirichletGluingStrength floor massFloor)
        (cutoffTwoDirichletGluingDenominator floor massFloor)
        (cutoffTwoDirichletGluingDenominator_pos hfloor hmass) := by
  let denominator := cutoffTwoDirichletGluingDenominator floor massFloor
  have hdenominator : (0 : Q') < denominator :=
    cutoffTwoDirichletGluingDenominator_pos hfloor hmass
  refine Q'.eqv_trans _
    (Q'.divPos (denominator - 1) denominator hdenominator) _ ?_ ?_
  · exact one_sub_divPos_eqv_local 1 denominator hdenominator
  · unfold Q'.divPos
    exact Q'.mul_eqv_congr_right
      (denominator - 1)
      (cutoffTwoDirichletGluingStrength floor massFloor)
      (Q'.recipPos denominator hdenominator)
      (denominator_sub_one_eqv_strength floor massFloor)

/-! ## 1. The explicit dynamic strength -/

/-- The exact rooted Poincare strength whose reciprocal denominator defines
the compiled completed rate at one physical scale. -/
def dynamicVacuumRootStrength {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) : Q' :=
  cutoffTwoDirichletGluingStrength
    (family.linearRatio scale).delta
    (centralPhysicalFiniteVacuumSectorUniformMassFloor
      (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) half)

theorem dynamicVacuumRootStrength_pos {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) :
    (0 : Q') < dynamicVacuumRootStrength family scale :=
  cutoffTwoDirichletGluingStrength_pos
    (family.linearRatio scale).delta_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) half)

/-- The rate inside the actual completed gap is definitionally the reciprocal
rate generated by the explicit rooted strength factors. -/
theorem dynamicVacuumRootCompletedGapAt_rate_eq {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) :
    (family.completedGapAt scale).rate =
      cutoffTwoDirichletGluingRate
        (family.linearRatio scale).delta
        (centralPhysicalFiniteVacuumSectorUniformMassFloor
          (family.nome scale)
          (Q'.le_of_lt (family.nome_pos scale)) half)
        (family.linearRatio scale).delta_pos
        (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
          (family.nome scale)
          (Q'.le_of_lt (family.nome_pos scale)) half) := rfl

/-- The lattice margin of the actual completed transfer is exactly the
normalized explicit rooted strength. -/
theorem dynamicVacuumRootLatticeMargin_eqv_strengthRatio {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) :
    family.latticeMargin scale ≈
      Q'.divPos
        (dynamicVacuumRootStrength family scale)
        (1 + dynamicVacuumRootStrength family scale)
        (Q'.pos_add_nonneg (by decide)
          (Q'.le_of_lt
            (dynamicVacuumRootStrength_pos family scale))) := by
  unfold FixedHalfDynamicVacuumRootLinearFamily.latticeMargin
  rw [dynamicVacuumRootCompletedGapAt_rate_eq family scale]
  exact cutoffTwoDirichletGluingMargin_eqv_strengthRatio
    (family.linearRatio scale).delta
    (centralPhysicalFiniteVacuumSectorUniformMassFloor
      (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) half)
    (family.linearRatio scale).delta_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) half)

/-! ## 2. Strength scaling compiles to the physical rate band -/

/-- Geometric/RG bounds on the explicit rooted coercivity strength.  The cap
controls the denominator in the lower margin estimate; the upper multiple
also provides the finite physical-rate ceiling. -/
structure FixedHalfDynamicVacuumRootStrengthBand
    {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half) : Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  upper_pos : (0 : Q') < upper
  cap : Q'
  cap_nonnegative : (0 : Q') ≤ cap
  lowerScale : ∀ scale,
    lower * family.transferSpacing.spacing scale ≤
      dynamicVacuumRootStrength family scale
  upperScale : ∀ scale,
    dynamicVacuumRootStrength family scale ≤
      upper * family.transferSpacing.spacing scale
  strengthCap : ∀ scale,
    dynamicVacuumRootStrength family scale ≤ cap

namespace FixedHalfDynamicVacuumRootStrengthBand

/-- The denominator-adjusted physical floor produced by the rooted strength
lower bound and its common finite cap. -/
def physicalFloor {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootStrengthBand family) : Q' :=
  Q'.divPos band.lower (1 + band.cap)
    (Q'.pos_add_nonneg (by decide) band.cap_nonnegative)

theorem physicalFloor_pos {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootStrengthBand family) :
    (0 : Q') < band.physicalFloor :=
  Q'.divPos_pos band.lower (1 + band.cap)
    (Q'.pos_add_nonneg (by decide) band.cap_nonnegative)
    band.lower_pos

private theorem physicalFloor_mul_spacing_mul_capDen_eqv
    {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootStrengthBand family)
    (scale : Nat) :
    (band.physicalFloor * family.transferSpacing.spacing scale) *
        (1 + band.cap) ≈
      band.lower * family.transferSpacing.spacing scale := by
  unfold physicalFloor
  refine Q'.eqv_trans _
    (Q'.divPos band.lower (1 + band.cap)
        (Q'.pos_add_nonneg (by decide) band.cap_nonnegative) *
      (family.transferSpacing.spacing scale * (1 + band.cap))) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (Q'.divPos band.lower (1 + band.cap)
        (Q'.pos_add_nonneg (by decide) band.cap_nonnegative) *
      ((1 + band.cap) * family.transferSpacing.spacing scale)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv
        (family.transferSpacing.spacing scale) (1 + band.cap))) ?_
  refine Q'.eqv_trans _
    ((Q'.divPos band.lower (1 + band.cap)
        (Q'.pos_add_nonneg (by decide) band.cap_nonnegative) *
      (1 + band.cap)) * family.transferSpacing.spacing scale) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _
      (family.transferSpacing.spacing scale)
      (Q'.divPos_mul_eqv band.lower (1 + band.cap)
        (Q'.pos_add_nonneg (by decide) band.cap_nonnegative))

/-- Denominator control turns the strength lower bound into the physical
lower bound on the normalized strength ratio. -/
theorem physicalFloor_mul_spacing_le_strengthRatio {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootStrengthBand family)
    (scale : Nat) :
    band.physicalFloor * family.transferSpacing.spacing scale ≤
      Q'.divPos
        (dynamicVacuumRootStrength family scale)
        (1 + dynamicVacuumRootStrength family scale)
        (Q'.pos_add_nonneg (by decide)
          (Q'.le_of_lt
            (dynamicVacuumRootStrength_pos family scale))) := by
  apply Q'.le_divPos_of_mul_le
  have hdenominator :
      (1 : Q') + dynamicVacuumRootStrength family scale ≤
        1 + band.cap :=
    Q'.add_le_add_left 1 _ _ (band.strengthCap scale)
  have hfactorNonnegative : (0 : Q') ≤
      band.physicalFloor * family.transferSpacing.spacing scale :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt band.physicalFloor_pos)
      (Q'.le_of_lt (family.transferSpacing.spacing_pos scale))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hdenominator hfactorNonnegative
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (band.physicalFloor_mul_spacing_mul_capDen_eqv scale))
      (band.lowerScale scale))

/-- The normalized strength ratio never exceeds the raw nonnegative strength. -/
theorem strengthRatio_le_strength {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) :
    Q'.divPos
        (dynamicVacuumRootStrength family scale)
        (1 + dynamicVacuumRootStrength family scale)
        (Q'.pos_add_nonneg (by decide)
          (Q'.le_of_lt
            (dynamicVacuumRootStrength_pos family scale))) ≤
      dynamicVacuumRootStrength family scale := by
  apply Q'.divPos_le_of_le_mul
  have hone : (1 : Q') ≤
      1 + dynamicVacuumRootStrength family scale :=
    Q'.add_le_add_left 1 0 (dynamicVacuumRootStrength family scale)
      (Q'.le_of_lt (dynamicVacuumRootStrength_pos family scale))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (dynamicVacuumRootStrength family scale) hone
    (Q'.le_of_lt (dynamicVacuumRootStrength_pos family scale))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_one_eqv (dynamicVacuumRootStrength family scale))))
    hscaled

/-- The explicit strength band constructs the honest two-sided rate band for
the definitionally same completed transfer. -/
def toPhysicalRateBand {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootStrengthBand family) :
    FixedHalfDynamicVacuumRootPhysicalRateBand family where
  floor := band.physicalFloor
  floor_pos := band.physicalFloor_pos
  ceiling := band.upper
  ceiling_pos := band.upper_pos
  lowerRate := fun scale =>
    Q'.le_trans' _ _ _
      (band.physicalFloor_mul_spacing_le_strengthRatio scale)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (dynamicVacuumRootLatticeMargin_eqv_strengthRatio family scale)))
  upperRate := fun scale =>
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (dynamicVacuumRootLatticeMargin_eqv_strengthRatio family scale))
      (Q'.le_trans' _ _ _
        (strengthRatio_le_strength family scale)
        (band.upperScale scale))

/-- The rooted strength band reaches the sharp continuum-gap interface through
the same-object dynamic physical-rate compiler. -/
def toContinuumGapTheorem {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootStrengthBand family) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  band.toPhysicalRateBand.toContinuumGapTheorem

end FixedHalfDynamicVacuumRootStrengthBand

end YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.cutoffTwoDirichletGluingMargin_eqv_strengthRatio
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.dynamicVacuumRootCompletedGapAt_rate_eq
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.dynamicVacuumRootLatticeMargin_eqv_strengthRatio
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.FixedHalfDynamicVacuumRootStrengthBand.physicalFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.FixedHalfDynamicVacuumRootStrengthBand.physicalFloor_mul_spacing_le_strengthRatio
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.FixedHalfDynamicVacuumRootStrengthBand.strengthRatio_le_strength
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.FixedHalfDynamicVacuumRootStrengthBand.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.FixedHalfDynamicVacuumRootStrengthBand.toContinuumGapTheorem
