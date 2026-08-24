/-
# Source-independent dynamic family of completed BF4 vacuum sectors

Several finite analytic routes can produce a strict contraction on the same
completed canonical BF4 vacuum sector.  The global minimum-edge/root-linear
route is empty at half-extent zero, while the local spin-ray/off-ray route has
a viable capacity interface.  Downstream physical scaling and continuum
arguments should therefore depend on the completed object, not on the
particular finite producer.

This module defines that common dynamic interface.  At every physical scale it
carries the actual nome, completed sector strict contraction, and physical
transfer spacing.  It retains the literal completed same-object
autocorrelation and compiles a two-sided rate/spacing band into the sharp
physical-gap floor interface.  Thus different finite coercivity routes can
join one observable-connected downstream path without identifying unrelated
operators or rates.

No dynamic family, physical rate band, graph-norm limit, continuum measure,
continuum Yang--Mills theory, or Clay conclusion is inhabited here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.SharpContinuumObligation

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.SharpContinuumObligation
open YMGap.Continuum.UnifiedContinuumFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One source-independent family of actual completed transfers -/

/-- A scale-indexed family of actual completed canonical vacuum-sector
transfers.  The finite proof route is deliberately erased only after it has
produced the concrete `completedGap`; the carrier, transfer, rate, nome, and
physical spacing remain in the same dependent record. -/
structure DynamicVacuumSectorCompletedFamily (half : Nat) : Type 1 where
  nome : Nat → Q'
  nome_pos : ∀ scale, (0 : Q') < nome scale
  nome_lt_one : ∀ scale, nome scale < (1 : Q')
  transferSpacing : PhysicalSpacing
  transferSpacingToZero : SpacingToZero transferSpacing
  completedGap : ∀ scale,
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (nome_pos scale) (nome_lt_one scale) half

namespace DynamicVacuumSectorCompletedFamily

/-- The dimensionless lattice margin of the actual completed transfer at one
scale. -/
def latticeMargin {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (scale : Nat) : Q' :=
  (1 : Q') - (family.completedGap scale).rate

/-- The exact rational physical gap of the same completed transfer. -/
def physicalGap {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (scale : Nat) : Q' :=
  Q'.divPos (family.latticeMargin scale)
    (family.transferSpacing.spacing scale)
    (family.transferSpacing.spacing_pos scale)

theorem latticeMargin_pos {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (scale : Nat) :
    (0 : Q') < family.latticeMargin scale :=
  one_sub_pos_of_lt_one (family.completedGap scale).rate_lt_one

/-- The common interface retains geometric decay of the literal same-object
completed autocorrelation; it does not replace it by an abstract correlator. -/
theorem completedAutocorrelation_sq_decay {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (scale n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (family.nome_pos scale) (family.nome_lt_one scale) half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (family.nome_pos scale) (family.nome_lt_one scale)
          half n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (family.nome_pos scale) (family.nome_lt_one scale)
          half n vector.1))
      (CReal.RCmul
        (CReal.RCscale
          ((((family.completedGap scale).rate *
              (family.completedGap scale).rate)) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (family.nome_pos scale) (family.nome_lt_one scale)
            half vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (family.nome_pos scale) (family.nome_lt_one scale)
          half vector.1 vector.1)) :=
  centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    (family.completedGap scale) n vector

end DynamicVacuumSectorCompletedFamily

/-! ## 2. Honest two-sided physical scaling on that same family -/

/-- A two-sided rate/spacing law for the definitionally same completed
transfer family.  The lower inequality carries the mass-gap content; the
upper inequality forces the lattice margin to vanish with the spacing. -/
structure DynamicVacuumSectorPhysicalRateBand
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  lowerRate : ∀ scale,
    floor * family.transferSpacing.spacing scale ≤
      family.latticeMargin scale
  upperRate : ∀ scale,
    family.latticeMargin scale ≤
      ceiling * family.transferSpacing.spacing scale

namespace DynamicVacuumSectorPhysicalRateBand

theorem floor_le_physicalGap {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (scale : Nat) :
    band.floor ≤ family.physicalGap scale :=
  Q'.le_divPos_of_mul_le
    (family.latticeMargin scale)
    (family.transferSpacing.spacing scale)
    (family.transferSpacing.spacing_pos scale)
    (band.lowerRate scale)

theorem physicalGap_le_ceiling {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (scale : Nat) :
    family.physicalGap scale ≤ band.ceiling :=
  Q'.divPos_le_of_le_mul
    (family.latticeMargin scale)
    (family.transferSpacing.spacing scale)
    (family.transferSpacing.spacing_pos scale)
    (band.upperRate scale)

/-- A computable scale after which the actual lattice margin is below a
requested positive tolerance. -/
def marginModulus {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (epsilon : Q') : Nat :=
  family.transferSpacingToZero.modulus
    (Q'.divPos epsilon band.ceiling band.ceiling_pos)

theorem latticeMargin_le_epsilon {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : band.marginModulus epsilon ≤ scale) :
    family.latticeMargin scale ≤ epsilon := by
  let threshold := Q'.divPos epsilon band.ceiling band.ceiling_pos
  have hthreshold : (0 : Q') < threshold :=
    Q'.divPos_pos epsilon band.ceiling band.ceiling_pos hepsilon
  have hspacing : family.transferSpacing.spacing scale ≤ threshold :=
    family.transferSpacingToZero.spacing_le threshold hthreshold
      scale hscale
  have hscaled :
      band.ceiling * family.transferSpacing.spacing scale ≤
        band.ceiling * threshold :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hspacing
      (Q'.le_of_lt band.ceiling_pos)
  have hcollapse : band.ceiling * threshold ≈ epsilon :=
    Q'.eqv_trans _
      (threshold * band.ceiling) _
      (Q'.mul_comm_eqv band.ceiling threshold)
      (Q'.divPos_mul_eqv epsilon band.ceiling band.ceiling_pos)
  exact Q'.le_trans' _ _ _ (band.upperRate scale)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse))

/-- The actual completed rate tends effectively to one in lattice units. -/
theorem one_sub_epsilon_le_rate {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : band.marginModulus epsilon ≤ scale) :
    (1 : Q') - epsilon ≤ (family.completedGap scale).rate := by
  have hmargin := band.latticeMargin_le_epsilon
    epsilon hepsilon scale hscale
  have hadd := Q'.add_le_add_right
    (family.latticeMargin scale) epsilon
    (family.completedGap scale).rate hmargin
  have hcancel :
      family.latticeMargin scale +
          (family.completedGap scale).rate ≈ (1 : Q') := by
    unfold DynamicVacuumSectorCompletedFamily.latticeMargin
    refine Q'.eqv_trans _
      ((1 : Q') +
        (-(family.completedGap scale).rate +
          (family.completedGap scale).rate)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((1 : Q') + 0) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_self_eqv (family.completedGap scale).rate)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' 1)
  have hone : (1 : Q') ≤
      epsilon + (family.completedGap scale).rate :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hadd
  exact Q'.sub_le_of_le_add hone

/-! ## 3. Contraction to the scalar physical-gap interfaces -/

/-- The same-object dynamic rate band constructs the sharp scalar continuum
gap interface.  This remains a physical-gap compiler, not a continuum carrier
or Yang--Mills construction. -/
def toContinuumGapTheorem {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    ContinuumGapTheorem where
  a := family.transferSpacing.spacing
  a_pos := family.transferSpacing.spacing_pos
  latMargin := family.latticeMargin
  latMargin_pos := family.latticeMargin_pos
  c := band.floor
  c_pos := band.floor_pos
  rate_matched := band.lowerRate

def toUniformPhysicalGapFloor {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    QFloor family.physicalGap where
  floor := band.floor
  floor_pos := band.floor_pos
  bound := band.floor_le_physicalGap

end DynamicVacuumSectorPhysicalRateBand

/-! ## 4. A source-independent normalized-strength compiler -/

/-- An exact normalized-strength presentation of the actual completed rate.
Finite coercivity routes should provide this law from their own explicit
strength; downstream scaling no longer needs to know how that strength was
produced. -/
structure DynamicVacuumSectorNormalizedStrengthLaw
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  strength : Nat → Q'
  strength_pos : ∀ scale, (0 : Q') < strength scale
  margin_eqv : ∀ scale,
    family.latticeMargin scale ≈
      Q'.divPos (strength scale) (1 + strength scale)
        (Q'.pos_add_nonneg (by decide)
          (Q'.le_of_lt (strength_pos scale)))

/-- Two-sided physical scaling and one finite cap for an exact normalized
strength law. -/
structure DynamicVacuumSectorStrengthBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (law : DynamicVacuumSectorNormalizedStrengthLaw family) : Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  upper_pos : (0 : Q') < upper
  cap : Q'
  cap_nonnegative : (0 : Q') ≤ cap
  lowerScale : ∀ scale,
    lower * family.transferSpacing.spacing scale ≤ law.strength scale
  upperScale : ∀ scale,
    law.strength scale ≤ upper * family.transferSpacing.spacing scale
  strengthCap : ∀ scale, law.strength scale ≤ cap

namespace DynamicVacuumSectorStrengthBand

def physicalFloor {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) : Q' :=
  Q'.divPos band.lower (1 + band.cap)
    (Q'.pos_add_nonneg (by decide) band.cap_nonnegative)

theorem physicalFloor_pos {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) :
    (0 : Q') < band.physicalFloor :=
  Q'.divPos_pos band.lower (1 + band.cap)
    (Q'.pos_add_nonneg (by decide) band.cap_nonnegative)
    band.lower_pos

private theorem physicalFloor_mul_spacing_mul_capDen_eqv
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law)
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

theorem physicalFloor_mul_spacing_le_strengthRatio {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law)
    (scale : Nat) :
    band.physicalFloor * family.transferSpacing.spacing scale ≤
      Q'.divPos (law.strength scale) (1 + law.strength scale)
        (Q'.pos_add_nonneg (by decide)
          (Q'.le_of_lt (law.strength_pos scale))) := by
  apply Q'.le_divPos_of_mul_le
  have hdenominator :
      (1 : Q') + law.strength scale ≤ 1 + band.cap :=
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

theorem strengthRatio_le_strength {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (law : DynamicVacuumSectorNormalizedStrengthLaw family)
    (scale : Nat) :
    Q'.divPos (law.strength scale) (1 + law.strength scale)
        (Q'.pos_add_nonneg (by decide)
          (Q'.le_of_lt (law.strength_pos scale))) ≤
      law.strength scale := by
  apply Q'.divPos_le_of_le_mul
  have hone : (1 : Q') ≤ 1 + law.strength scale :=
    Q'.add_le_add_left 1 0 (law.strength scale)
      (Q'.le_of_lt (law.strength_pos scale))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (law.strength scale) hone
    (Q'.le_of_lt (law.strength_pos scale))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.mul_one_eqv (law.strength scale))))
    hscaled

/-- Exact strength scaling compiles to the honest physical rate band for the
definitionally same completed transfer. -/
def toPhysicalRateBand {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) :
    DynamicVacuumSectorPhysicalRateBand family where
  floor := band.physicalFloor
  floor_pos := band.physicalFloor_pos
  ceiling := band.upper
  ceiling_pos := band.upper_pos
  lowerRate := fun scale =>
    Q'.le_trans' _ _ _
      (band.physicalFloor_mul_spacing_le_strengthRatio scale)
      (Q'.le_of_eqv (Q'.eqv_symm (law.margin_eqv scale)))
  upperRate := fun scale =>
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (law.margin_eqv scale))
      (Q'.le_trans' _ _ _
        (strengthRatio_le_strength law scale)
        (band.upperScale scale))

def toContinuumGapTheorem {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) :
    ContinuumGapTheorem :=
  band.toPhysicalRateBand.toContinuumGapTheorem

end DynamicVacuumSectorStrengthBand

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily.latticeMargin_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily.completedAutocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand.floor_le_physicalGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand.physicalGap_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand.latticeMargin_le_epsilon
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand.one_sub_epsilon_le_rate
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorPhysicalRateBand.toUniformPhysicalGapFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorStrengthBand.physicalFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorStrengthBand.physicalFloor_mul_spacing_le_strengthRatio
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorStrengthBand.strengthRatio_le_strength
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorStrengthBand.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorStrengthBand.toContinuumGapTheorem
