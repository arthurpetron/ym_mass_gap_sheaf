/-
# A dynamic physical-rate band for the completed BF4 vacuum-root sector

The fixed-nome root-flow route now compiles one cofinal linear traffic ratio
into an actual strict contraction of the completed physical vacuum-sector
transfer.  A continuum argument must not silently reuse one fixed rate while
the physical transfer length tends to zero.  The honest dynamic datum is a
family of those same completed transfers, together with two-sided scaling

  floor * a_j <= 1 - q_j <= ceiling * a_j,

where `a_j` is explicitly the physical length assigned to one member of this
concrete transfer family and `q_j` is definitionally its compiled rate.

This module packages that same-object family and proves the purely causal
consequences:

* every scale has the actual completed operator and autocorrelation gap;
* the lower scaling inequality gives a uniform positive physical gap;
* the upper scaling inequality and the supplied Type-level zero modulus force
  the lattice margin to vanish, ruling out a fixed-rate-as-spacing-zero
  shortcut;
* the family constructs the existing sharp `ContinuumGapTheorem` interface.

No dynamic family, cofinal ratio, physical rate band, continuum carrier, or
Yang--Mills measure is inhabited here.  In particular the rate band is genuine
RG/dimensional-transmutation input, not a consequence of the finite compiler.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.SharpContinuumObligation

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.SharpContinuumObligation
open YMGap.Continuum.UnifiedContinuumFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The same completed rooted sector at every physical scale -/

/-- A scale-indexed family of the already-compiled completed vacuum-root
sector.  `transferSpacing.spacing j` is the physical time length assigned to
the concrete completed transfer at scale `j`; its interpretation is therefore
part of the same-object pin rather than an unrelated lattice sequence. -/
structure FixedHalfDynamicVacuumRootLinearFamily (half : Nat) : Type 1 where
  nome : Nat → Q'
  nome_pos : ∀ scale, (0 : Q') < nome scale
  nome_lt_one : ∀ scale, nome scale < (1 : Q')
  transferSpacing : PhysicalSpacing
  transferSpacingToZero : SpacingToZero transferSpacing
  linearRatio : ∀ scale,
    FixedNomeCofinalVacuumRootLinearRatio (nome_pos scale) half

namespace FixedHalfDynamicVacuumRootLinearFamily

/-- The actual completed strict-contraction datum compiled at one dynamic
scale from that scale's cofinal representation-cutoff ratio. -/
def completedGapAt {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half) (scale : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (family.nome_pos scale) (family.nome_lt_one scale) half :=
  (family.linearRatio scale).toCompletedStrictContractionData
    (family.nome_pos scale) (family.nome_lt_one scale) half

/-- The dimensionless lattice margin of the very same completed transfer. -/
def latticeMargin {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) : Q' :=
  (1 : Q') - (family.completedGapAt scale).rate

/-- The exact dimensionful rational gap of the compiled completed transfer. -/
def physicalGap {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) : Q' :=
  Q'.divPos (family.latticeMargin scale)
    (family.transferSpacing.spacing scale)
    (family.transferSpacing.spacing_pos scale)

/-- Every compiled member of the dynamic family has a positive lattice-unit
margin. -/
theorem latticeMargin_pos {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
    (scale : Nat) :
    (0 : Q') < family.latticeMargin scale :=
  one_sub_pos_of_lt_one (family.completedGapAt scale).rate_lt_one

/-- The dynamic wrapper retains the literal squared same-object completed
autocorrelation decay at each scale; no independently selected observable or
separator appears in the statement. -/
theorem completedAutocorrelation_sq_decay {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half)
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
          ((((family.completedGapAt scale).rate *
              (family.completedGapAt scale).rate)) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (family.nome_pos scale) (family.nome_lt_one scale)
            half vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (family.nome_pos scale) (family.nome_lt_one scale)
          half vector.1 vector.1)) :=
  centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    (family.completedGapAt scale) n vector

end FixedHalfDynamicVacuumRootLinearFamily

/-! ## 2. The honest two-sided physical scaling seam -/

/-- A finite, positive physical-rate band for the same completed transfer
family.  The lower inequality is the mass-gap content.  The upper inequality
prevents treating a cutoff-independent lattice rate as a continuum transfer
rate and supplies the finite physical-scale side of the construction. -/
structure FixedHalfDynamicVacuumRootPhysicalRateBand
    {half : Nat}
    (family : FixedHalfDynamicVacuumRootLinearFamily half) : Type 1 where
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

namespace FixedHalfDynamicVacuumRootPhysicalRateBand

/-- The supplied positive floor lies below the exact physical gap at every
scale. -/
theorem floor_le_physicalGap {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family)
    (scale : Nat) :
    band.floor ≤ family.physicalGap scale :=
  Q'.le_divPos_of_mul_le
    (family.latticeMargin scale)
    (family.transferSpacing.spacing scale)
    (family.transferSpacing.spacing_pos scale)
    (band.lowerRate scale)

/-- The exact physical gap is finite under the matching upper scaling law. -/
theorem physicalGap_le_ceiling {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family)
    (scale : Nat) :
    family.physicalGap scale ≤ band.ceiling :=
  Q'.divPos_le_of_le_mul
    (family.latticeMargin scale)
    (family.transferSpacing.spacing scale)
    (family.transferSpacing.spacing_pos scale)
    (band.upperRate scale)

/-- A computable scale after which the lattice margin is at most a requested
positive tolerance. -/
def marginModulus {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family)
    (epsilon : Q') : Nat :=
  family.transferSpacingToZero.modulus
    (Q'.divPos epsilon band.ceiling band.ceiling_pos)

/-- The upper physical-rate law and the Type-level spacing modulus force the
dimensionless lattice margin to vanish effectively. -/
theorem latticeMargin_le_epsilon {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family)
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

/-- Equivalently, the actual completed contraction rate approaches one in
lattice units; a fixed strict rate cannot be smuggled through the zero-spacing
limit. -/
theorem one_sub_epsilon_le_rate {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : band.marginModulus epsilon ≤ scale) :
    (1 : Q') - epsilon ≤ (family.completedGapAt scale).rate := by
  have hmargin := band.latticeMargin_le_epsilon
    epsilon hepsilon scale hscale
  have hadd := Q'.add_le_add_right
    (family.latticeMargin scale) epsilon
    (family.completedGapAt scale).rate hmargin
  have hcancel :
      family.latticeMargin scale +
          (family.completedGapAt scale).rate ≈ (1 : Q') := by
    unfold FixedHalfDynamicVacuumRootLinearFamily.latticeMargin
    refine Q'.eqv_trans _
      ((1 : Q') +
        (-(family.completedGapAt scale).rate +
          (family.completedGapAt scale).rate)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((1 : Q') + 0) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_self_eqv (family.completedGapAt scale).rate)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' 1)
  have hone : (1 : Q') ≤
      epsilon + (family.completedGapAt scale).rate :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hadd
  exact Q'.sub_le_of_le_add hone

/-! ## 3. Contraction to the canonical continuum floor interface -/

/-- The same-object dynamic BF4 rate band inhabits the project's sharp
physical continuum-gap interface.  This is a compiler: its input rate band is
the still-open dimensional-transmutation estimate. -/
def toContinuumGapTheorem {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family) :
    ContinuumGapTheorem where
  a := family.transferSpacing.spacing
  a_pos := family.transferSpacing.spacing_pos
  latMargin := family.latticeMargin
  latMargin_pos := family.latticeMargin_pos
  c := band.floor
  c_pos := band.floor_pos
  rate_matched := band.lowerRate

/-- The dynamic rooted family therefore supplies the canonical uniform floor
on its exact rational physical gap. -/
def toUniformPhysicalGapFloor {half : Nat}
    {family : FixedHalfDynamicVacuumRootLinearFamily half}
    (band : FixedHalfDynamicVacuumRootPhysicalRateBand family) :
    QFloor family.physicalGap where
  floor := band.floor
  floor_pos := band.floor_pos
  bound := band.floor_le_physicalGap

end FixedHalfDynamicVacuumRootPhysicalRateBand

end YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootLinearFamily.completedGapAt
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootLinearFamily.completedAutocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootPhysicalRateBand.floor_le_physicalGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootPhysicalRateBand.physicalGap_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootPhysicalRateBand.latticeMargin_le_epsilon
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootPhysicalRateBand.one_sub_epsilon_le_rate
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootPhysicalRateBand.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumRootLinearPhysicalBand.FixedHalfDynamicVacuumRootPhysicalRateBand.toUniformPhysicalGapFloor
