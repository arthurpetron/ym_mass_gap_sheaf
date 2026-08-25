/-
# Canonical AF scalar spine for the dynamic adaptive BF4 family

The completed dynamic BF4 compiler asks simultaneously for a nome trajectory,
a vanishing physical spacing, a cofinal spin-ray capacity, and an adaptive
off-ray transition product.  Only the last two items are local analytic
content.  This module separates that content from the scalar trajectory.

The reusable `DynamicSpinCubeOffRayAdaptiveScalarTrajectory` carries exactly
the five scalar fields.  The canonical inhabitant uses the shifted asymptotic-
freedom schedule

  w_scale = afRateModulus_canonical.w (scale + 1)
          = 1 - 1 / (scale + 2),

so the nome is strictly positive already at scale zero, and the geometric
physical spacing `a_scale = (1/2)^scale`.  `HalfPow.pow_half_le` supplies an
explicit spacing-to-zero modulus.

`DynamicSpinCubeOffRayAdaptiveLocalProducer` then exposes only the two
dependent fixed-nome analytic fields that are genuinely missing: a cofinal
spin-ray capacity at each scale and an adaptive conditional transition product
for that same capacity.  Its compiler constructs the existing dynamic family
and hence its actual completed carrier, transfer, and vacuum sector without
changing any index.

The canonical scalar spine is a non-vacuous arithmetic construction, but it is
not identified here with the actual four-dimensional grouped BF4/AF block
trajectory.  No local producer, same-observable cross-scale pin, continuum
handoff, continuum Yang--Mills theory, or Clay conclusion is inhabited.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Constructive.HalfPow
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily

namespace YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate

/-! ## 1. Separate scalar trajectory data from local analytic data -/

/-- The scalar trajectory needed by the dynamic completed-family compiler,
before any spin-ray or off-ray estimate is supplied. -/
structure DynamicSpinCubeOffRayAdaptiveScalarTrajectory : Type where
  nome : Nat -> Q'
  nome_pos : forall scale, (0 : Q') < nome scale
  nome_lt_one : forall scale, nome scale < (1 : Q')
  transferSpacing : PhysicalSpacing
  transferSpacingToZero : SpacingToZero transferSpacing

/-- The two dependent local analytic producers left after the scalar
trajectory is fixed.  The transition product is indexed by the exact capacity
chosen in the preceding field, preventing cross-scale or cross-capacity
substitution. -/
structure DynamicSpinCubeOffRayAdaptiveLocalProducer
    (trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory) : Type 1 where
  rayCapacity : forall scale,
    FixedNomeCofinalSpinCubeRayCapacity (trajectory.nome_pos scale)
  transitionProduct : forall scale,
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      (trajectory.nome_pos scale) (rayCapacity scale)

namespace DynamicSpinCubeOffRayAdaptiveLocalProducer

/-- Losslessly reassemble the scalar trajectory and its two local analytic
fields into the existing dynamic adaptive family. -/
def toDynamicFamily
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    (producer : DynamicSpinCubeOffRayAdaptiveLocalProducer trajectory) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily where
  nome := trajectory.nome
  nome_pos := trajectory.nome_pos
  nome_lt_one := trajectory.nome_lt_one
  transferSpacing := trajectory.transferSpacing
  transferSpacingToZero := trajectory.transferSpacingToZero
  rayCapacity := producer.rayCapacity
  transitionProduct := producer.transitionProduct

/-- The actual completed carriers, transfers, and vacuum sectors constructed
scale by scale by the existing adaptive compiler. -/
def toCompletedFamily
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    (producer : DynamicSpinCubeOffRayAdaptiveLocalProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toDynamicFamily.toCompletedFamily

/-- The exact normalized strength law of those same completed transfers. -/
def toNormalizedStrengthLaw
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    (producer : DynamicSpinCubeOffRayAdaptiveLocalProducer trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw producer.toCompletedFamily :=
  producer.toDynamicFamily.toNormalizedStrengthLaw

end DynamicSpinCubeOffRayAdaptiveLocalProducer

/-! ## 2. A concrete strictly-positive canonical AF nome -/

/-- Shift the canonical AF nome once so that the dynamic trajectory starts at
`1/2` rather than at the zero value of the unshifted sanity witness. -/
def canonicalAFPositiveNome (scale : Nat) : Q' :=
  afRateModulus_canonical.w (scale + 1)

theorem canonicalAFPositiveNome_pos (scale : Nat) :
    (0 : Q') < canonicalAFPositiveNome scale := by
  unfold canonicalAFPositiveNome
  change (0 : Q') < 1 - Q'.invSucc (scale + 1)
  apply one_sub_pos_of_lt_one
  exact Q'.lt_of_le_of_lt
    (ExpNeg.invSucc_le_of_le
      (Nat.succ_le_succ (Nat.zero_le scale)))
    (by decide : Q'.invSucc 1 < (1 : Q'))

theorem canonicalAFPositiveNome_lt_one (scale : Nat) :
    canonicalAFPositiveNome scale < (1 : Q') := by
  unfold canonicalAFPositiveNome
  exact afRateModulus_canonical.w_lt_one (scale + 1)

/-! ## 3. A concrete geometric physical spacing with modulus -/

/-- The geometric spacing paired with the canonical scalar AF nome.  It has
the dimensional-transmutation shape `a_scale = (1/2)^scale`. -/
def canonicalAFGeometricSpacing (scale : Nat) : Q' :=
  HalfPow.half ^ scale

theorem canonicalAFGeometricSpacing_pos : forall scale,
    (0 : Q') < canonicalAFGeometricSpacing scale
  | 0 => by
      unfold canonicalAFGeometricSpacing
      decide
  | scale + 1 => by
      unfold canonicalAFGeometricSpacing
      exact Q'.mul_pos (by decide)
        (canonicalAFGeometricSpacing_pos scale)

def canonicalAFGeometricPhysicalSpacing : PhysicalSpacing where
  spacing := canonicalAFGeometricSpacing
  spacing_pos := canonicalAFGeometricSpacing_pos

/-- The denominator of the requested positive rational tolerance is an
explicit cutoff for the geometric spacing. -/
def canonicalAFGeometricSpacingToZero :
    SpacingToZero canonicalAFGeometricPhysicalSpacing where
  modulus := fun epsilon => epsilon.den
  spacing_le := by
    intro epsilon hepsilon scale hscale
    change HalfPow.half ^ scale <= epsilon
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hscale
    exact Q'.le_trans' _ _ _
      (ExpNeg.pow_half_antitone epsilon.den offset)
      (HalfPow.pow_half_le epsilon hepsilon)

/-! ## 4. Canonical scalar spine and its exact remaining frontier -/

/-- A fully inhabited scalar trajectory: shifted canonical AF nome plus a
geometrically vanishing positive physical spacing. -/
def canonicalAFGeometricScalarTrajectory :
    DynamicSpinCubeOffRayAdaptiveScalarTrajectory where
  nome := canonicalAFPositiveNome
  nome_pos := canonicalAFPositiveNome_pos
  nome_lt_one := canonicalAFPositiveNome_lt_one
  transferSpacing := canonicalAFGeometricPhysicalSpacing
  transferSpacingToZero := canonicalAFGeometricSpacingToZero

/-- The exact remaining local analytic certificate on the canonical scalar
spine.  No inhabitant is asserted here. -/
abbrev CanonicalAFGeometricLocalProducer : Type 1 :=
  DynamicSpinCubeOffRayAdaptiveLocalProducer
    canonicalAFGeometricScalarTrajectory

/-- Any inhabitant of the remaining two-field local certificate constructs
the existing dynamic family on the canonical AF/geometric scalar spine. -/
def canonicalAFGeometricDynamicFamily
    (producer : CanonicalAFGeometricLocalProducer) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  producer.toDynamicFamily

/-- Consequently the same local certificate constructs the actual completed
carrier, transfer, and vacuum sector at every scale. -/
def canonicalAFGeometricCompletedFamily
    (producer : CanonicalAFGeometricLocalProducer) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toCompletedFamily

@[simp] theorem canonicalAFGeometricDynamicFamily_nome
    (producer : CanonicalAFGeometricLocalProducer) (scale : Nat) :
    (canonicalAFGeometricDynamicFamily producer).nome scale =
      canonicalAFPositiveNome scale := rfl

@[simp] theorem canonicalAFGeometricDynamicFamily_spacing
    (producer : CanonicalAFGeometricLocalProducer) (scale : Nat) :
    (canonicalAFGeometricDynamicFamily producer).transferSpacing.spacing scale =
      canonicalAFGeometricSpacing scale := rfl

end YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.DynamicSpinCubeOffRayAdaptiveLocalProducer.toDynamicFamily
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.DynamicSpinCubeOffRayAdaptiveLocalProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFPositiveNome_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFPositiveNome_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFGeometricSpacing_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFGeometricSpacingToZero
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFGeometricScalarTrajectory
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFGeometricDynamicFamily
#print axioms
  YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler.canonicalAFGeometricCompletedFamily
