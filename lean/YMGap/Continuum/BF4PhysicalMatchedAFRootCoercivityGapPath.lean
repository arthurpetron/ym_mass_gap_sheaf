/-
# The matched AF path from rooted coercivity to the completed OS transfer

At every physical scale, suppose the literal matched BF4 nome carries:

* a cofinal off-ray rooted coercivity certificate; and
* a cofinal spin-ray capacity certificate.

The fixed-nome bridge then constructs the exact cofinal posterior fraction

    min 1 (componentMassFloor_j * rootedStrength_j),

and hence the actual completed canonical-sector OS transfer at rate one minus
that fraction.  This module packages that construction on one matched
asymptotically-free trajectory and reuses the existing same-object observable
and physical-gap compilers.

The scale comparison of this explicit product with the physical lattice
spacing is retained as named input.  No rooted family, scaling estimate,
continuum carrier, continuum QFT, or Clay conclusion is inhabited here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge

namespace YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath

set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Scale-indexed rooted data at the exact matched nome -/

/-- The two cofinal rooted inputs, attached scale by scale to one literal
matched BF4 scalar trajectory. -/
structure MatchedPhysicalRootCoercivityGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRay : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootCoercivity
      (trajectory.nome_pos scale)
  ray : ∀ scale,
    FixedNomeCofinalSpinCubeRayCapacity
      (trajectory.nome_pos scale)

namespace MatchedPhysicalRootCoercivityGapProducer

/-- The explicit posterior fraction produced by the rooted route at scale
`scale`. -/
def fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory)
    (scale : Nat) : Q' :=
  rootedCofinalGapFraction (producer.offRay scale) (producer.ray scale)

@[simp] theorem fraction_eq_massFloor_mul_rootedStrength
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory)
    (scale : Nat) :
    producer.fraction scale =
      Q'.min' 1
        (centralPhysicalFiniteVacuumSectorUniformMassFloor
            (trajectory.nome scale)
            (Q'.le_of_lt (trajectory.nome_pos scale)) 0 *
          (producer.offRay scale).compiledStrength
            (producer.ray scale)) :=
  rfl

/-- The rooted inputs inhabit the exact posterior-variance producer required
by the existing matched completed-transfer path. -/
def toConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory) :
    MatchedPhysicalConditionalVarianceGapProducer trajectory where
  cofinalFraction := fun scale =>
    toFixedNomeCofinalConditionalVarianceFraction
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale)
      (producer.offRay scale) (producer.ray scale)

/-- The actual completed canonical-sector OS transfer family on the matched
trajectory. -/
def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toConditionalVarianceGapProducer.toCompletedFamily

/-- The lattice margin of that same completed transfer is exactly the
explicit mass-floor/rooted-strength fraction. -/
theorem toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale ≈
      producer.fraction scale := by
  exact producer.toConditionalVarianceGapProducer
    |>.toCompletedFamily_latticeMargin_eqv_fraction scale

/-! ## 2. The sole physical scalar comparison -/

/-- The exact remaining scale estimate for the unnormalized rooted route.
Expanding `producer.fraction` exposes the load-bearing component-mass floor. -/
structure FractionScaling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory) : Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  upper_pos : (0 : Q') < upper
  lowerScale : ∀ scale,
    lower * spacing.a (trajectory.coupling scale) ≤ producer.fraction scale
  upperScale : ∀ scale,
    producer.fraction scale ≤ upper * spacing.a (trajectory.coupling scale)

namespace FractionScaling

/-- Forget only the rooted presentation and enter the generic posterior-gap
scaling compiler without changing either constant. -/
def toConditionalVarianceFractionScaling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalRootCoercivityGapProducer trajectory}
    (scaling : FractionScaling producer) :
    MatchedPhysicalConditionalVarianceGapProducer.FractionScaling
      producer.toConditionalVarianceGapProducer where
  lower := scaling.lower
  lower_pos := scaling.lower_pos
  upper := scaling.upper
  upper_pos := scaling.upper_pos
  lowerScale := scaling.lowerScale
  upperScale := scaling.upperScale

/-- The explicit product scaling yields the physical rate band on the same
completed OS transfer family. -/
def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalRootCoercivityGapProducer trajectory}
    (scaling : FractionScaling producer) :
    DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily :=
  scaling.toConditionalVarianceFractionScaling.toPhysicalRateBand

/-- Scalar continuum-gap export from the same matched completed transfer.
This is an interface theorem, not an inhabited continuum Yang--Mills model. -/
def toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalRootCoercivityGapProducer trajectory}
    (scaling : FractionScaling producer) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  scaling.toConditionalVarianceFractionScaling.toContinuumGapTheorem

end FractionScaling

/-! ## 3. Same-object observable consequences -/

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalRootCoercivityGapProducer trajectory) : Type 1 :=
  MatchedPhysicalConditionalVarianceGapProducer.SameObjectObservablePin
    producer.toConditionalVarianceGapProducer

theorem connectedCorrSq_control
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalRootCoercivityGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (O : pin.Obs) (hO : pin.GaugeInvariantLocal O)
    (scale n : Nat) :
    pin.connectedCorrSq scale O n ≤
      pin.amplitude O * (((1 : Q') + (-producer.fraction scale)) ^ n) := by
  exact producer.toConditionalVarianceGapProducer.connectedCorrSq_control
    pin O hO scale n

def physicalGapFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalRootCoercivityGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (scaling : FractionScaling producer) :
    PhysicalGapFloor
      (producer.toConditionalVarianceGapProducer.physicalSeparator pin)
      producer.toCompletedFamily.transferSpacing.spacing
      producer.toCompletedFamily.transferSpacing.spacing_pos :=
  producer.toConditionalVarianceGapProducer.physicalGapFloor pin
    scaling.toConditionalVarianceFractionScaling

end MatchedPhysicalRootCoercivityGapProducer

end YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath.MatchedPhysicalRootCoercivityGapProducer.toConditionalVarianceGapProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath.MatchedPhysicalRootCoercivityGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath.MatchedPhysicalRootCoercivityGapProducer.FractionScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath.MatchedPhysicalRootCoercivityGapProducer.connectedCorrSq_control
