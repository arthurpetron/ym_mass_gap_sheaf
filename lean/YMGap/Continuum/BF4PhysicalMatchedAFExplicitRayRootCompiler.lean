/-
# The explicit ray removes one dynamic matched-AF input

`explicitSubunitCentralSpinCubeCofinalRayCapacity` constructs a positive
cofinal ray capacity for every positive subunit nome.  The matched physical
root compiler previously asked for that ray capacity and an off-ray root
certificate as two independent scale-indexed fields.  This module supplies
the ray field definitionally from the literal matched nome, so the dynamic
rooted route has exactly one remaining analytic input: the off-ray root
certificate at each physical scale.

The resulting compiler still constructs the same completed carrier, transfer,
vacuum complement, and conditional-variance family as the existing rooted
route.  It does not construct the off-ray certificate, a strength/spacing
band, a same-object observable pin, an OS/GNS passage, a continuum theory, or
the Clay mass-gap theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap

namespace YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap

/-! ## 1. The strictly smaller dynamic input -/

/-- The only scale-indexed rooted datum not supplied by the explicit ray
construction.  Its `offRay` field is intentionally left as a named analytic
input; no inhabitant is asserted here. -/
structure MatchedPhysicalExplicitRayOffRayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRay : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootCoercivity
      (trajectory.nome_pos scale)

/-! ## 2. Definitionally construct the ray field -/

/-- The explicit selected-term row supplies the ray capacity at the literal
matched nome of every physical scale. -/
def explicitRay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) :
    FixedNomeCofinalSpinCubeRayCapacity
      (trajectory.nome_pos scale) :=
  explicitSubunitCentralSpinCubeCofinalRayCapacity
    (trajectory.nome scale)
    (trajectory.nome_pos scale)
    (trajectory.nome_lt_one scale)

theorem explicitRay_delta_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) :
    (0 : Q') < (explicitRay trajectory scale).delta :=
  (explicitRay trajectory scale).delta_pos

/-- Insert the explicit ray into the existing matched physical rooted
compiler.  The completed family is unchanged; only the redundant ray input is
removed from the constructor boundary. -/
def MatchedPhysicalExplicitRayOffRayProducer.toRootProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory) :
    MatchedPhysicalRootCoercivityGapProducer trajectory where
  offRay := producer.offRay
  ray := fun scale => explicitRay trajectory scale

@[simp] theorem toRootProducer_offRay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory)
    (scale : Nat) :
    (producer.toRootProducer.offRay scale) = producer.offRay scale :=
  rfl

@[simp] theorem toRootProducer_ray
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory)
    (scale : Nat) :
    (producer.toRootProducer.ray scale) = explicitRay trajectory scale :=
  rfl

/-! ## 3. Consequences on the same completed objects -/

/-- The explicit-ray compiler reaches the existing completed canonical-sector
family from the single remaining off-ray input. -/
def MatchedPhysicalExplicitRayOffRayProducer.toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toRootProducer.toCompletedFamily

/-- The corresponding conditional-variance producer for the same completed
family. -/
def MatchedPhysicalExplicitRayOffRayProducer.toConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory) :
    MatchedPhysicalConditionalVarianceGapProducer trajectory :=
  producer.toRootProducer.toConditionalVarianceGapProducer

/-- The exact positive posterior fraction at each scale, now visibly using
the literal explicit ray and the one supplied off-ray certificate. -/
theorem MatchedPhysicalExplicitRayOffRayProducer.fraction_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory)
    (scale : Nat) :
    (0 : Q') <
      (producer.toRootProducer.fraction scale) := by
  exact rootedCofinalGapFraction_pos
    (producer.offRay scale)
    (explicitRay trajectory scale)

theorem MatchedPhysicalExplicitRayOffRayProducer.fraction_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayOffRayProducer trajectory)
    (scale : Nat) :
    producer.toRootProducer.fraction scale ≤ (1 : Q') := by
  exact rootedCofinalGapFraction_le_one
    (producer.offRay scale)
    (explicitRay trajectory scale)

/-! ## 4. Lower the boundary once more to resistance congestion -/

/-- The primitive scale-indexed input for the same rooted dynamic route:
one cofinal resistance-congestion bound for the off-ray root at each scale.
The existing resistance compiler supplies the rooted coercivity consumed
above. -/
structure MatchedPhysicalExplicitRayResistanceProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRayResistance : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound
      (trajectory.nome_pos scale)

/-- Compile the resistance-congestion input into the already reduced
off-ray-root input, without changing its physical scale or nome. -/
def MatchedPhysicalExplicitRayResistanceProducer.toOffRayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory) :
    MatchedPhysicalExplicitRayOffRayProducer trajectory where
  offRay := fun scale =>
    (producer.offRayResistance scale).toCofinalOffRayRootCoercivity

/-- The resistance-level input reaches the same explicit-ray rooted producer
through the two checked local compilers. -/
def MatchedPhysicalExplicitRayResistanceProducer.toRootProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory) :
    MatchedPhysicalRootCoercivityGapProducer trajectory :=
  producer.toOffRayProducer.toRootProducer

/-- Consequently the resistance-level input reaches the same completed
carrier, transfer, and vacuum complement. -/
def MatchedPhysicalExplicitRayResistanceProducer.toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toOffRayProducer.toCompletedFamily

theorem MatchedPhysicalExplicitRayResistanceProducer.fraction_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory)
    (scale : Nat) :
    (0 : Q') < producer.toRootProducer.fraction scale := by
  exact producer.toOffRayProducer.fraction_pos scale

end YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.explicitRay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.explicitRay_delta_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayOffRayProducer.toRootProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayOffRayProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayOffRayProducer.toConditionalVarianceGapProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayOffRayProducer.fraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayOffRayProducer.fraction_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.toOffRayProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.toRootProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.fraction_pos
