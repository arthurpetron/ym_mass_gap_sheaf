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
import YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
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
open YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.SharpContinuumObligation
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFRootCoercivityGapPath
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap
open YMGap.Continuum.BoundedTransferCalculus

local infix:50 " ≈ " => Q'.eqv

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

/-- The resistance-level route preserves the conditional-variance producer
for the same completed family. -/
def MatchedPhysicalExplicitRayResistanceProducer.toConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory) :
    MatchedPhysicalConditionalVarianceGapProducer trajectory :=
  producer.toOffRayProducer.toConditionalVarianceGapProducer

theorem MatchedPhysicalExplicitRayResistanceProducer.toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale ≈
      producer.toRootProducer.fraction scale := by
  exact MatchedPhysicalRootCoercivityGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
    producer.toOffRayProducer.toRootProducer scale

theorem MatchedPhysicalExplicitRayResistanceProducer.fraction_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayResistanceProducer trajectory)
    (scale : Nat) :
    (0 : Q') < producer.toRootProducer.fraction scale := by
  exact producer.toOffRayProducer.fraction_pos scale

/-! ## 5. Lower the boundary to a scalar resistance moment -/

/-- A still smaller scale-indexed input: one uniform first-resistance-moment
bound for the off-ray root at each literal matched nome. -/
structure MatchedPhysicalExplicitRayMomentProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRayMoment : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound
      (trajectory.nome_pos scale)

/-- The checked first-moment compiler supplies the resistance-congestion
certificate consumed by the preceding resistance-level adapter. -/
def MatchedPhysicalExplicitRayMomentProducer.toResistanceProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMomentProducer trajectory) :
    MatchedPhysicalExplicitRayResistanceProducer trajectory where
  offRayResistance := fun scale =>
    (producer.offRayMoment scale).toResistanceCongestionBound

/-- The scalar-moment input reaches the same explicit-ray rooted producer. -/
def MatchedPhysicalExplicitRayMomentProducer.toRootProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMomentProducer trajectory) :
    MatchedPhysicalRootCoercivityGapProducer trajectory :=
  producer.toResistanceProducer.toRootProducer

/-- Consequently the scalar-moment input reaches the same completed carrier,
transfer, and vacuum complement. -/
def MatchedPhysicalExplicitRayMomentProducer.toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMomentProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toResistanceProducer.toCompletedFamily

theorem MatchedPhysicalExplicitRayMomentProducer.toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMomentProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale ≈
      producer.toRootProducer.fraction scale := by
  exact MatchedPhysicalRootCoercivityGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
    producer.toResistanceProducer.toRootProducer scale

/-! ## 6. A physical-mass shell route to the same boundary -/

/-- A physically organized alternative input: entropy and state-load decay on
the literal physical-mass shells of every matched off-ray edge. -/
structure MatchedPhysicalExplicitRayMassShellProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRayMassShell : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound
      (trajectory.nome_pos scale)

/-- The physical-mass shell compiler supplies the same local resistance
congestion certificate consumed by the matched route. -/
def MatchedPhysicalExplicitRayMassShellProducer.toResistanceProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMassShellProducer trajectory) :
    MatchedPhysicalExplicitRayResistanceProducer trajectory where
  offRayResistance := fun scale =>
    (producer.offRayMassShell scale).toResistanceCongestionBound

def MatchedPhysicalExplicitRayMassShellProducer.toRootProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMassShellProducer trajectory) :
    MatchedPhysicalRootCoercivityGapProducer trajectory :=
  producer.toResistanceProducer.toRootProducer

def MatchedPhysicalExplicitRayMassShellProducer.toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMassShellProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toResistanceProducer.toCompletedFamily

def MatchedPhysicalExplicitRayMassShellProducer.toConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMassShellProducer trajectory) :
    MatchedPhysicalConditionalVarianceGapProducer trajectory :=
  producer.toResistanceProducer.toConditionalVarianceGapProducer

theorem MatchedPhysicalExplicitRayMassShellProducer.toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMassShellProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale ≈
      producer.toRootProducer.fraction scale := by
  exact MatchedPhysicalRootCoercivityGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
    producer.toResistanceProducer.toRootProducer scale

theorem MatchedPhysicalExplicitRayMassShellProducer.fraction_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayMassShellProducer trajectory)
    (scale : Nat) :
    (0 : Q') < producer.toRootProducer.fraction scale := by
  exact producer.toResistanceProducer.fraction_pos scale

/-! ## 7. The unconditional entropy compiler leaves only pointwise load decay -/

/-- The smallest physical-mass input on this route: a cofinal pointwise
state-load decay certificate.  Shell cardinality/entropy is supplied by the
literal finite BF4 carrier. -/
structure MatchedPhysicalExplicitRayStateLoadDecayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRayStateLoadDecay : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
      (trajectory.nome_pos scale)

/-- The proved physical-mass entropy count expands pointwise decay into the
mass-shell certificate consumed by the matched route. -/
def MatchedPhysicalExplicitRayStateLoadDecayProducer.toMassShellProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory) :
    MatchedPhysicalExplicitRayMassShellProducer trajectory where
  offRayMassShell := fun scale =>
    (producer.offRayStateLoadDecay scale).toPhysicalMassShellBound

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toResistanceProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory) :
    MatchedPhysicalExplicitRayResistanceProducer trajectory :=
  producer.toMassShellProducer.toResistanceProducer

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toRootProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory) :
    MatchedPhysicalRootCoercivityGapProducer trajectory :=
  producer.toResistanceProducer.toRootProducer

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toResistanceProducer.toCompletedFamily

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory) :
    MatchedPhysicalConditionalVarianceGapProducer trajectory :=
  producer.toResistanceProducer.toConditionalVarianceGapProducer

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale ≈
      producer.toRootProducer.fraction scale := by
  exact MatchedPhysicalRootCoercivityGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
    producer.toResistanceProducer.toRootProducer scale

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.fraction_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale : Nat) :
    (0 : Q') < producer.toRootProducer.fraction scale := by
  exact producer.toResistanceProducer.fraction_pos scale

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.transferPower_norm_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner
        (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector).1)
      (CReal.RCscale
        (((producer.toConditionalVarianceGapProducer.completedGapAt scale).rate *
          (producer.toConditionalVarianceGapProducer.completedGapAt scale).rate) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
          vector.1 vector.1)) := by
  exact transferPower_norm_decay_of_matchedScale
    producer.toConditionalVarianceGapProducer scale n vector

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.autocorrelation_sq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector.1))
      (CReal.RCmul
        (CReal.RCscale
          (((producer.toConditionalVarianceGapProducer.completedGapAt scale).rate *
            (producer.toConditionalVarianceGapProducer.completedGapAt scale).rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
            vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
          vector.1 vector.1)) := by
  exact autocorrelation_sq_decay_of_matchedScale
    producer.toConditionalVarianceGapProducer scale n vector

/-- The minimal state-load route carries the concrete moving-cube channel on
the same completed matched family. -/
def MatchedPhysicalExplicitRayStateLoadDecayProducer.toSameObjectRCChannel
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory) :
    DynamicVacuumSectorSameObjectRCChannel producer.toCompletedFamily :=
  centralPhysicalDynamicMovingCubeRCChannel producer.toCompletedFamily

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.sameObjectRCChannel_zero_isPositive
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        producer.toSameObjectRCChannel scale 0) := by
  exact centralPhysicalDynamicMovingCube_connected_zero_isPositive
    producer.toCompletedFamily scale

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.sameObjectRCChannel_connectedSq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale time : Nat) :
    CReal.RCle
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq
        producer.toSameObjectRCChannel scale time)
      (CReal.RCmul
        (CReal.RCscale
          (((producer.toCompletedFamily.completedGap scale).rate *
            (producer.toCompletedFamily.completedGap scale).rate) ^ time)
          (producer.toSameObjectRCChannel.normSq scale))
        (producer.toSameObjectRCChannel.normSq scale)) := by
  exact centralPhysicalDynamicMovingCube_connectedSq_decay
    producer.toCompletedFamily scale time

theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.sameObjectRCChannel_connectedAutocorrelation_eq_global
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale time : Nat) :
    DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        producer.toSameObjectRCChannel scale time =
      centralPhysicalCutoffCompletedInner
        (producer.toCompletedFamily.nome_pos scale)
        (producer.toCompletedFamily.nome_lt_one scale) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (producer.toCompletedFamily.nome_pos scale)
          (producer.toCompletedFamily.nome_lt_one scale) 0 time
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (producer.toSameObjectRCChannel.vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (producer.toSameObjectRCChannel.vectorAt scale).1) := by
  exact DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_eq_global
    producer.toSameObjectRCChannel scale time

/-- An explicit rationalization certificate exposes the concrete state-load
channel through the downstream singleton-observable interface. -/
def MatchedPhysicalExplicitRayStateLoadDecayProducer.toObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate) :
    DynamicVacuumSectorObservablePin producer.toCompletedFamily :=
  rationalization.toObservablePin rate_pos

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toPhysicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate) :
    PhysicalSeparator :=
  (producer.toObservablePin rationalization rate_pos).toPhysicalSeparator

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toPhysicalGapFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate)
    (band : DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily) :
    PhysicalGapFloor
      (producer.toPhysicalSeparator rationalization rate_pos)
      producer.toCompletedFamily.transferSpacing.spacing
      producer.toCompletedFamily.transferSpacing.spacing_pos :=
  (producer.toObservablePin rationalization rate_pos).toPhysicalGapFloor band

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toRegScalingBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate)
    (band : DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily) :
    RegScalingBand :=
  (producer.toObservablePin rationalization rate_pos).toRegScalingBand band

def MatchedPhysicalExplicitRayStateLoadDecayProducer.toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate)
    (band : DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily) :
    ContinuumGapTheorem :=
  band.toContinuumGapTheorem

def MatchedPhysicalExplicitRayStateLoadDecayProducer.continuumZeroTime_isPositive
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (limit : ScheduledRCContinuumLimit producer.toSameObjectRCChannel)
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      producer.toSameObjectRCChannel) :
    RCIsPositive (limit.continuumConnectedAutocorrelation 0) :=
  limit.continuumConnectedAutocorrelation_zero_isPositive uniform

def MatchedPhysicalExplicitRayStateLoadDecayProducer.continuumConnectedAutocorrelationSq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (limit : ScheduledRCContinuumLimit producer.toSameObjectRCChannel)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit
      producer.toCompletedFamily)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (limit.continuumConnectedAutocorrelation time)
        (limit.continuumConnectedAutocorrelation time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (ratePower.limitRepresentative time))
          (limit.continuumConnectedAutocorrelation 0))
        (limit.continuumConnectedAutocorrelation 0)) := by
  exact rawMovingCubeContinuumConnectedAutocorrelationSq_decay
    producer.toCompletedFamily limit ratePower time

def MatchedPhysicalExplicitRayStateLoadDecayProducer.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    {raw : MovingCubeRawScheduledRepresentativeVariation producer.toCompletedFamily}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {B : RawMovingCubeProjectiveOSCorrelationHandoff
      producer.toCompletedFamily raw H W.measureLinked}
    (C : RawMovingCubeWilsonMatrixCoefficientPin
      producer.toCompletedFamily raw H W B)
    (time : Nat) :
    ScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (rawMovingCubeContinuumLimitOfVariation producer.toCompletedFamily raw)
        time =
      W.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow W.timeTranslation.op time C.gapState) C.gapState :=
  C.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient time

/-! ## 8. Split the remaining decay into weight and path mechanisms -/

/-- A factored analytic input for the same route: stationary-weight decay and
canonical-path resistance growth are kept as separate witnessed mechanisms. -/
structure MatchedPhysicalExplicitRayFactorizedDecayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  offRayFactorized : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay
      (trajectory.nome_pos scale)

/-- Rejoin the two factored mechanisms through the checked product compiler. -/
def MatchedPhysicalExplicitRayFactorizedDecayProducer.toStateLoadDecayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory) :
    MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory where
  offRayStateLoadDecay := fun scale =>
    (producer.offRayFactorized scale).toPhysicalMassStateLoadDecay

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toResistanceProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory) :
    MatchedPhysicalExplicitRayResistanceProducer trajectory :=
  producer.toStateLoadDecayProducer.toResistanceProducer

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toRootProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory) :
    MatchedPhysicalRootCoercivityGapProducer trajectory :=
  producer.toResistanceProducer.toRootProducer

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toResistanceProducer.toCompletedFamily

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory) :
    MatchedPhysicalConditionalVarianceGapProducer trajectory :=
  producer.toResistanceProducer.toConditionalVarianceGapProducer

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale ≈
      producer.toRootProducer.fraction scale := by
  exact MatchedPhysicalRootCoercivityGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
    producer.toResistanceProducer.toRootProducer scale

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.fraction_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale : Nat) :
    (0 : Q') < producer.toRootProducer.fraction scale := by
  exact producer.toResistanceProducer.fraction_pos scale

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.transferPower_norm_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner
        (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector).1)
      (CReal.RCscale
        (((producer.toConditionalVarianceGapProducer.completedGapAt scale).rate *
          (producer.toConditionalVarianceGapProducer.completedGapAt scale).rate) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
          vector.1 vector.1)) := by
  exact transferPower_norm_decay_of_matchedScale
    producer.toConditionalVarianceGapProducer scale n vector

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.autocorrelation_sq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 n vector.1))
      (CReal.RCmul
        (CReal.RCscale
          (((producer.toConditionalVarianceGapProducer.completedGapAt scale).rate *
            (producer.toConditionalVarianceGapProducer.completedGapAt scale).rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
            vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
          vector.1 vector.1)) := by
  exact autocorrelation_sq_decay_of_matchedScale
    producer.toConditionalVarianceGapProducer scale n vector

/-- The factorized route carries the same concrete moving-cube channel after
its checked product compiler rejoins the state-load certificate. -/
def MatchedPhysicalExplicitRayFactorizedDecayProducer.toSameObjectRCChannel
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory) :
    DynamicVacuumSectorSameObjectRCChannel producer.toCompletedFamily :=
  centralPhysicalDynamicMovingCubeRCChannel producer.toCompletedFamily

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.sameObjectRCChannel_zero_isPositive
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        producer.toSameObjectRCChannel scale 0) := by
  exact centralPhysicalDynamicMovingCube_connected_zero_isPositive
    producer.toCompletedFamily scale

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.sameObjectRCChannel_connectedSq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale time : Nat) :
    CReal.RCle
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq
        producer.toSameObjectRCChannel scale time)
      (CReal.RCmul
        (CReal.RCscale
          (((producer.toCompletedFamily.completedGap scale).rate *
            (producer.toCompletedFamily.completedGap scale).rate) ^ time)
          (producer.toSameObjectRCChannel.normSq scale))
        (producer.toSameObjectRCChannel.normSq scale)) := by
  exact centralPhysicalDynamicMovingCube_connectedSq_decay
    producer.toCompletedFamily scale time

theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.sameObjectRCChannel_connectedAutocorrelation_eq_global
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale time : Nat) :
    DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        producer.toSameObjectRCChannel scale time =
      centralPhysicalCutoffCompletedInner
        (producer.toCompletedFamily.nome_pos scale)
        (producer.toCompletedFamily.nome_lt_one scale) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (producer.toCompletedFamily.nome_pos scale)
          (producer.toCompletedFamily.nome_lt_one scale) 0 time
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (producer.toSameObjectRCChannel.vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (producer.toSameObjectRCChannel.vectorAt scale).1) := by
  exact DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_eq_global
    producer.toSameObjectRCChannel scale time

/-- The factorized route reaches the same observable interface once its
explicit rationalization certificate and strict-rate witness are supplied. -/
def MatchedPhysicalExplicitRayFactorizedDecayProducer.toObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate) :
    DynamicVacuumSectorObservablePin producer.toCompletedFamily :=
  rationalization.toObservablePin rate_pos

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toPhysicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate) :
    PhysicalSeparator :=
  (producer.toObservablePin rationalization rate_pos).toPhysicalSeparator

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toPhysicalGapFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate)
    (band : DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily) :
    PhysicalGapFloor
      (producer.toPhysicalSeparator rationalization rate_pos)
      producer.toCompletedFamily.transferSpacing.spacing
      producer.toCompletedFamily.transferSpacing.spacing_pos :=
  (producer.toObservablePin rationalization rate_pos).toPhysicalGapFloor band

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toRegScalingBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate)
    (band : DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily) :
    RegScalingBand :=
  (producer.toObservablePin rationalization rate_pos).toRegScalingBand band

def MatchedPhysicalExplicitRayFactorizedDecayProducer.toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (rationalization :
      DynamicVacuumSectorSameObjectRationalization
        producer.toSameObjectRCChannel)
    (rate_pos : ∀ scale,
      (0 : Q') < (producer.toCompletedFamily.completedGap scale).rate)
    (band : DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily) :
    ContinuumGapTheorem :=
  band.toContinuumGapTheorem

def MatchedPhysicalExplicitRayFactorizedDecayProducer.continuumZeroTime_isPositive
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (limit : ScheduledRCContinuumLimit producer.toSameObjectRCChannel)
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      producer.toSameObjectRCChannel) :
    RCIsPositive (limit.continuumConnectedAutocorrelation 0) :=
  limit.continuumConnectedAutocorrelation_zero_isPositive uniform

def MatchedPhysicalExplicitRayFactorizedDecayProducer.continuumConnectedAutocorrelationSq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (limit : ScheduledRCContinuumLimit producer.toSameObjectRCChannel)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit
      producer.toCompletedFamily)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (limit.continuumConnectedAutocorrelation time)
        (limit.continuumConnectedAutocorrelation time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (ratePower.limitRepresentative time))
          (limit.continuumConnectedAutocorrelation 0))
        (limit.continuumConnectedAutocorrelation 0)) := by
  exact rawMovingCubeContinuumConnectedAutocorrelationSq_decay
    producer.toCompletedFamily limit ratePower time

def MatchedPhysicalExplicitRayFactorizedDecayProducer.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    {raw : MovingCubeRawScheduledRepresentativeVariation producer.toCompletedFamily}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {B : RawMovingCubeProjectiveOSCorrelationHandoff
      producer.toCompletedFamily raw H W.measureLinked}
    (C : RawMovingCubeWilsonMatrixCoefficientPin
      producer.toCompletedFamily raw H W B)
    (time : Nat) :
    ScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (rawMovingCubeContinuumLimitOfVariation producer.toCompletedFamily raw)
        time =
      W.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow W.timeTranslation.op time C.gapState) C.gapState :=
  C.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient time

/-! ## 9. Occupied-shell obstruction at the matched boundary -/

/-- Every occupied physical-mass shell forces the matched state-load envelope
to pay at least one unit.  This is inherited from the exact finite row
identity, not an additional analytic assumption. -/
theorem MatchedPhysicalExplicitRayStateLoadDecayProducer.one_le_envelope_of_shell_member
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayStateLoadDecayProducer trajectory)
    (scale K : Nat) (hK :
      (producer.offRayStateLoadDecay scale).start ≤ K)
    (source target shell state : Nat)
    (hshell : shell <
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        (trajectory.nome scale)
        (Q'.le_of_lt (trajectory.nome_pos scale)) K)
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        (trajectory.nome scale)
        (Q'.le_of_lt (trajectory.nome_pos scale)) K source target shell) :
    (1 : Q') ≤
      (producer.offRayStateLoadDecay scale).loadAmplitude *
        (producer.offRayStateLoadDecay scale).loadRatio ^ shell := by
  exact
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.one_le_decayEnvelope_of_shell_member
      (producer.offRayStateLoadDecay scale) K hK source target shell state
      hshell hstate

/-- The same occupied-shell obstruction after the stationary-weight/path
resistance factorization. -/
theorem MatchedPhysicalExplicitRayFactorizedDecayProducer.one_le_envelope_of_shell_member
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalExplicitRayFactorizedDecayProducer trajectory)
    (scale K : Nat) (hK :
      (producer.offRayFactorized scale).start ≤ K)
    (source target shell state : Nat)
    (hshell : shell <
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        (trajectory.nome scale)
        (Q'.le_of_lt (trajectory.nome_pos scale)) K)
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        (trajectory.nome scale)
        (Q'.le_of_lt (trajectory.nome_pos scale)) K source target shell) :
    (1 : Q') ≤
      ((producer.offRayFactorized scale).stationaryAmplitude *
          (producer.offRayFactorized scale).resistanceAmplitude) *
        ((producer.offRayFactorized scale).stationaryRatio *
          (producer.offRayFactorized scale).resistanceRatio) ^ shell := by
  exact
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay.one_le_factorizedEnvelope_of_shell_member
      (producer.offRayFactorized scale) K hK source target shell state
      hshell hstate

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
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.toConditionalVarianceGapProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayResistanceProducer.fraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMomentProducer.toResistanceProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMomentProducer.toRootProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMomentProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMomentProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMassShellProducer.toResistanceProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMassShellProducer.toRootProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMassShellProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMassShellProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMassShellProducer.fraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayMassShellProducer.toConditionalVarianceGapProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toMassShellProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toResistanceProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toRootProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.fraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toConditionalVarianceGapProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.transferPower_norm_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.autocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toSameObjectRCChannel
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.sameObjectRCChannel_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.sameObjectRCChannel_connectedSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.sameObjectRCChannel_connectedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toObservablePin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toPhysicalSeparator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toPhysicalGapFloor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toRegScalingBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.continuumZeroTime_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.continuumConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toStateLoadDecayProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toResistanceProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toRootProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.fraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toConditionalVarianceGapProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.transferPower_norm_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.autocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toSameObjectRCChannel
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.sameObjectRCChannel_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.sameObjectRCChannel_connectedSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.sameObjectRCChannel_connectedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toObservablePin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toPhysicalSeparator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toPhysicalGapFloor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toRegScalingBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.continuumZeroTime_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.continuumConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayStateLoadDecayProducer.one_le_envelope_of_shell_member
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFExplicitRayRootCompiler.MatchedPhysicalExplicitRayFactorizedDecayProducer.one_le_envelope_of_shell_member
