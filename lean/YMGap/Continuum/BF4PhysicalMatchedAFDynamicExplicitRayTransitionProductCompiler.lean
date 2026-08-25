/-
# Decidable transition-product frontier on the explicit matched ray

The exact matched BF4/AF ray compiler now supplies a cofinal capacity at every
physical scale.  The remaining local field is the adaptive off-ray transition
product indexed by that dependent capacity.  The arbitrary-nome finite
decision compiler turns this field into scale-wise families of exact Boolean
capacity checks.

Two honest producers are retained.  The adaptive producer may select a
different positive routing at each spin cutoff.  The canonical producer uses
the already constructed loop-erased physical routing and therefore contains
only the assertion that every exact finite check succeeds.  The canonical
producer maps into the adaptive one; conclusions from different routings are
never mixed.

Either producer contracts to the existing matched extension, completed
carrier, transfer, vacuum complement, normalized strength law, strength-band
consumer, and same-object observable interface.  Nome and physical spacing
remain definitionally those of the matched trajectory.

No all-cutoff check family is inhabited here.  Decidability at each finite
cutoff does not prove uniform success.  No strength band, observable pin,
projective OS/GNS handoff, continuum Yang--Mills theory, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision

/-! ## 1. Adaptive and canonical all-check producers -/

/-- At every physical scale, choose a cutoff-dependent routing whose exact
finite capacity check succeeds for the explicit matched ray capacity. -/
structure MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  capacityCheck : forall scale,
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
      (trajectory.nome_pos scale)
      (((explicitSelectedTermRayProducer trajectory).toRayCapacityProducer).rayCapacity
        scale)

namespace MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer

/-- Successful exact finite checks construct the sole matched local extension. -/
def toTransitionProductExtension
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer
        trajectory) :
    ExplicitTransitionProductExtension trajectory where
  transitionProduct := fun scale =>
    (producer.capacityCheck scale).toAdaptiveConditionalTransitionProduct

end MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer

/-- The shorter producer fixes the canonical positive routing and asks only
for success of its exact finite checks at every scale and cutoff. -/
structure MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  capacityCheck : forall scale,
    FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess
      (trajectory.nome_pos scale)
      (((explicitSelectedTermRayProducer trajectory).toRayCapacityProducer).rayCapacity
        scale)

namespace MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer

def toAdaptiveProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) :
    MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer
      trajectory where
  capacityCheck := fun scale =>
    (producer.capacityCheck scale).toAdaptiveCheckSuccess

def toTransitionProductExtension
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) :
    ExplicitTransitionProductExtension trajectory :=
  producer.toAdaptiveProducer.toTransitionProductExtension

/-! ## 2. Preserve the exact matched completed and observable paths -/

def toDynamicFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toDynamicFamily
    producer.toTransitionProductExtension

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toCompletedFamily
    producer.toTransitionProductExtension

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw producer.toCompletedFamily :=
  BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toNormalizedStrengthLaw
    producer.toTransitionProductExtension

@[simp] theorem toDynamicFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory)
    (scale : Nat) :
    producer.toDynamicFamily.nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toDynamicFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory)
    (scale : Nat) :
    producer.toDynamicFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorStrengthBand producer.toNormalizedStrengthLaw

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory)
    (band : StrengthBand producer) :
    DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily :=
  band.toPhysicalRateBand

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

end MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer.toTransitionProductExtension
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toAdaptiveProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toTransitionProductExtension
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toDynamicFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toCompletedFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toNormalizedStrengthLaw
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toDynamicFamily_nome
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toDynamicFamily_spacing
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.toPhysicalRateBand
