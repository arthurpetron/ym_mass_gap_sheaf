/-
# Eventual transition-product checks on the exact matched explicit ray

The completed cutoff-limit consumers are cofinal: their ray-capacity input
contains its own starting cutoff.  The explicit arbitrary-nome row ceiling
happens to hold from cutoff zero, but this does not make finite-prefix
transition-product checks mathematically necessary.

This module removes that accidental overconstraint.  Any cofinal ray capacity
can raise its start without changing its positive rational delta or any later
capacity field.  At each matched physical scale we may therefore choose an
eventual cutoff, retain the exact explicit ray constant, and ask for canonical
or adaptive Boolean capacity-check success only beyond that cutoff.

Either eventual producer constructs the existing matched dynamic family,
completed carrier, transfer, vacuum complement, normalized strength law, and
same-object observable interface.  Nome and physical spacing remain
definitionally pinned to the same matched BF4/AF trajectory.

No eventual success family is inhabited here.  Raising the start removes only
a finite prefix; it does not turn pointwise decidability into an asymptotic
estimate.  No strength band, observable pin, projective OS/GNS handoff,
continuum Yang--Mills theory, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

/-! ## 1. Losslessly raise a cofinal ray-capacity start -/

/-- Forget an arbitrary finite prefix while retaining the identical positive
ray constant and every later capacity comparison. -/
def raiseCofinalRayCapacityStart
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (start : Nat) :
    FixedNomeCofinalSpinCubeRayCapacity hw where
  delta := capacity.delta
  delta_pos := capacity.delta_pos
  start := max capacity.start start
  twice_le_return := fun K hK offset hoffset =>
    capacity.twice_le_return K
      (Nat.le_trans (Nat.le_max_left _ _) hK) offset hoffset
  left_spoke := fun K hK offset hoffset =>
    capacity.left_spoke K
      (Nat.le_trans (Nat.le_max_left _ _) hK) offset hoffset
  right_spoke := fun K hK offset hoffset =>
    capacity.right_spoke K
      (Nat.le_trans (Nat.le_max_left _ _) hK) offset hoffset

@[simp] theorem raiseCofinalRayCapacityStart_delta
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (start : Nat) :
    (raiseCofinalRayCapacityStart capacity start).delta = capacity.delta :=
  rfl

@[simp] theorem raiseCofinalRayCapacityStart_start
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (start : Nat) :
    (raiseCofinalRayCapacityStart capacity start).start =
      max capacity.start start :=
  rfl

theorem original_start_le_raised_start
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (start : Nat) :
    capacity.start <= (raiseCofinalRayCapacityStart capacity start).start :=
  Nat.le_max_left _ _

theorem requested_start_le_raised_start
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (start : Nat) :
    start <= (raiseCofinalRayCapacityStart capacity start).start :=
  Nat.le_max_right _ _

/-! ## 2. The exact matched eventual capacity -/

/-- At one physical scale, retain the explicit matched ray delta but begin its
cofinal use only after the requested transition-product cutoff. -/
def eventualExplicitRayCapacity
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) :
    FixedNomeCofinalSpinCubeRayCapacity (trajectory.nome_pos scale) :=
  raiseCofinalRayCapacityStart
    (((explicitSelectedTermRayProducer trajectory).toRayCapacityProducer).rayCapacity
      scale)
    (transitionStart scale)

@[simp] theorem eventualExplicitRayCapacity_delta
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) :
    (eventualExplicitRayCapacity trajectory transitionStart scale).delta =
      (((explicitSelectedTermRayProducer trajectory).toRayCapacityProducer).rayCapacity
        scale).delta :=
  rfl

@[simp] theorem eventualExplicitRayCapacity_start
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) :
    (eventualExplicitRayCapacity trajectory transitionStart scale).start =
      transitionStart scale := by
  change max 0 (transitionStart scale) = transitionStart scale
  exact Nat.max_eq_right (Nat.zero_le _)

theorem eventualExplicitRayCapacity_delta_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) :
    (0 : Q') <
      (eventualExplicitRayCapacity trajectory transitionStart scale).delta :=
  (eventualExplicitRayCapacity trajectory transitionStart scale).delta_pos

/-! ## 3. Eventual adaptive and canonical check producers -/

/-- Choose a cofinal start at every physical scale and, after that start, a
cutoff-dependent routing whose exact finite capacity check succeeds. -/
structure MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  transitionStart : Nat -> Nat
  capacityCheck : forall scale,
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
      (trajectory.nome_pos scale)
      (eventualExplicitRayCapacity trajectory transitionStart scale)

namespace MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer

/-- Eventual exact checks construct the matched local producer directly. -/
def toLocalProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer
        trajectory) :
    trajectory.LocalProducer where
  rayCapacity := fun scale =>
    eventualExplicitRayCapacity trajectory producer.transitionStart scale
  transitionProduct := fun scale =>
    (producer.capacityCheck scale).toAdaptiveConditionalTransitionProduct

def toDynamicFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer
        trajectory) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  trajectory.toDynamicFamily producer.toLocalProducer

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer
        trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  trajectory.toCompletedFamily producer.toLocalProducer

end MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer

/-- The shortest eventual producer fixes the canonical loop-erased routing;
only its exact Boolean check family beyond the chosen cutoff remains. -/
structure MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  transitionStart : Nat -> Nat
  capacityCheck : forall scale,
    FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess
      (trajectory.nome_pos scale)
      (eventualExplicitRayCapacity trajectory transitionStart scale)

namespace MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer

def toAdaptiveProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) :
    MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer
      trajectory where
  transitionStart := producer.transitionStart
  capacityCheck := fun scale =>
    (producer.capacityCheck scale).toAdaptiveCheckSuccess

def toLocalProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) :
    trajectory.LocalProducer :=
  producer.toAdaptiveProducer.toLocalProducer

def toDynamicFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  trajectory.toDynamicFamily producer.toLocalProducer

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  trajectory.toCompletedFamily producer.toLocalProducer

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw producer.toCompletedFamily :=
  trajectory.toNormalizedStrengthLaw producer.toLocalProducer

@[simp] theorem toDynamicFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory)
    (scale : Nat) :
    producer.toDynamicFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

@[simp] theorem toLocalProducer_rayCapacity_delta
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory)
    (scale : Nat) :
    (producer.toLocalProducer.rayCapacity scale).delta =
      (((explicitSelectedTermRayProducer trajectory).toRayCapacityProducer).rayCapacity
        scale).delta :=
  rfl

abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorStrengthBand producer.toNormalizedStrengthLaw

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

end MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.raiseCofinalRayCapacityStart
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.eventualExplicitRayCapacity_delta
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.eventualExplicitRayCapacity_start
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer.toLocalProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.toAdaptiveProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.toCompletedFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.toNormalizedStrengthLaw
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.toLocalProducer_rayCapacity_delta
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.toPhysicalRateBand
