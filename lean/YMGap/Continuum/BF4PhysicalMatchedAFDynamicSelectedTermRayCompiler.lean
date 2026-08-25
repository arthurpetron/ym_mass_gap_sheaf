/-
# Selected-term ray capacities on the exact matched BF4/AF trajectory

The exact matched-action dynamic compiler leaves a cofinal spin-ray capacity
and an adaptive off-ray transition product at every physical scale.  A raw
capacity record hides more analytic structure than is necessary: the existing
selected-term theorem already constructs that capacity from one geometric
comparison of the complete positive raw row with its literal zero-boundary
production term.

This module lifts that lossless compiler scale by scale on the exact matched
trajectory.  The sole ray input is now

  rawRow <= ceiling * selectedPhysicalTerm

uniformly over all sufficiently large spin cutoffs, at the literal nome
`blockedWeight family (coupling scale)`.  Its reciprocal is a positive return
floor and half of that return floor is the cofinal ray capacity.  A dependent
one-field extension then asks only for the adaptive conditional transition
product at that exact compiled capacity.

Any inhabitant constructs the same completed matched-action carrier,
transfer, vacuum complement, normalized strength law, and optional
same-object observable path from the preceding module.  No selected-term
ceiling or transition-product extension is inhabited here.  The fixed-anchor
selected-row theorem cannot be reused because its nome is definitionally
`1/400`, not the changing matched block output.

No four-dimensional cubic law, dimensional-transmutation spacing, strength
band, observable pin, projective OS/GNS handoff, continuum Yang--Mills theory,
or Clay conclusion is asserted.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

/-! ## 1. The exact scale-wise selected-term ray producer -/

/-- At every matched physical scale, compare the complete positive spin-cube
raw row with a cutoff-independent multiple of its literal selected physical
production term.  Each field is indexed by the exact matched nome. -/
structure MatchedPhysicalDynamicSelectedTermRayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  selectedTermCeiling : forall scale,
    FixedNomeCofinalSpinCubeSelectedTermRowCeiling
      (trajectory.nome_pos scale)

namespace MatchedPhysicalDynamicSelectedTermRayProducer

/-- Compile each selected-term ceiling through its exact return floor to the
generic scale-wise ray-capacity producer. -/
def toRayCapacityProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory) :
    DynamicSpinCubeOffRayAdaptiveRayCapacityProducer
      trajectory.toAdaptiveScalarTrajectory where
  rayCapacity := fun scale =>
    (producer.selectedTermCeiling scale).toCofinalRayCapacity

/-- The only remaining local analytic field after a selected-term family is
supplied: an adaptive off-ray transition product indexed by the exact ray
capacity compiled from the ceiling at that same scale. -/
abbrev TransitionProductExtension
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory) :
    Type 1 :=
  DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
    producer.toRayCapacityProducer

/-- Reassemble the selected-term ray producer and its dependent one-field
extension into the exact matched local producer. -/
def toLocalProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension) :
    trajectory.LocalProducer :=
  extension.toLocalProducer

/-! ## 2. Contract to the exact matched completed path -/

def toDynamicFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  trajectory.toDynamicFamily extension.toLocalProducer

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension) :
    DynamicVacuumSectorCompletedFamily 0 :=
  trajectory.toCompletedFamily extension.toLocalProducer

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension) :
    DynamicVacuumSectorNormalizedStrengthLaw extension.toCompletedFamily :=
  trajectory.toNormalizedStrengthLaw extension.toLocalProducer

@[simp] theorem toDynamicFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension)
    (scale : Nat) :
    (extension.toDynamicFamily).nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toDynamicFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension)
    (scale : Nat) :
    extension.toDynamicFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-- The compiled ray constant is literally half of the positive reciprocal
return floor generated by the same selected-term ceiling. -/
@[simp] theorem toRayCapacityProducer_delta
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory)
    (scale : Nat) :
    (producer.toRayCapacityProducer.rayCapacity scale).delta =
      Q'.divPos (producer.selectedTermCeiling scale).returnFloor
        2 (by decide) :=
  rfl

theorem toRayCapacityProducer_delta_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory)
    (scale : Nat) :
    (0 : Q') <
      (producer.toRayCapacityProducer.rayCapacity scale).delta :=
  (producer.toRayCapacityProducer.rayCapacity scale).delta_pos

/-! ## 3. Preserve the exact remaining physical consumers -/

abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension) : Type 1 :=
  DynamicVacuumSectorStrengthBand extension.toNormalizedStrengthLaw

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension)
    (band : StrengthBand extension) :
    DynamicVacuumSectorPhysicalRateBand extension.toCompletedFamily :=
  band.toPhysicalRateBand

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalDynamicSelectedTermRayProducer trajectory}
    (extension : producer.TransitionProductExtension) : Type 1 :=
  DynamicVacuumSectorObservablePin extension.toCompletedFamily

end MatchedPhysicalDynamicSelectedTermRayProducer

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toRayCapacityProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toLocalProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toDynamicFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toNormalizedStrengthLaw
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toRayCapacityProducer_delta
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toRayCapacityProducer_delta_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.MatchedPhysicalDynamicSelectedTermRayProducer.toPhysicalRateBand
