/-
# Explicit ray capacity on the exact matched BF4/AF trajectory

The selected-term compiler previously exposed two serial local obligations:
an arbitrary-nome raw-row ceiling and the adaptive transition product at the
capacity compiled from that ceiling.  The degree-thirteen face envelope now
constructs the first obligation at every rational `0 < w < 1`.

This module installs that construction at the literal matched block weight

  blockedWeight family (trajectory.coupling scale)

and contracts the exact matched local frontier to one dependent field: the
adaptive off-ray transition product at the resulting explicit ray capacity.
Every downstream carrier, transfer, vacuum complement, strength law, and
observable interface is the existing one on the same matched nome and physical
spacing.  Nothing is relabelled from the fixed `1/400` anchor.

The explicit ceiling is nome-dependent and may grow as the nome approaches
one.  Thus this module proves neither a uniform physical strength band nor a
continuum mass gap.  It does not inhabit the remaining transition-product
extension, same-object observable pin, projective OS/GNS handoff, continuum
Yang--Mills theory, or Clay conclusion.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler

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
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling

/-! ## 1. Inhabit the exact matched selected-term ray producer -/

/-- At every scale, install the explicit selected-term row ceiling at the
literal matched nome. -/
def explicitSelectedTermRayProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    MatchedPhysicalDynamicSelectedTermRayProducer trajectory where
  selectedTermCeiling := fun scale =>
    explicitSubunitCentralSpinCubeSelectedTermRowCeiling
      (trajectory.nome scale)
      (trajectory.nome_pos scale)
      (trajectory.nome_lt_one scale)

/-- The sole remaining local matched analytic field.  Its capacity index is
definitionally compiled from the explicit arbitrary-nome row ceiling above. -/
abbrev ExplicitTransitionProductExtension
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 :=
  (explicitSelectedTermRayProducer trajectory).TransitionProductExtension

@[simp] theorem explicitSelectedTermRayProducer_start
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) :
    ((explicitSelectedTermRayProducer trajectory).selectedTermCeiling scale).start = 0 :=
  rfl

/-- The exact scale-wise ray capacity obtained from the explicit ceiling is
strictly positive.  No scale-uniform lower bound is asserted. -/
theorem explicitMatchedRayCapacity_delta_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) :
    (0 : Q') <
      (((explicitSelectedTermRayProducer trajectory).toRayCapacityProducer).rayCapacity
        scale).delta :=
  (explicitSelectedTermRayProducer trajectory).toRayCapacityProducer_delta_pos scale

/-! ## 2. Contract any one-field extension to the existing matched path -/

def toLocalProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory) :
    trajectory.LocalProducer :=
  extension.toLocalProducer

def toDynamicFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  extension.toDynamicFamily

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  extension.toCompletedFamily

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw
      (toCompletedFamily extension) :=
  extension.toNormalizedStrengthLaw

@[simp] theorem toDynamicFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory)
    (scale : Nat) :
    (toDynamicFamily extension).nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toDynamicFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory)
    (scale : Nat) :
    (toDynamicFamily extension).transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-! ## 3. Preserve the two independent downstream physical consumers -/

abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory) : Type 1 :=
  DynamicVacuumSectorStrengthBand (toNormalizedStrengthLaw extension)

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory)
    (band : StrengthBand extension) :
    DynamicVacuumSectorPhysicalRateBand (toCompletedFamily extension) :=
  band.toPhysicalRateBand

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (extension : ExplicitTransitionProductExtension trajectory) : Type 1 :=
  DynamicVacuumSectorObservablePin (toCompletedFamily extension)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.explicitSelectedTermRayProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.explicitSelectedTermRayProducer_start
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.explicitMatchedRayCapacity_delta_pos
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toLocalProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toDynamicFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toCompletedFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toNormalizedStrengthLaw
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toDynamicFamily_nome
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toDynamicFamily_spacing
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayCompiler.toPhysicalRateBand
