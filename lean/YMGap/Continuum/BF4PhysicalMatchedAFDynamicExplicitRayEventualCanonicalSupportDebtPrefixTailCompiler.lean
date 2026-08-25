/-
# Automatic support proxy for matched eventual canonical debt

The matched prefix-tail compiler still accepted a free positive lower proxy
for the exact canonical routed finite margin.  The existing support-aware BF4
construction already removes that field at arbitrary positive nome and
cutoff.  On the exact canonical routing it takes the conditional-kernel floor
only over positively loaded edges, divides half of that floor by one plus the
literal routed-load maximum, and proves the result is positive and below the
exact finite margin.

This module specializes that construction to every offset beyond every
matched physical transition start.  The resulting lower proxy is therefore
data, not a new analytic hypothesis.  A producer now supplies only summable
variation of this exact support-debt stream, a positive tail allowance, and
the computed initial-slack inequality.  These fields contract through the
same eventual checks, completed carrier, transfer, vacuum complement,
strength law, and same-object observable interface.

No summable variation, tail allowance, or slack family is inhabited here.
No physical strength band, observable pin, projective OS/GNS handoff,
continuum Yang--Mills theory, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Prefix-tail persistence with no free proxy -/

structure MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  transitionStart : Nat -> Nat
  debtVariation : forall scale,
    SummableRationalStepVariation
      (matchedEventualCanonicalSupportCapacityDebt
        trajectory transitionStart scale)
  tailAllowance : Nat -> Q'
  tailAllowance_pos : forall scale, (0 : Q') < tailAllowance scale
  initial_closure : forall scale,
    matchedEventualCanonicalSupportCapacityDebt
          trajectory transitionStart scale 0 +
        prefixTailTotalBudget
          (debtVariation scale) (tailAllowance scale) <=
      (1 : Q')

namespace MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer

/-- Transport compact support-debt variation to the exact debt stream.  The
variation and tail modulus are retained literally; only stream values move
along their kernel-checked rational setoid equality. -/
def exactDebtVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory)
    (scale : Nat) :
    SummableRationalStepVariation
      (matchedEventualCanonicalCapacityDebt
        (matchedEventualCanonicalSupportMarginLowerProxy
          trajectory producer.transitionStart)
        scale) :=
  ofPointwiseEqv
    (producer.debtVariation scale)
    (matchedEventualCanonicalSupportCapacityDebt_eqv_exact
      trajectory producer.transitionStart scale)

def toPrefixTailProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory) :
    MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
      trajectory where
  transitionStart := producer.transitionStart
  proxy := matchedEventualCanonicalSupportMarginLowerProxy
    trajectory producer.transitionStart
  debtVariation := producer.exactDebtVariation
  tailAllowance := producer.tailAllowance
  tailAllowance_pos := producer.tailAllowance_pos
  initial_closure := by
    intro scale
    have hdebt :
        matchedEventualCanonicalCapacityDebt
            (matchedEventualCanonicalSupportMarginLowerProxy
              trajectory producer.transitionStart)
            scale 0 <=
          matchedEventualCanonicalSupportCapacityDebt
            trajectory producer.transitionStart scale 0 :=
      Q'.ge_of_eqv
        (matchedEventualCanonicalSupportCapacityDebt_eqv_exact
          trajectory producer.transitionStart scale 0)
    have hsum := Q'.add_le_add_right _ _
      (prefixTailTotalBudget
        (producer.debtVariation scale)
        (producer.tailAllowance scale)) hdebt
    exact Q'.le_trans' _ _ _ hsum (producer.initial_closure scale)

theorem debt_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory)
    (scale offset : Nat) :
    matchedEventualCanonicalCapacityDebt
        (matchedEventualCanonicalSupportMarginLowerProxy
          trajectory producer.transitionStart)
        scale offset <= (1 : Q') :=
  producer.toPrefixTailProducer.debt_le_one scale offset

def toEventualCanonicalCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory) :=
  producer.toPrefixTailProducer.toEventualCanonicalCapacityCheckProducer

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toPrefixTailProducer.toCompletedFamily

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw producer.toCompletedFamily :=
  producer.toPrefixTailProducer.toNormalizedStrengthLaw

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toCompletedFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorStrengthBand producer.toNormalizedStrengthLaw

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

end MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer.toPrefixTailProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer.exactDebtVariation
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer.debt_le_one
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer.toCompletedFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer.toNormalizedStrengthLaw
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer.toPhysicalRateBand
