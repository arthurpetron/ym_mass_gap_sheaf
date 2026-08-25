/-
# Computed prefix-tail closure for matched eventual canonical debt

The matched eventual canonical-debt compiler previously asked for a positive
total variation budget whose stored tail rate was already zero.  That field is
redundant once a summable two-sided debt variation is known.  For every
physical scale, this module accepts only a positive analytic tail allowance,
asks the variation modulus for its cutoff, computes the exact finite prefix,
and uses their sum as the total budget.

One remaining scalar inequality says that the initial normalized proxy debt
plus this computed budget is at most one.  The generic prefix-tail compiler
then normalizes the modulus and constructs the existing matched persistence
producer.  All downstream data therefore remain tied to the same exact nome,
cofinal ray, routed finite margin, completed carrier, transfer, vacuum
complement, and same-object observable interface.

No lower proxy, summable variation, tail allowance, or initial-slack family is
inhabited here.  No physical strength band, observable pin, projective OS/GNS
handoff, continuum Yang--Mills theory, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler
import YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Per-scale tail data and one computed scalar closure -/

/-- A matched proxy-debt producer whose total budget is computed rather than
supplied.  The analytic input is reduced to summable local variation, one
positive tail allowance at every physical scale, and the resulting exact
initial-slack comparison. -/
structure MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  transitionStart : Nat -> Nat
  proxy : MatchedEventualCanonicalMarginLowerProxy trajectory transitionStart
  debtVariation : forall scale,
    SummableRationalStepVariation
      (matchedEventualCanonicalCapacityDebt proxy scale)
  tailAllowance : Nat -> Q'
  tailAllowance_pos : forall scale, (0 : Q') < tailAllowance scale
  initial_closure : forall scale,
    matchedEventualCanonicalCapacityDebt proxy scale 0 +
        prefixTailTotalBudget
          (debtVariation scale) (tailAllowance scale) <=
      (1 : Q')

namespace MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer

/-- The executable total budget at one physical scale: analytic tail
allowance plus the exact finite prefix selected by its modulus. -/
def totalBudget
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory)
    (scale : Nat) : Q' :=
  prefixTailTotalBudget
    (producer.debtVariation scale) (producer.tailAllowance scale)

theorem totalBudget_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory)
    (scale : Nat) :
    (0 : Q') < producer.totalBudget scale :=
  prefixTailTotalBudget_pos
    (producer.debtVariation scale)
    (producer.tailAllowance scale)
    (producer.tailAllowance_pos scale)

/-! ## 2. Contract the computed data to the existing persistence compiler -/

def toDebtVariationProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory) :
    MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
      trajectory where
  transitionStart := producer.transitionStart
  proxy := producer.proxy
  debtVariation := fun scale =>
    budgetedVariation
      (producer.debtVariation scale)
      (producer.tailAllowance scale)
      (producer.tailAllowance_pos scale)
  budget := producer.totalBudget
  budget_pos := producer.totalBudget_pos
  budget_from_zero := by
    intro scale
    change
      (budgetedTailControl
          (producer.debtVariation scale)
          (producer.tailAllowance scale)
          (producer.tailAllowance_pos scale)).tailRate
        (prefixTailTotalBudget
          (producer.debtVariation scale)
          (producer.tailAllowance scale)) = 0
    exact budgetedTailControl_rate_totalBudget
      (producer.debtVariation scale)
      (producer.tailAllowance scale)
      (producer.tailAllowance_pos scale)
  initial_closure := producer.initial_closure

theorem debt_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory)
    (scale offset : Nat) :
    matchedEventualCanonicalCapacityDebt producer.proxy scale offset <=
      (1 : Q') :=
  producer.toDebtVariationProducer.debt_le_one scale offset

def toEventualCanonicalCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory) :=
  producer.toDebtVariationProducer.toEventualCanonicalCapacityCheckProducer

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toDebtVariationProducer.toCompletedFamily

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw producer.toCompletedFamily :=
  producer.toDebtVariationProducer.toNormalizedStrengthLaw

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-! ## 3. The same two downstream branches remain available -/

abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorStrengthBand producer.toNormalizedStrengthLaw

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

end MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.totalBudget_pos
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.toDebtVariationProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.debt_le_one
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.toEventualCanonicalCapacityCheckProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.toCompletedFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.toNormalizedStrengthLaw
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer.toPhysicalRateBand
