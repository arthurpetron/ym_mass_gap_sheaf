/-
# Eventual canonical capacity debt on the exact matched explicit ray

After finite prefixes are removed cofinally, the remaining canonical
transition-product question is an eventual scalar inequality.  Unfolding the
exact finite minimum inside every variation term is needlessly expensive and
obscures the analytic target.  This module uses a positive rational lower
proxy whose comparison to that exact minimum remains an explicit proof field.

At a fixed nome, normalize the unchanged shared explicit-ray floor by the
positive proxy.  Debt at most one pays the proxy, and the proxy comparison
pays the exact canonical routed margin.  Along a chosen eventual tail at each
matched physical scale, summable two-sided variation of this debt, a total
variation budget, and one initial-slack inequality therefore construct every
later exact Boolean check.

The proxy is not a different observable: it cannot be consumed without its
pointwise lower-bound proof into the exact margin built from the same routing,
load, conditional kernel, ray capacity, nome, and cutoff.  The resulting
producer contracts through the existing matched completed carrier, transfer,
vacuum complement, strength law, and same-object observable interface.

No proxy, variation, budget, or slack family is inhabited here.  No physical
strength band, observable pin, projective OS/GNS handoff, continuum
Yang--Mills theory, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A light fixed-nome normalized debt -/

/-- Normalize the unchanged shared ray floor by a supplied positive lower
proxy.  The exact-margin comparison is deliberately kept outside this term. -/
def fixedNomeFiniteCapacityDebt
    {w : Q'} {hw : (0 : Q') < w}
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (marginLower : Nat -> Q')
    (marginLower_pos : forall K, (0 : Q') < marginLower K)
    (K : Nat) : Q' :=
  Q'.divPos (HalfPow.half * rayCapacity.delta)
    (marginLower K) (marginLower_pos K)

theorem fixedNomeFiniteCapacityDebt_pos
    {w : Q'} {hw : (0 : Q') < w}
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (marginLower : Nat -> Q')
    (marginLower_pos : forall K, (0 : Q') < marginLower K)
    (K : Nat) :
    (0 : Q') <
      fixedNomeFiniteCapacityDebt rayCapacity marginLower marginLower_pos K := by
  unfold fixedNomeFiniteCapacityDebt
  exact Q'.divPos_pos _ _ (marginLower_pos K)
    (Q'.mul_pos (by decide) rayCapacity.delta_pos)

/-- Debt at most one reconstructs the unnormalized shared-floor comparison
against the supplied positive proxy. -/
theorem sharedFloor_le_marginLower_of_debt_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (marginLower : Nat -> Q')
    (marginLower_pos : forall K, (0 : Q') < marginLower K)
    (K : Nat)
    (hdebt :
      fixedNomeFiniteCapacityDebt
        rayCapacity marginLower marginLower_pos K <= (1 : Q')) :
    HalfPow.half * rayCapacity.delta <= marginLower K := by
  let margin := marginLower K
  have hmargin : (0 : Q') < margin := marginLower_pos K
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ margin hdebt
    (Q'.le_of_lt hmargin)
  have hrecover :
      fixedNomeFiniteCapacityDebt
          rayCapacity marginLower marginLower_pos K * margin ≈
        HalfPow.half * rayCapacity.delta := by
    unfold fixedNomeFiniteCapacityDebt
    exact Q'.divPos_mul_eqv
      (HalfPow.half * rayCapacity.delta) margin hmargin
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hrecover)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.one_mul_eqv margin)))

/-! ## 2. The matched eventual proxy and debt stream -/

/-- One observable-connected positive lower proxy for every offset beyond a
chosen transition start at every physical scale. -/
structure MatchedEventualCanonicalMarginLowerProxy
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) : Type 1 where
  marginLower : Nat -> Nat -> Q'
  marginLower_pos : forall scale offset,
    (0 : Q') < marginLower scale offset
  marginLower_le_exact : forall scale offset,
    marginLower scale offset <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
          (trajectory.nome scale)
          (Q'.le_of_lt (trajectory.nome_pos scale))
          (transitionStart scale + offset))

/-- The exact matched shared floor divided by the same-cutoff proxy. -/
def matchedEventualCanonicalCapacityDebt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    (proxy :
      MatchedEventualCanonicalMarginLowerProxy trajectory transitionStart)
    (scale offset : Nat) : Q' :=
  fixedNomeFiniteCapacityDebt
    (eventualExplicitRayCapacity trajectory transitionStart scale)
    (proxy.marginLower scale)
    (proxy.marginLower_pos scale)
    offset

theorem matchedEventualCanonicalCapacityDebt_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    (proxy :
      MatchedEventualCanonicalMarginLowerProxy trajectory transitionStart)
    (scale offset : Nat) :
    (0 : Q') < matchedEventualCanonicalCapacityDebt proxy scale offset :=
  fixedNomeFiniteCapacityDebt_pos
    (eventualExplicitRayCapacity trajectory transitionStart scale)
    (proxy.marginLower scale) (proxy.marginLower_pos scale) offset

/-! ## 3. Summable persistence constructs every eventual check -/

/-- At every physical scale, one correlated proxy plus summable two-sided
cutoff variation and an initial total-budget slack keep the normalized debt
below one throughout the chosen cofinal tail. -/
structure MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
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
  budget : Nat -> Q'
  budget_pos : forall scale, (0 : Q') < budget scale
  budget_from_zero : forall scale,
    (debtVariation scale).tailControl.tailRate (budget scale) = 0
  initial_closure : forall scale,
    matchedEventualCanonicalCapacityDebt proxy scale 0 + budget scale <=
      (1 : Q')

namespace MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer

theorem debt_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
        trajectory)
    (scale offset : Nat) :
    matchedEventualCanonicalCapacityDebt producer.proxy scale offset <=
      (1 : Q') :=
  (producer.debtVariation scale).le_of_initial_add_totalBudget_le
    (producer.budget_pos scale)
    (producer.budget_from_zero scale)
    (producer.initial_closure scale)
    offset

/-- Summable debt persistence discharges the exact eventual Boolean family.
The final comparison returns explicitly to the exact canonical finite margin. -/
def toEventualCanonicalCapacityCheckProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
        trajectory) :
    MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
      trajectory where
  transitionStart := producer.transitionStart
  capacityCheck := fun scale => {
    check_success := by
      intro K hK
      rw [eventualExplicitRayCapacity_start] at hK
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hK
      apply adaptiveFiniteCapacityMarginCheck_complete
      exact Q'.le_trans' _ _ _
        (sharedFloor_le_marginLower_of_debt_le_one
          (eventualExplicitRayCapacity
            trajectory producer.transitionStart scale)
          (producer.proxy.marginLower scale)
          (producer.proxy.marginLower_pos scale)
          offset
          (producer.debt_le_one scale offset))
        (producer.proxy.marginLower_le_exact scale offset)
  }

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
        trajectory) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toEventualCanonicalCapacityCheckProducer.toCompletedFamily

def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
        trajectory) :
    DynamicVacuumSectorNormalizedStrengthLaw producer.toCompletedFamily :=
  producer.toEventualCanonicalCapacityCheckProducer.toNormalizedStrengthLaw

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorStrengthBand producer.toNormalizedStrengthLaw

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
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
      MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer
        trajectory) : Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

end MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.fixedNomeFiniteCapacityDebt_pos
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.sharedFloor_le_marginLower_of_debt_le_one
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.matchedEventualCanonicalCapacityDebt_pos
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer.debt_le_one
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer.toEventualCanonicalCapacityCheckProducer
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer.toCompletedFamily
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer.toNormalizedStrengthLaw
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer.toPhysicalRateBand
