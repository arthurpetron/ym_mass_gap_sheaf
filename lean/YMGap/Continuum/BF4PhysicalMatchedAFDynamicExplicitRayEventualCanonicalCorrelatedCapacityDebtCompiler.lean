/-
# Correlated matched canonical capacity-debt persistence

The separated support-proxy route asks for routed-load variation, supported-
kernel variation, and a uniform positive kernel floor.  That is sufficient
but stronger than the exact edge-capacity inequality: a small conditional
kernel is harmless when the routed load on the same edge is comparably small.

At each matched physical scale and eventual-tail offset, this module forms the
literal same-edge normalized debt

  shared ray floor * routed load / (half * conditional kernel),

using zero only to totalize the ambient function when the denominator is not
positive.  On the exact vacuum-sector carrier, positive load already implies
positive conditional kernel.  Debt at most one therefore proves the exact
edge-capacity field without passing through a separated proxy or a uniform
kernel floor.

The located maximum over the exact pair carrier is controlled by one summable
pointwise envelope along the already constructed canonical pair recodings.
Computed prefix-plus-tail closure then constructs the same matched local
producer and hence the same completed carrier, transfer, and vacuum family.

No envelope, tail allowance, or initial slack is inhabited here.  No physical
strength band, observable pin, continuum Yang--Mills theory, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem q_nonpos_of_not_pos_local
    (value : Q') (hnot : ¬ (0 : Q') < value) :
    value <= (0 : Q') := by
  show value.num * (1 : Int) <= (0 : Int) * (value.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum => hnot (CReal.pos_of_num_pos hnum))

/-! ## 1. Exact correlated same-edge debt -/

/-- Normalize the exact routed load by the half conditional-kernel capacity
on the same ordered pair. -/
def matchedEventualCanonicalRoutedCapacityDebtOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Q' :=
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0 pair.1 pair.2
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos
      (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalRoutedLoadOnPair
          trajectory transitionStart physicalScale offset pair)
      capacity hcapacity
  else
    0

theorem matchedEventualCanonicalRoutedCapacityDebtOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    (0 : Q') <=
      matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale offset pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  have hload : (0 : Q') <=
      matchedEventualCanonicalRoutedLoadOnPair
        trajectory transitionStart physicalScale offset pair :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
      (matchedEventualCanonicalRoutingAt
        trajectory transitionStart physicalScale offset)
      hmembers.1 pair.2
  unfold matchedEventualCanonicalRoutedCapacityDebtOnPair
  dsimp only
  by_cases hcapacity : (0 : Q') <
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + offset) 0 pair.1 pair.2
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
        hload)
      (Q'.le_of_lt (Q'.recipPos_pos _ hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

/-- On the literal carrier, correlated debt at most one proves the exact
canonical edge-capacity inequality. -/
theorem matchedEventualCanonicalRoutedCapacityDebtOnPair_le_one_implies_edge_capacity
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset)
    (hdebt :
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset pair <=
        (1 : Q')) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalRoutedLoadOnPair
          trajectory transitionStart physicalScale offset pair <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + offset) 0 pair.1 pair.2 := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  let load := matchedEventualCanonicalRoutedLoadOnPair
    trajectory transitionStart physicalScale offset pair
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0 pair.1 pair.2
  have hloadNonnegative : (0 : Q') <= load :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
      (matchedEventualCanonicalRoutingAt
        trajectory transitionStart physicalScale offset)
      hmembers.1 pair.2
  by_cases hload : (0 : Q') < load
  · have hkernel : (0 : Q') <
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + offset) 0 pair.1 pair.2 :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale offset)
        hmembers.1 pair.2 hload
    have hcapacity : (0 : Q') < capacity :=
      Q'.mul_pos (by decide) hkernel
    have hdebt' : Q'.divPos
          (matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale * load)
          capacity hcapacity <= (1 : Q') := by
      unfold matchedEventualCanonicalRoutedCapacityDebtOnPair at hdebt
      change (if h : (0 : Q') < capacity then
          Q'.divPos
            (matchedEventualCanonicalSupportSharedFloor
                trajectory transitionStart physicalScale * load)
            capacity h
        else 0) <= (1 : Q') at hdebt
      rw [dif_pos hcapacity] at hdebt
      exact hdebt
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ capacity
      hdebt' (Q'.le_of_lt hcapacity)
    change
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale * load <= capacity
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (Q'.divPos_mul_eqv
          (matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale * load)
          capacity hcapacity))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.one_mul_eqv capacity)))
  · have hloadNonpositive : load <= (0 : Q') :=
      q_nonpos_of_not_pos_local load hload
    have hloadZero : load ≈ (0 : Q') :=
      Q'.eqv_of_le_le hloadNonpositive hloadNonnegative
    change
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale * load <= capacity
    exact Q'.le_trans' _ (0 : Q') _
      (Q'.le_of_eqv
        (Q'.eqv_trans _
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * 0) _
          (Q'.mul_eqv_congr_left
            (matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale)
            load 0 hloadZero)
          (Q'.mul_zero_eqv _)))
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg
        (centralPhysicalFiniteConditionalKernel_nonnegative
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + offset) 0 pair.1 pair.2))

/-! ## 2. One dynamic maximum on the exact carrier -/

def matchedEventualCanonicalRoutedCapacityDebtMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalRoutedCapacityDebtOnPair
      trajectory transitionStart physicalScale offset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset)

theorem matchedEventualCanonicalRoutedCapacityDebtOnPair_le_maximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale offset pair <=
      matchedEventualCanonicalRoutedCapacityDebtMaximum
        trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalRoutedCapacityDebtMaximum
  exact le_listQMaxZero_of_mem _ _ hpair

/-- The sole analytic envelope on the correlated canonical route. -/
structure MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  current_le_next : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1)
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale offset pair) +
          variation offset
  next_le_current : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair) +
          variation offset

def MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope.toMaximumVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.DynamicFiniteMaximumVariation
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale) where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  value_nonnegative :=
    matchedEventualCanonicalRoutedCapacityDebtOnPair_nonnegative
      trajectory transitionStart physicalScale
  currentToNext :=
    matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale
  currentToNext_mem :=
    matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale
  current_le_next := data.current_le_next
  nextToCurrent :=
    matchedEventualCanonicalNextPairToCurrent
      trajectory transitionStart physicalScale
  nextToCurrent_mem := fun offset pair _ =>
    matchedEventualCanonicalNextPairToCurrent_mem
      trajectory transitionStart physicalScale offset pair
  next_le_current := data.next_le_current

def matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    SummableRationalStepVariation
      (matchedEventualCanonicalRoutedCapacityDebtMaximum
        trajectory transitionStart physicalScale) := by
  change SummableRationalStepVariation
    (fun offset => listQMaxZero
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale offset))
  exact data.toMaximumVariation.toSummableRationalStepVariation

/-! ## 3. Prefix-tail persistence and contraction to the matched family -/

theorem matchedEventualCanonicalRoutedCapacityDebtMaximum_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              envelope)
            tailAllowance <=
        (1 : Q'))
    (offset : Nat) :
    matchedEventualCanonicalRoutedCapacityDebtMaximum
        trajectory transitionStart physicalScale offset <= (1 : Q') := by
  let variation :=
    matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope
  let normalized := budgetedVariation
    variation tailAllowance tailAllowance_pos
  exact normalized.le_of_initial_add_totalBudget_le
    (prefixTailTotalBudget_pos variation tailAllowance tailAllowance_pos)
    (budgetedTailControl_rate_totalBudget
      variation tailAllowance tailAllowance_pos)
    initial_closure offset

/-- One correlated envelope family, its positive tail allowances, and the
computed initial slack construct the exact matched local capacity/product
producer directly, without a separated proxy or uniform kernel floor. -/
def matchedEventualCanonicalCorrelatedCapacityDebtLocalProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (envelope : forall physicalScale,
      MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (envelope physicalScale))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    trajectory.LocalProducer where
  rayCapacity := fun physicalScale =>
    eventualExplicitRayCapacity trajectory transitionStart physicalScale
  transitionProduct := fun physicalScale => {
    routing := fun K _hK =>
      canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale)) K
    product := fun K hK => by
      rw [eventualExplicitRayCapacity_start] at hK
      refine {
        edge_capacity := fun source hsource target htarget => ?_
      }
      let offset := K - transitionStart physicalScale
      have hK_eq : transitionStart physicalScale + offset = K :=
        Nat.add_sub_of_le hK
      have hpair : (source, target) ∈
          matchedEventualCanonicalVacuumSectorPairs
            trajectory transitionStart physicalScale offset := by
        unfold matchedEventualCanonicalVacuumSectorPairs
        rw [hK_eq]
        exact (mem_cartesian_iff _ _ (source, target)).mpr
          ⟨hsource, htarget⟩
      have hdebt :
          matchedEventualCanonicalRoutedCapacityDebtOnPair
              trajectory transitionStart physicalScale offset
              (source, target) <= (1 : Q') :=
        Q'.le_trans' _ _ _
          (matchedEventualCanonicalRoutedCapacityDebtOnPair_le_maximum
            trajectory transitionStart physicalScale offset
            (source, target) hpair)
          (matchedEventualCanonicalRoutedCapacityDebtMaximum_le_one
            (envelope physicalScale)
            (tailAllowance physicalScale)
            (tailAllowance_pos physicalScale)
            (initial_closure physicalScale) offset)
      change
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale *
            centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
              (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
                (trajectory.nome physicalScale)
                (Q'.le_of_lt (trajectory.nome_pos physicalScale)) K)
              (source, target) <=
          HalfPow.half *
            centralPhysicalFiniteConditionalKernel
              (trajectory.nome physicalScale)
              (Q'.le_of_lt (trajectory.nome_pos physicalScale))
              K 0 source target
      rw [← hK_eq]
      change
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale *
            matchedEventualCanonicalRoutedLoadOnPair
              trajectory transitionStart physicalScale offset
              (source, target) <=
          HalfPow.half *
            centralPhysicalFiniteConditionalKernel
              (trajectory.nome physicalScale)
              (Q'.le_of_lt (trajectory.nome_pos physicalScale))
              (transitionStart physicalScale + offset) 0 source target
      exact
        matchedEventualCanonicalRoutedCapacityDebtOnPair_le_one_implies_edge_capacity
          trajectory transitionStart physicalScale offset
          (source, target) hpair hdebt
  }

/-- The correlated route reaches the same completed carrier, transfer, and
vacuum-complement family as the separated route. -/
def matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (envelope : forall physicalScale,
      MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (envelope physicalScale))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    DynamicVacuumSectorCompletedFamily 0 :=
  trajectory.toCompletedFamily
    (matchedEventualCanonicalCorrelatedCapacityDebtLocalProducer
      trajectory transitionStart envelope tailAllowance
      tailAllowance_pos initial_closure)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.matchedEventualCanonicalRoutedCapacityDebtOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.matchedEventualCanonicalRoutedCapacityDebtOnPair_le_one_implies_edge_capacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope.toMaximumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.matchedEventualCanonicalRoutedCapacityDebtMaximum_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.matchedEventualCanonicalCorrelatedCapacityDebtLocalProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamily
