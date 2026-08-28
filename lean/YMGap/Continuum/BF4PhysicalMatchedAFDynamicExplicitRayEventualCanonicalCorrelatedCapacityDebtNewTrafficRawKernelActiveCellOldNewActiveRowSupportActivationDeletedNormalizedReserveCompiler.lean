/-
# Normalized debt slack compiles to a literal transported reserve

The transported-reserve frontier is stated in physical capacity units, while
the existing persistence campaign controls a normalized same-edge debt.  This
module proves the exact conversion between those two descriptions.

For an arbitrary positive routing on the later vacuum carrier, normalized
debt recovers the literal capacity use after multiplication by the same half-
kernel denominator.  Hence

  debt + margin <= 1

implies that `margin * half-kernel-capacity` is a literal reserve left by the
transported load.  A second field asks the constructed new-route ceiling to
fit under that same quantity.  The two normalized fields compile directly to
the transported-reserve certificate and then to the all-cutoff observable.

The prefix-plus-tail persistence theorem is also strengthened without adding
an analytic hypothesis: any slack explicitly present in the initial closure
is preserved at every cutoff rather than discarded by contraction to
`debt <= 1`.

No normalized margin family is inhabited here.  No regional tail, completed
gap, continuum limit, continuum Yang--Mills theory, isolated vacuum, or Clay
conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedTransportedReserveCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem cancel_right_add_neg_local (left right : Q') :
    (left + right) + -right ≈ left := by
  refine Q'.eqv_trans _ (left + (right + -right)) _
    (Q'.add_assoc_eqv left right (-right)) ?_
  refine Q'.eqv_trans _ (left + 0) _
    (Q'.add_eqv_congr_left left (right + -right) 0
      (Q'.add_neg_self_eqv right)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' left)

private theorem left_le_sub_of_add_le_local
    {left margin bound : Q'} (h : left + margin <= bound) :
    left <= bound + -margin := by
  have hadd := Q'.add_le_add_right
    (left + margin) bound (-margin) h
  exact Q'.le_trans' _ ((left + margin) + -margin) _
    (Q'.ge_of_eqv (cancel_right_add_neg_local left margin)) hadd

private theorem add_neg_add_right_local (left right : Q') :
    (left + -right) + right ≈ left := by
  refine Q'.eqv_trans _ (left + ((-right) + right)) _
    (Q'.add_assoc_eqv left (-right) right) ?_
  refine Q'.eqv_trans _ (left + 0) _
    (Q'.add_eqv_congr_left left ((-right) + right) 0
      (Q'.neg_add_self_eqv right)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' left)

/-! ## 1. Preserve explicit slack in prefix-plus-tail persistence -/

theorem matchedEventualCanonicalRoutedCapacityDebtMaximum_add_margin_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (margin : Q')
    (initial_closure_with_margin :
      (matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              envelope)
            tailAllowance) + margin <=
        (1 : Q'))
    (offset : Nat) :
    matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale offset + margin <=
      (1 : Q') := by
  let variation :=
    matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope
  let normalized := budgetedVariation
    variation tailAllowance tailAllowance_pos
  have hinitial :
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget variation tailAllowance <=
        (1 : Q') + -margin :=
    left_le_sub_of_add_le_local initial_closure_with_margin
  have hpoint :
      matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale offset <=
        (1 : Q') + -margin :=
    normalized.le_of_initial_add_totalBudget_le
      (prefixTailTotalBudget_pos variation tailAllowance tailAllowance_pos)
      (budgetedTailControl_rate_totalBudget
        variation tailAllowance tailAllowance_pos)
      hinitial offset
  have hadd := Q'.add_le_add_right
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
      trajectory transitionStart physicalScale offset)
    ((1 : Q') + -margin) margin hpoint
  exact Q'.le_trans' _ (((1 : Q') + -margin) + margin) _ hadd
    (Q'.le_of_eqv (add_neg_add_right_local (1 : Q') margin))

theorem matchedEventualCanonicalRoutedCapacityDebtOnPair_add_margin_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (margin : Q')
    (initial_closure_with_margin :
      (matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              envelope)
            tailAllowance) + margin <=
        (1 : Q'))
    (offset : Nat) (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset edge + margin <=
      (1 : Q') := by
  have hmax := matchedEventualCanonicalRoutedCapacityDebtMaximum_add_margin_le_one
    envelope tailAllowance tailAllowance_pos margin
    initial_closure_with_margin offset
  exact Q'.le_trans' _
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
        trajectory transitionStart physicalScale offset + margin) _
    (Q'.add_le_add_right _ _ margin
      (matchedEventualCanonicalRoutedCapacityDebtOnPair_le_maximum
        trajectory transitionStart physicalScale offset edge hedge))
    hmax

/-! ## 2. A normalized arbitrary-routing debt recovers literal use -/

theorem matchedEventualRoutedCapacityDebtOnPairForRouting_mul_capacity_eqv_use
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset))
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
          trajectory transitionStart physicalScale cutoffOffset routing edge *
        (HalfPow.half *
          centralPhysicalFiniteConditionalKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2) ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          routing edge := by
  let load :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
      routing edge
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  let use := matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale * load
  have hmembers := (mem_cartesian_iff _ _ edge).mp hedge
  have hloadNonnegative : (0 : Q') <= load :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
      routing hmembers.1 edge.2
  by_cases hcapacity : (0 : Q') < capacity
  · unfold matchedEventualRoutedCapacityDebtOnPairForRouting
    change (if h : (0 : Q') < capacity then
        Q'.divPos use capacity h else 0) * capacity ≈ use
    rw [dif_pos hcapacity]
    exact Q'.divPos_mul_eqv use capacity hcapacity
  · have hloadNotPositive : ¬ (0 : Q') < load := by
      intro hload
      have hkernel : (0 : Q') <
          centralPhysicalFiniteConditionalKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2 :=
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
          routing hmembers.1 edge.2 hload
      exact hcapacity (Q'.mul_pos (by decide) hkernel)
    have hloadNonpositive : load <= (0 : Q') := by
      show load.num * (1 : Int) <= (0 : Int) * (load.den : Int)
      rw [Int.mul_one, Int.zero_mul]
      exact Int.not_lt.mp (fun hnum =>
        hloadNotPositive (CReal.pos_of_num_pos hnum))
    have hloadZero : load ≈ (0 : Q') :=
      Q'.eqv_of_le_le hloadNonpositive hloadNonnegative
    have huseZero : use ≈ (0 : Q') :=
      Q'.eqv_trans _
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * 0) _
        (Q'.mul_eqv_congr_left
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale)
          load 0 hloadZero)
        (Q'.mul_zero_eqv _)
    unfold matchedEventualRoutedCapacityDebtOnPairForRouting
    change (if h : (0 : Q') < capacity then
        Q'.divPos use capacity h else 0) * capacity ≈ use
    rw [dif_neg hcapacity]
    exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv capacity) (Q'.eqv_symm huseZero)

theorem matchedEventualRoutedCapacityDebtOnPairForRouting_add_margin_le_one_implies_reserve
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset))
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (margin : Q')
    (hdebt :
      matchedEventualRoutedCapacityDebtOnPairForRouting
            trajectory transitionStart physicalScale cutoffOffset routing edge +
          margin <= (1 : Q')) :
    (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          routing edge) +
        margin *
          (HalfPow.half *
            centralPhysicalFiniteConditionalKernel
              (trajectory.nome physicalScale)
              (Q'.le_of_lt (trajectory.nome_pos physicalScale))
              (transitionStart physicalScale + cutoffOffset)
              0 edge.1 edge.2) <=
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset)
          0 edge.1 edge.2 := by
  let debt := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale cutoffOffset routing edge
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  let use := matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
      routing edge
  have hcapacity : (0 : Q') <= capacity :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (centralPhysicalFiniteConditionalKernel_nonnegative
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2)
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (debt + margin) 1 capacity hdebt hcapacity
  have hrecover : debt * capacity ≈ use :=
    matchedEventualRoutedCapacityDebtOnPairForRouting_mul_capacity_eqv_use
      trajectory transitionStart physicalScale cutoffOffset routing edge hedge
  have hleft : (debt + margin) * capacity ≈
      use + margin * capacity :=
    Q'.eqv_trans _ (debt * capacity + margin * capacity) _
      (Q'.add_mul_eqv debt margin capacity)
      (Q'.add_eqv_congr' hrecover (Q'.eqv_refl _))
  exact Q'.le_trans' _ ((debt + margin) * capacity) _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ (1 * capacity) _ hscaled
      (Q'.le_of_eqv (Q'.one_mul_eqv capacity)))

/-! ## 3. Two normalized lanes compile to the literal reserve -/

structure MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type where
  margin : Nat -> Nat × Nat -> Q'
  transported_debt_add_margin_le_one : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualRoutedCapacityDebtOnPairForRouting
            trajectory transitionStart physicalScale (cutoffOffset + 1)
            (matchedEventualCanonicalTransportedRoutingAtNext
              trajectory transitionStart physicalScale cutoffOffset) edge +
          margin cutoffOffset edge <= (1 : Q')
  new_ceiling_le_margin_capacity : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
            trajectory transitionStart physicalScale cutoffOffset)
          edge <=
        margin cutoffOffset edge *
          matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
            trajectory transitionStart physicalScale cutoffOffset edge

def MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve.toTransportedReserve
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data : MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve
      trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffTransportedReserve
      trajectory transitionStart physicalScale where
  reserve := fun cutoffOffset edge =>
    data.margin cutoffOffset edge *
      matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
        trajectory transitionStart physicalScale cutoffOffset edge
  transported_le_capacity := by
    intro cutoffOffset edge hedge
    exact
      matchedEventualRoutedCapacityDebtOnPairForRouting_add_margin_le_one_implies_reserve
        trajectory transitionStart physicalScale (cutoffOffset + 1)
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset)
        edge hedge (data.margin cutoffOffset edge)
        (data.transported_debt_add_margin_le_one cutoffOffset edge hedge)
  new_ceiling_le_reserve := data.new_ceiling_le_margin_capacity

def MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data : MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve
      trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toTransportedReserve.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler.matchedEventualCanonicalRoutedCapacityDebtMaximum_add_margin_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler.matchedEventualRoutedCapacityDebtOnPairForRouting_mul_capacity_eqv_use
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler.matchedEventualRoutedCapacityDebtOnPairForRouting_add_margin_le_one_implies_reserve
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler.MatchedEventualActivatedDeletedSupportAllCutoffNormalizedReserve.toObservableCertificate
