/-
# Raw-kernel payment for the exact adaptive ceiling

Source-weight cancellation bounds the constructed adaptive ceiling by the
actual new-block mass times carrier length.  This module keeps normalization
honest by cross-multiplying against the literal used raw-kernel entry.  At one
cutoff and edge, the visible sufficient condition is

  shared floor * (2 * new-block mass * carrier length)
    <= allowance * (half * raw kernel on that edge).

It implies that the constructed normalized ceiling debt is at most the same
allowance.  A finite maximum and the existing scalar-payment compiler then
turn all edgewise raw-capacity payments into the exact all-cutoff observable
certificate.

No raw-kernel lower bound, allowance estimate, or initial strict closure is
inhabited here.  No completed gap, continuum limit, continuum Yang--Mills
theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSourceMassCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem listQMaxZero_le_bound_local
    {A : Type} (value : A -> Q') (bound : Q')
    (hbound : (0 : Q') <= bound) : forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      listQMaxZero value items <= bound
  | [], _ => hbound
  | head :: tail, hall => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact hall head List.mem_cons_self
      · exact listQMaxZero_le_bound_local value bound hbound tail
          (fun item hitem => hall item (List.mem_cons_of_mem head hitem))

private theorem mul_left_swap_nested_local (left middle right : Q') :
    left * (middle * right) ≈ middle * (left * right) := by
  refine Q'.eqv_trans _ ((left * middle) * right) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv left middle right)) ?_
  refine Q'.eqv_trans _ ((middle * left) * right) _
    (Q'.mul_eqv_congr_right _ _ right
      (Q'.mul_comm_eqv left middle)) ?_
  exact Q'.mul_assoc_eqv middle left right

/-! ## 1. One literal raw-capacity payment -/

structure MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type where
  allowance : Q'
  allowance_nonnegative : (0 : Q') <= allowance
  raw_capacity_payment : forall edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      (0 : Q') < HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2 ->
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          ((Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
              trajectory transitionStart physicalScale cutoffOffset) *
            Q'.ofNat
              (matchedEventualCanonicalVacuumSectorIndices
                trajectory transitionStart physicalScale
                (cutoffOffset + 1)).length) <=
        allowance *
          matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
            trajectory transitionStart physicalScale cutoffOffset edge

theorem MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt.ceilingDebtOnPair_le_allowance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    {paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset}
    (data :
      MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)) :
    matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset paths edge <=
      data.allowance := by
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let sourceWeight := centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1
  let ceiling :=
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
      paths edge
  let massScale :=
    (Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset) *
      Q'.ofNat
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length
  let conditionalCapacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      edge.1 edge.2
  let rawCapacity :=
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  have hmembers := (mem_cartesian_iff _ _ edge).mp hedge
  have hsource : (0 : Q') < sourceWeight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hmembers.1
  have hfloor : (0 : Q') <= floor :=
    Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)
  have hceiling : sourceWeight * ceiling <= massScale := by
    exact
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.sourceWeight_mul_weightedCeiling_le_two_newBlockMass_mul_carrierLength
        paths edge
  have hraw : sourceWeight * conditionalCapacity ≈ rawCapacity := by
    exact
      matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
        trajectory transitionStart physicalScale cutoffOffset edge hmembers.1
  unfold matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
    matchedEventualActivatedDeletedSupportHalfKernelCapacityOnPair
    matchedEventualActivatedDeletedSupportNewCeilingCapacityUseOnPair
  change (if hcapacity : (0 : Q') < conditionalCapacity then
      Q'.divPos (floor * ceiling) conditionalCapacity hcapacity else 0) <=
    data.allowance
  by_cases hcapacity : (0 : Q') < conditionalCapacity
  · rw [dif_pos hcapacity]
    have hfloorScaled : floor * (sourceWeight * ceiling) <=
        floor * massScale :=
      Q'.mul_le_mul_of_nonneg_left _ _ floor hceiling hfloor
    have hsourceScaled : sourceWeight * (floor * ceiling) <=
        sourceWeight * (data.allowance * conditionalCapacity) := by
      exact Q'.le_trans' _ (floor * (sourceWeight * ceiling)) _
        (Q'.le_of_eqv
          (mul_left_swap_nested_local sourceWeight floor ceiling))
        (Q'.le_trans' _ (floor * massScale) _ hfloorScaled
          (Q'.le_trans' _ (data.allowance * rawCapacity) _
            (data.raw_capacity_payment edge hedge hcapacity)
            (Q'.le_of_eqv
              (Q'.eqv_trans _ (data.allowance *
                  (sourceWeight * conditionalCapacity)) _
                (Q'.mul_eqv_congr_left data.allowance _ _
                  (Q'.eqv_symm hraw))
                (mul_left_swap_nested_local
                  data.allowance sourceWeight conditionalCapacity)))))
    have hnumerator : floor * ceiling <=
        data.allowance * conditionalCapacity :=
      Q'.le_of_mul_le_mul_left hsourceScaled hsource
    exact Q'.divPos_le_of_le_mul _ _ hcapacity hnumerator
  · rw [dif_neg hcapacity]
    exact data.allowance_nonnegative

/-! ## 2. All edge payments contract through the finite maximum -/

theorem MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt.ceilingDebtMaximum_le_allowance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualActivatedDeletedSupportConstructedNewCeilingDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      data.allowance := by
  unfold
    matchedEventualActivatedDeletedSupportConstructedNewCeilingDebtMaximum
  apply listQMaxZero_le_bound_local _ data.allowance
    data.allowance_nonnegative
  intro edge hedge
  exact data.ceilingDebtOnPair_le_allowance
    (paths := matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
      trajectory transitionStart physicalScale cutoffOffset)
    edge hedge

/-! ## 3. One allowance stream supplies the exact scalar payment -/

structure MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    trajectory transitionStart physicalScale
  tailAllowance : Q'
  tailAllowance_pos : (0 : Q') < tailAllowance
  margin : Q'
  initial_closure_with_margin :
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale 0 +
        prefixTailTotalBudget
          (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope)
          tailAllowance) + margin <=
      (1 : Q')
  ceilingAllowance : Nat -> Q'
  ceilingAllowance_nonnegative : forall cutoffOffset,
    (0 : Q') <= ceilingAllowance cutoffOffset
  raw_capacity_payment : forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      (0 : Q') < HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2 ->
      matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          ((Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
              trajectory transitionStart physicalScale cutoffOffset) *
            Q'.ofNat
              (matchedEventualCanonicalVacuumSectorIndices
                trajectory transitionStart physicalScale
                (cutoffOffset + 1)).length) <=
        ceilingAllowance cutoffOffset *
          matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
            trajectory transitionStart physicalScale cutoffOffset edge
  total_payment_le_margin : forall cutoffOffset,
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        ceilingAllowance cutoffOffset <= margin

def MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment.toConstructedCeilingScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin := data.margin
  initial_closure_with_margin := data.initial_closure_with_margin
  ceiling_payment_le_margin := by
    intro cutoffOffset
    let payment :
        MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt
          trajectory transitionStart physicalScale cutoffOffset :=
      { allowance := data.ceilingAllowance cutoffOffset
        allowance_nonnegative :=
          data.ceilingAllowance_nonnegative cutoffOffset
        raw_capacity_payment := data.raw_capacity_payment cutoffOffset }
    have hmaximum := payment.ceilingDebtMaximum_le_allowance
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left
        (matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset)
        _ _ hmaximum)
      (data.total_payment_le_margin cutoffOffset)

def MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toConstructedCeilingScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler.MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt.ceilingDebtOnPair_le_allowance
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler.MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt.ceilingDebtMaximum_le_allowance
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler.MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment.toObservableCertificate
