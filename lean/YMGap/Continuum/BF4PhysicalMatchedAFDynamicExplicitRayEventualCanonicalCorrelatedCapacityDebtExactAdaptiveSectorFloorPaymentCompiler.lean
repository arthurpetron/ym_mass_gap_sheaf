/-
# Canonical sector-floor payment for exact adaptive debt

The raw-capacity compiler leaves one visible edgewise cross inequality.  On a
positive-capacity later carrier edge, the located positive raw-kernel floor of
the entire later vacuum sector bounds that exact used entry.  Hence the
canonical allowance is the explicit quotient

  shared floor * (2 * new-block mass * carrier length)
    / later sector raw-kernel capacity floor.

This module proves that the quotient supplies every raw-capacity payment and
therefore contracts the adaptive lane to one explicit scalar stream per
cutoff.

No bound on that quotient, transported data drift, or initial strict closure
is inhabited here.  No completed gap, continuum limit, continuum Yang--Mills
theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveRawCapacityPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
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

private theorem q_right_pos_of_mul_pos_local
    {left right : Q'}
    (hleft : (0 : Q') <= left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) <= left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num <= 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-! ## 1. Explicit numerator and quotient -/

def matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale *
    ((Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset) *
      Q'.ofNat
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale (cutoffOffset + 1)).length)

theorem matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (matchedEventualCanonicalLaterNewBlockMass_nonnegative
          trajectory transitionStart physicalScale cutoffOffset))
      (Q'.ofNat_le_ofNat (Nat.zero_le _)))

def matchedEventualActivatedDeletedSupportSectorFloorAllowance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  Q'.divPos
    (matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualActivatedDeletedSupportSectorFloorAllowance_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualActivatedDeletedSupportSectorFloorAllowance
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualActivatedDeletedSupportSectorFloorAllowance Q'.divPos
  exact Q'.mul_nonneg _ _
    (matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset)))

/-! ## 2. The sector floor bounds every positive used edge -/

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_rawCapacityOnPositiveEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat)
    (hedge : edge ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hcapacity : (0 : Q') < HalfPow.half *
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2) :
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge := by
  have hmembers := (mem_cartesian_iff _ _ edge).mp hedge
  have hconditional : (0 : Q') <
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2 :=
    q_right_pos_of_mul_pos_local (by decide) hcapacity
  have hsource := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
    hmembers.1
  have hweighted : (0 : Q') <
      centralPhysicalFiniteWeight
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1 *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + (cutoffOffset + 1)) 0
          edge.1 edge.2 :=
    Q'.mul_pos hsource hconditional
  have hkernelEq := centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
    hmembers.1 edge.2
  have hkernel : (0 : Q') <
      centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2 :=
    Q'.pos_of_lt_of_le hweighted (Q'.le_of_eqv hkernelEq)
  have hfloor := centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0
    edge.1 edge.2 hmembers.1 hmembers.2 hkernel
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
  exact Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hfloor (by decide)

/-! ## 3. The canonical quotient supplies the raw payment -/

def matchedEventualActivatedDeletedSupportSectorFloorRawCapacityAllowanceAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualActivatedDeletedSupportConstructedCeilingRawCapacityAllowanceAt
      trajectory transitionStart physicalScale cutoffOffset where
  allowance := matchedEventualActivatedDeletedSupportSectorFloorAllowance
    trajectory transitionStart physicalScale cutoffOffset
  allowance_nonnegative :=
    matchedEventualActivatedDeletedSupportSectorFloorAllowance_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  raw_capacity_payment := by
    intro edge hedge hcapacity
    let numerator :=
      matchedEventualActivatedDeletedSupportSectorFloorPaymentNumerator
        trajectory transitionStart physicalScale cutoffOffset
    let sectorFloor :=
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset
    let allowance :=
      matchedEventualActivatedDeletedSupportSectorFloorAllowance
        trajectory transitionStart physicalScale cutoffOffset
    let rawCapacity :=
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
        trajectory transitionStart physicalScale cutoffOffset edge
    have hfloor :=
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_rawCapacityOnPositiveEdge
        trajectory transitionStart physicalScale cutoffOffset edge hedge hcapacity
    have hallowance : (0 : Q') <= allowance :=
      matchedEventualActivatedDeletedSupportSectorFloorAllowance_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
    have hscaled : allowance * sectorFloor <= allowance * rawCapacity :=
      Q'.mul_le_mul_of_nonneg_left _ _ allowance hfloor hallowance
    have hcancel : allowance * sectorFloor ≈ numerator := by
      exact Q'.divPos_mul_eqv numerator sectorFloor
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset)
    exact Q'.le_trans' _ (allowance * sectorFloor) _
      (Q'.ge_of_eqv hcancel) hscaled

/-! ## 4. One explicit quotient stream closes the adaptive compiler -/

structure MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment
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
  total_payment_le_margin : forall cutoffOffset,
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportSectorFloorAllowance
          trajectory transitionStart physicalScale cutoffOffset <=
      margin

def MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment.toRawCapacityScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffRawCapacityScalarPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin := data.margin
  initial_closure_with_margin := data.initial_closure_with_margin
  ceilingAllowance := fun cutoffOffset =>
    matchedEventualActivatedDeletedSupportSectorFloorAllowance
      trajectory transitionStart physicalScale cutoffOffset
  ceilingAllowance_nonnegative := fun cutoffOffset =>
    matchedEventualActivatedDeletedSupportSectorFloorAllowance_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  raw_capacity_payment := by
    intro cutoffOffset
    exact
      (matchedEventualActivatedDeletedSupportSectorFloorRawCapacityAllowanceAt
        trajectory transitionStart physicalScale cutoffOffset).raw_capacity_payment
  total_payment_le_margin := data.total_payment_le_margin

def MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toRawCapacityScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler.matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_rawCapacityOnPositiveEdge
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler.matchedEventualActivatedDeletedSupportSectorFloorRawCapacityAllowanceAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveSectorFloorPaymentCompiler.MatchedEventualActivatedDeletedSupportAllCutoffSectorFloorScalarPayment.toObservableCertificate
