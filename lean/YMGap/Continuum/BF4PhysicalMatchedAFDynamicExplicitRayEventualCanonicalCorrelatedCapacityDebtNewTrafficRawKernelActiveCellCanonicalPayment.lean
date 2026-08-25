/-
# Canonical exact active-cell payment for matched new traffic

The preceding three-face compiler permits an arbitrary nonnegative allowance
provided it pays the stationary-weighted routed numerator against the capacity
of the same active cell.  Here that shared payment is made canonical: the
allowance is the actual endpoint stationary weight times the exact raw-kernel
amplification on the mapped current cell.

This allowance is globally nonnegative.  On an active cell its positive
capacity denominator cancels exactly, so the active-payment field is automatic.
On every actual current-pair/new-endpoint cell it is also exactly the existing
new-traffic debt term.  Consequently the only remaining quantitative inputs
are three independently inhabitable inverse-square row estimates, one for each
literal endpoint shell face.

No face estimate, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Global positivity of the stationary pair factor -/

theorem matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative_all
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointStationaryPairWeight
        trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  unfold matchedEventualCanonicalNewEndpointStationaryPairWeight
    matchedEventualCanonicalLaterIndexWeight
    centralPhysicalFiniteWeight
  exact Q'.mul_nonneg _ _
    (centralPhysicalRowMarginal_nonnegative
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0
      (centralPhysicalFiniteStateAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 endpointPair.1))
    (centralPhysicalRowMarginal_nonnegative
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0
      (centralPhysicalFiniteStateAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 endpointPair.2))

/-! ## 2. The canonical allowance is the literal exact debt term -/

def matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointStationaryPairWeight
      trajectory transitionStart physicalScale cutoffOffset cell.2 *
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset cell.1)
      cell.2

theorem matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
  exact Q'.mul_nonneg _ _
    (matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative_all
      trajectory transitionStart physicalScale cutoffOffset cell.2)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRawKernelAmplificationOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset cell.1)
      cell.2)

theorem matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_active_payment
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hcell : cell ∈
      matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell <=
      matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
          trajectory transitionStart physicalScale cutoffOffset cell *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset cell := by
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset cell.2
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let route := matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  let capacity := matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  have hcapacity : (0 : Q') < capacity :=
    (matchedEventualCanonicalNewEndpointTrafficActiveCell_route_capacity_pos
      trajectory transitionStart physicalScale cutoffOffset cell hcell).2
  change weight * (floor * route) <=
    (weight *
      (if hcapacity' : (0 : Q') < capacity then
        Q'.divPos (floor * route) capacity hcapacity'
      else 0)) * capacity
  rw [dif_pos hcapacity]
  have hcancel :
      (weight * Q'.divPos (floor * route) capacity hcapacity) * capacity ≈
        weight * (floor * route) := by
    exact Q'.eqv_trans _
      (weight *
        (Q'.divPos (floor * route) capacity hcapacity * capacity)) _
      (Q'.mul_assoc_eqv weight
        (Q'.divPos (floor * route) capacity hcapacity) capacity)
      (Q'.mul_eqv_congr_left weight _ _
        (Q'.divPos_mul_eqv (floor * route) capacity hcapacity))
  exact Q'.ge_of_eqv hcancel

theorem matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_debtTermOnMappedPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair endpointPair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair) ≈
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair := by
  exact Q'.eqv_symm
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermOnMappedPair_eqv_stationaryWeight_mul_rawKernelAmplification
      trajectory transitionStart physicalScale cutoffOffset
      pair endpointPair hpair hendpointPair)

/-! ## 3. Three independently inhabitable canonical face budgets -/

structure MatchedEventualCanonicalNewEndpointTrafficCanonicalOldNewFaceRowInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
            trajectory transitionStart physicalScale
            (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
              trajectory transitionStart physicalScale)
            cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficCanonicalNewOldFaceRowInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
            trajectory transitionStart physicalScale
            (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
              trajectory transitionStart physicalScale)
            cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficCanonicalNewNewFaceRowInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
            trajectory transitionStart physicalScale
            (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
              trajectory transitionStart physicalScale)
            cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

/-! ## 4. Parallel join to the unchanged exact observable -/

def matchedEventualCanonicalNewEndpointTrafficCanonicalThreeFacePaymentControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficCanonicalOldNewFaceRowInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld :
      MatchedEventualCanonicalNewEndpointTrafficCanonicalNewOldFaceRowInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew :
      MatchedEventualCanonicalNewEndpointTrafficCanonicalNewNewFaceRowInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := offset
  offset_at_least_two := offset_at_least_two
  oldNewCoefficient := oldNew.coefficient
  newOldCoefficient := newOld.coefficient
  newNewCoefficient := newNew.coefficient
  oldNewCoefficient_nonnegative := oldNew.coefficient_nonnegative
  newOldCoefficient_nonnegative := newOld.coefficient_nonnegative
  newNewCoefficient_nonnegative := newNew.coefficient_nonnegative
  allowance :=
    matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
      trajectory transitionStart physicalScale
  allowance_nonnegative :=
    matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_nonnegative
      trajectory transitionStart physicalScale
  active_payment :=
    matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_active_payment
      trajectory transitionStart physicalScale
  oldNew_row_allowance_le := oldNew.row_allowance_le
  newOld_row_allowance_le := newOld.row_allowance_le
  newNew_row_allowance_le := newNew.row_allowance_le

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_canonicalThreeFaceControls
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficCanonicalOldNewFaceRowInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld :
      MatchedEventualCanonicalNewEndpointTrafficCanonicalNewOldFaceRowInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew :
      MatchedEventualCanonicalNewEndpointTrafficCanonicalNewNewFaceRowInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient +
          (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  (matchedEventualCanonicalNewEndpointTrafficCanonicalThreeFacePaymentControl
    oldNew newOld newNew).debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment.matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative_all
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment.matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment.matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_active_payment
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment.matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_debtTermOnMappedPair
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment.matchedEventualCanonicalNewEndpointTrafficCanonicalThreeFacePaymentControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_canonicalThreeFaceControls
