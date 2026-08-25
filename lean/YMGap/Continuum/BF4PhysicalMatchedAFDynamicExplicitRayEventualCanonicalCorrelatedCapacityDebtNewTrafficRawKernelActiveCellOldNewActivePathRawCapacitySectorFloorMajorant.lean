/-
# Exact old--new amplification below the used-route sector-floor majorant

The least-dyadic schedule leaves one exact observable-connected obstruction:
the maximum of the row-active path-square divided by the raw capacity of the
same mapped current pair.  This module bounds that exact quotient by a
face-specific used-route sector-floor envelope.

The bridge is activity-sensitive.  On a used row, positive old--new traffic
places the mapped edge in the later vacuum sector and makes its raw kernel
positive, so the later-sector floor is below that exact capacity.  On an
unused row, the active path-square and exact quotient are both zero.  Thus no
positive denominator is demanded from inactive rows.

The resulting dyadic compiler says that a cross-multiplied payment against the
sector-floor majorant bounds the least exact joint precision.  The numerator
retains the old--new face maximum rather than enlarging to the unmasked
all-face maximum.  This preserves the observable-connected exact quotient
while exposing a coarser denominator fallback.  It does not supply the
payment, a sector-floor growth law, merger
control, continuum theory, or a Clay conclusion.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacitySectorFloorMajorant

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

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
          (fun item hitem =>
            hall item (List.mem_cons_of_mem head hitem))

/-! ## 1. Face-specific used-route sector-floor envelope -/

/-- The coarser capacity denominator is paired with the old--new face path
maximum, rather than the still coarser unmasked all-face path maximum. -/
def matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

/-! ## 2. Exact row quotient below the used-route sector-floor envelope -/

private theorem sectorFloorPathAmplificationEnvelope_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
            trajectory transitionStart physicalScale cutoffOffset))))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_eqv_zero_of_routeMaximum_not_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hroute : ¬ (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair ≈ 0 := by
  let routeMaximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  let activeMaximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  let capacity :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  have hrouteNonnegative : (0 : Q') <= routeMaximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset pair
  have hrouteZero : routeMaximum ≈ 0 :=
    Q'.eqv_of_le_le (Int.not_lt.mp hroute) hrouteNonnegative
  have hactiveZero : activeMaximum ≈ 0 :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_eqv_zero_of_routeFactorMaximum_eqv_zero
      trajectory transitionStart physicalScale cutoffOffset pair hrouteZero
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
  by_cases hcapacity : (0 : Q') < capacity
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    have hnumerator :
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale * activeMaximum ≈
          0 := by
      refine Q'.eqv_trans _
        (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale * 0) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _ hactiveZero
      · exact Q'.mul_zero_eqv _
    refine Q'.eqv_trans _
      (0 * Q'.recipPos capacity hcapacity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hnumerator
    · exact Q'.zero_mul_eqv _
  · rw [dif_neg hcapacity]
    exact Q'.eqv_refl 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_sectorFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let routeMaximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  let activeMaximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  let pathMaximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
      trajectory transitionStart physicalScale cutoffOffset
  let capacity :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  let sectorFloor :=
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  by_cases hroute : (0 : Q') < routeMaximum
  · have hsectorCapacity : sectorFloor <= capacity :=
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
        trajectory transitionStart physicalScale cutoffOffset pair hpair hroute
    have hsectorPos : (0 : Q') < sectorFloor :=
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
        trajectory transitionStart physicalScale cutoffOffset
    have hcapacityPos : (0 : Q') < capacity :=
      Q'.pos_of_lt_of_le hsectorPos hsectorCapacity
    have hactivePath : activeMaximum <= pathMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_le_faceMaximum
        trajectory transitionStart physicalScale cutoffOffset pair
    have hreciprocal :
        Q'.recipPos capacity hcapacityPos <=
          Q'.recipPos sectorFloor hsectorPos :=
      recipPos_antitone sectorFloor capacity hsectorPos hcapacityPos
        hsectorCapacity
    have hfirst :
        activeMaximum * Q'.recipPos capacity hcapacityPos <=
          pathMaximum * Q'.recipPos capacity hcapacityPos :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hactivePath
        (Q'.le_of_lt (Q'.recipPos_pos capacity hcapacityPos))
    have hsecond :
        pathMaximum * Q'.recipPos capacity hcapacityPos <=
          pathMaximum * Q'.recipPos sectorFloor hsectorPos :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
          trajectory transitionStart physicalScale cutoffOffset)
    have hinner := Q'.le_trans' _ _ _ hfirst hsecond
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
    rw [dif_pos hcapacityPos]
    unfold Q'.divPos
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_assoc_eqv
          (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale)
          activeMaximum
          (Q'.recipPos capacity hcapacityPos)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hinner
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_eqv_zero_of_routeMaximum_not_pos
          trajectory transitionStart physicalScale cutoffOffset pair hroute))
      (sectorFloorPathAmplificationEnvelope_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_sectorFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
  apply listQMaxZero_le_bound_local
    _ _
    (sectorFloorPathAmplificationEnvelope_nonnegative_local
      trajectory transitionStart physicalScale cutoffOffset)
  intro pair hpair
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_sectorFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset pair hpair

/-! ## 3. Cross-multiplied sector-floor payment bounds least joint precision -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_sectorFloorPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hpayment :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      candidate := by
  let amplification :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  let majorant :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  let target := invSqTerm offset offset_at_least_two cutoffOffset
  have hamplification : amplification <= majorant :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_sectorFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  have hdenominator : (0 : Q') < amplification + 1 := by
    have hamp0 : (0 : Q') <= amplification :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
    have hone : (0 : Q') < (1 : Q') + amplification :=
      Q'.pos_add_nonneg (by decide) hamp0
    exact Q'.pos_of_lt_of_le hone
      (Q'.le_of_eqv (Q'.add_comm_eqv 1 amplification))
  have hdenominatorLe : amplification + 1 <= majorant + 1 :=
    Q'.add_le_add_right amplification majorant 1 hamplification
  have hscaled :
      dyad candidate * (amplification + 1) <=
        dyad candidate * (majorant + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominatorLe
      (dyad_nonneg candidate)
  have hcandidatetolerance :
      dyad candidate <=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
          trajectory transitionStart physicalScale offset
          offset_at_least_two cutoffOffset := by
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
    exact Q'.le_divPos_of_mul_le target (amplification + 1) hdenominator
      (Q'.le_trans' _ _ _ hscaled hpayment)
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_dyad_le_tolerance
      trajectory transitionStart physicalScale offset
      offset_at_least_two cutoffOffset candidate hcandidatetolerance

/-! ## 4. Sector-floor analytic data compiles to the consecutive schedule -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSectorFloorDyadicLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  precisionIntercept : Nat
  sectorFloor_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSectorFloorDyadicLinearData.toLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSectorFloorDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two where
  precisionIntercept := data.precisionIntercept
  precision_le := by
    intro cutoffOffset
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_sectorFloorPayment
        trajectory transitionStart physicalScale offset offset_at_least_two
        cutoffOffset (data.precisionIntercept + cutoffOffset)
        (data.sectorFloor_payment cutoffOffset)
  start_absorbs_fixed_tail_cost := data.start_absorbs_fixed_tail_cost

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_eqv_zero_of_routeMaximum_not_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_sectorFloorPathEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_sectorFloorPathEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_sectorFloorPayment
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSectorFloorDyadicLinearData.toLinearData

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacitySectorFloorMajorant
