/-
# The active old--new row floor is an exact used raw-kernel floor

The preceding factorization leaves the minimum of source-weighted conditional
capacity on precisely the current rows used by old--new traffic.  At every
mapped current edge, the positive stationary source weight cancels the
conditional-kernel normalization.  The resulting capacity is setoid-equal to
one half of the genuine later raw physical kernel on that same edge.

This module transports that pointwise cancellation through the constructive
positive minimum on the unchanged filtered active-row list.  It then compiles
a payment stated entirely with the used raw-kernel floor into the exact joint
dyadic schedule.  No global sector minimum or unrelated edge is introduced.

The module does not prove a cutoff-growth law for the used raw entries, pay the
fixed nome/dimension burn, control route churn or merger, construct the other
traffic faces, complete the transfer gap, or take a continuum limit.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowRawKernelFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem listPositiveMinOne_eqv_on_local
    {A : Type} (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item ≈ right item) ->
      listPositiveMinOne left items ≈ listPositiveMinOne right items
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hall => by
      have hhead := hall head List.mem_cons_self
      have htail := listPositiveMinOne_eqv_on_local left right tail
        (fun item hitem =>
          hall item (List.mem_cons_of_mem head hitem))
      unfold listPositiveMinOne
      apply Q'.eqv_of_le_le
      · exact (Q'.le_min'_iff _ _ _).mpr
          ⟨Q'.le_trans' _ _ _ (Q'.min_le_left' _ _)
              (Q'.le_of_eqv hhead),
            Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
              (Q'.le_of_eqv htail)⟩
      · exact (Q'.le_min'_iff _ _ _).mpr
          ⟨Q'.le_trans' _ _ _ (Q'.min_le_left' _ _)
              (Q'.ge_of_eqv hhead),
            Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
              (Q'.ge_of_eqv htail)⟩

/-! ## 1. Source normalization cancels on every mapped current pair -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair)

theorem matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_mappedRawKernelCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hsource := (mem_cartesian_iff _ _ edge).mp hedge |>.1
  unfold
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
  exact
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
      trajectory transitionStart physicalScale cutoffOffset edge hsource

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnActiveCurrentPair_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  have hparts :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hcapacity :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_capacity_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  have heq :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_mappedRawKernelCapacity
      trajectory transitionStart physicalScale cutoffOffset pair hparts.1
  exact Q'.pos_of_lt_of_le hcapacity (Q'.le_of_eqv heq)

/-! ## 2. Exact positive minimum on the unchanged used-row list -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listPositiveMinOne
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
  apply listPositiveMinOne_pos
  intro pair hpair
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnActiveCurrentPair_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_eqv_rawKernelCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
  apply listPositiveMinOne_eqv_on_local
  intro pair hpair
  have hparts :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  exact
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_mappedRawKernelCapacity
      trajectory transitionStart physicalScale cutoffOffset pair hparts.1

/-! ## 3. Raw used-edge envelope compiles to the exact amplification -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_rawKernelFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let capacityFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  let rawFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hcapacityPos : (0 : Q') < capacityFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hrawPos : (0 : Q') < rawFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hrawCapacity : rawFloor <= capacityFloor :=
    Q'.ge_of_eqv
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_eqv_rawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset)
  have hreciprocal :
      Q'.recipPos capacityFloor hcapacityPos <=
        Q'.recipPos rawFloor hrawPos :=
    recipPos_antitone rawFloor capacityFloor hrawPos hcapacityPos
      hrawCapacity
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowRawKernelFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_rawKernelFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. A raw-edge dyadic payment feeds the unchanged exact schedule -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowRawKernelFloorPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hpayment :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      candidate := by
  have henvelope :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_rawKernelFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  have hdenominator := Q'.add_le_add_right _ _ 1 henvelope
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominator
    (dyad_nonneg candidate)
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowCapacityFloorPayment
      trajectory transitionStart physicalScale offset offset_at_least_two
      cutoffOffset candidate (Q'.le_trans' _ _ _ hscaled hpayment)

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowRawKernelFloorDyadicLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  precisionIntercept : Nat
  activeRowRawKernelFloor_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowRawKernelFloorDyadicLinearData.toLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowRawKernelFloorDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two where
  precisionIntercept := data.precisionIntercept
  precision_le := by
    intro cutoffOffset
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowRawKernelFloorPayment
        trajectory transitionStart physicalScale offset offset_at_least_two
        cutoffOffset (data.precisionIntercept + cutoffOffset)
        (data.activeRowRawKernelFloor_payment cutoffOffset)
  start_absorbs_fixed_tail_cost := data.start_absorbs_fixed_tail_cost

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_mappedRawKernelCapacity
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnActiveCurrentPair_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_eqv_rawKernelCapacityFloor
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowRawKernelFloorPathEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowRawKernelFloorPayment
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowRawKernelFloorDyadicLinearData.toLinearData

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowRawKernelFloor
