/-
# Exact old--new amplification factored through the used current rows

The exact old--new quotient is indexed by mapped current carrier pairs, while
the earlier active-capacity floor is indexed by every used route cell.  This
module filters the current carrier itself by positive old--new row traffic and
takes the constructive positive minimum of the exact current-pair capacity on
that same list.

Consequently the exact amplification maximum is bounded by the product of two
separate, observable-connected quantities: the old--new face path-square
maximum and the reciprocal used-row capacity floor.  The numerator also has
an explicit ambient-carrier fallback.  Inactive rows remain exact zeros and
do not force an artificial positive denominator.

This is a factorization, not an asymptotic estimate.  It supplies neither a
cutoff-uniform lower bound for the used-row floor nor the dyadic payment needed
by the consecutive schedule.  It does not prove merger control, a completed
transfer gap, a continuum theory, or the Clay conclusion.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacitySectorFloorMajorant
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacitySectorFloorMajorant
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
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
      BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero value items <= bound
  | [], _ => hbound
  | head :: tail, hall => by
      unfold BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact hall head List.mem_cons_self
      · exact listQMaxZero_le_bound_local value bound hbound tail
          (fun item hitem =>
            hall item (List.mem_cons_of_mem head hitem))

private theorem lower_le_listPositiveMinOne_local
    {A : Type} (value : A -> Q') (lower : Q') : forall items : List A,
      lower <= 1 ->
      (forall item, item ∈ items -> lower <= value item) ->
      lower <= listPositiveMinOne value items
  | [], hlower, _ => hlower
  | head :: tail, hlower, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value head <= listPositiveMinOne value tail
      · rw [if_pos hle]
        exact hall head List.mem_cons_self
      · rw [if_neg hle]
        exact lower_le_listPositiveMinOne_local value lower tail hlower
          (fun item hitem =>
            hall item (List.mem_cons_of_mem head hitem))

/-! ## 1. The exact list of current rows used by old--new traffic -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairB
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Bool :=
  decide ((0 : Q') <
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List (Nat × Nat) :=
  (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset).filter
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairB
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ∧
      (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  have hfiltered := List.mem_filter.mp hpair
  constructor
  · exact hfiltered.1
  · unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairB
      at hfiltered
    exact of_decide_eq_true hfiltered.2

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_capacity_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  have hparts :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hfloorLe :=
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset pair hparts.1 hparts.2
  exact Q'.pos_of_lt_of_le
    (matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset)
    hfloorLe

/-! ## 2. Positive minimum of exact capacity on precisely those rows -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listPositiveMinOne
    (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
  apply listPositiveMinOne_pos
  intro pair hpair
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_capacity_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_le_capacityOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
  exact listPositiveMinOne_le_of_mem
    (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset)
    pair hpair

theorem matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_oldNewFaceActiveRowCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
  apply lower_le_listPositiveMinOne_local
  · exact
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_one
        trajectory transitionStart physicalScale cutoffOffset
  · intro pair hpair
    have hparts :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
        trajectory transitionStart physicalScale cutoffOffset pair hpair
    exact
      matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_capacityOnCurrentPair_of_oldNewRouteFactorMaximum_pos
        trajectory transitionStart physicalScale cutoffOffset pair hparts.1 hparts.2

/-! ## 3. Exact amplification below the separated path/floor envelope -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
            trajectory transitionStart physicalScale cutoffOffset))))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_activeRowCapacityFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
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
  let activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  by_cases hroute : (0 : Q') < routeMaximum
  · have hactivePair : pair ∈
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset := by
      apply List.mem_filter.mpr
      constructor
      · exact hpair
      · unfold
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairB
        exact decide_eq_true hroute
    have hcapacityPos : (0 : Q') < capacity :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_capacity_pos
        trajectory transitionStart physicalScale cutoffOffset pair hactivePair
    have hfloorPos : (0 : Q') < activeFloor :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
        trajectory transitionStart physicalScale cutoffOffset
    have hfloorCapacity : activeFloor <= capacity :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_le_capacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair hactivePair
    have hactivePath : activeMaximum <= pathMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_le_faceMaximum
        trajectory transitionStart physicalScale cutoffOffset pair
    have hreciprocal :
        Q'.recipPos capacity hcapacityPos <=
          Q'.recipPos activeFloor hfloorPos :=
      recipPos_antitone activeFloor capacity hfloorPos hcapacityPos
        hfloorCapacity
    have hfirst :
        activeMaximum * Q'.recipPos capacity hcapacityPos <=
          pathMaximum * Q'.recipPos capacity hcapacityPos :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hactivePath
        (Q'.le_of_lt (Q'.recipPos_pos capacity hcapacityPos))
    have hsecond :
        pathMaximum * Q'.recipPos capacity hcapacityPos <=
          pathMaximum * Q'.recipPos activeFloor hfloorPos :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
          trajectory transitionStart physicalScale cutoffOffset)
    have hinner := Q'.le_trans' _ _ _ hfirst hsecond
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
    rw [dif_pos hcapacityPos]
    unfold Q'.divPos
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
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
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
  apply listQMaxZero_le_bound_local
    _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)
  intro pair hpair
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_activeRowCapacityFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset pair hpair

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_sectorFloorPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let sectorFloor :=
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  let activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hsectorPos : (0 : Q') < sectorFloor :=
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hactivePos : (0 : Q') < activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hsectorActive : sectorFloor <= activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_oldNewFaceActiveRowCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hreciprocal :
      Q'.recipPos activeFloor hactivePos <=
        Q'.recipPos sectorFloor hsectorPos :=
    recipPos_antitone sectorFloor activeFloor hsectorPos hactivePos
      hsectorActive
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSectorFloorPathAmplificationEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))

/-! ## 4. Explicit ambient numerator without a maximum-to-maximum detour -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_le_laterAmbientCarrierSquareScale
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
  apply listQMaxZero_le_bound_local
    _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale_pos
        trajectory transitionStart physicalScale cutoffOffset))
  intro endpointPair hendpointPair
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_le_unmasked
      trajectory transitionStart physicalScale cutoffOffset endpointPair)
    (Q'.le_trans' _ _ _
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_le_laterSimpleCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset endpointPair
        hendpointPair)
      (matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale_le_ambient
        trajectory transitionStart physicalScale cutoffOffset))

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorAmbientAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_ambientEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorAmbientAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorAmbientAmplificationEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_le_laterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset)
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
            trajectory transitionStart physicalScale cutoffOffset))))
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorAmbientEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorAmbientAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_ambientEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 5. Cross-multiplied payment compiles to the exact joint schedule -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowCapacityFloorPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hpayment :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
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
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset
  let target := invSqTerm offset offset_at_least_two cutoffOffset
  have hamplification : amplification <= majorant :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorPathEnvelope
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

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowCapacityFloorDyadicLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  precisionIntercept : Nat
  activeRowCapacityFloor_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowCapacityFloorDyadicLinearData.toLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowCapacityFloorDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two where
  precisionIntercept := data.precisionIntercept
  precision_le := by
    intro cutoffOffset
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowCapacityFloorPayment
        trajectory transitionStart physicalScale offset offset_at_least_two
        cutoffOffset (data.precisionIntercept + cutoffOffset)
        (data.activeRowCapacityFloor_payment cutoffOffset)
  start_absorbs_fixed_tail_cost := data.start_absorbs_fixed_tail_cost

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_capacity_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloor_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor_le_oldNewFaceActiveRowCapacityFloor
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorPathEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowCapacityFloorPathAmplificationEnvelope_le_sectorFloorPathEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_le_laterAmbientCarrierSquareScale
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowCapacityFloorAmbientEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowCapacityFloorPayment
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActiveRowCapacityFloorDyadicLinearData.toLinearData

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
