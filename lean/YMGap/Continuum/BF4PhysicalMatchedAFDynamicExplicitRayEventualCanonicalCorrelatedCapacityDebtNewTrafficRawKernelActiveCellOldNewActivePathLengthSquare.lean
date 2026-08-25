/-
# Old--new row-active path-length-square contraction

The face-specific path-length-square maximum forgets the selected mapped
current row.  This module restores observable connectivity before using that
quadratic route bound.  A cell contributes its old--new routed path square
only when the literal old--new route factor for the selected mapped edge is
strictly positive; otherwise it contributes zero.  The resulting row-local
maximum therefore vanishes on unused rows.

The literal route factor is bounded by this active quadratic scale, which in
turn is bounded by the preceding row-independent face maximum.  General-
merger and executable no-merger interfaces are supplied against both the exact
mapped-pair raw capacity and the coarser conditional sector floor.  Every
conversion returns to the unchanged exact old--new row and three-face debt
maximum.

No route-length asymptotic, raw-capacity lower bound, sector-floor persistence,
mass decay, inverse-square estimate, no-merger theorem, continuum theory, or
Clay conclusion is supplied.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.SummableInverseSquare

private theorem listQMaxZero_mono_on_local
    {A : Type} (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
      BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero left items <=
        BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hall => by
      unfold BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact Q'.le_trans' _ _ _
          (hall head List.mem_cons_self)
          (Q'.le_max'_left _ _)
      · exact Q'.le_trans' _ _ _
          (listQMaxZero_mono_on_local left right tail
            (fun item hitem =>
              hall item (List.mem_cons_of_mem head hitem)))
          (Q'.le_max'_right _ _)

private theorem listQMaxZero_nonnegative_on_local
    {A : Type} (value : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      (0 : Q') <=
        BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero value items
  | [], _ => Q'.le_refl' 0
  | head :: _tail, hvalue =>
      Q'.le_trans' _ _ _
        (hvalue head List.mem_cons_self)
        (Q'.le_max'_left _ _)

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

private theorem correctedSlabIncrement_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
  exact slabParametricKCutoffIncrement_nonnegative
    (Q'.le_of_lt (trajectory.nome_pos physicalScale)) _ _ _

private theorem componentMergerResidual_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
  exact centralPhysicalFiniteNewComponentMergerMass_nonnegative
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale)) _ _ _

/-! ## 1. A quadratic scale masked by literal selected-edge activity -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  if (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell then
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
      trajectory transitionStart physicalScale cutoffOffset cell.2
  else 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
  by_cases hroute : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell
  · rw [if_pos hroute]
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_neg hroute]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_activeRoutedPathLengthSquareOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
  by_cases hroute : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell
  · rw [if_pos hroute]
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_routedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset cell
  · rw [if_neg hroute]
    exact Int.not_lt.mp hroute

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell_le_facePathLengthSquare
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
        trajectory transitionStart physicalScale cutoffOffset cell <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset cell.2 := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
  by_cases hroute : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell
  · rw [if_pos hroute]
    exact Q'.le_refl' _
  · rw [if_neg hroute]
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset cell.2

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
  apply listQMaxZero_nonnegative_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_activeRoutedPathLengthSquareMaximumOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
  apply listQMaxZero_mono_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_activeRoutedPathLengthSquareOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_le_faceMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
  apply listQMaxZero_mono_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell_le_facePathLengthSquare
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_eqv_zero_of_routeFactorMaximum_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hrouteMaximumZero :
      Q'.eqv
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair)
        0) :
    Q'.eqv
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      0 := by
  have hactiveLe :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair <= 0 := by
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
    apply listQMaxZero_le_bound_local _ 0 (Q'.le_refl' 0)
    intro endpointPair hendpointPair
    have hrouteLeMaximum :=
      BF4PhysicalFiniteVacuumSectorPathMaximum.le_listQMaxZero_of_mem
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset)
        hendpointPair
    have hrouteLeZero :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair) <= 0 :=
      Q'.le_trans' _ _ _ hrouteLeMaximum
        (Q'.le_of_eqv hrouteMaximumZero)
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
    by_cases hroute : (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair)
    · exact False.elim ((Int.not_lt_of_ge hrouteLeZero) hroute)
    · rw [if_neg hroute]
      exact Q'.le_refl' 0
  exact Q'.eqv_of_le_le hactiveLe
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset pair)

/-! ## 2. Active quadratic paths compile to exact row capacity -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareRawCapacityInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        ((matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
              trajectory transitionStart physicalScale cutoffOffset +
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
              trajectory transitionStart physicalScale cutoffOffset) *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareRawCapacityInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := by
    intro cutoffOffset pair hpair
    have hmass0 : (0 : Q') <=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
            trajectory transitionStart physicalScale cutoffOffset :=
      Q'.add_le_add
        (correctedSlabIncrement_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
        (componentMergerResidual_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
    have hmassRoute := Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_activeRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      hmass0
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmassRoute
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitActivePathLengthSquareRawCapacity_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareRawCapacityInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRawCapacity_and_otherFaces
    oldNew.toRawCapacityControl newOld newNew cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareRawCapacityInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  noMerger : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
      trajectory transitionStart physicalScale cutoffOffset = true
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareRawCapacityInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  noMerger := control.noMerger
  envelope_le := by
    intro cutoffOffset pair hpair
    have hmassRoute := Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_activeRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (correctedSlabIncrement_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmassRoute
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerActivePathLengthSquareRawCapacity_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareRawCapacityInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRawCapacity_and_otherFaces
    oldNew.toRawCapacityControl newOld newNew cutoffOffset

/-! ## 3. The same active quadratic scale admits the conditional sector floor -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareSectorFloorInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        ((matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
              trajectory transitionStart physicalScale cutoffOffset +
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
              trajectory transitionStart physicalScale cutoffOffset) *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareSectorFloorInverseSquareControl.toRouteSectorFloorControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRouteSectorFloorInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := by
    intro cutoffOffset pair hpair
    have hmass0 : (0 : Q') <=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
            trajectory transitionStart physicalScale cutoffOffset :=
      Q'.add_le_add
        (correctedSlabIncrement_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
        (componentMergerResidual_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
    have hmassRoute := Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_activeRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      hmass0
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmassRoute
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitActivePathLengthSquareSectorFloor_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRouteSectorFloor_and_otherFaces
    oldNew.toRouteSectorFloorControl newOld newNew cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareSectorFloorInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  noMerger : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
      trajectory transitionStart physicalScale cutoffOffset = true
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficLaterSectorRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareSectorFloorInverseSquareControl.toRouteSectorFloorControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRouteSectorFloorInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  noMerger := control.noMerger
  envelope_le := by
    intro cutoffOffset pair hpair
    have hmassRoute := Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_activeRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (correctedSlabIncrement_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmassRoute
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerActivePathLengthSquareSectorFloor_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareSectorFloorInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRouteSectorFloor_and_otherFaces
    oldNew.toRouteSectorFloorControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_activeRoutedPathLengthSquareOnCell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell_le_facePathLengthSquare
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_activeRoutedPathLengthSquareMaximumOnCurrentPair
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_le_faceMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_eqv_zero_of_routeFactorMaximum_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareSectorFloorInverseSquareControl.toRouteSectorFloorControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareSectorFloorInverseSquareControl.toRouteSectorFloorControl
