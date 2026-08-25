/-
# Old--new traffic: cross-multiply the row source weight into raw capacity

The source weight in the old--new source-normalized route factor is constant
across a fixed mapped current row.  This module takes the maximum of the
literal old--new masked route factor before division and proves that the
source-normalized maximum is bounded by that route maximum divided by the
strictly positive mapped source weight.

Positive cross-multiplication then moves the row source weight to the
conditional-capacity side, where it is definitionally the source-weighted raw
capacity on the mapped current pair.  The resulting analytic interfaces are
division-free in the source weight.  No raw-capacity lower bound, route bound,
mass decay estimate, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInOldNewShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

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

private theorem listQMaxZero_nonnegative_on_local
    {A : Type} (value : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      (0 : Q') <= listQMaxZero value items
  | [], _ => Q'.le_refl' 0
  | head :: _tail, hvalue =>
      Q'.le_trans' _ _ _
        (hvalue head List.mem_cons_self)
        (Q'.le_max'_left _ _)

private theorem nested_mul_divPos_eqv_divPos_nested_mul_local
    (left mass route source : Q') (hsource : (0 : Q') < source) :
    left * (mass * Q'.divPos route source hsource) ≈
      Q'.divPos (left * (mass * route)) source hsource := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ ((left * mass) *
    (route * Q'.recipPos source hsource)) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv left mass
        (route * Q'.recipPos source hsource))
  refine Q'.eqv_trans _ (((left * mass) * route) *
    Q'.recipPos source hsource) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (left * mass) route
        (Q'.recipPos source hsource))
  exact Q'.mul_eqv_congr_right _ _
    (Q'.recipPos source hsource)
    (Q'.mul_assoc_eqv left mass route)

private theorem mul_nested_swap_right_local (a b c : Q') :
    a * (b * c) ≈ (a * c) * b := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  refine Q'.eqv_trans _ (b * (a * c)) _
    (Q'.mul_assoc_eqv b a c) ?_
  exact Q'.mul_comm_eqv b (a * c)

private theorem scaled_row_le_of_raw_capacity_cross_local
    (floor mass row sourceNormalizedMaximum routeMaximum
      sourceWeight conditionalCapacity coefficientTerm : Q')
    (hfloor : (0 : Q') <= floor)
    (hmass : (0 : Q') <= mass)
    (hsourceWeight : (0 : Q') < sourceWeight)
    (hrow : row <= mass * sourceNormalizedMaximum)
    (hmaximum : sourceNormalizedMaximum <=
      Q'.divPos routeMaximum sourceWeight hsourceWeight)
    (hcross : floor * (mass * routeMaximum) <=
      coefficientTerm * (sourceWeight * conditionalCapacity)) :
    floor * row <= coefficientTerm * conditionalCapacity := by
  have hfirst : floor * row <=
      floor * (mass * sourceNormalizedMaximum) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrow hfloor
  have hmassMaximum : mass * sourceNormalizedMaximum <=
      mass * Q'.divPos routeMaximum sourceWeight hsourceWeight :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmaximum hmass
  have hsecond : floor * (mass * sourceNormalizedMaximum) <=
      floor * (mass * Q'.divPos routeMaximum sourceWeight hsourceWeight) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmassMaximum hfloor
  have hcross' : floor * (mass * routeMaximum) <=
      (coefficientTerm * conditionalCapacity) * sourceWeight :=
    Q'.le_trans' _ _ _ hcross
      (Q'.le_of_eqv
        (mul_nested_swap_right_local
          coefficientTerm sourceWeight conditionalCapacity))
  have hdivision := Q'.divPos_le_of_le_mul
    (floor * (mass * routeMaximum)) sourceWeight hsourceWeight hcross'
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (nested_mul_divPos_eqv_divPos_nested_mul_local
            floor mass routeMaximum sourceWeight hsourceWeight))
        hdivision))

/-! ## 1. Remove the row-constant source denominator from the maximum -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (fun cutoffOffset cell =>
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        cell.2)
    cutoffOffset cell

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_pos hface]
    exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        cell.2
  · rw [if_neg hface]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_oldNewFaceSourceNormalizedRouteFactor_eqv_routeFactor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hpair : cell.1 ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset cell.1 *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset cell.1 hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  have hsourceWeight : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset cell.1 := by
    unfold matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
    exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_pos hface, if_pos hface]
    unfold
      matchedEventualCanonicalNewEndpointTrafficSourceNormalizedRouteFactorOnCell
    rw [dif_pos hsourceWeight]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        (Q'.divPos
          (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
            trajectory transitionStart physicalScale cutoffOffset
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale cutoffOffset cell.1)
            cell.2)
          (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
            trajectory transitionStart physicalScale cutoffOffset cell.1)
          hsourceWeight))
      (Q'.divPos_mul_eqv _ _ hsourceWeight)
  · rw [if_neg hface, if_neg hface]
    exact Q'.mul_zero_eqv _

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQMaxZero
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
  apply listQMaxZero_nonnegative_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximum_le_routeFactorMaximum_div_sourceWeight
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    let sourceWeight :=
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset pair
    let hsourceWeight : (0 : Q') < sourceWeight := by
      have hedge := matchedEventualCanonicalCurrentPairToNext_mem
        trajectory transitionStart physicalScale cutoffOffset pair hpair
      exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        ((mem_cartesian_iff _ _ _).mp hedge |>.1)
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      Q'.divPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair)
        sourceWeight hsourceWeight := by
  dsimp only
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  have hsourceWeight : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset pair := by
    unfold matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
    exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
  apply listQMaxZero_le_bound_local
  · unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair)
      (Q'.le_of_lt (Q'.recipPos_pos _ hsourceWeight))
  intro endpointPair hendpointPair
  apply Q'.le_divPos_of_mul_le
  have hpoint :=
    matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_oldNewFaceSourceNormalizedRouteFactor_eqv_routeFactor
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair))
          (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
            trajectory transitionStart physicalScale cutoffOffset pair))
        hpoint))
    (le_listQMaxZero_of_mem
      (fun endpointPair =>
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
      hendpointPair)

/-! ## 2. Division-free raw-capacity analytic interfaces -/

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

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl
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
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  endpointRatio_le := by
    intro cutoffOffset pair hpair
    let floor := matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale
    let mass :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset
    let row := matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
      trajectory transitionStart physicalScale cutoffOffset pair
    let sourceNormalizedMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let routeMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let sourceWeight :=
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset pair
    let conditionalCapacity :=
      matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let coefficientTerm := control.coefficient *
      invSqTerm offset offset_at_least_two cutoffOffset
    have hedge := matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale cutoffOffset pair hpair
    have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
    have hsourceWeight : (0 : Q') < sourceWeight := by
      dsimp only [sourceWeight]
      unfold matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
      exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have hcross := control.envelope_le cutoffOffset pair hpair
    have hcapacity :=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
        trajectory transitionStart physicalScale cutoffOffset pair
    have hcross' : floor * (mass * routeMaximum) <=
        coefficientTerm * (sourceWeight * conditionalCapacity) :=
      Q'.le_trans' _ _ _ hcross
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left coefficientTerm _ _ hcapacity))
    exact scaled_row_le_of_raw_capacity_cross_local
      floor mass row sourceNormalizedMaximum routeMaximum
      sourceWeight conditionalCapacity coefficientTerm
      (Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale))
      (Q'.add_le_add
        (correctedSlabIncrement_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
        (componentMergerResidual_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset))
      hsourceWeight
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_sourceNormalizedRouteMaximum
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximum_le_routeFactorMaximum_div_sourceWeight
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      hcross'

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRawCapacity_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
    oldNew.toEndpointRatioControl newOld newNew cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl
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
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  endpointRatio_le := by
    intro cutoffOffset pair hpair
    let floor := matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale
    let mass :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset
    let row := matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
      trajectory transitionStart physicalScale cutoffOffset pair
    let sourceNormalizedMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let routeMaximum :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let sourceWeight :=
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset pair
    let conditionalCapacity :=
      matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    let coefficientTerm := control.coefficient *
      invSqTerm offset offset_at_least_two cutoffOffset
    have hedge := matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale cutoffOffset pair hpair
    have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
    have hsourceWeight : (0 : Q') < sourceWeight := by
      dsimp only [sourceWeight]
      unfold matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
      exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have hcross := control.envelope_le cutoffOffset pair hpair
    have hcapacity :=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
        trajectory transitionStart physicalScale cutoffOffset pair
    have hcross' : floor * (mass * routeMaximum) <=
        coefficientTerm * (sourceWeight * conditionalCapacity) :=
      Q'.le_trans' _ _ _ hcross
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left coefficientTerm _ _ hcapacity))
    exact scaled_row_le_of_raw_capacity_cross_local
      floor mass row sourceNormalizedMaximum routeMaximum
      sourceWeight conditionalCapacity coefficientTerm
      (Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale))
      (correctedSlabIncrement_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)
      hsourceWeight
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_sourceNormalizedRouteMaximum_of_noMerger
        trajectory transitionStart physicalScale cutoffOffset pair hpair
        (control.noMerger cutoffOffset))
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximum_le_routeFactorMaximum_div_sourceWeight
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      hcross'

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRawCapacity_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
    oldNew.toEndpointRatioControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_oldNewFaceSourceNormalizedRouteFactor_eqv_routeFactor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximum_le_routeFactorMaximum_div_sourceWeight
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRawCapacity_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRawCapacity_and_otherFaces
