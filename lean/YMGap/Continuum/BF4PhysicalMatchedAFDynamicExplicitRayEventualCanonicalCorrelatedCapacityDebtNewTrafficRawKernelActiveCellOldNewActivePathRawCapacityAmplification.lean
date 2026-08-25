/-
# Old--new row-active path/raw-capacity amplification

The sharp old--new frontier is a joint estimate, not separate extrema.  This
module divides the row-active routed path-length square by the raw capacity of
the same mapped current pair, with the shared ray floor kept in the numerator.
The quotient is totalized by zero only when capacity is not positive.

On the exact current carrier this totalization is lossless.  Positive literal
route traffic implies positive row capacity through the actual used edge.  If
capacity is not positive, the route maximum and hence the row-active quadratic
maximum are both setoid-equal to zero.  A located maximum over the literal
current-pair carrier therefore gives one exact, observable-connected scalar
amplification stream.

General-merger and executable no-merger compilers need only bound the relevant
new-mass term times this joint maximum by an inverse-square sequence.  They
return the preceding exact raw-capacity interfaces and unchanged three-face
debt maximum.  No cutoff estimate for the joint maximum, merger control,
no-merger theorem, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCapacitySectorFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRouteSectorCapacityFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

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

private theorem capacityOnCurrentPair_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  unfold
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource))
    (Q'.mul_nonneg _ _ (by decide)
      (centralPhysicalFiniteConditionalKernel_nonnegative
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        edge.1 edge.2))

private theorem capacityOnCurrentPair_pos_of_oldNewRouteFactorOnCell_pos_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair endpointPair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
    (hroute : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair)) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let rawCapacity :=
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
      trajectory transitionStart physicalScale cutoffOffset edge
  have hdata :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactor_pos_mappedEdge_mem_sector_and_kernel_pos
      trajectory transitionStart physicalScale cutoffOffset pair endpointPair
      hpair hendpointPair hroute
  dsimp only at hdata
  have hrawPositive : (0 : Q') < rawCapacity := by
    unfold rawCapacity
      matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
    exact Q'.mul_pos (by decide) hdata.2.2
  have heq :=
    matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge_eqv_rawKernelCapacity
      trajectory transitionStart physicalScale cutoffOffset edge hdata.1
  have hrawLeSource := Q'.ge_of_eqv heq
  unfold
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
  exact Q'.pos_of_lt_of_le hrawPositive hrawLeSource

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

private theorem activePathLengthSquareMaximum_eqv_zero_of_capacity_not_pos_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hcapacity : ¬ (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair ≈ 0 := by
  have hactiveLe :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair <= 0 := by
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
    apply listQMaxZero_le_bound_local _ 0 (Q'.le_refl' 0)
    intro endpointPair hendpointPair
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareOnCell
    by_cases hroute : (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair)
    · exact False.elim
        (hcapacity
          (capacityOnCurrentPair_pos_of_oldNewRouteFactorOnCell_pos_local
            trajectory transitionStart physicalScale cutoffOffset
            pair endpointPair hpair hendpointPair hroute))
    · rw [if_neg hroute]
      exact Q'.le_refl' 0
  exact Q'.eqv_of_le_le hactiveLe
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset pair)

private theorem floor_mul_mass_route_swap_local
    (floor mass route : Q') :
    floor * (mass * route) ≈ mass * (floor * route) := by
  refine Q'.eqv_trans _ ((floor * mass) * route) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv floor mass route)) ?_
  refine Q'.eqv_trans _ ((mass * floor) * route) _
    (Q'.mul_eqv_congr_right _ _ route
      (Q'.mul_comm_eqv floor mass)) ?_
  exact Q'.mul_assoc_eqv mass floor route

private theorem scaled_route_le_of_active_amplification_local
    (floor mass route active amplification amplificationMaximum
      coefficientTerm capacity : Q')
    (hfloor : (0 : Q') <= floor)
    (hmass : (0 : Q') <= mass)
    (hcapacity : (0 : Q') <= capacity)
    (hrouteActive : route <= active)
    (hfloorActive : floor * active <= amplification * capacity)
    (hamplificationMaximum : amplification <= amplificationMaximum)
    (hcontrol : mass * amplificationMaximum <= coefficientTerm) :
    floor * (mass * route) <= coefficientTerm * capacity := by
  have hrouteScaled : mass * route <= mass * active :=
    Q'.mul_le_mul_of_nonneg_left _ _ mass hrouteActive hmass
  have hfloorRoute : floor * (mass * route) <= floor * (mass * active) :=
    Q'.mul_le_mul_of_nonneg_left _ _ floor hrouteScaled hfloor
  have hactiveScaled : mass * (floor * active) <=
      mass * (amplification * capacity) :=
    Q'.mul_le_mul_of_nonneg_left _ _ mass hfloorActive hmass
  have hampScaled : mass * amplification <= mass * amplificationMaximum :=
    Q'.mul_le_mul_of_nonneg_left _ _ mass
      hamplificationMaximum hmass
  have hampCoefficient : mass * amplification <= coefficientTerm :=
    Q'.le_trans' _ _ _ hampScaled hcontrol
  have hcapacityScaled : (mass * amplification) * capacity <=
      coefficientTerm * capacity :=
    Q'.mul_le_mul_of_nonneg_right _ _ capacity
      hampCoefficient hcapacity
  exact Q'.le_trans' _ _ _ hfloorRoute
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (floor_mul_mass_route_swap_local floor mass active))
      (Q'.le_trans' _ _ _ hactiveScaled
        (Q'.le_trans' _ _ _
          (Q'.ge_of_eqv
            (Q'.mul_assoc_eqv mass amplification capacity))
          hcapacityScaled)))

/-! ## 1. Exact row-active path/raw-capacity amplification -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  let numerator :=
    matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
  let capacity :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos numerator capacity hcapacity
  else 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
  by_cases hcapacity : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair_nonnegative
          trajectory transitionStart physicalScale cutoffOffset pair))
      (Q'.le_of_lt (Q'.recipPos_pos _ hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficSharedFloor_mul_activePathLengthSquareMaximum_le_activePathRawCapacityAmplification_mul_capacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let numerator :=
    matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
  let capacity :=
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  by_cases hcapacity : (0 : Q') < capacity
  · unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
    rw [dif_pos hcapacity]
    exact Q'.ge_of_eqv (Q'.divPos_mul_eqv numerator capacity hcapacity)
  · have hactiveZero :=
      activePathLengthSquareMaximum_eqv_zero_of_capacity_not_pos_local
        trajectory transitionStart physicalScale cutoffOffset pair hpair hcapacity
    have hnumeratorZero : numerator ≈ 0 := by
      dsimp only [numerator]
      refine Q'.eqv_trans _
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * 0) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _ hactiveZero
      · exact Q'.mul_zero_eqv _
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
    rw [dif_neg hcapacity]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hnumeratorZero)
      (Q'.mul_nonneg _ _ (Q'.le_refl' 0)
        (capacityOnCurrentPair_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset pair hpair))

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
  exact BF4PhysicalFiniteVacuumSectorPathMaximum.listQMaxZero_nonnegative _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_maximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
  exact BF4PhysicalFiniteVacuumSectorPathMaximum.le_listQMaxZero_of_mem
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    hpair

/-! ## 2. One scalar joint-amplification stream compiles to exact debt -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathRawCapacityAmplificationInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset,
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset) *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathRawCapacityAmplificationInverseSquareControl.toActivePathLengthSquareRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathLengthSquareRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := by
    intro cutoffOffset pair hpair
    exact scaled_route_le_of_active_amplification_local
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset)
      (control.coefficient * invSqTerm offset offset_at_least_two cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale))
      (Q'.add_le_add
        (correctedSlabIncrement_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
        (componentMergerResidual_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset))
      (capacityOnCurrentPair_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (Q'.le_refl' _)
      (matchedEventualCanonicalNewEndpointTrafficSharedFloor_mul_activePathLengthSquareMaximum_le_activePathRawCapacityAmplification_mul_capacity
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_maximum
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (control.envelope_le cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitActivePathRawCapacityAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathRawCapacityAmplificationInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitActivePathLengthSquareRawCapacity_and_otherFaces
    oldNew.toActivePathLengthSquareRawCapacityControl newOld newNew cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathRawCapacityAmplificationInverseSquareControl
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
  envelope_le : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathRawCapacityAmplificationInverseSquareControl.toActivePathLengthSquareRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathLengthSquareRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  noMerger := control.noMerger
  envelope_le := by
    intro cutoffOffset pair hpair
    exact scaled_route_le_of_active_amplification_local
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRoutedPathLengthSquareMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset)
      (control.coefficient * invSqTerm offset offset_at_least_two cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)
      (Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale))
      (correctedSlabIncrement_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)
      (capacityOnCurrentPair_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (Q'.le_refl' _)
      (matchedEventualCanonicalNewEndpointTrafficSharedFloor_mul_activePathLengthSquareMaximum_le_activePathRawCapacityAmplification_mul_capacity
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_maximum
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (control.envelope_le cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerActivePathRawCapacityAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathRawCapacityAmplificationInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerActivePathLengthSquareRawCapacity_and_otherFaces
    oldNew.toActivePathLengthSquareRawCapacityControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.matchedEventualCanonicalNewEndpointTrafficSharedFloor_mul_activePathLengthSquareMaximum_le_activePathRawCapacityAmplification_mul_capacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationOnCurrentPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathRawCapacityAmplificationInverseSquareControl.toActivePathLengthSquareRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitActivePathRawCapacityAmplification_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathRawCapacityAmplificationInverseSquareControl.toActivePathLengthSquareRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerActivePathRawCapacityAmplification_and_otherFaces
