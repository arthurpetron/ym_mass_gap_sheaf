/-
# Old--new face: new-block mass times a row-local projective amplification

The old--new endpoint-ratio row contains one explicit stationary pair weight
and one remaining projective route factor.  On the literal new-endpoint list,
divide the exact old--new summand by its strictly positive stationary pair
weight and take a located maximum only over that list and the selected mapped
current edge.

This bounds the exact old--new row by stationary new-endpoint mass times a
row-local projective amplification, then by twice the later new-block mass
times that same maximum.  A corresponding inverse-square estimate compiles
to the exact old--new endpoint-ratio control, while the new--old and new--new
lanes remain independent.

No quantitative amplification or new-block decay estimate, continuum theory,
or Clay conclusion is supplied.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic
open YMGap.Continuum.FiniteDeterministicKernelPushforward
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
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem listQMaxZero_nonnegative_on_local
    {A : Type} (value : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      (0 : Q') <= listQMaxZero value items
  | [], _ => Q'.le_refl' 0
  | head :: _tail, hvalue =>
      Q'.le_trans' _ _ _
        (hvalue head List.mem_cons_self)
        (Q'.le_max'_left _ _)

/-! ## 1. Divide only by actual positive endpoint-pair mass -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset cell.2
  if hweight : (0 : Q') < weight then
    Q'.divPos
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset cell)
      weight hweight
  else 0

private theorem oldNewFaceEndpointRatio_nonnegative_on_actual_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  by_cases hface :
      YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_pos hface]
    have htransition : (0 : Q') <=
        matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
          trajectory transitionStart physicalScale cutoffOffset cell := by
      unfold matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
      exact
        centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative
          _ _ _ _
    exact Q'.le_trans' _ _ _ htransition
      (Q'.le_of_eqv
        (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
          trajectory transitionStart physicalScale cutoffOffset cell
          hendpointPair))
  · rw [if_neg hface]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell_nonnegative_on_actual
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
  by_cases hweight : (0 : Q') <
      matchedEventualCanonicalNewEndpointStationaryPairWeight
        trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [dif_pos hweight]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (oldNewFaceEndpointRatio_nonnegative_on_actual_local
        trajectory transitionStart physicalScale cutoffOffset cell
        hendpointPair)
      (Q'.le_of_lt (Q'.recipPos_pos _ hweight))
  · rw [dif_neg hweight]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_projectiveAmplification
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2 *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
          trajectory transitionStart physicalScale cutoffOffset cell := by
  have hweight := matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
    trajectory transitionStart physicalScale cutoffOffset cell.2
    hendpointPair
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
  rw [dif_pos hweight]
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.divPos_mul_eqv
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
          trajectory transitionStart physicalScale cutoffOffset cell)
        (matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2)
        hweight))
    (Q'.mul_comm_eqv _ _)

/-! ## 2. A located maximum on one mapped row and one face -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQMaxZero
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
  apply listQMaxZero_nonnegative_on_local
  intro endpointPair hendpointPair
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell_nonnegative_on_actual
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hendpointPair

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_stationaryMass_mul_projectiveAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointStationaryMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset
  let amplification := fun endpointPair =>
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)
  let maximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
  have hsum :
      listQSum
          (fun endpointPair =>
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
              trajectory transitionStart physicalScale cutoffOffset
              (pair, endpointPair)) items <=
        listQSum (fun endpointPair => weight endpointPair * maximum) items := by
    apply listQSum_le_termwise_local
    intro endpointPair hendpointPair
    have hamp : amplification endpointPair <= maximum :=
      le_listQMaxZero_of_mem amplification items hendpointPair
    have hweight0 : (0 : Q') <= weight endpointPair :=
      matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
        endpointPair hendpointPair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_projectiveAmplification
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) hendpointPair))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hamp hweight0)
  refine Q'.le_trans' _ _ _ hsum ?_
  unfold matchedEventualCanonicalNewEndpointStationaryMass
  exact Q'.le_of_eqv
    (YMGap.Continuum.FiniteWeightedGramSOS.listQSum_mul_right
      weight maximum items)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_twoNewBlockMass_mul_projectiveAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      (Q'.ofNat 2 *
          matchedEventualCanonicalLaterNewBlockMass
            trajectory transitionStart physicalScale cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_stationaryMass_mul_projectiveAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset pair)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalNewEndpointStationaryMass_le_two_newMass
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair))

/-! ## 3. The first facewise analytic interface -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNewBlockProjectiveAmplificationInverseSquareControl
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
        ((Q'.ofNat 2 *
            matchedEventualCanonicalLaterNewBlockMass
              trajectory transitionStart physicalScale cutoffOffset) *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNewBlockProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNewBlockProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  endpointRatio_le := by
    intro cutoffOffset pair hpair
    have hfloor0 : (0 : Q') <=
        matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale :=
      Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_twoNewBlockMass_mul_projectiveAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset pair)
        hfloor0)
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNewBlockProjectiveAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNewBlockProjectiveAmplificationInverseSquareControl
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

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell_nonnegative_on_actual
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_projectiveAmplification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_stationaryMass_mul_projectiveAmplificationMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_twoNewBlockMass_mul_projectiveAmplificationMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNewBlockProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNewBlockProjectiveAmplification_and_otherFaces
