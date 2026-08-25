/-
# Old--new traffic: cancel endpoint mass to a source-normalized route factor

On an actual old--new cell, the transition-product summand is the endpoint
stationary pair weight times the literal routed path factor, divided by the
mapped source weight.  The existing projective amplification divides that
same summand by the endpoint stationary pair weight.  Positivity therefore
allows the endpoint weight to cancel exactly.

This module carries that cancellation through the located row maximum and
through the corrected-slab/component-merger split.  The remaining analytic
quantity is explicit: route length times directed multiplicity, divided by
the mapped source stationary weight.  It does not bound that source-normalized
route maximum, the slab increment, or the merger residual.  No continuum
theory or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or declaration marked noncomputable is
used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
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

private theorem listQMaxZero_mono_on_local
    {A : Type} (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
      listQMaxZero left items <= listQMaxZero right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hall => by
      unfold listQMaxZero
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
      (0 : Q') <= listQMaxZero value items
  | [], _ => Q'.le_refl' 0
  | head :: _tail, hvalue =>
      Q'.le_trans' _ _ _
        (hvalue head List.mem_cons_self)
        (Q'.le_max'_left _ _)

private theorem mul_divPos_eqv_divPos_mul_left_local
    (weight route source : Q') (hsource : (0 : Q') < source) :
    weight * Q'.divPos route source hsource ≈
      Q'.divPos (weight * route) source hsource := by
  unfold Q'.divPos
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv weight route (Q'.recipPos source hsource))

/-! ## 1. The literal residual after endpoint-weight cancellation -/

def matchedEventualCanonicalNewEndpointTrafficSourceNormalizedRouteFactorOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let sourceWeight :=
    matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
      trajectory transitionStart physicalScale cutoffOffset cell.1
  if hsourceWeight : (0 : Q') < sourceWeight then
    Q'.divPos
      (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        cell.2)
      sourceWeight hsourceWeight
  else 0

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficSourceNormalizedRouteFactorOnCell
      trajectory transitionStart physicalScale)
    cutoffOffset cell

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_pos hface]
    unfold
      matchedEventualCanonicalNewEndpointTrafficSourceNormalizedRouteFactorOnCell
    by_cases hsource : (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset cell.1
    · rw [dif_pos hsource]
      unfold Q'.divPos
      exact Q'.mul_nonneg _ _
        (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_nonnegative
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset cell.1)
          cell.2)
        (Q'.le_of_lt (Q'.recipPos_pos _ hsource))
    · rw [dif_neg hsource]
      exact Q'.le_refl' 0
  · rw [if_neg hface]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_stationaryWeight_mul_sourceNormalizedRouteFactor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hpair : cell.1 ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2 *
        matchedEventualCanonicalNewEndpointTrafficSourceNormalizedRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset cell.1 hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  have hsourceWeight : (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset cell.1 := by
    unfold matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
    exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  unfold matchedEventualCanonicalNewEndpointTrafficSourceNormalizedRouteFactorOnCell
  rw [dif_pos hsourceWeight]
  refine Q'.eqv_trans _
    (Q'.divPos
      (matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2 *
        matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset cell.1)
          cell.2)
      (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
        trajectory transitionStart physicalScale cutoffOffset cell.1)
      hsourceWeight) _ ?_ ?_
  · unfold matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
    exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficTransitionTerm_eqv_stationaryWeightRouteFactor_div_sourceWeight
        trajectory transitionStart physicalScale cutoffOffset
        cell.1 cell.2 hpair hendpointPair
  · exact Q'.eqv_symm
      (mul_divPos_eqv_divPos_mul_left_local
        (matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2)
        (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale cutoffOffset cell.1)
          cell.2)
        (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        hsourceWeight)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_sourceNormalizedRouteFactor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hpair : cell.1 ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2 *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
          trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_pos hface, if_pos hface]
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
          trajectory transitionStart physicalScale cutoffOffset cell
          hendpointPair))
      (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_stationaryWeight_mul_sourceNormalizedRouteFactor
        trajectory transitionStart physicalScale cutoffOffset cell
        hpair hendpointPair)
  · rw [if_neg hface, if_neg hface]
    exact Q'.eqv_symm
      (Q'.mul_zero_eqv
        (matchedEventualCanonicalNewEndpointStationaryPairWeight
          trajectory transitionStart physicalScale cutoffOffset cell.2))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell_eqv_sourceNormalizedRouteFactor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hpair : cell.1 ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  have hweight := matchedEventualCanonicalNewEndpointStationaryPairWeight_pos
    trajectory transitionStart physicalScale cutoffOffset cell.2
    hendpointPair
  apply Q'.mul_left_cancel_of_pos hweight
  refine Q'.eqv_trans _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
      trajectory transitionStart physicalScale cutoffOffset cell) _ ?_ ?_
  · exact Q'.eqv_symm
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_projectiveAmplification
        trajectory transitionStart physicalScale cutoffOffset cell
        hendpointPair)
  · exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_sourceNormalizedRouteFactor
        trajectory transitionStart physicalScale cutoffOffset cell
        hpair hendpointPair

/-! ## 2. The exact row-local maximum after cancellation -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQMaxZero
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
  apply listQMaxZero_nonnegative_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximum_le_sourceNormalizedRouteMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
  apply listQMaxZero_mono_on_local
  intro endpointPair hendpointPair
  exact Q'.le_of_eqv
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell_eqv_sourceNormalizedRouteFactor
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_sourceNormalizedRouteMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_projectiveAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset pair)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximum_le_sourceNormalizedRouteMaximum
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_sourceNormalizedRouteMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_sourceNormalizedRouteMaximum
      trajectory transitionStart physicalScale cutoffOffset pair hpair)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_sourceNormalizedRouteMaximum_of_noMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hcheck :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
        trajectory transitionStart physicalScale cutoffOffset = true) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_sourceNormalizedRouteMaximum
      trajectory transitionStart physicalScale cutoffOffset pair hpair)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
        trajectory transitionStart physicalScale cutoffOffset hcheck)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair))

/-! ## 3. Source-normalized analytic interfaces compile to the exact debt -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitSourceNormalizedRouteInverseSquareControl
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
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitSourceNormalizedRouteInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitSourceNormalizedRouteInverseSquareControl
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
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_sourceNormalizedRouteMaximum
          trajectory transitionStart physicalScale cutoffOffset pair hpair)
        hfloor0)
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitSourceNormalizedRoute_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitSourceNormalizedRouteInverseSquareControl
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

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerSourceNormalizedRouteInverseSquareControl
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
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerSourceNormalizedRouteInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerSourceNormalizedRouteInverseSquareControl
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
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_sourceNormalizedRouteMaximum_of_noMerger
          trajectory transitionStart physicalScale cutoffOffset pair hpair
          (control.noMerger cutoffOffset))
        hfloor0)
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerSourceNormalizedRoute_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerSourceNormalizedRouteInverseSquareControl
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

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficOldNewFaceSourceNormalizedRouteFactorOnCell_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_stationaryWeight_mul_sourceNormalizedRouteFactor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_sourceNormalizedRouteFactor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell_eqv_sourceNormalizedRouteFactor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximum_le_sourceNormalizedRouteMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_sourceNormalizedRouteMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_sourceNormalizedRouteMaximum_of_noMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitSourceNormalizedRouteInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitSourceNormalizedRoute_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerSourceNormalizedRouteInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewSourceNormalizedRoute.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerSourceNormalizedRoute_and_otherFaces
