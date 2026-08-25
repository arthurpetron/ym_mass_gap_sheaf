/-
# Endpoint-ratio form of the three exact matched traffic faces

The exact transition product along a routed prefix telescopes to the
stationary weight of the left endpoint divided by the stationary weight of
the mapped edge source.  This module performs that telescope without changing
the endpoint list, mapped edge, transported route, incidence test, path
length, directed multiplicity, or shell face.

The resulting projective endpoint-ratio rows make the cutoff placement
visible: old--new has a new right-endpoint weight, new--old has a new left
endpoint in the ratio numerator, and new--new has both.  Three endpoint-ratio
capacity estimates compile losslessly to the exact transition-product path
and debt maximum.  No estimate, continuum theory, or Clay conclusion is
supplied.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceTransitionProduct
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
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

private def newOldShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private theorem masked_eqv_masked
    (face : Prop) [Decidable face] (left right : Q')
    (hvalue : left ≈ right) :
    (if face then left else 0) ≈ if face then right else 0 := by
  by_cases hface : face
  · rw [if_pos hface, if_pos hface]
    exact hvalue
  · rw [if_neg hface, if_neg hface]
    exact Q'.eqv_refl _

/-! ## 1. Telescope one exact cell to its endpoint/source ratio -/

def matchedEventualCanonicalNewEndpointTrafficEndpointRatioOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let w := trajectory.nome physicalScale
  let hw := Q'.le_of_lt (trajectory.nome_pos physicalScale)
  let K := transitionStart physicalScale + (cutoffOffset + 1)
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset cell.1
  if hendpoint : cell.2 ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hendpoint
    let path := routing.path cell.2.1 cell.2.2 hfull.1 hfull.2
    if (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
      (((centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
            w hw K edge.1 cell.2.1 *
          centralPhysicalFiniteWeight w hw K 0 cell.2.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) *
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing cell.2.1 cell.2.2 hfull.1 hfull.2 edge.1 edge.2)
    else 0
  else 0

theorem matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointTrafficEndpointRatioOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  have hendpoint := List.mem_filter.mp hendpointPair |>.1
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hendpoint
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset cell.1
  let path := routing.path cell.2.1 cell.2.2 hfull.1 hfull.2
  unfold matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell
    matchedEventualCanonicalNewEndpointTrafficEndpointRatioOnCell
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  rw [dif_pos hendpoint, dif_pos hendpoint]
  change
    (if hedge : (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (edge.1, edge.2) hedge
      (((centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            hfull.1 prefixData.pathPrefix *
          centralPhysicalFiniteWeight
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1)) 0 cell.2.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) *
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing cell.2.1 cell.2.2 hfull.1 hfull.2 edge.1 edge.2)
    else 0) ≈
    (if (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
      (((centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1))
            edge.1 cell.2.1 *
          centralPhysicalFiniteWeight
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + (cutoffOffset + 1)) 0 cell.2.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) *
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing cell.2.1 cell.2.2 hfull.1 hfull.2 edge.1 edge.2)
    else 0)
  by_cases hedge : (edge.1, edge.2) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [dif_pos hedge, if_pos hedge]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      hfull.1 path (edge.1, edge.2) hedge
    have hratio :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        hfull.1 prefixData.pathPrefix
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hratio)))
  · rw [dif_neg hedge, if_neg hedge]
    exact Q'.eqv_refl _

/-! ## 2. Preserve the telescope through all three face rows -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficEndpointRatioOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatio
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficEndpointRatioOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatio
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficEndpointRatioOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatio
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow_eqv_endpointRatioRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProduct
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  exact masked_eqv_masked _ _ _
    (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow_eqv_endpointRatioRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioRow
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  letI := newOldShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProduct
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatio
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
  exact masked_eqv_masked _ _ _
    (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow_eqv_endpointRatioRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioRow
  apply listQSum_congr_on
  intro endpointPair hendpointPair
  letI := newNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProduct
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatio
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
  exact masked_eqv_masked _ _ _
    (matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hendpointPair)

/-! ## 3. Endpoint-ratio estimates compile to exact debt -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  endpointRatio_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  endpointRatio_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  endpointRatio_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl.toTransitionProductControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  transitionProduct_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow_eqv_endpointRatioRow
          trajectory transitionStart physicalScale cutoffOffset pair)))
      (control.endpointRatio_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl.toTransitionProductControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  transitionProduct_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow_eqv_endpointRatioRow
          trajectory transitionStart physicalScale cutoffOffset pair)))
      (control.endpointRatio_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl.toTransitionProductControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  transitionProduct_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow_eqv_endpointRatioRow
          trajectory transitionStart physicalScale cutoffOffset pair)))
      (control.endpointRatio_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceTransitionProductCapacityBalances
    oldNew.toTransitionProductControl newOld.toTransitionProductControl
      newNew.toTransitionProductControl cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.matchedEventualCanonicalNewEndpointTrafficTransitionProductOnCell_eqv_endpointRatioOnCell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.matchedEventualCanonicalNewEndpointTrafficOldNewFaceTransitionProductRow_eqv_endpointRatioRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.matchedEventualCanonicalNewEndpointTrafficNewOldFaceTransitionProductRow_eqv_endpointRatioRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.matchedEventualCanonicalNewEndpointTrafficNewNewFaceTransitionProductRow_eqv_endpointRatioRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl.toTransitionProductControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl.toTransitionProductControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl.toTransitionProductControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
