/-
# Dimensionless relative-source loads for the three matched traffic faces

The literal routed path load and the mapped-pair capacity share the strictly
positive stationary weight of the mapped edge source.  This module cancels
that common factor without changing the routing, edge, endpoint list, or face.
Each face path-load row is identified exactly with source weight times a
face-restricted relative-source load row, while the row capacity is exactly
source weight times the corresponding conditional capacity.

Three dimensionless relative-load/conditional-capacity estimates therefore
compile to the routed-load balances and the unchanged exact debt maximum.
These are the direct inputs for the existing transition-product telescoping
theorems.

No relative-load estimate, continuum theory, or Clay conclusion is supplied.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
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

private theorem masked_weight_mul_eqv_masked
    (face : Prop) [Decidable face]
    (weight relative load : Q')
    (hvalue : weight * relative ≈ load) :
    weight * (if face then relative else 0) ≈
      if face then load else 0 := by
  by_cases hface : face
  · rw [if_pos hface, if_pos hface]
    exact hvalue
  · rw [if_neg hface, if_neg hface]
    exact Q'.mul_zero_eqv weight

private theorem mul_swap_middle_eqv_local (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-! ## 1. Source weight, conditional capacity, and one relative demand -/

def matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0 edge.1

def matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  HalfPow.half * centralPhysicalFiniteConditionalKernel
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0
    edge.1 edge.2

def matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemandOnCell
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset cell.1
  centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    edge.1 edge.2 cell.2

theorem matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset pair *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair :=
  Q'.eqv_refl _

theorem matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_relativeDemand_eqv_routedPathLoad
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hpair : cell.1 ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset cell.1 *
        matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemandOnCell
          trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
        trajectory transitionStart physicalScale cutoffOffset cell := by
  have hedge := matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale cutoffOffset cell.1 hpair
  have hsource := (mem_cartesian_iff _ _ _).mp hedge |>.1
  exact centralPhysicalFiniteWeight_mul_routedRelativePairDemand_eqv_pathLoad
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    hsource
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset cell.1).2
    cell.2

/-! ## 2. Three face-restricted relative-source rows -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceDemand
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemandOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceDemand
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemandOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceDemand
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficRelativeSourceDemandOnCell
      trajectory transitionStart physicalScale) cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceDemand
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceDemand
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceDemand
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

private theorem faceRow_eqv_sourceWeight_mul_relativeRow_local
    {A : Type} (pathLoad relative : A -> Q')
    (items : List A) (weight : Q')
    (hpoint : forall item, item ∈ items ->
      weight * relative item ≈ pathLoad item) :
    listQSum pathLoad items ≈ weight * listQSum relative items := by
  refine Q'.eqv_trans _
    (listQSum (fun item => weight * relative item) items) _ ?_ ?_
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_congr_on
      _ _ items (fun item hitem => Q'.eqv_symm (hpoint item hitem))
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_mul_left
      weight relative items

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset pair *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow
  apply faceRow_eqv_sourceWeight_mul_relativeRow_local
  intro endpointPair _
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceDemand
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  exact masked_weight_mul_eqv_masked _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_relativeDemand_eqv_routedPathLoad
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset pair *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow
  apply faceRow_eqv_sourceWeight_mul_relativeRow_local
  intro endpointPair _
  letI := newOldShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceDemand
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
  exact masked_weight_mul_eqv_masked _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_relativeDemand_eqv_routedPathLoad
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
          trajectory transitionStart physicalScale cutoffOffset pair *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow
  apply faceRow_eqv_sourceWeight_mul_relativeRow_local
  intro endpointPair _
  letI := newNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceDemand
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
  exact masked_weight_mul_eqv_masked _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_relativeDemand_eqv_routedPathLoad
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair) hpair)

/-! ## 3. Dimensionless controls compile back through the source weight -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  relative_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  relative_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  relative_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

private theorem routedLoadBalance_of_relativeSourceBalance_local
    (floor pathLoad relative weight coefficient term conditional capacity : Q')
    (hweight : (0 : Q') <= weight)
    (hpath : pathLoad ≈ weight * relative)
    (hcapacity : capacity ≈ weight * conditional)
    (hrelative : floor * relative <= (coefficient * term) * conditional) :
    floor * pathLoad <= (coefficient * term) * capacity := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ weight hrelative hweight
  have hleft : floor * pathLoad ≈ weight * (floor * relative) := by
    exact Q'.eqv_trans _ (floor * (weight * relative)) _
      (Q'.mul_eqv_congr_left floor _ _ hpath)
      (mul_swap_middle_eqv_local floor weight relative)
  have hright : (coefficient * term) * capacity ≈
      weight * ((coefficient * term) * conditional) := by
    exact Q'.eqv_trans _ ((coefficient * term) * (weight * conditional)) _
      (Q'.mul_eqv_congr_left (coefficient * term) _ _ hcapacity)
      (mul_swap_middle_eqv_local (coefficient * term) weight conditional)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

private theorem mappedSourceWeight_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    (0 : Q') <= matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
      trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight
    centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative
    (Q'.le_of_lt (trajectory.nome_pos physicalScale)) _ 0 _

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceCapacityBalanceInverseSquareControl.toRoutedLoadControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedLoadCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  load_le := by
    intro cutoffOffset pair hpair
    exact routedLoadBalance_of_relativeSourceBalance_local _ _ _ _ _ _ _ _
      (mappedSourceWeight_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
        trajectory transitionStart physicalScale cutoffOffset pair)
      (control.relative_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceCapacityBalanceInverseSquareControl.toRoutedLoadControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedLoadCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  load_le := by
    intro cutoffOffset pair hpair
    exact routedLoadBalance_of_relativeSourceBalance_local _ _ _ _ _ _ _ _
      (mappedSourceWeight_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
        trajectory transitionStart physicalScale cutoffOffset pair)
      (control.relative_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceCapacityBalanceInverseSquareControl.toRoutedLoadControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedLoadCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  load_le := by
    intro cutoffOffset pair hpair
    exact routedLoadBalance_of_relativeSourceBalance_local _ _ _ _ _ _ _ _
      (mappedSourceWeight_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset pair)
      (matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
        trajectory transitionStart physicalScale cutoffOffset pair hpair)
      (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
        trajectory transitionStart physicalScale cutoffOffset pair)
      (control.relative_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceRelativeSourceCapacityBalances
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceRoutedLoadCapacityBalances
    oldNew.toRoutedLoadControl newOld.toRoutedLoadControl
      newNew.toRoutedLoadControl cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair_eqv_sourceWeight_mul_conditionalCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.matchedEventualCanonicalNewEndpointTrafficMappedSourceWeight_mul_relativeDemand_eqv_routedPathLoad
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow_eqv_sourceWeight_mul_relativeSourceLoadRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRelativeSourceCapacityBalanceInverseSquareControl.toRoutedLoadControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRelativeSourceCapacityBalanceInverseSquareControl.toRoutedLoadControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRelativeSourceCapacityBalanceInverseSquareControl.toRoutedLoadControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceRelativeSourceCapacityBalances
