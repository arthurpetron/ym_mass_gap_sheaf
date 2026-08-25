/-
# Literal routed-load form of the three matched new-traffic faces

The denominator-free face numerators still display stationary weights and
route factors as a product.  The existing routed-occurrence theorem identifies
that product exactly with the weighted load contributed to the mapped current
edge by the actual transported path of the actual endpoint pair.

This module preserves each shell-face mask while lifting that pointwise
identity to the exact endpoint row.  Each face numerator row becomes the
shared coercivity floor times a literal face-restricted routed path-load row.
Three independently inhabitable routed-load/capacity balances then compile to
the preceding capacity-balance controls and the unchanged exact debt maximum.

No routed-load estimate, source/target reversal theorem, continuum theory, or
Clay conclusion is supplied.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newOldShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newNewShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private theorem masked_eqv_floor_mul_masked
    (face : Prop) [Decidable face]
    (numerator load floor : Q')
    (hvalue : numerator ≈ floor * load) :
    (if face then numerator else 0) ≈
      floor * (if face then load else 0) := by
  by_cases hface : face
  · rw [if_pos hface, if_pos hface]
    exact hvalue
  · rw [if_neg hface, if_neg hface]
    exact Q'.eqv_symm (Q'.mul_zero_eqv floor)

/-! ## 1. One exact cell as shared floor times literal routed load -/

def matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset cell.1
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset)
      cell.2.1 cell.2.2)
    edge.1 edge.2

theorem matchedEventualCanonicalNewEndpointTrafficWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
          trajectory transitionStart physicalScale cutoffOffset cell := by
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset cell.2
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let route := matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  let load := matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  have hload : load ≈ weight * route :=
    matchedEventualCanonicalTransportedBridgeNewEndpointPathLoad_eqv_stationaryWeight_mul_routeFactor
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset cell.1)
      cell.2 hendpointPair
  change weight * (floor * route) ≈ floor * load
  refine Q'.eqv_trans _ (floor * (weight * route)) _ ?_ ?_
  · refine Q'.eqv_trans _ ((weight * floor) * route) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv weight floor route)) ?_
    refine Q'.eqv_trans _ ((floor * weight) * route) _
      (Q'.mul_eqv_congr_right _ _ route (Q'.mul_comm_eqv weight floor)) ?_
    exact Q'.mul_assoc_eqv floor weight route
  · exact Q'.mul_eqv_congr_left floor _ _ (Q'.eqv_symm hload)

/-! ## 2. Preserve the three literal face masks -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
      trajectory transitionStart physicalScale)
    cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
      trajectory transitionStart physicalScale)
    cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLoadOnCell
      trajectory transitionStart physicalScale)
    cutoffOffset cell

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
          trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
  exact masked_eqv_floor_mul_masked _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
      trajectory transitionStart physicalScale cutoffOffset cell hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
          trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := newOldShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
  exact masked_eqv_floor_mul_masked _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
      trajectory transitionStart physicalScale cutoffOffset cell hendpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hendpointPair : cell.2 ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
          trajectory transitionStart physicalScale cutoffOffset cell := by
  letI := newNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
  exact masked_eqv_floor_mul_masked _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
      trajectory transitionStart physicalScale cutoffOffset cell hendpointPair)

/-! ## 3. Exact face-restricted routed-load rows -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow
  refine Q'.eqv_trans _
    (listQSum
      (fun endpointPair =>
        matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)) _ ?_ ?_
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_congr_on _ _ _
      (fun endpointPair hendpointPair =>
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) hendpointPair)
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_mul_left
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale)
      (fun endpointPair =>
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoad
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow
  refine Q'.eqv_trans _
    (listQSum
      (fun endpointPair =>
        matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)) _ ?_ ?_
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_congr_on _ _ _
      (fun endpointPair hendpointPair =>
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) hendpointPair)
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_mul_left
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale)
      (fun endpointPair =>
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoad
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow
        trajectory transitionStart physicalScale cutoffOffset pair ≈
      matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair := by
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow
  refine Q'.eqv_trans _
    (listQSum
      (fun endpointPair =>
        matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale *
          matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)) _ ?_ ?_
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_congr_on _ _ _
      (fun endpointPair hendpointPair =>
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) hendpointPair)
  · exact YMGap.Continuum.FiniteDeterministicKernelPushforward.listQSum_mul_left
      (matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale)
      (fun endpointPair =>
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoad
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair))
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. Routed-load capacity balances and their exact rejoin -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedLoadCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  load_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient *
          invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedLoadCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  load_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient *
          invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedLoadCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  load_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        matchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient *
          invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedLoadCapacityBalanceInverseSquareControl.toCapacityBalanceControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedLoadCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  numerator_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair))
      (control.load_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedLoadCapacityBalanceInverseSquareControl.toCapacityBalanceControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedLoadCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewOldFaceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  numerator_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair))
      (control.load_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedLoadCapacityBalanceInverseSquareControl.toCapacityBalanceControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedLoadCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficNewNewFaceCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  numerator_le := by
    intro cutoffOffset pair hpair
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
          trajectory transitionStart physicalScale cutoffOffset pair))
      (control.load_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceRoutedLoadCapacityBalances
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedLoadCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld :
      MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedLoadCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew :
      MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedLoadCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient +
          (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceCapacityBalances
    oldNew.toCapacityBalanceControl newOld.toCapacityBalanceControl
      newNew.toCapacityBalanceControl cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.matchedEventualCanonicalNewEndpointTrafficWeightedNumerator_eqv_sharedFloor_mul_routedPathLoad
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow_eqv_sharedFloor_mul_routedPathLoadRow
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedLoadCapacityBalanceInverseSquareControl.toCapacityBalanceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.MatchedEventualCanonicalNewEndpointTrafficNewOldFaceRoutedLoadCapacityBalanceInverseSquareControl.toCapacityBalanceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.MatchedEventualCanonicalNewEndpointTrafficNewNewFaceRoutedLoadCapacityBalanceInverseSquareControl.toCapacityBalanceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRoutedLoad.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceRoutedLoadCapacityBalances
