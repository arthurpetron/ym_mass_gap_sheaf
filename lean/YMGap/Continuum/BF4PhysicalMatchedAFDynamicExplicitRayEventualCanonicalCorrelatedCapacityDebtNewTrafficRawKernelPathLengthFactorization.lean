/-
# Routed path-length-square factorization of active raw-kernel traffic

The active-cell raw-kernel compiler leaves a literal route factor equal to
path length times the multiplicity of the selected directed edge.  This
module proves constructively that the multiplicity of any directed edge in
an arbitrary positive route is at most the total route length.  Repeated
edges are allowed; no simple-path hypothesis is inserted.

Consequently the active route-factor maximum is bounded by a located maximum
of the transported route's quadratic length scale on the same actual new
endpoint list.  The resulting envelope retains the active reciprocal raw-
kernel capacity maximum and contracts to the same exact new-debt observable.

This module supplies no quantitative path-length growth estimate, raw-kernel
floor, inverse-square estimate, no-merger certificate, continuum theory, or
Clay conclusion.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
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
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A -> Q')
    {bound : Q'} (hboundNonnegative : (0 : Q') <= bound) :
    forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      listQSum value items <= Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail :=
        listQSum_le_length_mul_local value hboundNonnegative tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value tail <=
            bound + Q'.ofNat tail.length * bound :=
        Q'.add_le_add hhead htail
      refine Q'.le_trans' _ _ _ hsum ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

private theorem weightedDirectedEdgeLoad_unitMap_le_length_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, (1 : Q')))) source target <=
      Q'.ofNat edges.length := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map]
  have hsum := listQSum_le_length_mul_local
    (fun edge : State × State =>
      weightedDirectedEdgeIndicator (edge, (1 : Q')) source target)
    (bound := (1 : Q')) (by decide) edges (by
      intro edge _hedge
      unfold weightedDirectedEdgeIndicator
      change (if edge = (source, target) then (1 : Q') else 0) <= 1
      by_cases heq : edge = (source, target)
      · rw [if_pos heq]
        exact Q'.le_refl' 1
      · rw [if_neg heq]
        decide)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat edges.length)))

/-! ## 1. Repeated-edge multiplicity is bounded by total route length -/

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_le_pathLength
    {w : Q'} {hw : (0 : Q') <= w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing left right hleft hright source target <=
      Q'.ofNat
        (PositiveKernelChainIn.edgeLength
          (routing.path left right hleft hright)) := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
  have hload := weightedDirectedEdgeLoad_unitMap_le_length_local
    (PositiveKernelChainIn.directedEdges
      (routing.path left right hleft hright)) source target
  rw [PositiveKernelChainIn.directedEdges_length_eq_edgeLength] at hload
  exact hload

/-! ## 2. Quadratic route scale on the actual new endpoint carrier -/

def matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) : Q' :=
  let w := trajectory.nome physicalScale
  let hw := Q'.le_of_lt (trajectory.nome_pos physicalScale)
  let K := transitionStart physicalScale + (cutoffOffset + 1)
  let routing := matchedEventualCanonicalTransportedRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset
  if hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    PositiveKernelChainIn.quadraticLengthScale
      (routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2)
  else 0

theorem matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair]
    exact Q'.ofNat_le_ofNat (Nat.zero_le _)
  · rw [dif_neg hpair]
    exact Q'.le_refl' 0

def matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
  apply listQMaxZero_nonnegative
  intro endpointPair
  exact
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset endpointPair

/-! ## 3. Literal route factors contract to the quadratic route scale -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_le_routedPathLengthSquare
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset edge endpointPair <=
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
  by_cases hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
  · rw [dif_pos hpair, dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let routing := matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    by_cases hedge : (edge.1, edge.2) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [if_pos hedge]
      have hmultiplicity :=
        centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_le_pathLength
          routing endpointPair.1 endpointPair.2 hfull.1 hfull.2
          edge.1 edge.2
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
        (Q'.ofNat (PositiveKernelChainIn.edgeLength path))
        hmultiplicity
        (Q'.ofNat_le_ofNat (Nat.zero_le _))
      exact Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (ofNat_mul_eqv
              (PositiveKernelChainIn.edgeLength path)
              (PositiveKernelChainIn.edgeLength path))))
    · rw [if_neg hedge]
      exact Q'.ofNat_le_ofNat (Nat.zero_le _)
  · rw [dif_neg hpair, dif_neg hpair]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell_le_routedPathLengthSquareMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat))
    (hcell : cell ∈
      matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell <=
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  have hfiltered := List.mem_filter.mp hcell
  have hcartesian := (mem_cartesian_iff _ _ _).mp hfiltered.1
  unfold matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_le_routedPathLengthSquare
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset cell.1)
      cell.2)
    (le_listQMaxZero_of_mem
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset)
      hcartesian.2)

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State -> Q') (bound : Q') :
    forall states : List State,
      (0 : Q') <= bound ->
      (forall state, state ∈ states -> value state <= bound) ->
      listQMaxZero value states <= bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hall => by
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hall head List.mem_cons_self,
          listQMaxZero_le_of_member_bound_local value bound tail hbound
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate))⟩

theorem matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum_le_routedPathLengthSquareMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
  · intro cell hcell
    exact
      matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell_le_routedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset cell hcell

/-! ## 4. Path-factorized amplification and new-block debt -/

def matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_le_pathFactorizedEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum_le_routedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  · exact Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)

def matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  (Q'.ofNat 2 *
      matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset) *
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope_le_pathFactorizedNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_le_pathFactorizedEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_pathFactorizedNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_activeFactorizedNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope_le_pathFactorizedNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 5. Type-level inverse-square interface and exact-observable contraction -/

structure MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl.toActiveFactorizedControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficActiveFactorizedInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalNewEndpointTrafficActiveFactorizedNewBlockDebtEnvelope_le_pathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

theorem MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toActiveFactorizedControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_le_pathLength
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_le_routedPathLengthSquare
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.matchedEventualCanonicalNewEndpointTrafficActiveRouteFactorMaximum_le_routedPathLengthSquareMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.matchedEventualCanonicalNewEndpointTrafficActiveFactorizedAmplificationEnvelope_le_pathFactorizedEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_pathFactorizedNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl.toActiveFactorizedControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization.MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl.debtMaximum_le
