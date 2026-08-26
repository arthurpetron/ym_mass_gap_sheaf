/-
# Birth-local adaptive routing compiler for activated old--new support

An activated old--new row is a mapped current edge which is absent from the
current support graph and present at the later cutoff.  This module states the
smallest route-level alternative to paying its later raw-kernel floor.

At one consecutive-cutoff step, an adaptive completion routing keeps the
already transported route whenever both endpoints are embedded old states and
uses a supplied later-cutoff routing otherwise.  A birth-avoidance certificate
then requires every activated mapped edge to be absent from every supplied
new-endpoint path.  This is exactly the part of the routed load in which those
edges could contribute.

The compiler proves that, on every activated row, the adaptive new-endpoint
route factor, transition-product term, total new-endpoint load, and associated
capacity debt are all zero (as constructive rational equalities where
appropriate).  The routing remains an inhabitant of the existing adaptive
flow compiler, so a routed flow-capacity proof feeds the same finite-sector
pairwise variance and physical Dirichlet form; no replacement observable is
introduced.

No birth-avoiding routing or routed capacity is inhabited here.  In
particular, the module does not prove that deleting the activated edges leaves
the required new-endpoint routes connected, nor any uniform route coherence,
thermodynamic/continuum limit, continuum Yang--Mills theory, or Clay result.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationGraphBirth
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationGraphBirth
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_of_pointwise_zero_local
    {A : Type} (value : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> value item = 0) ->
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hall => by
      unfold listQSum
      rw [hall head List.mem_cons_self]
      exact Q'.eqv_trans _ (listQSum value tail) _
        (Q'.eqv_of_eq (Q'.zero_add' (listQSum value tail)))
        (listQSum_eqv_zero_of_pointwise_zero_local value tail
          (fun item hitem =>
            hall item (List.mem_cons_of_mem head hitem)))

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (heq : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ heq

/-! ## 1. Preserve transported old routes and replace only new-endpoint routes -/

/-- A later-cutoff routing which keeps the exact transported route on the
embedded old carrier and delegates only endpoint pairs involving a new state
to `newRouting`. -/
def matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (newRouting :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) where
  path := fun left right hleft hright => by
    by_cases hleftOld : left ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset
    · by_cases hrightOld : right ∈
          matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset
      · exact
          (matchedEventualCanonicalTransportedRoutingAtNext
            trajectory transitionStart physicalScale cutoffOffset).path
              left right hleft hright
      · exact newRouting.path left right hleft hright
    · exact newRouting.path left right hleft hright

theorem matchedEventualTransportedOldAdaptiveNewRoutingAtNext_path_eq_transported_of_old
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (newRouting :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0)
    (hleftOld : left ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset)
    (hrightOld : right ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    (matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset newRouting).path
        left right hleft hright =
      (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset).path
        left right hleft hright := by
  simp only [matchedEventualTransportedOldAdaptiveNewRoutingAtNext,
    dif_pos hleftOld, dif_pos hrightOld]

/-! ## 2. The exact new-endpoint route factor, load, and debt for a routing -/

def matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge endpointPair : Nat × Nat) : Q' :=
  if hpair : endpointPair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2
    if (edge.1, edge.2) ∈ PositiveKernelChainIn.directedEdges path then
      Q'.ofNat (PositiveKernelChainIn.edgeLength path) *
        centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
          routing endpointPair.1 endpointPair.2 hfull.1 hfull.2
          edge.1 edge.2
    else 0
  else 0

theorem matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting_canonical
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge endpointPair : Nat × Nat) :
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset)
        edge endpointPair =
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
        trajectory transitionStart physicalScale cutoffOffset
        edge endpointPair := by
  unfold matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair
  rfl

def matchedEventualNewEndpointTrafficLoadOnPairForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      routing edge.1 edge.2)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualNewEndpointTrafficLoadOnPairForRouting_canonical
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualNewEndpointTrafficLoadOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge =
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge :=
  rfl

def matchedEventualNewEndpointTrafficDebtOnPairForRouting
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (routing :
      CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
    (edge : Nat × Nat) : Q' :=
  matchedEventualCapacityDebtFromLoadOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge
    (matchedEventualNewEndpointTrafficLoadOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset routing edge)

theorem matchedEventualNewEndpointTrafficDebtOnPairForRouting_canonical
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualNewEndpointTrafficDebtOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalTransportedRoutingAtNext
          trajectory transitionStart physicalScale cutoffOffset) edge =
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge :=
  rfl

private theorem matchedEventualCapacityDebtFromLoadOnPair_eqv_zero_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) (load : Q') (hload : load ≈ 0) :
    matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge load ≈ 0 := by
  unfold matchedEventualCapacityDebtFromLoadOnPair
  by_cases hcapacity : (0 : Q') < HalfPow.half *
      centralPhysicalFiniteConditionalKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2
  · rw [dif_pos hcapacity]
    have hnumerator :
        matchedEventualCanonicalSupportSharedFloor
              trajectory transitionStart physicalScale * load ≈ 0 :=
      Q'.eqv_trans _
        (matchedEventualCanonicalSupportSharedFloor
            trajectory transitionStart physicalScale * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hload)
        (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _
      (Q'.divPos 0
        (HalfPow.half * centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2)
        hcapacity) _
      (divPos_eqv_congr_numerator_local hcapacity hnumerator)
      (Q'.zero_mul_eqv
        (Q'.recipPos
          (HalfPow.half * centralPhysicalFiniteConditionalKernel
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (transitionStart physicalScale + cutoffOffset) 0 edge.1 edge.2)
          hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.eqv_refl 0

/-! ## 3. Exact birth-avoidance certificate on the same old--new rows -/

structure MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type 1 where
  newRouting :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
  avoids_activated : forall pair,
    pair ∈
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset ->
    forall endpointPair,
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) ->
      let hfull :=
        centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
          (List.mem_filter.mp hendpointPair).1
      let routing := matchedEventualTransportedOldAdaptiveNewRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset newRouting
      ((matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).1,
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).2) ∉
        PositiveKernelChainIn.directedEdges
          (routing.path endpointPair.1 endpointPair.2 hfull.1 hfull.2)

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.routing
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
        trajectory transitionStart physicalScale cutoffOffset) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) :=
  matchedEventualTransportedOldAdaptiveNewRoutingAtNext
    trajectory transitionStart physicalScale cutoffOffset data.newRouting

/-! ## 4. Avoidance deletes every activated new-endpoint contribution -/

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.routeFactor_eq_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset data.routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair)
        endpointPair = 0 := by
  unfold MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.routing
  unfold matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting
  have hfullPair := (List.mem_filter.mp hendpointPair).1
  rw [dif_pos hfullPair]
  rw [if_neg (data.avoids_activated pair hpair endpointPair hendpointPair)]

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.transitionTerm_eq_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        data.routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).1
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).2
        endpointPair = 0 := by
  unfold MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.routing
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  have hfullPair := (List.mem_filter.mp hendpointPair).1
  rw [dif_pos hfullPair]
  rw [dif_neg (data.avoids_activated pair hpair endpointPair hendpointPair)]

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.load_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficLoadOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset data.routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈ 0 := by
  unfold matchedEventualNewEndpointTrafficLoadOnPairForRouting
  apply listQSum_eqv_zero_of_pointwise_zero_local
  intro endpointPair hendpointPair
  exact data.transitionTerm_eq_zero pair hpair endpointPair hendpointPair

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.debt_eqv_zero
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
        trajectory transitionStart physicalScale cutoffOffset)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualNewEndpointTrafficDebtOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset data.routing
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) ≈ 0 := by
  unfold matchedEventualNewEndpointTrafficDebtOnPairForRouting
  exact matchedEventualCapacityDebtFromLoadOnPair_eqv_zero_local
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair)
    (matchedEventualNewEndpointTrafficLoadOnPairForRouting
      trajectory transitionStart physicalScale cutoffOffset data.routing
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair))
    (data.load_eqv_zero pair hpair)

/-! ## 5. The adaptive path still feeds the same finite observable compiler -/

structure MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingFlowCapacityAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt
      (trajectory.nome_pos physicalScale)
      (transitionStart physicalScale + (cutoffOffset + 1))) : Type 1 where
  avoidance :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt
      trajectory transitionStart physicalScale cutoffOffset
  flow_capacity :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
      (trajectory.nome_pos physicalScale)
      (transitionStart physicalScale + (cutoffOffset + 1))
      rayCapacity avoidance.routing

def MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingFlowCapacityAt.toOffRayResidualCoercivityAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale cutoffOffset : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt
      (trajectory.nome_pos physicalScale)
      (transitionStart physicalScale + (cutoffOffset + 1))}
    (data :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingFlowCapacityAt
        trajectory transitionStart physicalScale cutoffOffset rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
      (trajectory.nome_pos physicalScale)
      (transitionStart physicalScale + (cutoffOffset + 1))
      rayCapacity :=
  data.flow_capacity.toOffRayResidualCoercivityAt

/-! ## Axiom audit -/

#print axioms matchedEventualTransportedOldAdaptiveNewRoutingAtNext
#print axioms
  matchedEventualTransportedOldAdaptiveNewRoutingAtNext_path_eq_transported_of_old
#print axioms matchedEventualNewEndpointTrafficRouteFactorOnPairForRouting_canonical
#print axioms matchedEventualNewEndpointTrafficLoadOnPairForRouting_canonical
#print axioms matchedEventualNewEndpointTrafficDebtOnPairForRouting_canonical
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.routeFactor_eq_zero
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.transitionTerm_eq_zero
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.load_eqv_zero
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingRoutingAt.debt_eqv_zero
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedBirthAvoidingFlowCapacityAt.toOffRayResidualCoercivityAt

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationAdaptiveRoutingCompiler
