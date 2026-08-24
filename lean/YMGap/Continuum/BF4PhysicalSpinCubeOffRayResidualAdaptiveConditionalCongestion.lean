/-
# Dimensionless conditional congestion for adaptive BF4 residual routing

The adaptive-routing compiler permits a BF4-local or multiscale proof to
choose positive physical-kernel paths.  Its pointwise capacity is initially
stated for the stationary joint kernel.  On every actual source, however,
both the routed traffic and the joint kernel contain the same strictly
positive stationary source weight.

This module cancels that factor without changing the supplied paths.  It
defines the exact relative routed traffic, proves that multiplying it by the
source weight reconstructs the routed flow load, and establishes an iff
between routed joint capacity and dimensionless conditional congestion.  A
cofinal family compiles through the adaptive-routing coercivity theorem to
the existing completed strict contraction.

On the canonical loop-erased routing this relative load is definitionally
the previous conditional-congestion load, and the two certificate interfaces
convert in both directions.  This is a refinement of the same frontier, not
a second scorecard.

No cofinal adaptive conditional family is inhabited here.  No thermodynamic
or continuum limit, continuum Yang--Mills theory, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact routed relative traffic -/

/-- One endpoint pair's routed contribution to an edge, divided by the
strictly positive stationary mass of the edge source. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) (pair : Nat × Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    Q'.divPos
      (weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target)
      (centralPhysicalFiniteWeight w hw K 0 source)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  else 0

theorem centralPhysicalFiniteWeight_mul_routedRelativePairDemand_eqv_pathLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) (pair : Nat × Nat) :
    centralPhysicalFiniteWeight w hw K 0 source *
        centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
          routing source target pair ≈
      weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target := by
  let weight := centralPhysicalFiniteWeight w hw K 0 source
  let load := weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
      routing pair.1 pair.2)
    source target
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv weight (Q'.divPos load weight hweight))
    (Q'.divPos_mul_eqv load weight hweight)

/-- Dimensionless directed load for the supplied routing.  The endpoint list
and every Type-level path are retained literally. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
      routing source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_eqv_pathLoadSum
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target ≈
      listQSum
        (fun pair => weightedDirectedEdgeLoad
          (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
            routing pair.1 pair.2)
          source target)
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences
    weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

theorem centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralPhysicalFiniteWeight w hw K 0 source *
        centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
          routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target := by
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        centralPhysicalFiniteWeight w hw K 0 source *
          centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
            routing source target pair)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
    exact Q'.eqv_symm
      (listQSum_mul_left
        (centralPhysicalFiniteWeight w hw K 0 source)
        (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
          routing source target)
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K))
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _hpair
    exact centralPhysicalFiniteWeight_mul_routedRelativePairDemand_eqv_pathLoad
      routing hsource target pair
  exact Q'.eqv_symm
    (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_eqv_pathLoadSum
      routing source target)

/-! ## 2. Lossless cancellation against the conditional transition -/

private theorem mul_swap_middle_eqv (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

private theorem le_iff_of_eqv_positive_common_left
    {weight left right reducedLeft reducedRight : Q'}
    (hweight : (0 : Q') < weight)
    (hleft : left ≈ weight * reducedLeft)
    (hright : right ≈ weight * reducedRight) :
    left ≤ right ↔ reducedLeft ≤ reducedRight := by
  constructor
  · intro h
    have hscaled : weight * reducedLeft ≤ weight * reducedRight :=
      Q'.le_trans' _ left _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ right _ h (Q'.le_of_eqv hright))
    exact Q'.le_of_mul_le_mul_left hscaled hweight
  · intro h
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      reducedLeft reducedRight weight h (Q'.le_of_lt hweight)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedEdgeCapacity_iff_conditionalCongestion
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (target : Nat) :
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target) ↔
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) := by
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 source
  let load := centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
    routing source target
  let relative :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
      routing source target
  let kernel := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 source target
  let conditional := centralPhysicalFiniteConditionalKernel
    w (Q'.le_of_lt hw) K 0 source target
  let floor := centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hleft : floor * load ≈ weight * (floor * relative) := by
    refine Q'.eqv_trans _ (floor * (weight * relative)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left floor _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad
            routing hsource target))
    exact mul_swap_middle_eqv floor weight relative
  have hright : HalfPow.half * kernel ≈
      weight * (HalfPow.half * conditional) := by
    refine Q'.eqv_trans _
      (HalfPow.half * (weight * conditional)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
            hsource target))
    exact mul_swap_middle_eqv HalfPow.half weight conditional
  exact le_iff_of_eqv_positive_common_left hweight hleft hright

/-! ## 3. Adaptive conditional certificates and the canonical bridge -/

structure CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Type 1 where
  edge_capacity : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt

def ofRoutedFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualRoutedEdgeCapacity_iff_conditionalCongestion
      routing hsource target).mp
      (capacity.edge_capacity source hsource target htarget)

def toRoutedFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (congestion :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualRoutedEdgeCapacity_iff_conditionalCongestion
      routing hsource target).mpr
      (congestion.edge_capacity source hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_canonical_eq
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
        source target =
      centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
        w hw K source target := rfl

def CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.ofCanonical
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (congestion :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
      hw K rayCapacity
      (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        w (Q'.le_of_lt hw) K) where
  edge_capacity := fun source hsource target htarget => by
    rw [centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_canonical_eq]
    exact congestion.edge_capacity source hsource target htarget

def CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.toCanonical
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (congestion :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
        hw K rayCapacity
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
          w (Q'.le_of_lt hw) K)) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget => by
    rw [← centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_canonical_eq]
    exact congestion.edge_capacity source hsource target htarget

/-! ## 4. Cofinal adaptive conditional congestion reaches completion -/

structure FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  routing : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  congestion : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
      hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)
      (routing K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion

def toAdaptiveRoutingCapacity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity
      hw rayCapacity where
  routing := family.routing
  flow_capacity := fun K hK =>
    (family.congestion K hK).toRoutedFlowCapacityAt

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  family.toAdaptiveRoutingCapacity.toCompletedStrictContractionData hw0 hw1

end FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.centralPhysicalFiniteWeight_mul_routedRelativePairDemand_eqv_pathLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_eqv_pathLoadSum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.centralLowerExcitedSpinCubeOffRayResidualRoutedEdgeCapacity_iff_conditionalCongestion
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.ofRoutedFlowCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.toRoutedFlowCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_canonical_eq
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.ofCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.toCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion.toAdaptiveRoutingCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion.toCompletedStrictContractionData
