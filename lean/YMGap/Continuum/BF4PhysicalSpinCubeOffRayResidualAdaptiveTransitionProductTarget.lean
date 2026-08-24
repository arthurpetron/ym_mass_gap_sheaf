/-
# Transition-product target for adaptive BF4 residual routing

An adaptive positive route may revisit a directed physical edge.  Therefore
the canonical simple-path indicator is not a sound description of its load.
This module retains the literal directed-edge multiplicity of every supplied
route and rewrites each source-cancelled endpoint-pair contribution as the
exact product of reverse/forward physical conditional-transition ratios along
a constructive prefix to the selected edge source.

The summed transition-product load is exactly the adaptive relative flow
load.  Hence its pointwise capacity certificate is losslessly equivalent to
adaptive conditional congestion and compiles to the existing completed strict
transfer contraction.  The canonical specialization converts in both
directions to the previous simple-path transition-product certificate.

Every finite cutoff has a canonical-routed inhabitant with the existing
cutoff-dependent restricted ray floor.  No cofinal adaptive family is
inhabited here.  No uniform estimate, thermodynamic or continuum limit,
continuum Yang--Mills theory, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact repeated-edge multiplicity -/

/-- The number of occurrences of one directed edge in a positive route,
represented inside the exact rational setoid. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    ((PositiveKernelChainIn.directedEdges
      (routing.path left right hleft hright)).map
        (fun edge => (edge, (1 : Q'))))
    source target

private theorem weightedDirectedEdgeLoad_constantMap_eqv_scalarMultiplicity_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (load : Q') (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≈
      load * weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, (1 : Q')))) source target := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map, listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun edge => load *
        weightedDirectedEdgeIndicator (edge, (1 : Q')) source target)
      edges) _ ?_ ?_
  · apply listQSum_congr_on
    intro edge _hedge
    unfold weightedDirectedEdgeIndicator
    by_cases heq : edge = (source, target)
    · rw [if_pos heq, if_pos heq]
      exact Q'.eqv_symm (Q'.mul_one_eqv load)
    · rw [if_neg heq, if_neg heq]
      exact Q'.eqv_symm (Q'.mul_zero_eqv load)
  exact listQSum_mul_left load
    (fun edge =>
      weightedDirectedEdgeIndicator (edge, (1 : Q')) source target)
    edges

private theorem weightedDirectedEdgeLoad_constantMap_eqv_zero_of_not_mem_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (load : Q') (source target : State)
    (hnot : (source, target) ∉ edges) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≈ 0 := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map]
  refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) edges) _ ?_ ?_
  · apply listQSum_congr_on
    intro edge hedge
    unfold weightedDirectedEdgeIndicator
    have hne : edge ≠ (source, target) := by
      intro heq
      exact hnot (heq ▸ hedge)
    rw [if_neg hne]
    exact Q'.eqv_refl 0
  exact listQSum_zero edges

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (heq : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _
    (Q'.recipPos denominator hdenominator) heq

private theorem divPos_mul_right_eqv_local
    (left factor denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (left * factor) denominator hdenominator ≈
      Q'.divPos left denominator hdenominator * factor := by
  unfold Q'.divPos
  show (((left * factor) * Q'.recipPos denominator hdenominator) : Q') ≈
    ((left * Q'.recipPos denominator hdenominator) * factor)
  refine Q'.eqv_trans _ (left *
    (factor * Q'.recipPos denominator hdenominator)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv left factor _
  refine Q'.eqv_trans _ (left *
    (Q'.recipPos denominator hdenominator * factor)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left left _ _
      (Q'.mul_comm_eqv factor _)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv left _ factor)

private theorem divPos_product_eqv_ratio_product_local
    (left right length denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos ((left * right) * length)
        denominator hdenominator ≈
      (Q'.divPos left denominator hdenominator * right) * length := by
  unfold Q'.divPos
  show ((((left * right) * length) *
      Q'.recipPos denominator hdenominator) : Q') ≈
    (((left * Q'.recipPos denominator hdenominator) * right) * length)
  show
    ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).num *
      ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).den : Int)) =
    ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).num *
      ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).den : Int))
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 2. One routed pair as an observable transition product -/

/-- One adaptive pair contribution.  The prefix product records the actual
route from the left endpoint to the selected edge source, while the final
multiplicity factor records every repeated traversal of that edge. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path pair.1 pair.2 hfull.1 hfull.2
    if hedge : (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (source, target) hedge
      (((centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
            w hw K hfull.1 prefixData.pathPrefix *
          centralPhysicalFiniteWeight w hw K 0 pair.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) *
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing pair.1 pair.2 hfull.1 hfull.2 source target)
    else 0
  else 0

/-- The quotient-defined adaptive pair demand is exactly its prefix
transition product, including repeated-edge multiplicity. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand_eqv_transitionProduct
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
        routing source target pair ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        routing source target pair := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  let path := routing.path pair.1 pair.2 hfull.1 hfull.2
  let raw :=
    (centralPhysicalFiniteWeight w hw K 0 pair.1 *
      centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
  let multiplicity :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
      routing pair.1 pair.2 hfull.1 hfull.2 source target
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  rw [dif_pos hpair]
  change Q'.divPos
      (weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target)
      (centralPhysicalFiniteWeight w hw K 0 source) hweight ≈
    if hedge : (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (source, target) hedge
      (((centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
            w hw K hfull.1 prefixData.pathPrefix *
          centralPhysicalFiniteWeight w hw K 0 pair.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) * multiplicity)
    else 0
  by_cases hedge : (source, target) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [dif_pos hedge]
    have hload :
        weightedDirectedEdgeLoad
            (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
              routing pair.1 pair.2)
            source target ≈ raw * multiplicity := by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
      rw [dif_pos hfull.1, dif_pos hfull.2]
      exact
        weightedDirectedEdgeLoad_constantMap_eqv_scalarMultiplicity_local
          (PositiveKernelChainIn.directedEdges path) raw source target
    refine Q'.eqv_trans _
      (Q'.divPos (raw * multiplicity)
        (centralPhysicalFiniteWeight w hw K 0 source) hweight) _
      (divPos_eqv_congr_numerator_local hweight hload) ?_
    refine Q'.eqv_trans _
      (Q'.divPos raw
        (centralPhysicalFiniteWeight w hw K 0 source) hweight *
        multiplicity) _
      (divPos_mul_right_eqv_local raw multiplicity _ hweight) ?_
    refine Q'.eqv_trans _
      ((((Q'.divPos
          (centralPhysicalFiniteWeight w hw K 0 pair.1)
          (centralPhysicalFiniteWeight w hw K 0 source) hweight) *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) * multiplicity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ multiplicity
        (divPos_product_eqv_ratio_product_local _ _ _ _ hweight)
    have hratio :
        Q'.divPos
            (centralPhysicalFiniteWeight w hw K 0 pair.1)
            (centralPhysicalFiniteWeight w hw K 0 source) hweight =
          centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
            w hw K source pair.1 := by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
      rw [dif_pos hsource]
    rw [hratio]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      hfull.1 path (source, target) hedge
    have htelescope :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
        w hw K hfull.1 prefixData.pathPrefix
    exact Q'.mul_eqv_congr_right _ _ multiplicity
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ htelescope))
  · rw [dif_neg hedge]
    have hzero :
        weightedDirectedEdgeLoad
            (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
              routing pair.1 pair.2)
            source target ≈ 0 := by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
      rw [dif_pos hfull.1, dif_pos hfull.2]
      exact
        weightedDirectedEdgeLoad_constantMap_eqv_zero_of_not_mem_local
          (PositiveKernelChainIn.directedEdges path) raw source target hedge
    refine Q'.eqv_trans _
      (Q'.divPos 0
        (centralPhysicalFiniteWeight w hw K 0 source) hweight) _
      (divPos_eqv_congr_numerator_local hweight hzero) ?_
    unfold Q'.divPos
    exact Q'.zero_mul_eqv _

def centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      routing source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

/-- The observable compiler path is exact: the routed relative traffic and
the sum of route-prefix transition products are the same rational value. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
        routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
  apply listQSum_congr_on
  intro pair hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand_eqv_transitionProduct
      routing hsource target pair hpair

/-! ## 3. Lossless capacity certificates and the canonical bridge -/

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTarget_iff_transitionProductTarget
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    {source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
    (target : Nat) :
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) ↔
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) := by
  have heq :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
      routing hsource target
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
          _ _ (Q'.eqv_symm heq)))
      h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
          _ _ heq))
      h

structure CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
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
          centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt

def ofRoutedConditionalCongestionAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (congestion :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTarget_iff_transitionProductTarget
      routing hsource target).mp
      (congestion.edge_capacity source hsource target htarget)

def toRoutedConditionalCongestionAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (product :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTarget_iff_transitionProductTarget
      routing hsource target).mpr
      (product.edge_capacity source hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt

/-- On the canonical route, the multiplicity-aware adaptive load is exactly
equivalent to the previous simple-path transition-product load. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_canonical_eqv
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
        source target ≈
      centralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductLoad
        w hw K source target := by
  refine Q'.eqv_trans _
    (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
      (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
      source target) _ ?_ ?_
  · exact Q'.eqv_symm
      (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
        _ hsource target)
  refine Q'.eqv_trans _
    (centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
      w hw K source target) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_canonical_eq
        w hw K source target)
  refine Q'.eqv_trans _
    (centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
      w hw K source target) _ ?_ ?_
  · exact
      centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad_eqv_harnackLoad
        hsource target
  exact
    centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad_eqv_transitionProductLoad
      w hw K source target

def CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.ofCanonical
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (product :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
      hw K rayCapacity
      (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        w (Q'.le_of_lt hw) K) where
  edge_capacity := fun source hsource target htarget => by
    have heq :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_canonical_eqv
        hsource target
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
          _ _ heq))
      (product.edge_capacity source hsource target htarget)

def CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.toCanonical
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (product :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
        hw K rayCapacity
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
          w (Q'.le_of_lt hw) K)) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget => by
    have heq :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_canonical_eqv
        hsource target
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
          _ _ (Q'.eqv_symm heq)))
      (product.edge_capacity source hsource target htarget)

/-- A genuine finite-cutoff adaptive transition-product inhabitant, using
the canonical route and the existing cutoff-dependent restricted ray floor. -/
def centralLowerExcitedSpinCubeFiniteLinearRoutedConditionalTransitionProductAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
      hw K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity rayCapacity)
      (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        w (Q'.le_of_lt hw) K) :=
  CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.ofCanonical
    (centralLowerExcitedSpinCubeFiniteLinearConditionalTransitionProductAt
      rayCapacity)

/-! ## 4. A cofinal adaptive product family reaches the existing consumer -/

structure FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  routing : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  product : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
      hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)
      (routing K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct

def toAdaptiveConditionalCongestion
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion
      hw rayCapacity where
  routing := family.routing
  congestion := fun K hK =>
    (family.product K hK).toRoutedConditionalCongestionAt

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  family.toAdaptiveConditionalCongestion.toCompletedStrictContractionData
    hw0 hw1

end FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand_eqv_transitionProduct
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTarget_iff_transitionProductTarget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.ofRoutedConditionalCongestionAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.toRoutedConditionalCongestionAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_canonical_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.ofCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.toCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.centralLowerExcitedSpinCubeFiniteLinearRoutedConditionalTransitionProductAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct.toAdaptiveConditionalCongestion
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct.toCompletedStrictContractionData
