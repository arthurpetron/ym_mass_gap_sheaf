/-
# One orientation-free transition-product observable at every BF4 cutoff

The symmetrized routed load has an exact dimensionless description which is
more useful than a global positive-edge floor.  Divide both orientations by
the stationary mass at the displayed edge source.  The forward half is the
existing prefix-product traffic.  In the reverse half the same source is the
target of the reversed directed edge, so the relevant prefix is extended
through that edge before detailed balance is telescoped.

This module proves, for every constructive positive routing and arbitrary
finite cutoff, that the symmetric relative load is exactly the average of
those two transition-product loads.  It then proves that the physical joint-
kernel capacity inequality is equivalent to one dimensionless conditional-
transition inequality.  Thus the old/new block decomposition is not part of
the mathematical observable; it is only one possible way to prove the single
all-sector inequality.

No uniform transition-product estimate, cofinal return floor, completed
uniform gap, thermodynamic/continuum limit, continuum Yang--Mills theory, or
Clay conclusion is inhabited here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, functional extensionality, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSymmetricRouting
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSymmetricTransitionProduct

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSymmetricRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem mul_swap_middle_eqv_local (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

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
  refine Q'.eqv_trans _
    (left * (factor * Q'.recipPos denominator hdenominator)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv left factor _
  refine Q'.eqv_trans _
    (left * (Q'.recipPos denominator hdenominator * factor)) _ ?_ ?_
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

private theorem le_iff_of_eqv_positive_common_left_local
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

/-! ## 1. Normalize the reversed load at the displayed source -/

/-- One routed endpoint-pair contribution divided by the stationary mass at
the selected directed edge target. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) (pair : Nat × Nat) : Q' :=
  if htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    Q'.divPos
      (weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target)
      (centralPhysicalFiniteWeight w hw K 0 target)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
  else 0

theorem centralPhysicalFiniteWeight_mul_routedRelativeTargetPairDemand_eqv_pathLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K target : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source : Nat) (pair : Nat × Nat) :
    centralPhysicalFiniteWeight w hw K 0 target *
        centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
          routing source target pair ≈
      weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target := by
  let weight := centralPhysicalFiniteWeight w hw K 0 target
  let load := weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
      routing pair.1 pair.2)
    source target
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
  rw [dif_pos htarget]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv weight (Q'.divPos load weight hweight))
    (Q'.divPos_mul_eqv load weight hweight)

/-- The whole directed flow divided by the stationary mass at the selected
edge target, retained as an exact sum over endpoint pairs. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
      routing source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralPhysicalFiniteWeight_mul_routedRelativeTargetFlowLoad_eqv_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K target : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source : Nat) :
    centralPhysicalFiniteWeight w hw K 0 target *
        centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
          routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target := by
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        centralPhysicalFiniteWeight w hw K 0 target *
          centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
            routing source target pair)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
    exact Q'.eqv_symm
      (listQSum_mul_left
        (centralPhysicalFiniteWeight w hw K 0 target)
        (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
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
    exact
      centralPhysicalFiniteWeight_mul_routedRelativeTargetPairDemand_eqv_pathLoad
        routing htarget source pair
  exact Q'.eqv_symm
    (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_eqv_pathLoadSum
      routing source target)

/-! ## 2. Exact target-prefix transition products -/

/-- Extend a positive prefix ending at an edge source through that positive
edge to its target. -/
def positiveKernelPrefixThroughDirectedEdge {State : Type}
    {kernel : State → State → Q'} {support : List State}
    {first : State} {edge : State × State}
    (prefixData : PositiveKernelPrefixAtDirectedEdge
      kernel support first edge) :
    PositiveKernelChainIn kernel support first edge.2 :=
  PositiveKernelChainIn.trans
    prefixData.pathPrefix
    (PositiveKernelChainIn.step
      prefixData.edge_positive prefixData.target_mem
      (PositiveKernelChainIn.refl edge.2))

/-- One target-normalized routed pair, written as the product of local
reverse/forward conditional ratios along the prefix through the selected
edge.  The final factor retains exact repeated-edge multiplicity. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTargetTransitionProductTerm
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
            w hw K hfull.1
            (positiveKernelPrefixThroughDirectedEdge prefixData) *
          centralPhysicalFiniteWeight w hw K 0 pair.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) *
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing pair.1 pair.2 hfull.1 hfull.2 source target)
    else 0
  else 0

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand_eqv_transitionProduct
    {w : Q'} {hw : (0 : Q') ≤ w} {K target : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
        routing source target pair ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTargetTransitionProductTerm
        routing source target pair := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget
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
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand
  rw [dif_pos htarget]
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTargetTransitionProductTerm
  rw [dif_pos hpair]
  change Q'.divPos
      (weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing pair.1 pair.2)
        source target)
      (centralPhysicalFiniteWeight w hw K 0 target) hweight ≈
    if hedge : (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (source, target) hedge
      (((centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
            w hw K hfull.1
            (positiveKernelPrefixThroughDirectedEdge prefixData) *
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
        (centralPhysicalFiniteWeight w hw K 0 target) hweight) _
      (divPos_eqv_congr_numerator_local hweight hload) ?_
    refine Q'.eqv_trans _
      (Q'.divPos raw
        (centralPhysicalFiniteWeight w hw K 0 target) hweight *
        multiplicity) _
      (divPos_mul_right_eqv_local raw multiplicity _ hweight) ?_
    refine Q'.eqv_trans _
      ((((Q'.divPos
          (centralPhysicalFiniteWeight w hw K 0 pair.1)
          (centralPhysicalFiniteWeight w hw K 0 target) hweight) *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)) * multiplicity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ multiplicity
        (divPos_product_eqv_ratio_product_local _ _ _ _ hweight)
    have hratio :
        Q'.divPos
            (centralPhysicalFiniteWeight w hw K 0 pair.1)
            (centralPhysicalFiniteWeight w hw K 0 target) hweight =
          centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
            w hw K target pair.1 := by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
      rw [dif_pos htarget]
    rw [hratio]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      hfull.1 path (source, target) hedge
    have htelescope :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
        w hw K hfull.1
        (positiveKernelPrefixThroughDirectedEdge prefixData)
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
        (centralPhysicalFiniteWeight w hw K 0 target) hweight) _
      (divPos_eqv_congr_numerator_local hweight hzero) ?_
    unfold Q'.divPos
    exact Q'.zero_mul_eqv _

def centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTargetTransitionProductLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTargetTransitionProductTerm
      routing source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad_eqv_transitionProductLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K target : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
        routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTargetTransitionProductLoad
        routing source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTargetTransitionProductLoad
  apply listQSum_congr_on
  intro pair hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand_eqv_transitionProduct
      routing htarget source pair hpair

/-! ## 3. The one symmetric dimensionless observable -/

/-- Symmetric relative traffic based at `source`.  Both summands are divided
by the stationary weight of that same displayed source. -/
def centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
        routing source target +
    HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
        routing target source

theorem centralPhysicalFiniteWeight_mul_symmetricRoutedRelativeSourceFlowLoad_eqv_load
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralPhysicalFiniteWeight w hw K 0 source *
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad
          routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
        routing source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
  refine Q'.eqv_trans _
    (centralPhysicalFiniteWeight w hw K 0 source *
          (HalfPow.half *
            centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
              routing source target) +
      centralPhysicalFiniteWeight w hw K 0 source *
          (HalfPow.half *
            centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
              routing target source)) _
    (Q'.mul_add_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (HalfPow.half *
          (centralPhysicalFiniteWeight w hw K 0 source *
            centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
              routing source target) +
      HalfPow.half *
          (centralPhysicalFiniteWeight w hw K 0 source *
            centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
              routing target source)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_swap_middle_eqv_local
        (centralPhysicalFiniteWeight w hw K 0 source) HalfPow.half
        (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
          routing source target))
      (mul_swap_middle_eqv_local
        (centralPhysicalFiniteWeight w hw K 0 source) HalfPow.half
        (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad
          routing target source))
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad
        routing hsource target))
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (centralPhysicalFiniteWeight_mul_routedRelativeTargetFlowLoad_eqv_flowLoad
        routing hsource target))

/-- Average of the prefix-to-source and prefix-through-edge transition-
product traffic. -/
def centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target +
    HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTargetTransitionProductLoad
        routing target source

/-- The symmetric relative load is exactly the single orientation-free
transition-product observable. -/
theorem centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad
        routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductLoad
        routing source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductLoad
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
        routing hsource target))
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad_eqv_transitionProductLoad
        routing hsource target))

/-! ## 4. Lossless conditional-capacity equivalence -/

theorem centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedEdgeCapacity_iff_conditionalTransitionProduct
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (target : Nat) :
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target) ↔
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) := by
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 source
  let symmetricRelative :=
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad
      routing source target
  let product :=
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductLoad
      routing source target
  let load := centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
    routing source target
  let kernel := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 source target
  let conditional := centralPhysicalFiniteConditionalKernel
    w (Q'.le_of_lt hw) K 0 source target
  let floor := centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hrelativeProduct : symmetricRelative ≈ product :=
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
      routing hsource target
  have hleft : floor * load ≈ weight * (floor * product) := by
    refine Q'.eqv_trans _ (floor * (weight * symmetricRelative)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left floor _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteWeight_mul_symmetricRoutedRelativeSourceFlowLoad_eqv_load
            routing hsource target))
    refine Q'.eqv_trans _ (weight * (floor * symmetricRelative)) _
      (mul_swap_middle_eqv_local floor weight symmetricRelative) ?_
    exact Q'.mul_eqv_congr_left weight _ _
      (Q'.mul_eqv_congr_left floor _ _ hrelativeProduct)
  have hright : HalfPow.half * kernel ≈
      weight * (HalfPow.half * conditional) := by
    refine Q'.eqv_trans _
      (HalfPow.half * (weight * conditional)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
            hsource target))
    exact mul_swap_middle_eqv_local HalfPow.half weight conditional
  exact le_iff_of_eqv_positive_common_left_local
    hweight hleft hright

/-- The sole arbitrary-cutoff analytic datum after symmetry and detailed
balance: the conditional transition pays the orientation-free product load
on every retained pair. -/
structure CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt
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
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt

/-- The dimensionless transition-product datum produces the physical
symmetric routed-flow capacity with no lost constant. -/
def toSymmetricRoutedFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (product :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedEdgeCapacity_iff_conditionalTransitionProduct
      routing hsource target).mpr
      (product.edge_capacity source hsource target htarget)

/-- Conversely, physical symmetric capacity recovers the same dimensionless
transition-product datum exactly. -/
def ofSymmetricRoutedFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedEdgeCapacity_iff_conditionalTransitionProduct
      routing hsource target).mp
      (capacity.edge_capacity source hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt

/-! ## 5. Existing directed capacity pays the symmetric observable -/

namespace CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt

/-- A capacity inequality in both directed orientations pays their arithmetic
average at exactly the same coercivity strength. -/
def toSymmetricRoutedFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget => by
    let floor := centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity
    let forward :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target
    let reverse :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing target source
    let kernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 source target
    let reverseKernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 target source
    have hforward := capacity.edge_capacity
      source hsource target htarget
    have hreverse := capacity.edge_capacity
      target htarget source hsource
    have hforwardScaled := Q'.mul_le_mul_of_nonneg_left _ _
      HalfPow.half hforward HalfPow.half_nonneg
    have hreverseScaled := Q'.mul_le_mul_of_nonneg_left _ _
      HalfPow.half hreverse HalfPow.half_nonneg
    have hsum := Q'.add_le_add hforwardScaled hreverseScaled
    have hleft :
        floor *
            centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
              routing source target ≈
          HalfPow.half * (floor * forward) +
            HalfPow.half * (floor * reverse) := by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
      refine Q'.eqv_trans _
        (floor * (HalfPow.half * forward) +
          floor * (HalfPow.half * reverse)) _
        (Q'.mul_add_eqv floor _ _) ?_
      exact Q'.add_eqv_congr'
        (mul_swap_middle_eqv_local floor HalfPow.half forward)
        (mul_swap_middle_eqv_local floor HalfPow.half reverse)
    have hrightReverse :
        HalfPow.half * (HalfPow.half * reverseKernel) ≈
          HalfPow.half * (HalfPow.half * kernel) :=
      Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.mul_eqv_congr_left HalfPow.half _ _
          (centralPhysicalFiniteKernel_symm_on_vacuumSector
            htarget hsource))
    have hright :
        HalfPow.half * (HalfPow.half * kernel) +
            HalfPow.half * (HalfPow.half * reverseKernel) ≈
          HalfPow.half * kernel :=
      Q'.eqv_trans _
        (HalfPow.half * (HalfPow.half * kernel) +
          HalfPow.half * (HalfPow.half * kernel)) _
        (Q'.add_eqv_congr_left _ _ _ hrightReverse)
        (ExpNeg.two_halves (HalfPow.half * kernel))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hright))

end CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt

/-- Every finite cutoff has a genuine symmetric transition-product
certificate, using the existing finite restricted-ray capacity.  Its
constant may depend on the cutoff; this is not a cofinal estimate. -/
def centralLowerExcitedSpinCubeFiniteLinearSymmetricRoutedConditionalTransitionProductAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt
      hw K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity rayCapacity)
      (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        w (Q'.le_of_lt hw) K) :=
  CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt.ofSymmetricRoutedFlowCapacityAt
    (CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.toSymmetricRoutedFlowCapacityAt
      ((centralLowerExcitedSpinCubeFiniteLinearRoutedConditionalTransitionProductAt
          rayCapacity).toRoutedConditionalCongestionAt.toRoutedFlowCapacityAt))

/-! ## Axiom audit -/

#print axioms
  centralPhysicalFiniteWeight_mul_routedRelativeTargetFlowLoad_eqv_flowLoad
#print axioms positiveKernelPrefixThroughDirectedEdge
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeTargetDemand_eqv_transitionProduct
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeTargetFlowLoad_eqv_transitionProductLoad
#print axioms
  centralPhysicalFiniteWeight_mul_symmetricRoutedRelativeSourceFlowLoad_eqv_load
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedEdgeCapacity_iff_conditionalTransitionProduct
#print axioms
  CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedConditionalTransitionProductAt.toSymmetricRoutedFlowCapacityAt
#print axioms
  CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.toSymmetricRoutedFlowCapacityAt
#print axioms
  centralLowerExcitedSpinCubeFiniteLinearSymmetricRoutedConditionalTransitionProductAt

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSymmetricTransitionProduct
