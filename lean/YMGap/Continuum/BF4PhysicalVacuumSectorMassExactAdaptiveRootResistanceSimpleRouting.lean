/-
# Loop-erased normalization of adaptive BF4 resistance routing

An arbitrary positive-kernel route may revisit vertices and charge the same
directed edge more than once.  This module converts such a route to the
support-aware Boolean walk, erases loops constructively, and converts the
result back to a positive-kernel chain.

The normalized route has a duplicate-free directed-edge list which is an
order-preserving sublist of the original route's edge list.  In particular,
its electrical resistance cannot increase.  Consequently neither a single
state's directed-edge load nor the total routed flow load can increase.  Any
cofinal adaptive congestion certificate therefore normalizes to simple routes
with exactly the same bound.

No cofinal adaptive routing, uniform congestion constant, completed gap,
continuum limit, continuum Yang--Mills theory, or Clay conclusion is asserted.
No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive BF4 paths as support-aware Boolean walks -/

def centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        left right →
      Walk
        (supportedEdge
          (centralPhysicalFiniteSupportAdjacentB w hw K 0)
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0))
        left right
  | PositiveKernelChainIn.refl _ => Walk.single left
  | PositiveKernelChainIn.step positive hnext rest =>
      Walk.cons
        ((Bool.and_eq_true _ _).mpr
          ⟨(centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
              hleft hnext).mpr positive,
            decide_eq_true hnext⟩)
        (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
          hnext rest)

theorem centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath_directedEdges
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    ∀ (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        left right),
      Walk.directedEdges
          (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
            hleft path) =
        PositiveKernelChainIn.directedEdges path
  | PositiveKernelChainIn.refl _ => rfl
  | PositiveKernelChainIn.step (next := next) _ hnext rest => by
      simp only [centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath,
        Walk.directedEdges, PositiveKernelChainIn.directedEdges]
      exact congrArg (List.cons (left, next))
        (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath_directedEdges
          hnext rest)

/-! ## 2. Loop-erased positive routes -/

def centralPhysicalFiniteVacuumSectorLoopErasedPositivePath
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right :=
  BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
    (centralPhysicalFiniteSupportAdjacentB w hw K 0)
    (centralPhysicalFiniteKernel w hw K 0)
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (fun _first _next hfirst hnext hedge =>
      centralPhysicalFiniteKernel_pos_of_supportAdjacent
        hfirst hnext hedge)
    hleft
    (Walk.eraseLoops
      (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
        hleft path)).walk

theorem centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_sublist
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right) :
    List.Sublist
      (PositiveKernelChainIn.directedEdges
        (centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hleft path))
      (PositiveKernelChainIn.directedEdges path) := by
  unfold centralPhysicalFiniteVacuumSectorLoopErasedPositivePath
  rw [BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.directedEdges_ofSupportedWalk]
  have hsub := Walk.eraseLoops_directedEdges_sublist
    (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath hleft path)
  rw [centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath_directedEdges
    hleft path] at hsub
  exact hsub

theorem centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right) :
    (PositiveKernelChainIn.directedEdges
      (centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hleft path)).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorLoopErasedPositivePath
  rw [BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.directedEdges_ofSupportedWalk]
  exact Walk.directedEdges_nodup_of_vertices_nodup _
    (Walk.eraseLoops
      (centralPhysicalFiniteVacuumSectorSupportedWalkOfPositivePath
        hleft path)).nodup

/-! ## 3. Resistance cannot increase under loop erasure -/

def positiveEdgeResistance {State : Type}
    (kernel : State → State → Q') (edge : State × State) : Q' :=
  if hpositive : (0 : Q') < kernel edge.1 edge.2 then
    Q'.recipPos (kernel edge.1 edge.2) hpositive
  else 0

theorem positiveEdgeResistance_nonnegative {State : Type}
    (kernel : State → State → Q') (edge : State × State) :
    (0 : Q') ≤ positiveEdgeResistance kernel edge := by
  unfold positiveEdgeResistance
  by_cases hpositive : (0 : Q') < kernel edge.1 edge.2
  · rw [dif_pos hpositive]
    exact Q'.le_of_lt (Q'.recipPos_pos _ hpositive)
  · rw [dif_neg hpositive]
    exact Q'.le_refl' 0

theorem resistance_eqv_directedEdges_sum
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      PositiveKernelChainIn.resistance path ≈
        listQSum (positiveEdgeResistance kernel)
          (PositiveKernelChainIn.directedEdges path)
  | _, _, PositiveKernelChainIn.refl _ => Q'.eqv_refl 0
  | first, _, PositiveKernelChainIn.step (next := next)
      positive _ rest => by
      simp only [PositiveKernelChainIn.resistance,
        PositiveKernelChainIn.directedEdges, listQSum]
      apply Q'.add_eqv_congr'
      · unfold positiveEdgeResistance
        rw [dif_pos positive]
        exact Q'.eqv_refl _
      · exact resistance_eqv_directedEdges_sum rest

private theorem listQSum_sublist_le_local {Item : Type}
    (value : Item → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ {lower upper : List Item}, List.Sublist lower upper →
      listQSum value lower ≤ listQSum value upper := by
  intro lower upper hsub
  induction hsub with
  | slnil => exact Q'.le_refl' 0
  | @cons lower upper head hsub ih =>
      simp only [listQSum]
      refine Q'.le_trans' _ _ _ ih ?_
      have hadd := Q'.add_le_add_right
        (0 : Q') (value head) (listQSum value upper) (hvalue head)
      rwa [Q'.zero_add'] at hadd
  | @cons₂ lower upper head hsub ih =>
      exact Q'.add_le_add (Q'.le_refl' (value head)) ih

theorem centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_resistance_le
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right) :
    PositiveKernelChainIn.resistance
        (centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hleft path) ≤
      PositiveKernelChainIn.resistance path := by
  let erased :=
    centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hleft path
  have herased := resistance_eqv_directedEdges_sum erased
  have horiginal := resistance_eqv_directedEdges_sum path
  have hsub :=
    centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_sublist
      hleft path
  have hsum := listQSum_sublist_le_local
    (positiveEdgeResistance (centralPhysicalFiniteKernel w hw K 0))
    (positiveEdgeResistance_nonnegative
      (centralPhysicalFiniteKernel w hw K 0)) hsub
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv herased)
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv horiginal))

/-! ## 4. A normalized routing object -/

def loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K where
  path := fun left right hleft hright =>
    centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hleft
      (routing.path left right hleft hright)

/-! ## 5. Pointwise state-edge load domination -/

private theorem weightedDirectedEdgeLoad_constantMap_le_of_sublist_local
    {State : Type} [DecidableEq State]
    {smaller larger : List (State × State)}
    (hsub : List.Sublist smaller larger)
    (smallerLoad largerLoad : Q')
    (hload : smallerLoad ≤ largerLoad)
    (hlarger : (0 : Q') ≤ largerLoad)
    (source target : State) :
    weightedDirectedEdgeLoad
        (smaller.map (fun edge => (edge, smallerLoad))) source target ≤
      weightedDirectedEdgeLoad
        (larger.map (fun edge => (edge, largerLoad))) source target := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map, listQSum_map]
  have hpoint : listQSum
        (fun edge => weightedDirectedEdgeIndicator
          (edge, smallerLoad) source target) smaller ≤
      listQSum
        (fun edge => weightedDirectedEdgeIndicator
          (edge, largerLoad) source target) smaller := by
    apply listQSum_mono
    intro edge _hedge
    unfold weightedDirectedEdgeIndicator
    by_cases heq : edge = (source, target)
    · rw [if_pos heq, if_pos heq]
      exact hload
    · rw [if_neg heq, if_neg heq]
      exact Q'.le_refl' 0
  have hlargeValue : ∀ edge,
      (0 : Q') ≤ weightedDirectedEdgeIndicator
        (edge, largerLoad) source target := by
    intro edge
    unfold weightedDirectedEdgeIndicator
    by_cases heq : edge = (source, target)
    · rw [if_pos heq]
      exact hlarger
    · rw [if_neg heq]
      exact Q'.le_refl' 0
  exact Q'.le_trans' _ _ _ hpoint
    (listQSum_sublist_le_local _ hlargeValue hsub)

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_loopErased_le
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing)
        state source target ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
  by_cases hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0
  · rw [dif_pos hstate, dif_pos hstate]
    let hroot :=
      zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0
    let original := routing.path state 0 hstate hroot
    let erased :=
      centralPhysicalFiniteVacuumSectorLoopErasedPositivePath hstate original
    let weight := centralPhysicalFiniteWeight w hw K 0 state
    let originalSingle := weight * PositiveKernelChainIn.resistance original
    let erasedSingle := weight * PositiveKernelChainIn.resistance erased
    have hsub : List.Sublist
        (PositiveKernelChainIn.directedEdges erased)
        (PositiveKernelChainIn.directedEdges original) :=
      centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_sublist
        hstate original
    have hweight : (0 : Q') ≤ weight := by
      unfold weight
      exact centralPhysicalRowMarginal_nonnegative hw K 0
        (centralPhysicalFiniteStateAt w hw K 0 state)
    have hres : PositiveKernelChainIn.resistance erased ≤
        PositiveKernelChainIn.resistance original :=
      centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_resistance_le
        hstate original
    have hsingle : erasedSingle ≤ originalSingle := by
      unfold erasedSingle originalSingle
      exact Q'.mul_le_mul_of_nonneg_left _ _ weight hres hweight
    have horiginalSingle : (0 : Q') ≤ originalSingle := by
      unfold originalSingle
      exact Q'.mul_nonneg _ _ hweight
        (PositiveKernelChainIn.resistance_nonnegative original)
    have hdoubled : erasedSingle + erasedSingle ≤
        originalSingle + originalSingle :=
      Q'.add_le_add hsingle hsingle
    have horiginalDoubled : (0 : Q') ≤
        originalSingle + originalSingle :=
      Q'.zero_le_add _ _ horiginalSingle horiginalSingle
    exact weightedDirectedEdgeLoad_constantMap_le_of_sublist_local
      hsub (erasedSingle + erasedSingle)
      (originalSingle + originalSingle) hdoubled horiginalDoubled
      source target
  · rw [dif_neg hstate, dif_neg hstate]
    exact Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_stateEdgeLoad_sum
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source target ≈
      listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
            routing state source target)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0) := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_loopErased_le
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing)
        source target ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source target := by
  have herased :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_stateEdgeLoad_sum
      (loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing)
      source target
  have horiginal :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_stateEdgeLoad_sum
      routing source target
  have hsum := listQSum_mono
    (fun state =>
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing)
        state source target)
    (fun state =>
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target)
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (fun state _hstate =>
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_loopErased_le
        routing state source target)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv herased)
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv horiginal))

/-! ## 6. Route-level simplicity and resistance -/

theorem loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_directedEdges_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (PositiveKernelChainIn.directedEdges
      ((loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing).path
        left right hleft hright)).Nodup := by
  exact centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_nodup
    hleft (routing.path left right hleft hright)

theorem loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_resistance_le
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn.resistance
        ((loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing).path
          left right hleft hright) ≤
      PositiveKernelChainIn.resistance
        (routing.path left right hleft hright) := by
  exact centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_resistance_le
    hleft (routing.path left right hleft hright)

/-! ## 7. Cofinal congestion certificates normalize at no extra cost -/

namespace FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound

def loopErased
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) :
    FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
      hw where
  start := family.start
  bound := family.bound
  bound_nonnegative := family.bound_nonnegative
  routing := fun K hK =>
    loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (family.routing K hK)
  flowLoad_le := fun K hK source target => by
    exact Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_loopErased_le
        (family.routing K hK) source target)
      (family.flowLoad_le K hK source target)

theorem loopErased_routing_path_directedEdges_nodup
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    (PositiveKernelChainIn.directedEdges
      (((loopErased family).routing K hK).path
        left right hleft hright)).Nodup := by
  exact loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_directedEdges_nodup
    (family.routing K hK) hleft hright

end FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_sublist
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_resistance_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_loopErased_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_loopErased_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_directedEdges_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_resistance_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound.loopErased
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound.loopErased_routing_path_directedEdges_nodup
