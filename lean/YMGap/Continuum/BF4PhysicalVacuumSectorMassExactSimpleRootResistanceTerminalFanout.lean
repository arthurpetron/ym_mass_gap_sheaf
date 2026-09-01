/-
# Terminal-root fanout forced by simple BF4 resistance routing

Every non-vacuum route to the physical root has a literal final directed edge
`(predecessor, 0)`.  This module extracts that predecessor constructively and
partitions routed sources by it.  Each terminal-predecessor fiber is a subset
of the users of the corresponding root edge, so the exact resistance-flow
load bounds its cardinality.

Consequently a cutoff-independent simple-routing congestion certificate must
route the growing vacuum sector through positive root spokes with uniformly
bounded terminal fibers.  This is a necessary fanout condition, not a
construction of the required routing or congestion constant.  No completed
gap, continuum limit, continuum Yang--Mills theory, or Clay conclusion is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. The literal terminal source of every non-vacuum route -/

def centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) : Nat :=
  PositiveKernelChainIn.terminalSource
    (routing.path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalEdge_mem
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hne : state ≠ 0) :
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate, 0) ∈
      PositiveKernelChainIn.directedEdges
        (routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)) :=
  PositiveKernelChainIn.terminalSource_mem_directedEdges _ hne

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_sector
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  have hedge :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalEdge_mem
      routing state hstate hne
  exact (PositiveKernelChainIn.directedEdges_mem_support hstate
    (routing.path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))
    _ hedge).1

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalKernel_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hne : state ≠ 0) :
    (0 : Q') < centralPhysicalFiniteKernel w hw K 0
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate) 0 := by
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
  exact PositiveKernelChainIn.terminalSource_kernel_pos _ hne

/-! ## 2. Positive root predecessors and terminal fibers -/

def centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun source => decide
      ((0 : Q') < centralPhysicalFiniteKernel w hw K 0 source 0))

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_predecessors
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate ∈
      centralPhysicalFiniteVacuumSectorPositiveRootPredecessors w hw K := by
  apply List.mem_filter.mpr
  exact ⟨
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_sector
      routing state hstate hne,
    decide_eq_true
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalKernel_pos
        routing state hstate hne)⟩

def centralPhysicalFiniteVacuumSectorSimpleRootTerminalSourceB
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source : Nat) : Bool :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    if _hne : state ≠ 0 then
      decide
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
          routing state hstate = source)
    else false
  else false

def centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSourceB
      routing · source)

theorem mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K}
    {state source : Nat} :
    state ∈ centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        routing source ↔
      ∃ (hstate : state ∈
          centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        (_hne : state ≠ 0),
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
          routing state hstate = source := by
  constructor
  · intro hmem
    have hparts := List.mem_filter.mp hmem
    unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSourceB at hparts
    rw [dif_pos hparts.1] at hparts
    by_cases hne : state ≠ 0
    · rw [dif_pos hne] at hparts
      exact ⟨hparts.1, hne, of_decide_eq_true hparts.2⟩
    · rw [dif_neg hne] at hparts
      cases hparts.2
  · rintro ⟨hstate, hne, heq⟩
    apply List.mem_filter.mpr
    refine ⟨hstate, ?_⟩
    unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSourceB
    rw [dif_pos hstate, dif_pos hne]
    exact decide_eq_true heq

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_subset_edgeUsers
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat) :
    ∀ state,
      state ∈ centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          routing source →
        state ∈
          centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
            routing source 0 := by
  intro state hstate
  obtain ⟨hsector, hne, hterminal⟩ :=
    mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp hstate
  apply List.mem_filter.mpr
  constructor
  · apply
      mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mpr
    refine ⟨hsector, ?_⟩
    rw [← hterminal]
    exact centralPhysicalFiniteVacuumSectorSimpleRootTerminalEdge_mem
      routing state hsector hne
  · exact decide_eq_true hne

/-! ## 3. Every terminal fiber is paid by its root-edge congestion -/

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_cardinality_le_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          routing source).length ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source 0 := by
  have hnodup :
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        routing source).Nodup :=
    List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
  have hlength :
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          routing source).length ≤
        (centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
          routing source 0).length :=
    FiniteListBound.nodup_subset_length_le _ _ hnodup
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_subset_edgeUsers
        routing source)
  exact Q'.le_trans' _ _ _ (Q'.ofNat_le_ofNat hlength)
    (nonzeroRoutedRootEdgeUsingStates_cardinality_le_flowLoad
      routing source 0)

namespace FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound

/-- The promised congestion scalar bounds every terminal-root predecessor
fiber at every later cutoff. -/
theorem terminalFiber_cardinality_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) (source : Nat) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
          (family.routing K hK) source).length ≤
      family.bound := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_cardinality_le_flowLoad
      (family.routing K hK) source)
    (family.flowLoad_le K hK source 0)

end FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.centralPhysicalFiniteVacuumSectorSimpleRootTerminalEdge_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.centralPhysicalFiniteVacuumSectorSimpleRootTerminalKernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_predecessors
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_subset_edgeUsers
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_cardinality_le_flowLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.terminalFiber_cardinality_le_bound
