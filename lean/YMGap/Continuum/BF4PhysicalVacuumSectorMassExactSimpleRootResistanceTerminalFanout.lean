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
import YMGap.Continuum.FiniteKeyRepresentativePartition

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
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_one_eqv_ofNat_length_local {Item : Type} :
    ∀ items : List Item,
      listQSum (fun _ => (1 : Q')) items ≈ Q'.ofNat items.length
  | [] => Q'.eqv_symm Q'.ofNat_zero_eqv
  | _ :: tail => by
      refine Q'.eqv_trans _ (1 + Q'.ofNat tail.length) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ _
          (listQSum_one_eqv_ofNat_length_local tail)
      · change 1 + Q'.ofNat tail.length ≈
          Q'.ofNat (tail.length + 1)
        rw [Nat.add_comm tail.length 1]
        exact Q'.eqv_symm (Q'.ofNat_add_eqv 1 tail.length)

private theorem listQSum_le_length_mul_local {Item : Type}
    (value : Item → Q') {bound : Q'}
    (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List Item,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul_local value hbound0 tail
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead htail) ?_
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

/-- The literal non-vacuum source carrier partitioned by terminal spokes. -/
def centralPhysicalFiniteVacuumSectorNonzeroIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun state => decide (state ≠ 0))

theorem mem_centralPhysicalFiniteVacuumSectorNonzeroIndices_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {K state : Nat} :
    state ∈ centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K ↔
      state ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
        state ≠ 0 := by
  constructor
  · intro hmem
    have hparts := List.mem_filter.mp hmem
    exact ⟨hparts.1, of_decide_eq_true hparts.2⟩
  · rintro ⟨hsector, hne⟩
    exact List.mem_filter.mpr ⟨hsector, decide_eq_true hne⟩

/-- Total terminal-source code, with an irrelevant root fallback off the
finite sector.  On the non-vacuum carrier it is the literal final source. -/
def centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat) : Nat :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
      routing state hstate
  else 0

/-- One actual non-vacuum representative for every terminal source used by
the selected routing. -/
def centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    List Nat :=
  keyRepresentatives
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode routing)
    (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K)

/-- The duplicate-free list of terminal root spokes actually used. -/
def centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    List Nat :=
  (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
    routing).map
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode routing)

/-- The exact realized-key fiber used by the finite partition theorem. -/
def centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (representative : Nat) : List Nat :=
  representativeFiber
    (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K)
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode routing)
    representative

theorem centralPhysicalFiniteVacuumSectorNonzeroIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K).Nodup :=
  List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)

theorem centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
      routing).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
    centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
  exact keyRepresentatives_keys_nodup
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode routing)
    (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K)

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

theorem centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_subset_predecessors
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    ∀ source,
      source ∈
          centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
            routing →
        source ∈
          centralPhysicalFiniteVacuumSectorPositiveRootPredecessors w hw K := by
  intro source hsource
  unfold centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources at hsource
  obtain ⟨representative, hrepresentative, rfl⟩ :=
    List.mem_map.mp hsource
  have hnonzero := keyRepresentatives_mem_source
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode routing)
    (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K)
    representative hrepresentative
  have hparts :=
    mem_centralPhysicalFiniteVacuumSectorNonzeroIndices_iff.mp hnonzero
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
  rw [dif_pos hparts.1]
  exact
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_predecessors
      routing representative hparts.1 hparts.2

theorem centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber_subset
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (representative : Nat) :
    ∀ state,
      state ∈
          centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
            routing representative →
        state ∈
          centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber routing
            (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
              routing representative) := by
  intro state hstate
  unfold centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
    representativeFiber at hstate
  have hparts := List.mem_filter.mp hstate
  have hnonzero :=
    mem_centralPhysicalFiniteVacuumSectorNonzeroIndices_iff.mp hparts.1
  have hcode :
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
          routing representative =
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
          routing state :=
    of_decide_eq_true hparts.2
  apply mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mpr
  refine ⟨hnonzero.1, hnonzero.2, ?_⟩
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode at hcode
  rw [dif_pos hnonzero.1] at hcode
  exact hcode.symm

theorem centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber_cardinality_le
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (representative : Nat) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
          routing representative).length ≤
      Q'.ofNat
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber routing
          (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
            routing representative)).length := by
  have hnodup :
      (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
        routing representative).Nodup :=
    List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorNonzeroIndices_nodup w hw K)
  exact Q'.ofNat_le_ofNat
    (FiniteListBound.nodup_subset_length_le _ _ hnodup
      (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber_subset
        routing representative))

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

/-! ## 3. Exact finite terminal-fanout partition -/

theorem centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFibers_cardinality_total
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    listQSum
        (fun representative =>
          Q'.ofNat
            (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
              routing representative).length)
        (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
          routing) ≈
      Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K).length := by
  have hpartition := keyRepresentativeFibers_weight_total
    (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K)
    (fun _ : Nat => (1 : Q'))
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode routing)
  have houter :
      listQSum
          (fun representative =>
            listQSum (fun _ => (1 : Q'))
              (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
                routing representative))
          (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
            routing) ≈
        listQSum
          (fun representative =>
            Q'.ofNat
              (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
                routing representative).length)
          (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
            routing) := by
    apply listQSum_congr_on
    intro representative _
    exact listQSum_one_eqv_ofNat_length_local _
  have hpartition' :
      listQSum
          (fun representative =>
            listQSum (fun _ => (1 : Q'))
              (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
                routing representative))
          (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
            routing) ≈
        listQSum (fun _ => (1 : Q'))
          (centralPhysicalFiniteVacuumSectorNonzeroIndices w hw K) := by
    simpa only [
      centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber,
      centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives]
      using hpartition
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm houter)
    (Q'.eqv_trans _ _ _ hpartition'
      (listQSum_one_eqv_ofNat_length_local _))

/-! ## 4. Every terminal fiber is paid by its root-edge congestion -/

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

theorem realizedTerminalFiber_cardinality_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) (representative : Nat) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
          (family.routing K hK) representative).length ≤
      family.bound := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber_cardinality_le
      (family.routing K hK) representative)
    (terminalFiber_cardinality_le_bound family K hK
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
        (family.routing K hK) representative))

/-- The complete non-vacuum carrier must fit into the number of terminal
spokes actually used times the common congestion bound. -/
theorem nonzero_cardinality_le_usedTerminalSources_mul_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length ≤
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
            (family.routing K hK)).length *
        family.bound := by
  have htotal :=
    centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFibers_cardinality_total
      (family.routing K hK)
  have hsum :
      listQSum
          (fun representative =>
            Q'.ofNat
              (centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFiber
                (family.routing K hK) representative).length)
          (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
            (family.routing K hK)) ≤
        Q'.ofNat
            (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalRepresentatives
              (family.routing K hK)).length *
          family.bound :=
    listQSum_le_length_mul_local _ family.bound_nonnegative _
      (fun representative _ =>
        realizedTerminalFiber_cardinality_le_bound
          family K hK representative)
  have hresult := Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal) hsum
  simpa only [
    centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources,
    List.length_map] using hresult

/-- Necessary positive-root fanout inequality: all non-vacuum states must fit
inside the complete positive root-spoke carrier at the common fiber bound. -/
theorem nonzero_cardinality_le_positiveRootPredecessors_mul_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length ≤
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
            w (Q'.le_of_lt hw) K).length *
        family.bound := by
  have hused :=
    nonzero_cardinality_le_usedTerminalSources_mul_bound family K hK
  have hlength :
      (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
          (family.routing K hK)).length ≤
        (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
          w (Q'.le_of_lt hw) K).length :=
    FiniteListBound.nodup_subset_length_le _ _
      (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_nodup
        (family.routing K hK))
      (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_subset_predecessors
        (family.routing K hK))
  exact Q'.le_trans' _ _ _ hused
    (Q'.mul_le_mul_of_nonneg_right _ _ family.bound
      (Q'.ofNat_le_ofNat hlength) family.bound_nonnegative)

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
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.centralPhysicalFiniteVacuumSectorSimpleRootRealizedTerminalFibers_cardinality_total
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.nonzero_cardinality_le_usedTerminalSources_mul_bound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout.FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.nonzero_cardinality_le_positiveRootPredecessors_mul_bound
