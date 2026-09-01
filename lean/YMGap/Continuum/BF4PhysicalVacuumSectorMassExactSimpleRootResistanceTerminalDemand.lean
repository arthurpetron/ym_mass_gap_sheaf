/-
# Weighted terminal-root demand forced by simple BF4 routing

The terminal-fanout audit counts how many non-vacuum states finish through
each positive vacuum-root spoke.  Cardinality alone does not see the actual
resistance cost.  This module records the sharper necessary quantity.

For every state assigned to a terminal spoke `(u, 0)`, its full path
resistance contains `1 / kernel(u, 0)`.  Consequently the routed flow load on
that spoke pays the exact terminal-fiber demand

  sum_{state in fiber(u)}
    2 * stationaryWeight(state) / kernel(u, 0).

Thus a cutoff-independent simple-routing congestion certificate bounds both
the fiber cardinality and this stationary-mass-weighted inverse root-kernel
demand.  This is a necessary localized tail estimate, not a construction of
the routing, a uniform BF4 bound, a cofinal gap, or a continuum result.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_member_le_nonnegative_local
    {Item : Type} (value : Item → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ {items : List Item} {item : Item},
      item ∈ items → value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local value hvalue htail
        have htailLe : listQSum value tail ≤
            value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

/-! ## 1. Every terminal edge contributes its reciprocal to path resistance -/

theorem reciprocalKernel_le_pathResistance_of_edge_mem
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last source target : State}
    (path : PositiveKernelChainIn kernel support first last)
    (hedge : (source, target) ∈ PositiveKernelChainIn.directedEdges path)
    (hpositive : (0 : Q') < kernel source target) :
    Q'.recipPos (kernel source target) hpositive ≤
      PositiveKernelChainIn.resistance path := by
  have hmember :
      positiveEdgeResistance kernel (source, target) ≤
        listQSum (positiveEdgeResistance kernel)
          (PositiveKernelChainIn.directedEdges path) :=
    listQSum_member_le_nonnegative_local
      (positiveEdgeResistance kernel)
      (positiveEdgeResistance_nonnegative kernel) hedge
  have hreciprocal :
      Q'.recipPos (kernel source target) hpositive ≤
        listQSum (positiveEdgeResistance kernel)
          (PositiveKernelChainIn.directedEdges path) := by
    unfold positiveEdgeResistance at hmember
    rw [dif_pos hpositive] at hmember
    exact hmember
  exact Q'.le_trans' _ _ _ hreciprocal
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (resistance_eqv_directedEdges_sum path)))

/-! ## 2. Pointwise and fiberwise terminal resistance demand -/

theorem twice_weight_mul_terminalReciprocal_le_stateEdgeLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hne : state ≠ 0) :
    let source :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate
    let hpositive :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalKernel_pos
        routing state hstate hne
    let singleDemand :=
      centralPhysicalFiniteWeight w hw K 0 state *
        Q'.recipPos
          (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
    singleDemand + singleDemand ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source 0 := by
  let path := routing.path state 0 hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
  let source :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
      routing state hstate
  let hpositive :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalKernel_pos
      routing state hstate hne
  let reciprocal := Q'.recipPos
    (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
  let weight := centralPhysicalFiniteWeight w hw K 0 state
  let singleDemand := weight * reciprocal
  have hedge : (source, 0) ∈ PositiveKernelChainIn.directedEdges path := by
    exact centralPhysicalFiniteVacuumSectorSimpleRootTerminalEdge_mem
      routing state hstate hne
  have hreciprocal : reciprocal ≤ PositiveKernelChainIn.resistance path := by
    exact reciprocalKernel_le_pathResistance_of_edge_mem
      path hedge hpositive
  have hweight0 : (0 : Q') ≤ weight :=
    Q'.le_of_lt (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hstate)
  have hsingle : singleDemand ≤
      weight * PositiveKernelChainIn.resistance path :=
    Q'.mul_le_mul_of_nonneg_left _ _ weight hreciprocal hweight0
  have hstateLoad : singleDemand + singleDemand ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        routing state := by
    unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
    rw [dif_pos hstate]
    exact Q'.add_le_add hsingle hsingle
  exact Q'.le_trans' _ _ _ hstateLoad
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad_le_stateEdgeLoad
      routing state source 0 hstate hedge)

/-- The stationary-mass-weighted reciprocal demand of one positive terminal
root spoke, summed over the states assigned to it by the selected routing. -/
def centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw K 0 source 0) : Q' :=
  listQSum
    (fun state =>
      let singleDemand :=
        centralPhysicalFiniteWeight w hw K 0 state *
          Q'.recipPos
            (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
      singleDemand + singleDemand)
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber routing source)

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand_le_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw K 0 source 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        routing source hpositive ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source 0 := by
  let demand := fun state =>
    let singleDemand :=
      centralPhysicalFiniteWeight w hw K 0 state *
        Q'.recipPos
          (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
    singleDemand + singleDemand
  let edgeLoad := fun state =>
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
      routing state source 0
  let fiber :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber routing source
  let users :=
    centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates routing source 0
  have hpoint : ∀ state, state ∈ fiber → demand state ≤ edgeLoad state := by
    intro state hstate
    obtain ⟨hsector, hne, hterminal⟩ :=
      mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp hstate
    subst source
    exact twice_weight_mul_terminalReciprocal_le_stateEdgeLoad
      routing state hsector hne
  have hfiber : listQSum demand fiber ≤ listQSum edgeLoad fiber :=
    listQSum_mono demand edgeLoad fiber hpoint
  have hfiberNodup : fiber.Nodup :=
    List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
  have hsubset : ∀ state, state ∈ fiber → state ∈ users := by
    intro state hstate
    have hnonzero :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_subset_edgeUsers
        routing source state hstate
    exact (List.mem_filter.mp hnonzero).1
  have husers : listQSum edgeLoad fiber ≤ listQSum edgeLoad users := by
    apply listQSum_le_of_injective fiber users edgeLoad edgeLoad
      (fun state => state) hfiberNodup hsubset
    · intro left _ right _ heq
      exact heq
    · intro state _
      exact Q'.le_refl' (edgeLoad state)
    · intro state _
      exact
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_nonnegative
          routing state source 0
  have htail : listQSum edgeLoad users =
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
        routing source 0 := rfl
  exact Q'.le_trans' _ _ _ hfiber
    (Q'.le_trans' _ _ _ husers
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_of_eq htail))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_edgeTail
              routing source 0)))))

namespace FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound

/-- A common simple-routing congestion bound necessarily bounds the weighted
inverse-kernel demand on every positive terminal root spoke. -/
theorem terminalFiberResistanceDemand_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (family.routing K hK) source hpositive ≤
      family.bound := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand_le_flowLoad
      (family.routing K hK) source hpositive)
    (family.flowLoad_le K hK source 0)

end FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand.reciprocalKernel_le_pathResistance_of_edge_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand.twice_weight_mul_terminalReciprocal_le_stateEdgeLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand.centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand_le_flowLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand.FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.terminalFiberResistanceDemand_le_bound
