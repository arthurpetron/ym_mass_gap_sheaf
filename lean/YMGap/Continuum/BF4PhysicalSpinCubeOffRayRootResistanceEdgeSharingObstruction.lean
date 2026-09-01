/-
# Literal edge-sharing obstruction for BF4 off-ray root resistance flow

Every state whose selected vertex-simple root path uses a directed edge is
nonzero and contributes at least one unit to that edge's resistance flow.
This module removes the legacy nonzero filter from the necessary
combinatorial condition: literal edge-user cardinality is bounded by literal
resistance congestion.  The same statement holds shell by shell.

Consequently, any cofinal uniform resistance-congestion certificate for the
current canonical routing entails a cutoff-uniform bound on the number of
selected paths sharing every directed edge.  This is a necessary condition,
not a construction of the bound and not a continuum or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_length_le_listQSum_of_one_le_local {A : Type}
    (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → (1 : Q') ≤ value item) →
        Q'.ofNat items.length ≤ listQSum value items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hone => by
      have hhead : (1 : Q') ≤ value head :=
        hone head List.mem_cons_self
      have htail : Q'.ofNat tail.length ≤ listQSum value tail :=
        ofNat_length_le_listQSum_of_one_le_local value tail
          (fun item hitem => hone item (List.mem_cons_of_mem head hitem))
      have hsum : (1 : Q') + Q'.ofNat tail.length ≤
          value head + listQSum value tail :=
        Q'.add_le_add hhead htail
      have hcount : Q'.ofNat (head :: tail).length ≈
          (1 : Q') + Q'.ofNat tail.length := by
        simp only [List.length_cons]
        exact Q'.eqv_trans _ (Q'.ofNat tail.length + 1) _
          (Q'.ofNat_add_eqv tail.length 1)
          (Q'.add_comm_eqv _ _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcount) hsum

/-! ## 1. Every literal edge user is nonzero and costs at least one -/

theorem centralLowerExcitedSpinCubeOffRayRootEdgeUsingState_ne_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target state : Nat}
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
        w hw K source target) :
    state ≠ 0 := by
  apply
    centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellState_ne_zero
      (shell :=
        centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass w hw K state)
  unfold centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
  exact List.mem_filter.mpr ⟨hstate, by simp⟩

theorem one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_edgeUsingStates
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target state : Nat}
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
        w hw K source target) :
    (1 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w hw K state := by
  obtain ⟨hoffRay, _hedge⟩ :=
    mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hstate
  exact one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w hw K state hoffRay
      (centralLowerExcitedSpinCubeOffRayRootEdgeUsingState_ne_zero hstate)

/-! ## 2. Shell and total edge-user cardinality are paid by congestion -/

theorem centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_cardinality_le_load
    (w : Q') (hw : (0 : Q') ≤ w)
    (K source target shell : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
          w hw K source target shell).length ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
        w hw K source target shell := by
  unfold
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
  apply ofNat_length_le_listQSum_of_one_le_local
  intro state hstate
  exact
    one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
      hstate

theorem centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_cardinality_le_flowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
          w hw K source target).length ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target := by
  have hcount : Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
          w hw K source target).length ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
        w hw K source target := by
    unfold centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
    apply ofNat_length_le_listQSum_of_one_le_local
    intro state hstate
    exact
      one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_edgeUsingStates
        hstate
  exact Q'.le_trans' _ _ _ hcount
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
          w hw K source target)))

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound

/-- A cofinal resistance-congestion certificate for the selected canonical
paths necessarily bounds their literal directed-edge sharing multiplicity. -/
theorem edgeUsingStates_cardinality_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
          w (Q'.le_of_lt hw) K source target).length ≤ family.bound := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_cardinality_le_flowLoad
      w (Q'.le_of_lt hw) K source target)
    (family.flowLoad_le K hK source target)

end FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction.centralLowerExcitedSpinCubeOffRayRootEdgeUsingState_ne_zero
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction.centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_cardinality_le_load
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction.centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_cardinality_le_flowLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction.FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound.edgeUsingStates_cardinality_le_bound
