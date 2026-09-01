/-
# Exact edge-local tails for BF4 off-ray root resistance flow

The global first resistance moment forgets which selected root paths use a
fixed directed edge.  This module retains that incidence information.  For
each edge it defines the literal subcarrier of off-ray source states whose
selected simple path traverses the edge and proves the exact identity

    resistance flow load(edge)
      = sum_{state using edge} weight(state) * pathResistance(state, vacuum).

Thus the remaining cofinal estimate is genuinely edge-local.  The same
identity also gives a necessary combinatorial condition: because every
nontrivial source load is at least one, the number of nonzero selected paths
using an edge is bounded by that edge's resistance congestion.  A uniform
congestion bound therefore requires uniformly bounded nonzero edge-use
multiplicity for this particular routing.

No such upper bound is constructed here.  In particular, no cofinal gap,
thermodynamic or continuum limit, continuum Yang--Mills theory, or Clay
conclusion is asserted.  No `Classical`, choice, `native_decide`, `sorry`, new
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact load of one duplicate-free constant path -/

private theorem weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
    {State : Type} [DecidableEq State]
    (load : Q') (source target : State) :
    ∀ edges : List (State × State), edges.Nodup →
      weightedDirectedEdgeLoad
          (edges.map (fun edge => (edge, load))) source target ≈
        if (source, target) ∈ edges then load else 0
  | [], _ => Q'.eqv_refl 0
  | edge :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [weightedDirectedEdgeLoad, List.map_cons, listQSum,
        weightedDirectedEdgeIndicator]
      by_cases hhead : edge = (source, target)
      · rw [if_pos hhead]
        have hnotmem : (source, target) ∉ rest := by
          intro hmem
          exact hparts.1 (hhead ▸ hmem)
        have hmem : (source, target) ∈ edge :: rest :=
          List.mem_cons.mpr (Or.inl hhead.symm)
        rw [if_pos hmem]
        have htail : weightedDirectedEdgeLoad
            (rest.map (fun traversed => (traversed, load)))
            source target ≈ 0 :=
          Q'.eqv_trans _ (if (source, target) ∈ rest then load else 0) _
            (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
              load source target rest hparts.2)
            (by rw [if_neg hnotmem]; exact Q'.eqv_refl 0)
        change load + weightedDirectedEdgeLoad
            (rest.map (fun traversed => (traversed, load)))
            source target ≈ load
        exact Q'.eqv_trans _ (load + 0) _
          (Q'.add_eqv_congr_left load _ _ htail)
          (Q'.eqv_of_eq (Q'.add_zero' load))
      · rw [if_neg hhead]
        have hne : (source, target) ≠ edge := fun heq => hhead heq.symm
        by_cases htailMem : (source, target) ∈ rest
        · have hmem : (source, target) ∈ edge :: rest :=
            List.mem_cons_of_mem edge htailMem
          rw [if_pos hmem]
          have htail : weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ load :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then load else 0) _
              (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
                load source target rest hparts.2)
              (by rw [if_pos htailMem]; exact Q'.eqv_refl load)
          change 0 + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ load
          exact Q'.eqv_trans _ (0 + load) _
            (Q'.add_eqv_congr_left 0 _ _ htail)
            (Q'.eqv_of_eq (Q'.zero_add' load))
        · have hnotmem : (source, target) ∉ edge :: rest := by
            intro hmem
            rcases List.mem_cons.mp hmem with hedge | hrest
            · exact hne hedge
            · exact htailMem hrest
          rw [if_neg hnotmem]
          have htail : weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0 :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then load else 0) _
              (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
                load source target rest hparts.2)
              (by rw [if_neg htailMem]; exact Q'.eqv_refl 0)
          change 0 + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0
          exact Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr_left 0 _ _ htail)
            (Q'.eqv_of_eq (Q'.zero_add' 0))

/-! ## 2. The literal source subcarrier using one edge -/

def centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB
    (w : Q') (hw : (0 : Q') ≤ w) (K state source target : Nat) : Bool :=
  if hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K then
    decide
      ((source, target) ∈ PositiveKernelChainIn.directedEdges
        (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate))
  else false

def centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : List Nat :=
  (centralLowerExcitedSpinCubeOffRayIndices w hw K).filter
    (centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB
      w hw K · source target)

theorem mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {K state source target : Nat} :
    state ∈ centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
        w hw K source target ↔
      ∃ hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K,
        (source, target) ∈ PositiveKernelChainIn.directedEdges
          (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate) := by
  constructor
  · intro hstate
    have hparts := List.mem_filter.mp hstate
    refine ⟨hparts.1, ?_⟩
    unfold centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB at hparts
    rw [dif_pos hparts.1] at hparts
    exact of_decide_eq_true hparts.2
  · rintro ⟨hstate, hedge⟩
    apply List.mem_filter.mpr
    refine ⟨hstate, ?_⟩
    unfold centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB
    rw [dif_pos hstate]
    exact decide_eq_true hedge

theorem centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathLoad_eqv_mask
    (w : Q') (hw : (0 : Q') ≤ w) (K state source target : Nat) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
          w hw K state)
        source target ≈
      if centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB
          w hw K state source target then
        centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
          w hw K state
      else 0 := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB
  by_cases hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K
  · rw [dif_pos hstate, dif_pos hstate, dif_pos hstate]
    simpa only [decide_eq_true_eq] using
      (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
        (centralPhysicalFiniteWeight w hw K 0 state *
          PositiveKernelChainIn.resistance
            (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate))
        source target
        (PositiveKernelChainIn.directedEdges
          (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate))
        (centralLowerExcitedSpinCubeOffRayRootPositivePath_directedEdges_nodup
          w hw K state hstate))
  · rw [dif_neg hstate, dif_neg hstate, dif_neg hstate]
    exact Q'.eqv_refl 0

/-! ## 3. Exact edge-local stationary resistance tail -/

private def maskedValue {Item : Type}
    (test : Item → Bool) (value : Item → Q') (item : Item) : Q' :=
  if test item then value item else 0

private theorem listQSum_maskedValue_eqv_filter_local
    {Item : Type} (test : Item → Bool) (value : Item → Q') :
    ∀ items : List Item,
      listQSum (maskedValue test value) items ≈
        listQSum value (items.filter test)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases htest : test head with
      | false =>
          simp only [maskedValue, htest, Bool.false_eq_true,
            ↓reduceIte, List.filter_cons, listQSum]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.eqv_refl 0)
              (listQSum_maskedValue_eqv_filter_local test value tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [maskedValue, htest, ↓reduceIte,
            List.filter_cons, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl (value head))
            (listQSum_maskedValue_eqv_filter_local test value tail)

def centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
    (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
      w hw K source target)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target ≈
      centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
        w hw K source target := by
  let test := fun state =>
    centralLowerExcitedSpinCubeOffRayRootStateUsesDirectedEdgeB
      w hw K state source target
  let value := centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w hw K
  refine Q'.eqv_trans _
    (listQSum (maskedValue test value)
      (centralLowerExcitedSpinCubeOffRayIndices w hw K)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          weightedDirectedEdgeLoad
            (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
              w hw K state)
            source target)
        (centralLowerExcitedSpinCubeOffRayIndices w hw K)) _ ?_ ?_
    · exact centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_stateLoadSum
        w hw K source target
    · apply listQSum_congr_on
      intro state _hstate
      exact centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathLoad_eqv_mask
        w hw K state source target
  · unfold centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
      centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
    exact listQSum_maskedValue_eqv_filter_local test value
      (centralLowerExcitedSpinCubeOffRayIndices w hw K)

/-! ## 4. Necessary edge-use multiplicity bound -/

private theorem ofNat_length_le_listQSum_of_one_le_local {Item : Type}
    (value : Item → Q') :
    ∀ items : List Item,
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

private theorem listQSum_filter_le_local {Item : Type}
    (value : Item → Q') (test : Item → Bool)
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List Item,
      listQSum value (items.filter test) ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_local value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have hmono : listQSum value tail ≤
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail) (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

def centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : List Nat :=
  (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
      w hw K source target).filter
    (fun state => decide (state ≠ 0))

theorem nonzeroEdgeUsingStates_cardinality_le_resistanceFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
          w hw K source target).length ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target := by
  have hcount : Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
          w hw K source target).length ≤
      listQSum
        (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
        (centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
          w hw K source target) := by
    apply ofNat_length_le_listQSum_of_one_le_local
    intro state hstate
    have hparts := List.mem_filter.mp hstate
    have hedgeParts :=
      mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hparts.1
    exact one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
      w hw K state hedgeParts.1 (of_decide_eq_true hparts.2)
  have hfilter : listQSum
        (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
        (centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
          w hw K source target) ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
        w hw K source target := by
    unfold centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
      centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
    exact listQSum_filter_le_local
      (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
      (fun state => decide (state ≠ 0))
      (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_nonnegative
        w hw K)
      (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
        w hw K source target)
  exact Q'.le_trans' _ _ _ hcount
    (Q'.le_trans' _ _ _ hfilter
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
            w hw K source target))))

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound

/-- A cofinal resistance-congestion bound necessarily bounds the number of
selected root paths using every fixed directed edge by the same rational. -/
theorem nonzeroEdgeUsingStates_cardinality_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootNonzeroEdgeUsingStates
          w (Q'.le_of_lt hw) K source target).length ≤ family.bound := by
  exact Q'.le_trans' _ _ _
    (nonzeroEdgeUsingStates_cardinality_le_resistanceFlowLoad
      w (Q'.le_of_lt hw) K source target)
    (family.flowLoad_le K hK source target)

end FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound

#print axioms
  mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff
#print axioms
  centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathLoad_eqv_mask
#print axioms
  centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
#print axioms nonzeroEdgeUsingStates_cardinality_le_resistanceFlowLoad
#print axioms
  FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound.nonzeroEdgeUsingStates_cardinality_le_bound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
