/-
# Multiplicity-aware edge tails for adaptive BF4 root routing

The full-sector exact-mass resistance compiler permits an arbitrary positive
route from every vacuum-sector state to the root.  Unlike the canonical
loop-erased route, an adaptive route is not required to be simple, so a
directed edge may occur more than once in a single path.

This module retains that multiplicity exactly.  For every adaptive routing it
defines the doubled stationary resistance load of one source state, the
rational occurrence multiplicity of a directed edge in that state's route,
and proves

    state edge load = doubled state resistance load * edge multiplicity.

It then identifies the total routed flow load with the literal tail over
states whose route uses that edge.  Every non-vacuum edge user contributes at
least one unit, so any cofinal adaptive congestion bound necessarily gives a
uniform bound on the number of non-vacuum routed sources sharing each edge.

This is a diagnostic for path design, not a bounded-sharing construction.  No
cofinal adaptive routing, cofinal gap, continuum limit, continuum Yang--Mills
theory, or Clay conclusion is asserted.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_nonnegative_local {Item : Type}
    (value : Item → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List Item, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_nonnegative_local {Item : Type}
    (value : Item → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List Item) {item : Item}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have ih :=
          listQSum_member_le_nonnegative_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hscaled := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hscaled
        exact Q'.le_trans' _ _ _ ih hmono

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
  · exact listQSum_mul_left load
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
  · exact listQSum_zero edges

/-! ## 1. One routed state's multiplicity-aware edge load -/

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat) : Q' :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    let path := routing.path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    let singleLoad := centralPhysicalFiniteWeight w hw K 0 state *
      PositiveKernelChainIn.resistance path
    singleLoad + singleLoad
  else 0

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeMultiplicity
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat) : Q' :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    weightedDirectedEdgeLoad
      ((PositiveKernelChainIn.directedEdges
        (routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))).map
        (fun edge => (edge, (1 : Q'))))
      source target
  else 0

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
      routing state)
    source target

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_eqv_load_mul_multiplicity
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target ≈
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
          routing state *
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeMultiplicity
          routing state source target := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeMultiplicity
  by_cases hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0
  · rw [dif_pos hstate, dif_pos hstate, dif_pos hstate]
    exact weightedDirectedEdgeLoad_constantMap_eqv_scalarMultiplicity_local
      _ _ source target
  · rw [dif_neg hstate, dif_neg hstate, dif_neg hstate]
    exact Q'.eqv_symm (Q'.zero_mul_eqv 0)

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
  by_cases hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0
  · rw [dif_pos hstate]
    let path := routing.path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    let singleLoad := centralPhysicalFiniteWeight w hw K 0 state *
      PositiveKernelChainIn.resistance path
    have hsingle : (0 : Q') ≤ singleLoad := by
      exact Q'.mul_nonneg _ _
        (centralPhysicalRowMarginal_nonnegative hw K 0
          (centralPhysicalFiniteStateAt w hw K 0 state))
        (PositiveKernelChainIn.resistance_nonnegative path)
    apply weightedDirectedEdgeLoad_nonnegative
    intro occurrence hoccurrence
    obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hoccurrence
    subst occurrence
    exact Q'.zero_le_add _ _ hsingle hsingle
  · rw [dif_neg hstate]
    exact Q'.le_refl' 0

theorem one_le_centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hne : state ≠ 0) :
    (1 : Q') ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        routing state := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
  rw [dif_pos hstate]
  let path := routing.path state 0 hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
  let singleLoad := centralPhysicalFiniteWeight w hw K 0 state *
    PositiveKernelChainIn.resistance path
  have hone : (1 : Q') ≤ singleLoad := by
    exact sourceWeight_mul_resistance_ge_one
      (centralPhysicalFiniteWeight w hw K 0)
      hne
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw K 0
          (centralPhysicalFiniteStateAt w hw K 0 source)
          (centralPhysicalFiniteStateAt w hw K 0 target))
      (centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hstate)
      path
  have hsingle : (0 : Q') ≤ singleLoad :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hone
  exact Q'.le_trans' _ singleLoad _ hone
    (Q'.add_le_self_of_nonneg singleLoad singleLoad hsingle)

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad_le_stateEdgeLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hedge : (source, target) ∈ PositiveKernelChainIn.directedEdges
      (routing.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        routing state ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
  rw [dif_pos hstate, dif_pos hstate]
  let path := routing.path state 0 hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
  let singleLoad := centralPhysicalFiniteWeight w hw K 0 state *
    PositiveKernelChainIn.resistance path
  let load := singleLoad + singleLoad
  have hsingle : (0 : Q') ≤ singleLoad := by
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative hw K 0
        (centralPhysicalFiniteStateAt w hw K 0 state))
      (PositiveKernelChainIn.resistance_nonnegative path)
  have hload : (0 : Q') ≤ load :=
    Q'.zero_le_add _ _ hsingle hsingle
  change load ≤ weightedDirectedEdgeLoad
    ((PositiveKernelChainIn.directedEdges path).map
      (fun edge => (edge, load))) source target
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map]
  let value := fun edge : Nat × Nat =>
    weightedDirectedEdgeIndicator (edge, load) source target
  have hvalue : ∀ edge, (0 : Q') ≤ value edge := by
    intro edge
    unfold value weightedDirectedEdgeIndicator
    by_cases heq : edge = (source, target)
    · rw [if_pos heq]
      exact hload
    · rw [if_neg heq]
      exact Q'.le_refl' 0
  have hmember := listQSum_member_le_nonnegative_local
    value hvalue (PositiveKernelChainIn.directedEdges path) hedge
  unfold value weightedDirectedEdgeIndicator at hmember
  rw [if_pos rfl] at hmember
  exact hmember

/-! ## 2. Literal edge users and their exact adaptive tail -/

def centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat) : Bool :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    decide ((source, target) ∈ PositiveKernelChainIn.directedEdges
      (routing.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)))
  else false

def centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB
      routing · source target)

theorem mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {K state source target : Nat}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K} :
    state ∈ centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        routing source target ↔
      ∃ hstate : state ∈
          centralPhysicalFiniteVacuumSectorIndices w hw K 0,
        (source, target) ∈ PositiveKernelChainIn.directedEdges
          (routing.path state 0 hstate
            (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)) := by
  constructor
  · intro hstate
    have hparts := List.mem_filter.mp hstate
    refine ⟨hparts.1, ?_⟩
    unfold centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB at hparts
    rw [dif_pos hparts.1] at hparts
    exact of_decide_eq_true hparts.2
  · rintro ⟨hstate, hedge⟩
    apply List.mem_filter.mpr
    refine ⟨hstate, ?_⟩
    unfold centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB
    rw [dif_pos hstate]
    exact decide_eq_true hedge

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_eqv_zero_of_not_uses
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state source target : Nat)
    (hnot : centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB
      routing state source target = false) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB at hnot
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
  by_cases hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0
  · rw [dif_pos hstate] at hnot
    rw [dif_pos hstate]
    have hedge : (source, target) ∉ PositiveKernelChainIn.directedEdges
        (routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)) := by
      intro hedge
      have htrue : decide ((source, target) ∈ PositiveKernelChainIn.directedEdges
          (routing.path state 0 hstate
            (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))) = true :=
        decide_eq_true hedge
      rw [htrue] at hnot
      exact Bool.noConfusion hnot
    exact weightedDirectedEdgeLoad_constantMap_eqv_zero_of_not_mem_local
      _ _ source target hedge
  · rw [dif_neg hstate]
    exact Q'.eqv_refl 0

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

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  listQSum
    (fun state =>
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        routing state source target)
    (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
      routing source target)

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_edgeTail
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source target ≈
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
        routing source target := by
  let test := fun state =>
    centralPhysicalFiniteVacuumSectorRoutedRootStateUsesDirectedEdgeB
      routing state source target
  let value := fun state =>
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
      routing state source target
  refine Q'.eqv_trans _
    (listQSum value
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
      value centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
      weightedDirectedEdgeLoad
    exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum (maskedValue test value)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)) _ ?_ ?_
    · apply listQSum_congr_on
      intro state _hstate
      unfold maskedValue
      cases htest : test state with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold value
          exact
            centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_eqv_zero_of_not_uses
              routing state source target htest
      | true =>
          simp only [↓reduceIte]
          unfold value
          exact Q'.eqv_refl _
    · unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
        centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
      exact listQSum_maskedValue_eqv_filter_local test value
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)

/-! ## 3. Necessary adaptive edge-sharing bound -/

def centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
      routing source target).filter
    (fun state => decide (state ≠ 0))

theorem nonzeroRoutedRootEdgeUsingStates_cardinality_le_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
          routing source target).length ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source target := by
  let value := fun state =>
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
      routing state source target
  have hcount : Q'.ofNat
        (centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
          routing source target).length ≤
      listQSum value
        (centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
          routing source target) := by
    apply ofNat_length_le_listQSum_of_one_le_local
    intro state hstate
    have hparts := List.mem_filter.mp hstate
    obtain ⟨hsector, hedge⟩ :=
      mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mp
        hparts.1
    exact Q'.le_trans' _
      (centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        routing state) _
      (one_le_centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        routing state hsector (of_decide_eq_true hparts.2))
      (centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad_le_stateEdgeLoad
        routing state source target hsector hedge)
  have hfilter : listQSum value
        (centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
          routing source target) ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
        routing source target := by
    unfold centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
    exact listQSum_filter_le_local value
      (fun state => decide (state ≠ 0))
      (fun state =>
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_nonnegative
          routing state source target)
      (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        routing source target)
  exact Q'.le_trans' _ _ _ hcount
    (Q'.le_trans' _ _ _ hfilter
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_edgeTail
            routing source target))))

namespace FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound

/-- Every supplied cofinal adaptive resistance-congestion family necessarily
bounds the non-vacuum route users of each directed edge by the same scalar. -/
theorem nonzeroRoutedRootEdgeUsingStates_cardinality_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorRoutedRootNonzeroEdgeUsingStates
          (family.routing K hK) source target).length ≤
      family.bound := by
  exact Q'.le_trans' _ _ _
    (nonzeroRoutedRootEdgeUsingStates_cardinality_le_flowLoad
      (family.routing K hK) source target)
    (family.flowLoad_le K hK source target)

end FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound

#print axioms
  centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_eqv_load_mul_multiplicity
#print axioms one_le_centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
#print axioms
  centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_edgeTail
#print axioms nonzeroRoutedRootEdgeUsingStates_cardinality_le_flowLoad
#print axioms
  FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound.nonzeroRoutedRootEdgeUsingStates_cardinality_le_bound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
