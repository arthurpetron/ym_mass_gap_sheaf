/-
# Canonical finite physical vacuum sector

The literal positive-row BF4 carrier can be reducible, so it must not be used
as though it had a unique vacuum.  This module makes the required sector
choice constructively: index the exact finite positive-row Markov carrier,
form the symmetric support graph of the production reflected kernel, and
select the connected component containing the vacuum index.

The result exists at every finite cutoff and coupling with nonnegative weight.
It is an exact finite superselection sector, not yet a compatible cofinal
family across cutoffs and not a thermodynamic or continuum construction.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
import YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
import YMGap.Continuum.FiniteBoolGraphRootComponent

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSector

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The physical enumeration starts at the vacuum -/

private theorem range_succ_shift_local (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        List.range (Nat.succ n + 1) =
            List.range (n + 1) ++ [n + 1] := by
          simpa only [Nat.succ_eq_add_one] using
            (List.range_succ (n := n + 1))
        _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] :=
          congrArg (fun items => items ++ [n + 1]) ih
        _ = 0 :: (List.range (n + 1)).map Nat.succ := by
          simp only [List.range_succ, List.map_append, List.map,
            List.cons_append, Nat.succ_eq_add_one]

private theorem setEdgeLabel_zero_zero (edge : Nat) :
    setEdgeLabel zeroEdgeLabelling edge 0 = zeroEdgeLabelling := by
  funext id
  unfold setEdgeLabel zeroEdgeLabelling
  split <;> rfl

/-- The Cartesian bounded-labelling enumeration literally begins with the
all-zero labelling for every cutoff and every finite coordinate list. -/
theorem boundedEdgeLabellings_starts_vacuum (K : Nat) :
    ∀ ids : List Nat,
      ∃ tail, boundedEdgeLabellings K ids = zeroEdgeLabelling :: tail
  | [] => ⟨[], rfl⟩
  | edge :: rest => by
      obtain ⟨restTail, hrest⟩ :=
        boundedEdgeLabellings_starts_vacuum K rest
      refine ⟨
        restTail.map (fun label => setEdgeLabel label edge 0) ++
          ((List.range K).map Nat.succ).flatMap (fun spin =>
            (zeroEdgeLabelling :: restTail).map
              (fun label => setEdgeLabel label edge spin)), ?_⟩
      unfold boundedEdgeLabellings
      rw [range_succ_shift_local, List.flatMap_cons, hrest]
      simp only [List.map]
      rw [setEdgeLabel_zero_zero]
      rfl

/-- Filtering to positive rows retains the leading vacuum because its exact
physical row marginal is strictly positive. -/
theorem centralPositiveHalfStates_starts_vacuum
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    ∃ tail,
      centralPositiveHalfStates w hw K half =
        zeroEdgeLabelling :: tail := by
  obtain ⟨tail, hstates⟩ :=
    boundedEdgeLabellings_starts_vacuum K (centralLowerFaceIds half)
  unfold centralPositiveHalfStates centralHalfStates
  rw [hstates]
  simp only [List.filter_cons]
  have hvacuum := centralPhysicalRowMarginal_vacuum_pos hw K half
  simp only [hvacuum, decide_true, if_true]
  exact ⟨tail.filter (fun source =>
    decide ((0 : Q') < centralPhysicalRowMarginal w hw K half source)), rfl⟩

theorem finiteListStateAt_exists_of_mem {State : Type}
    (fallback : State) (state : State) : ∀ {states : List State},
    state ∈ states →
      ∃ index, index < states.length ∧
        finiteListStateAt states fallback index = state
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst state
        exact ⟨0, by simp, rfl⟩
      · obtain ⟨index, hindex, hget⟩ :=
          finiteListStateAt_exists_of_mem fallback state htail
        exact ⟨index + 1, by simpa using Nat.succ_lt_succ hindex,
          by simpa [finiteListStateAt] using hget⟩

theorem centralPhysicalFiniteStateAt_zero_eq_vacuum
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPhysicalFiniteStateAt w hw K half 0 = zeroEdgeLabelling := by
  obtain ⟨tail, hstates⟩ :=
    centralPositiveHalfStates_starts_vacuum w hw K half
  unfold centralPhysicalFiniteStateAt finiteListStateAt
  rw [hstates]
  rfl

theorem centralPhysicalFiniteStateAt_mem_positive
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) {index : Nat}
    (hindex : index < centralPhysicalFiniteCarrierSize w hw K half) :
    centralPhysicalFiniteStateAt w hw K half index ∈
      centralPositiveHalfStates w hw K half := by
  unfold centralPhysicalFiniteCarrierSize at hindex
  unfold centralPhysicalFiniteStateAt finiteListStateAt
  rw [← List.getElem_eq_getD
    (l := centralPositiveHalfStates w hw K half)
    (i := index)
    (h := hindex)
    zeroEdgeLabelling]
  exact List.getElem_mem hindex

theorem centralPhysicalFiniteStateAt_exists
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈ centralPositiveHalfStates w hw K half) :
    ∃ index, index < centralPhysicalFiniteCarrierSize w hw K half ∧
      centralPhysicalFiniteStateAt w hw K half index = state := by
  exact finiteListStateAt_exists_of_mem zeroEdgeLabelling state hstate

/-! ## 2. Exact indexed support graph -/

def centralPhysicalFiniteRawKernel
    (w : Q') (hw : (0 : Q') ≤ w) (K half row column : Nat) : Q' :=
  centralPhysicalReflectedKernel w K half
    (centralPhysicalFiniteStateAt w hw K half row)
    (centralPhysicalFiniteStateAt w hw K half column)

def centralPhysicalFiniteKernelNonzeroB
    (w : Q') (hw : (0 : Q') ≤ w) (K half row column : Nat) : Bool :=
  decide (¬ centralPhysicalFiniteRawKernel w hw K half row column ≈ 0)

/-- Symmetrization makes adjacency definitionally undirected even away from
the in-range carrier, while still detecting every directed nonzero entry. -/
def centralPhysicalFiniteSupportAdjacentB
    (w : Q') (hw : (0 : Q') ≤ w) (K half row column : Nat) : Bool :=
  centralPhysicalFiniteKernelNonzeroB w hw K half row column ||
    centralPhysicalFiniteKernelNonzeroB w hw K half column row

theorem centralPhysicalFiniteSupportAdjacentB_symmetric
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    SymmetricAdj
      (centralPhysicalFiniteSupportAdjacentB w hw K half) := by
  intro left right
  unfold centralPhysicalFiniteSupportAdjacentB
  exact Bool.or_comm _ _

/-- Generic support bridge: a positive production-kernel entry between the
states represented by two finite-carrier indices produces a Boolean support
edge.  Keeping `w`, `K`, and the indices abstract prevents downstream
cutoff-specialized proofs from unfolding the full positive carrier. -/
theorem centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {row column : Nat} {source target : EdgeLabelling}
    (hrow : centralPhysicalFiniteStateAt w hw K half row = source)
    (hcolumn : centralPhysicalFiniteStateAt w hw K half column = target)
    (hpos : (0 : Q') <
      centralPhysicalReflectedKernel w K half source target) :
    centralPhysicalFiniteSupportAdjacentB
      w hw K half row column = true := by
  have hrawPos : (0 : Q') <
      centralPhysicalFiniteRawKernel w hw K half row column := by
    unfold centralPhysicalFiniteRawKernel
    cases hrow
    cases hcolumn
    exact hpos
  have hnonzero : ¬
      centralPhysicalFiniteRawKernel w hw K half row column ≈ 0 := by
    intro hzero
    exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) hrawPos
  unfold centralPhysicalFiniteSupportAdjacentB
    centralPhysicalFiniteKernelNonzeroB
  simp [hnonzero]

theorem centralPhysicalFiniteRawKernel_eqv_zero_of_adj_false
    (w : Q') (hw : (0 : Q') ≤ w) (K half row column : Nat)
    (hadj :
      centralPhysicalFiniteSupportAdjacentB
        w hw K half row column = false) :
    centralPhysicalFiniteRawKernel w hw K half row column ≈ 0 := by
  by_cases hzero :
      centralPhysicalFiniteRawKernel w hw K half row column ≈ 0
  · exact hzero
  · have hforward :
        centralPhysicalFiniteKernelNonzeroB
          w hw K half row column = true := by
      unfold centralPhysicalFiniteKernelNonzeroB
      simp [hzero]
    unfold centralPhysicalFiniteSupportAdjacentB at hadj
    rw [hforward] at hadj
    cases hadj

/-! ## 3. The canonical vacuum component -/

def centralPhysicalFiniteIndexCarrier
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : List Nat :=
  List.range (centralPhysicalFiniteCarrierSize w hw K half)

/-- The canonical finite vacuum/superselection sector: the connected
component of index zero, which is the literal all-zero labelling. -/
def centralPhysicalFiniteVacuumSectorIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : List Nat :=
  rootComponent
    (centralPhysicalFiniteSupportAdjacentB w hw K half)
    (centralPhysicalFiniteIndexCarrier w hw K half) 0

/-- Literal physical half states in the canonical vacuum component. -/
def centralPhysicalFiniteVacuumSectorStates
  (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    List EdgeLabelling :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K half).map
    (centralPhysicalFiniteStateAt w hw K half)

/-- Generic introduction rule for the state-level vacuum component.  It keeps
cutoff-specialized consumers from unfolding the concrete component list. -/
theorem centralPhysicalFiniteVacuumSectorState_mem_of_index
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {index : Nat} {state : EdgeLabelling}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hstate : centralPhysicalFiniteStateAt w hw K half index = state) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorStates
  exact List.mem_map.mpr ⟨index, hindex, hstate⟩

theorem zero_mem_centralPhysicalFiniteIndexCarrier
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    0 ∈ centralPhysicalFiniteIndexCarrier w hw K half := by
  unfold centralPhysicalFiniteIndexCarrier centralPhysicalFiniteCarrierSize
  apply List.mem_range.mpr
  exact List.length_pos_of_mem
    (by
      obtain ⟨tail, hstates⟩ :=
        centralPositiveHalfStates_starts_vacuum w hw K half
      rw [hstates]
      exact List.mem_cons_self)

theorem zero_mem_centralPhysicalFiniteVacuumSectorIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    0 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K half := by
  exact root_mem_rootComponent _
    (zero_mem_centralPhysicalFiniteIndexCarrier w hw K half)

/-- Generic two-edge introduction rule for the canonical vacuum component.
If the root is adjacent to a hub and the hub is adjacent to a represented
state, then that state belongs to the state-level vacuum component. -/
theorem centralPhysicalFiniteVacuumSectorState_mem_of_two_edges
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {hubIndex stateIndex : Nat} {state : EdgeLabelling}
    (hhubIndex : hubIndex < centralPhysicalFiniteCarrierSize w hw K half)
    (hstateIndex : stateIndex < centralPhysicalFiniteCarrierSize w hw K half)
    (hrootHub : centralPhysicalFiniteSupportAdjacentB
      w hw K half 0 hubIndex = true)
    (hhubState : centralPhysicalFiniteSupportAdjacentB
      w hw K half hubIndex stateIndex = true)
    (hstate : centralPhysicalFiniteStateAt w hw K half stateIndex = state) :
    state ∈ centralPhysicalFiniteVacuumSectorStates w hw K half := by
  have hzeroVertex := zero_mem_centralPhysicalFiniteIndexCarrier
    w hw K half
  have hzeroSector := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w hw K half
  have hhubVertex : hubIndex ∈
      centralPhysicalFiniteIndexCarrier w hw K half :=
    List.mem_range.mpr hhubIndex
  have hstateVertex : stateIndex ∈
      centralPhysicalFiniteIndexCarrier w hw K half :=
    List.mem_range.mpr hstateIndex
  have hhubSector : hubIndex ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB w hw K half)
      (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K half)
      hzeroVertex hzeroSector hhubVertex hrootHub
  have hstateSector : stateIndex ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB w hw K half)
      (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K half)
      hzeroVertex hhubSector hstateVertex hhubState
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index
    w hw K half hstateSector hstate

theorem zeroEdgeLabelling_mem_centralPhysicalFiniteVacuumSectorStates
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    zeroEdgeLabelling ∈
      centralPhysicalFiniteVacuumSectorStates w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorStates
  apply List.mem_map.mpr
  exact ⟨0,
    zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half,
    centralPhysicalFiniteStateAt_zero_eq_vacuum w hw K half⟩

theorem centralPhysicalFiniteVacuumSectorIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (centralPhysicalFiniteVacuumSectorIndices w hw K half).Nodup :=
  rootComponent_nodup _ _ _

theorem centralPhysicalFiniteVacuumSectorIndex_lt
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    index < centralPhysicalFiniteCarrierSize w hw K half := by
  exact List.mem_range.mp
    (rootComponent_subset _
      (zero_mem_centralPhysicalFiniteIndexCarrier w hw K half) hindex)

theorem centralPhysicalFiniteVacuumSectorState_mem_positive
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorStates w hw K half) :
    state ∈ centralPositiveHalfStates w hw K half := by
  rcases List.mem_map.mp hstate with ⟨index, hindex, heq⟩
  rw [← heq]
  exact centralPhysicalFiniteStateAt_mem_positive w hw K half
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w hw K half hindex)

theorem centralPhysicalFiniteVacuumSectorState_mem_halfStates
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorStates w hw K half) :
    state ∈ centralHalfStates K half :=
  (mem_centralPositiveHalfStates_iff.mp
    (centralPhysicalFiniteVacuumSectorState_mem_positive
      w hw K half hstate)).1

def centralPhysicalFiniteVacuumSector_connected
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    InternallyConnected
      (centralPhysicalFiniteSupportAdjacentB w hw K half)
      (centralPhysicalFiniteVacuumSectorIndices w hw K half) :=
  rootComponent_connected _
    (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K half)
    (zero_mem_centralPhysicalFiniteIndexCarrier w hw K half)

/-- Exact row closure of the canonical physical vacuum component inside the
genuine positive-row Markov carrier. -/
theorem centralPhysicalFiniteVacuumSector_rowClosed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (htarget : target < centralPhysicalFiniteCarrierSize w hw K half)
    (houtside : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    centralPhysicalFiniteRawKernel w hw K half source target ≈ 0 := by
  have hadj := rootComponent_adj_false_of_not_mem
    (centralPhysicalFiniteSupportAdjacentB w hw K half)
    (centralPhysicalFiniteSupportAdjacentB_symmetric w hw K half)
    (zero_mem_centralPhysicalFiniteIndexCarrier w hw K half)
    hsource (List.mem_range.mpr htarget) houtside
  exact centralPhysicalFiniteRawKernel_eqv_zero_of_adj_false
    w hw K half source target hadj

end YMGap.Continuum.BF4PhysicalFiniteVacuumSector

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteStateAt_zero_eq_vacuum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSectorState_mem_of_index
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSectorState_mem_of_two_edges
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.zero_mem_centralPhysicalFiniteVacuumSectorIndices
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.zeroEdgeLabelling_mem_centralPhysicalFiniteVacuumSectorStates
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSectorState_mem_positive
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSector_connected
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSector_rowClosed
