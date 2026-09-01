/-
# Non-vacuum central-face terminal assignment for BF4 root routing

The literal central-face assignment sends a state whose face-zero spin is
zero to the spin-zero cube, which is the vacuum itself.  Appending the
classified spin-zero vacuum spoke then creates a terminal self-loop.  This
module removes that defect at every positive cutoff: zero-labelled sources
are assigned to spin one, while positive admitted face-zero labels retain
their own spin.

The selected terminal spin is always in `1,...,K`; consequently the compiled
root path ends through a genuinely non-vacuum spin-cube predecessor.  Prefixes
remain the canonical loop-erased positive-sector paths.  It is not proved here
that such a prefix avoids the vacuum internally, nor that its edge sharing or
resistance load is cutoff-uniform.  No spectral, continuum, or Clay conclusion
is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

/-! ## 1. A totalized positive admitted spin -/

/-- Keep an admitted positive label; replace zero or an out-of-range label by
spin one.  The latter branch totalizes the function outside the finite
carrier. -/
def positiveCentralFaceTerminalSpin (K raw : Nat) : Nat :=
  if raw = 0 then 1 else if raw ≤ K then raw else 1

theorem positiveCentralFaceTerminalSpin_le
    {K raw : Nat} (hK : 1 ≤ K) :
    positiveCentralFaceTerminalSpin K raw ≤ K := by
  unfold positiveCentralFaceTerminalSpin
  by_cases hzero : raw = 0
  · rw [if_pos hzero]
    exact hK
  · rw [if_neg hzero]
    by_cases hle : raw ≤ K
    · rw [if_pos hle]
      exact hle
    · rw [if_neg hle]
      exact hK

theorem positiveCentralFaceTerminalSpin_pos
    {K raw : Nat} :
    0 < positiveCentralFaceTerminalSpin K raw := by
  unfold positiveCentralFaceTerminalSpin
  by_cases hzero : raw = 0
  · rw [if_pos hzero]
    decide
  · rw [if_neg hzero]
    by_cases hle : raw ≤ K
    · rw [if_pos hle]
      omega
    · rw [if_neg hle]
      decide

/-! ## 2. The repaired finite assignment -/

def positiveCentralFaceSpinTerminalPrefixAssignment
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) :
    CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
      w hw K :=
  fun state =>
    let spin := positiveCentralFaceTerminalSpin K
      (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0)
    ⟨{
      spin := spin
      spin_le := positiveCentralFaceTerminalSpin_le hK
    }, fun hstate _hne =>
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        w (Q'.le_of_lt hw) K 0 state
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)
        hstate
        (centralLowerSpinCubeIndex_mem_vacuumSector hw
          (positiveCentralFaceTerminalSpin_le hK))⟩

theorem positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K) :
    (positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).terminalSpin
        state =
      positiveCentralFaceTerminalSpin K
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) K 0 state 0) := by
  rfl

/-- On a represented sector state only the zero-label repair remains; the
out-of-range totalization branch is impossible. -/
theorem positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin_on_sector
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    (positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).terminalSpin
        state =
      if centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) K 0 state 0 = 0 then 1
      else centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) K 0 state 0 := by
  rw [positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin]
  unfold positiveCentralFaceTerminalSpin
  by_cases hzero :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state 0 = 0
  · simp only [hzero, if_pos]
  · have hle := centralPhysicalFiniteStateAt_faceZero_le_cutoff
      (hw := hw) hstate
    simp only [hzero, if_false, hle, if_true]

theorem positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin_pos
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K) :
    0 <
      (positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).terminalSpin
        state := by
  rw [positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin]
  exact positiveCentralFaceTerminalSpin_pos

/-! ## 3. The compiled terminal predecessor is genuinely non-vacuum -/

theorem centralLowerSpinCubeIndex_ne_zero_of_pos
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hspin : spin ≤ K) (hspinPos : 0 < spin) :
    centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin ≠ 0 := by
  intro hindex
  have hstate := centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin
  rw [hindex, centralPhysicalFiniteStateAt_zero_eq_vacuum] at hstate
  have hface : (0 : Nat) = spin := by
    calc
      0 = zeroEdgeLabelling 0 := rfl
      _ = centralLowerSpinCubeState spin 0 := congrFun hstate 0
      _ = spin := centralLowerSpinCubeState_eq_spin_on_cube spin (by decide)
  omega

theorem positiveCentralFaceSpinRouting_terminalSource
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting state hstate =
      centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (positiveCentralFaceTerminalSpin K
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) K 0 state 0)) := by
  rw [toPositiveRouting_terminalSource
    (positiveCentralFaceSpinTerminalPrefixAssignment hw K hK)
      hstate hne,
    positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin]

/-- The terminal edge of every compiled non-vacuum root route is not a
vacuum self-loop. -/
theorem positiveCentralFaceSpinRouting_terminalSource_ne_zero
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting state hstate ≠ 0 := by
  rw [positiveCentralFaceSpinRouting_terminalSource hw hK hstate hne]
  exact centralLowerSpinCubeIndex_ne_zero_of_pos hw
    (positiveCentralFaceTerminalSpin_le hK)
    positiveCentralFaceTerminalSpin_pos

/-! ## 4. No-loss loop erasure produces a genuinely simple root routing -/

/-- Every edge of a vertex-simple positive chain has distinct endpoints. -/
theorem positiveKernelChain_directedEdge_ne_of_vertices_nodup
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      (PositiveKernelChainIn.vertices path).Nodup →
      ∀ edge, edge ∈ PositiveKernelChainIn.directedEdges path →
        edge.1 ≠ edge.2
  | _, _, PositiveKernelChainIn.refl _, _hnodup, edge, hedge => by
      exact False.elim (List.not_mem_nil hedge)
  | first, _, PositiveKernelChainIn.step (next := next) _ _ rest,
      hnodup, edge, hedge => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hedge with hhead | htail
      · rw [hhead]
        intro heq
        have hnext : next ∈ PositiveKernelChainIn.vertices rest := by
          cases rest <;> exact List.mem_cons_self
        apply hparts.1
        change first = next at heq
        rw [heq]
        exact hnext
      · exact positiveKernelChain_directedEdge_ne_of_vertices_nodup
          rest hparts.2 edge htail

/-- On a nontrivial vertex-simple path, the source of the final edge differs
from the endpoint. -/
theorem positiveKernelChain_terminalSource_ne_last_of_vertices_nodup
    {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State}
    (path : PositiveKernelChainIn kernel support first last)
    (hne : first ≠ last)
    (hnodup : (PositiveKernelChainIn.vertices path).Nodup) :
    PositiveKernelChainIn.terminalSource path ≠ last :=
  positiveKernelChain_directedEdge_ne_of_vertices_nodup
    path hnodup (PositiveKernelChainIn.terminalSource path, last)
    (PositiveKernelChainIn.terminalSource_mem_directedEdges path hne)

/-- Normalize the repaired central-face routing.  Loop erasure cannot increase
any exact routed resistance load by the existing generic theorem. -/
def simplePositiveCentralFaceRouting
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K :=
  loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
    (positiveCentralFaceSpinTerminalPrefixAssignment hw K hK).toPositiveRouting

theorem simplePositiveCentralFaceRouting_path_vertices_nodup
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    (PositiveKernelChainIn.vertices
      ((simplePositiveCentralFaceRouting hw K hK).path
        left right hleft hright)).Nodup :=
  loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_vertices_nodup
    (positiveCentralFaceSpinTerminalPrefixAssignment
      hw K hK).toPositiveRouting hleft hright

/-- Even if the selected prefix first reaches the vacuum internally, loop
erasure yields a vertex-simple root route whose final predecessor is still
genuinely non-vacuum. -/
theorem simplePositiveCentralFaceRouting_terminalSource_ne_zero
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (simplePositiveCentralFaceRouting hw K hK) state hstate ≠ 0 := by
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
  apply positiveKernelChain_terminalSource_ne_last_of_vertices_nodup
    ((simplePositiveCentralFaceRouting hw K hK).path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)) hne
  exact simplePositiveCentralFaceRouting_path_vertices_nodup
    hw hK state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveCentralFaceTerminalSpin_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveCentralFaceTerminalSpin_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveCentralFaceSpinTerminalPrefixAssignment_terminalSpin_on_sector
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.centralLowerSpinCubeIndex_ne_zero_of_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveCentralFaceSpinRouting_terminalSource
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveCentralFaceSpinRouting_terminalSource_ne_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveKernelChain_directedEdge_ne_of_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.positiveKernelChain_terminalSource_ne_last_of_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.simplePositiveCentralFaceRouting_path_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment.simplePositiveCentralFaceRouting_terminalSource_ne_zero
