/-
# Spin-labelled terminal assignment for BF4 root routing

The exact root-spoke classifier turns the terminal predecessor of every
non-vacuum positive route into a computable spin label.  The final source is
the carrier index of the uniform central cube with that label, and the label
is admitted by the current cutoff.  Thus every selected routing partitions
its non-vacuum users among exactly the `K + 1` certified spin-cube terminal
bins.

Substituting this exact spoke count into the existing terminal-fanout audit
shows that any cutoff-independent simple resistance-congestion certificate
must pay the full non-vacuum carrier through only `K + 1` bins.  This is a
necessary routing condition, not a construction of the required assignment
or load bound, and it implies no spectral, continuum, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. A computable spin label for every selected terminal source -/

def centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) : Nat :=
  centralPhysicalFiniteStateAt w hw K 0
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
      routing state hstate) 0

theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin_le
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
      routing state hstate ≤ K := by
  have hterminalSector :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_sector
      routing state hstate hne
  have hterminalState :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0
          (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
            routing state hstate) ∈
        centralPhysicalFiniteVacuumSectorStates
          w (Q'.le_of_lt hw) K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) K 0 hterminalSector rfl
  have hhalf := centralPhysicalFiniteVacuumSectorState_mem_halfStates
    w (Q'.le_of_lt hw) K 0 hterminalState
  have hsound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds 0)
    (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate)) hhalf
  have hlt := hsound.1 0 (by decide : 0 ∈ centralLowerFaceIds 0)
  exact Nat.le_of_lt_succ hlt

/-- Every non-vacuum route ends at the root through the spin-cube spoke
decoded by its represented terminal state's label on face zero. -/
theorem centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_eq_spinCubeIndex
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        routing state hstate =
      centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
          routing state hstate) := by
  have hpredecessor :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_mem_predecessors
      routing state hstate hne
  obtain ⟨spin, hspin, hsource⟩ :=
    (mem_centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_iff_spinCubeIndex
      hw).mp hpredecessor
  have hterminalSpin :
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
          routing state hstate = spin := by
    unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
    rw [hsource,
      centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin]
    exact centralLowerSpinCubeState_eq_spin_on_cube spin (by decide)
  exact hsource.trans
    (congrArg (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K)
      hterminalSpin.symm)

theorem centralPhysicalFiniteStateAt_terminalSource_eq_spinCubeState
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
          routing state hstate) =
      centralLowerSpinCubeState
        (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
          routing state hstate) := by
  rw [centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_eq_spinCubeIndex
      hw routing hstate hne,
    centralPhysicalFiniteStateAt_spinCubeIndex_eq hw
      (centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin_le
        hw routing hstate hne)]

/-! ## 2. Exact terminal-bin carrier -/

theorem centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_subset_spinCubeRootIndices
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) :
    ∀ source,
      source ∈
          centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
            routing →
        source ∈ centralLowerSpinCubeRootIndices
          w (Q'.le_of_lt hw) K := by
  intro source hsource
  have hpredecessor :=
    centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_subset_predecessors
      routing source hsource
  exact (List.Perm.mem_iff
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_perm_spinCubeRootIndices
      hw K)).mp hpredecessor

theorem centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_length_le_cutoff_succ
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) :
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
      routing).length ≤ K + 1 := by
  have hlength := FiniteListBound.nodup_subset_length_le
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources routing)
    (centralLowerSpinCubeRootIndices w (Q'.le_of_lt hw) K)
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_nodup
      routing)
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_subset_spinCubeRootIndices
      hw K routing)
  rw [centralLowerSpinCubeRootIndices_length] at hlength
  exact hlength

/-! ## 3. Necessary cofinal fanout after exact classification -/

/-- Any cutoff-independent simple routing certificate must pay the complete
non-vacuum sector through exactly `K + 1` available spin-cube terminal bins. -/
theorem fixedNomeCofinal_nonzero_cardinality_le_cutoff_succ_mul_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length ≤
      Q'.ofNat (K + 1) * family.bound := by
  have hfanout :=
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.nonzero_cardinality_le_positiveRootPredecessors_mul_bound
      family K hK
  rw [centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_cutoff_succ
    hw K] at hfanout
  exact hfanout

end YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment.centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin_le
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment.centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_eq_spinCubeIndex
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment.centralPhysicalFiniteStateAt_terminalSource_eq_spinCubeState
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment.centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_length_le_cutoff_succ
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment.fixedNomeCofinal_nonzero_cardinality_le_cutoff_succ_mul_bound
