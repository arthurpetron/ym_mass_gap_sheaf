/-
# Exact excited terminal carrier for the normalized central-face routing

The repaired central-face construction assigns every non-vacuum sector state
to a positive spin cube and then loop-erases the complete path to the vacuum.
Loop erasure can change the final predecessor, so the original assignment
label alone does not classify the normalized terminal edge.

This module classifies that final edge directly.  Simplicity makes its source
non-vacuum, the generic BF4 root-spoke theorem decodes it as an admitted spin
cube, and faithfulness of the finite carrier excludes spin zero.  Consequently
all terminal sources actually used by the normalized routing lie in the exact
list of `K` excited spin cubes, improving the generic `K + 1` terminal-bin
bound for this construction to `K`.

This is a finite carrier theorem.  It does not bound the size, stationary
mass, inverse-kernel resistance, or preceding-edge load of any terminal fiber,
and therefore proves no cutoff-uniform congestion, spectral, continuum, or
Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

/-! ## 1. Spin zero is exactly the vacuum carrier index -/

theorem centralLowerSpinCubeIndex_zero
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K 0 = 0 := by
  apply centralPhysicalFiniteStateAt_injective_of_lt
    (centralLowerSpinCubeIndex_lt hw (Nat.zero_le K))
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w (Q'.le_of_lt hw) K 0
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0))
  rw [centralPhysicalFiniteStateAt_spinCubeIndex_eq hw (Nat.zero_le K),
    centralPhysicalFiniteStateAt_zero_eq_vacuum]
  funext id
  simp [centralLowerSpinCubeState, zeroEdgeLabelling]

/-! ## 2. Direct classification after loop erasure -/

theorem simplePositiveCentralFaceRouting_terminalSpin_pos
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    0 < centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
      (simplePositiveCentralFaceRouting hw K hK) state hstate := by
  have hspinNe :
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
          (simplePositiveCentralFaceRouting hw K hK) state hstate ≠ 0 := by
    intro hspinZero
    have hsource :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_eq_spinCubeIndex
        hw (simplePositiveCentralFaceRouting hw K hK) hstate hne
    rw [hspinZero, centralLowerSpinCubeIndex_zero hw K] at hsource
    exact simplePositiveCentralFaceRouting_terminalSource_ne_zero
      hw hK hstate hne hsource
  omega

/-- The final predecessor of every normalized non-vacuum route is one of the
`K` certified excited spin cubes. -/
theorem simplePositiveCentralFaceRouting_terminalSource_mem_excitedSpinCubes
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        (simplePositiveCentralFaceRouting hw K hK) state hstate ∈
      centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K := by
  let spin := centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
    (simplePositiveCentralFaceRouting hw K hK) state hstate
  have hspinPos : 0 < spin :=
    simplePositiveCentralFaceRouting_terminalSpin_pos hw hK hstate hne
  have hspinLe : spin ≤ K :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin_le
      hw (simplePositiveCentralFaceRouting hw K hK) hstate hne
  unfold centralLowerExcitedSpinCubeIndices
  apply List.mem_map.mpr
  refine ⟨spin - 1, List.mem_range.mpr (by omega), ?_⟩
  unfold centralLowerExcitedSpinCubeIndex
  rw [centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource_eq_spinCubeIndex
    hw (simplePositiveCentralFaceRouting hw K hK) hstate hne]
  congr 1
  omega

/-! ## 3. The exact used-bin carrier -/

theorem simplePositiveCentralFaceRouting_usedTerminalSources_subset_excitedSpinCubes
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K) :
    ∀ source,
      source ∈
          centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
            (simplePositiveCentralFaceRouting hw K hK) →
        source ∈ centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K := by
  intro source hsource
  unfold centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources at hsource
  obtain ⟨representative, hrepresentative, rfl⟩ :=
    List.mem_map.mp hsource
  have hnonzero := keyRepresentatives_mem_source
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
      (simplePositiveCentralFaceRouting hw K hK))
    (centralPhysicalFiniteVacuumSectorNonzeroIndices
      w (Q'.le_of_lt hw) K)
    representative hrepresentative
  have hparts :=
    mem_centralPhysicalFiniteVacuumSectorNonzeroIndices_iff.mp hnonzero
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalCode
  rw [dif_pos hparts.1]
  exact simplePositiveCentralFaceRouting_terminalSource_mem_excitedSpinCubes
    hw hK hparts.1 hparts.2

/-- The normalized repaired routing uses at most `K` terminal root spokes. -/
theorem simplePositiveCentralFaceRouting_usedTerminalSources_length_le_cutoff
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K) :
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
      (simplePositiveCentralFaceRouting hw K hK)).length ≤ K := by
  have hlength := FiniteListBound.nodup_subset_length_le
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources
      (simplePositiveCentralFaceRouting hw K hK))
    (centralLowerExcitedSpinCubeIndices w (Q'.le_of_lt hw) K)
    (centralPhysicalFiniteVacuumSectorSimpleRootUsedTerminalSources_nodup
      (simplePositiveCentralFaceRouting hw K hK))
    (simplePositiveCentralFaceRouting_usedTerminalSources_subset_excitedSpinCubes
      hw hK)
  rw [centralLowerExcitedSpinCubeIndices_length] at hlength
  exact hlength

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier.centralLowerSpinCubeIndex_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier.simplePositiveCentralFaceRouting_terminalSpin_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier.simplePositiveCentralFaceRouting_terminalSource_mem_excitedSpinCubes
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier.simplePositiveCentralFaceRouting_usedTerminalSources_subset_excitedSpinCubes
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier.simplePositiveCentralFaceRouting_usedTerminalSources_length_le_cutoff
