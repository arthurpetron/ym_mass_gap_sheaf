/-
# The cutoff-one vacuum/cube block is the canonical vacuum component

One-step no-escape for the exact two-state block is proved separately.  This
module propagates that closure along every rooted support-graph chain and
proves the converse inclusion from the strictly positive vacuum-to-cube
entry.  Hence the canonical finite vacuum component has exactly the state
support `{vacuum, central cube}` at cutoff one and half-extent zero.

This is a finite-cutoff identification, not a compatible cofinal sector
family or a thermodynamic/continuum statement.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. Every canonical path remains in the two-state block -/

private theorem chain_stays_in_cutoffOneVacuumCubeBlock
    {w : Q'} (hw : (0 : Q') < w)
    {sourceIndex targetIndex : Nat}
    (chain : ChainIn
      (centralPhysicalFiniteSupportAdjacentB w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) 1 0)
      sourceIndex targetIndex)
    (hsourceIndex : sourceIndex < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw) 1 0)
    (hsource : centralPhysicalFiniteStateAt w (Q'.le_of_lt hw)
      1 0 sourceIndex ∈ cutoffOneVacuumCubePhysicalSources) :
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw)
      1 0 targetIndex ∈ cutoffOneVacuumCubePhysicalSources := by
  induction chain with
  | refl _ => exact hsource
  | @step source next target hedge hnext rest ih =>
      have hnextIndex :=
        centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw) 1 0 hnext
      have hnextBlock :=
        next_state_mem_cutoffOneVacuumCubeBlock_of_adjacent
          hw hsourceIndex hnextIndex hsource hedge
      exact ih hnextIndex hnextBlock

theorem canonicalVacuumSectorState_mem_cutoffOneVacuumCubeBlock
    {w : Q'} (hw : (0 : Q') < w)
    {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0) :
    state ∈ cutoffOneVacuumCubePhysicalSources := by
  rcases List.mem_map.mp hstate with ⟨index, hindex, hstateAt⟩
  have hzero := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) 1 0
  have hchain := centralPhysicalFiniteVacuumSector_connected
    w (Q'.le_of_lt hw) 1 0 0 index hzero hindex
  have hrootBlock :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0 0 ∈
        cutoffOneVacuumCubePhysicalSources := by
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
    exact List.mem_cons_self
  have hrootIndex := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw) 1 0 hzero
  have hfinal := chain_stays_in_cutoffOneVacuumCubeBlock
    hw hchain hrootIndex hrootBlock
  rw [hstateAt] at hfinal
  exact hfinal

/-! ## 2. The positive vacuum-to-cube entry supplies the converse -/

theorem centralPhysicalReflectedKernel_cutoffOne_vacuum_cube_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < centralPhysicalReflectedKernel
      w 1 0 zeroEdgeLabelling centralLowerCubeState := by
  have hcubePositive := centralLowerCubeState_mem_centralPositiveHalfStates
    hw (by decide : 1 ≤ 1)
  have hrow := centralPhysicalReflectedKernel_cutoffOne_vacuum_row_eqv
    hw centralLowerCubeState hcubePositive
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos
      (centralBoundaryWeight_cutoffOne_vacuum_pos hw)
      (centralHalfAmplitude_cutoffOne_cube_vacuum_pos hw))
    (Q'.ge_of_eqv hrow)

theorem centralLowerCubeState_mem_cutoffOneCanonicalVacuumSector
    {w : Q'} (hw : (0 : Q') < w) :
    centralLowerCubeState ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0 := by
  have hcubePositive := centralLowerCubeState_mem_centralPositiveHalfStates
    hw (by decide : 1 ≤ 1)
  obtain ⟨cubeIndex, hcubeIndex, hcubeState⟩ :=
    centralPhysicalFiniteStateAt_exists
      w (Q'.le_of_lt hw) 1 0 hcubePositive
  have hrootCube : centralPhysicalFiniteSupportAdjacentB
      w (Q'.le_of_lt hw) 1 0 0 cubeIndex = true :=
    centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
      w (Q'.le_of_lt hw) 1 0
      (centralPhysicalFiniteStateAt_zero_eq_vacuum
        w (Q'.le_of_lt hw) 1 0)
      hcubeState
      (centralPhysicalReflectedKernel_cutoffOne_vacuum_cube_pos hw)
  have hcubeSector : cubeIndex ∈
      centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) 1 0 :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        w (Q'.le_of_lt hw) 1 0)
      (zero_mem_centralPhysicalFiniteIndexCarrier
        w (Q'.le_of_lt hw) 1 0)
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0)
      (List.mem_range.mpr hcubeIndex)
      hrootCube
  exact centralPhysicalFiniteVacuumSectorState_mem_of_index
    w (Q'.le_of_lt hw) 1 0 hcubeSector hcubeState

/-- Exact state-support equality for the cutoff-one canonical vacuum sector. -/
theorem centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
    {w : Q'} (hw : (0 : Q') < w) (state : EdgeLabelling) :
    state ∈ centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) 1 0 ↔
      state ∈ cutoffOneVacuumCubePhysicalSources := by
  constructor
  · exact canonicalVacuumSectorState_mem_cutoffOneVacuumCubeBlock hw
  · intro hstate
    simp only [cutoffOneVacuumCubePhysicalSources,
      List.mem_cons, List.not_mem_nil, or_false] at hstate
    rcases hstate with hstate | hstate
    · subst state
      exact zeroEdgeLabelling_mem_centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) 1 0
    · subst state
      exact centralLowerCubeState_mem_cutoffOneCanonicalVacuumSector hw

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector.canonicalVacuumSectorState_mem_cutoffOneVacuumCubeBlock
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector.centralPhysicalReflectedKernel_cutoffOne_vacuum_cube_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector.centralLowerCubeState_mem_cutoffOneCanonicalVacuumSector
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector.centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
