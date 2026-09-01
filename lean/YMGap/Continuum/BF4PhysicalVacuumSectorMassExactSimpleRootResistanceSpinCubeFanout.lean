/-
# Explicit spin-cube lower bound on BF4 positive root fanout

The exact terminal-fanout obstruction asks how the non-vacuum sector compares
with the carrier of positive predecessors of the vacuum root.  The existing
arbitrary-spin BF4 ray already supplies `K` distinct non-vacuum vertices at
cutoff `K`, and each has a literal strictly positive directed edge into the
root.  This module embeds that ray into both sides of the fanout comparison.

Thus the positive root-spoke carrier grows at least linearly with the
representation cutoff.  This is constructive evidence for fanout, not an
upper bound on the full non-vacuum sector divided by the spoke count, not a
weighted resistance estimate, and not a cofinal gap or continuum result.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## 1. Every excited spin cube is a positive root predecessor -/

theorem centralLowerExcitedSpinCubeIndices_subset_positiveRootPredecessors
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    ∀ index,
      index ∈ centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K →
        index ∈
          centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
            w (Q'.le_of_lt hw) K := by
  intro index hindex
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hindex
  unfold centralLowerExcitedSpinCubeIndex
  have hoffsetBound : offset + 1 ≤ K := by
    have hlt := List.mem_range.mp hoffset
    omega
  apply List.mem_filter.mpr
  exact ⟨
    centralLowerSpinCubeIndex_mem_vacuumSector hw hoffsetBound,
    decide_eq_true
      (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos
        hw hoffsetBound)⟩

theorem centralLowerExcitedSpinCubeIndices_subset_nonzeroSector
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    ∀ index,
      index ∈ centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K →
        index ∈ centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K := by
  intro index hindex
  apply mem_centralPhysicalFiniteVacuumSectorNonzeroIndices_iff.mpr
  exact ⟨
    centralLowerExcitedSpinCubeIndices_subset_vacuumSector hw K index hindex,
    by
      obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hindex
      exact centralLowerExcitedSpinCubeIndex_ne_zero hw
        (List.mem_range.mp hoffset)⟩

/-! ## 2. Linear constructive lower bounds on both fanout carriers -/

theorem centralLowerExcitedSpinCubeIndices_length
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (centralLowerExcitedSpinCubeIndices w hw K).length = K := by
  simp [centralLowerExcitedSpinCubeIndices]

theorem cutoff_le_positiveRootPredecessors_cardinality
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    Q'.ofNat K ≤
      Q'.ofNat
        (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
          w (Q'.le_of_lt hw) K).length := by
  have hlength :
      (centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K).length ≤
        (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
          w (Q'.le_of_lt hw) K).length :=
    FiniteListBound.nodup_subset_length_le _ _
      (centralLowerExcitedSpinCubeIndices_nodup hw K)
      (centralLowerExcitedSpinCubeIndices_subset_positiveRootPredecessors
        hw K)
  rw [centralLowerExcitedSpinCubeIndices_length] at hlength
  exact Q'.ofNat_le_ofNat hlength

theorem cutoff_le_nonzeroSector_cardinality
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    Q'.ofNat K ≤
      Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length := by
  have hlength :
      (centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K).length ≤
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length :=
    FiniteListBound.nodup_subset_length_le _ _
      (centralLowerExcitedSpinCubeIndices_nodup hw K)
      (centralLowerExcitedSpinCubeIndices_subset_nonzeroSector hw K)
  rw [centralLowerExcitedSpinCubeIndices_length] at hlength
  exact Q'.ofNat_le_ofNat hlength

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout.centralLowerExcitedSpinCubeIndices_subset_positiveRootPredecessors
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout.centralLowerExcitedSpinCubeIndices_subset_nonzeroSector
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout.cutoff_le_positiveRootPredecessors_cardinality
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeFanout.cutoff_le_nonzeroSector_cardinality
