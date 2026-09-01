/-
# Cutoff-two obstruction to strict physical-mass descent

The generic mass-descending route compiler is sound, but its local producer
cannot exist even in the first nontrivial canonical BF4 vacuum sector.  The
table state at coordinate two has literal lower-half twice-spin mass two.
Every sector state of smaller mass is the vacuum coordinate one, while the
exact production kernel between those two coordinates vanishes by a local
fixed-interface incompatibility certificate.

Consequently neither the indexed nor the literal-state local producer can be
inhabited at cutoff two and half coupling.  This is a finite obstruction to a
particular routing ansatz, not an obstruction to positive-kernel connectivity:
the already-verified cube hub still connects the sector.  A successful
routing construction must therefore use a different well-founded rank or a
multi-edge macro-step that permits temporary physical-mass increase.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalIndexWitness
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalIndexWitness
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite mass classification below table coordinate two -/

def cutoffTwoSectorPhysicalMass (index : Nat) : Nat :=
  listNatWeight (cutoffTwoSectorLocalZeroStateAt index)
    (centralLowerFaceIds 0)

def cutoffTwoRowTwoStrictLowerMassCheck : Bool :=
  (List.range 65).all fun column =>
    decide (cutoffTwoSectorPhysicalMass column <
        cutoffTwoSectorPhysicalMass 2 → column = 1)

theorem cutoffTwoRowTwoStrictLowerMassCheck_eq_true :
    cutoffTwoRowTwoStrictLowerMassCheck = true := by
  decide

theorem cutoffTwoSectorPhysicalMass_two :
    cutoffTwoSectorPhysicalMass 2 = 2 := by
  decide

theorem cutoffTwoSectorPhysicalMass_zeroEdgeLabelling :
    listNatWeight zeroEdgeLabelling (centralLowerFaceIds 0) = 0 := by
  decide

theorem cutoffTwo_strictly_lower_than_row_two_column_eq_one
    {column : Nat} (hcolumn : column < 65)
    (hmass : cutoffTwoSectorPhysicalMass column <
      cutoffTwoSectorPhysicalMass 2) :
    column = 1 := by
  have hentry := List.all_eq_true.mp
    cutoffTwoRowTwoStrictLowerMassCheck_eq_true
      column (List.mem_range.mpr hcolumn)
  exact (of_decide_eq_true hentry) hmass

/-! ## 2. The only lower-mass target has zero production kernel -/

theorem cutoffTwo_row_two_vacuum_normalizedKernel_eqv_zero :
    centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        (cutoffTwoSectorLocalZeroStateAt 2)
        (cutoffTwoSectorLocalZeroStateAt 1) ≈ 0 := by
  have hrawForward :
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          (cutoffTwoSectorLocalZeroStateAt 1)
          (cutoffTwoSectorLocalZeroStateAt 2) ≈ 0 := by
    apply centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_zero_of_local_check
    · exact cutoffTwoSectorLocalZeroStateAt_mem (by omega)
    · exact cutoffTwoSectorLocalZeroStateAt_mem (by omega)
    · simpa only [cutoffTwoSectorIndexPairLocalZeroCheck] using
        cutoffTwoSectorIndexPairLocalZeroCheck_one_two
  have hraw :
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          (cutoffTwoSectorLocalZeroStateAt 2)
          (cutoffTwoSectorLocalZeroStateAt 1) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
        (cutoffTwoCubeSectorState_mem_halfStates
          (cutoffTwoSectorLocalZeroStateAt_mem (by omega)))
        (cutoffTwoCubeSectorState_mem_halfStates
          (cutoffTwoSectorLocalZeroStateAt_mem (by omega))))
      hrawForward
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (slabParametricKPhysicalPartition cutoffTwoHalfCoupling 2
        (centralExtent 0))
      (slabParametricKPhysicalPartition_pos
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2
        (centralExtent 0))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hraw
  · exact Q'.zero_mul_eqv _

/-! ## 3. No strict physical-mass local producer exists -/

theorem no_cutoffTwo_positiveMassDescendingRootStepAt :
    ¬ Nonempty
      (CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
        cutoffTwoHalfCoupling (by decide) 2) := by
  intro hstep
  rcases hstep with ⟨step⟩
  obtain ⟨source, hsourceMem, hsourceAt⟩ :=
    exists_canonical_index_for_cutoffTwo_table_state
      (row := 2) (by omega)
  have hsourceNonzero : source ≠ 0 := by
    intro hsourceZero
    subst source
    have hstateEq : cutoffTwoSectorLocalZeroStateAt 2 =
        zeroEdgeLabelling := by
      rw [← hsourceAt]
      exact centralPhysicalFiniteStateAt_zero_eq_vacuum
        cutoffTwoHalfCoupling (by decide) 2 0
    have hmassEq := congrArg
      (fun state => listNatWeight state (centralLowerFaceIds 0)) hstateEq
    change listNatWeight (cutoffTwoSectorLocalZeroStateAt 2)
        (centralLowerFaceIds 0) =
      listNatWeight zeroEdgeLabelling (centralLowerFaceIds 0) at hmassEq
    rw [show listNatWeight (cutoffTwoSectorLocalZeroStateAt 2)
        (centralLowerFaceIds 0) = 2 by
          exact cutoffTwoSectorPhysicalMass_two,
      cutoffTwoSectorPhysicalMass_zeroEdgeLabelling] at hmassEq
    omega
  let target := step.next source hsourceMem hsourceNonzero
  have htargetMem := step.next_mem source hsourceMem hsourceNonzero
  have htargetSector : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 target ∈ cutoffTwoCubeSectorStates := by
    apply (centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _).mp
    unfold centralPhysicalFiniteVacuumSectorStates
    exact List.mem_map.mpr ⟨target, htargetMem, rfl⟩
  obtain ⟨column, hcolumn, hcolumnAt⟩ :=
    cutoffTwoCubeSectorState_exists_tableIndex htargetSector
  have hmass := step.physicalMass_lt source hsourceMem hsourceNonzero
  have hmassColumn : cutoffTwoSectorPhysicalMass column <
      cutoffTwoSectorPhysicalMass 2 := by
    unfold centralPhysicalFiniteVacuumSectorStatePhysicalMass
      centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass at hmass
    rw [hsourceAt, ← hcolumnAt] at hmass
    simpa only [cutoffTwoSectorPhysicalMass,
      cutoffTwoSectorLocalZeroStateAt, cutoffTwoSectorStateAt] using hmass
  have hcolumnOne :=
    cutoffTwo_strictly_lower_than_row_two_column_eq_one
      hcolumn hmassColumn
  have hpos := step.kernel_pos source hsourceMem hsourceNonzero
  unfold centralPhysicalFiniteKernel at hpos
  rw [hsourceAt, ← hcolumnAt, hcolumnOne] at hpos
  have hzero := cutoffTwo_row_two_vacuum_normalizedKernel_eqv_zero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) hpos

theorem no_cutoffTwo_physicalStateMassDescendingRootStepAt :
    ¬ Nonempty
      (CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
        cutoffTwoHalfCoupling (by decide) 2) := by
  intro hstep
  rcases hstep with ⟨step⟩
  exact no_cutoffTwo_positiveMassDescendingRootStepAt
    ⟨step.toPositiveMassDescendingRootStepAt⟩

end YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction.cutoffTwo_strictly_lower_than_row_two_column_eq_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction.cutoffTwo_row_two_vacuum_normalizedKernel_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction.no_cutoffTwo_positiveMassDescendingRootStepAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction.no_cutoffTwo_physicalStateMassDescendingRootStepAt
