/-
# The cutoff-two cube hub inhabits the mass-amortized macro-step

The exact cutoff-two sector has a positive fundamental-cube hub.  Every
non-vacuum sector index reaches that hub and the hub reaches the vacuum, so a
two-edge positive path exists even when the direct lower-mass edge vanishes.
Every non-vacuum table state has literal twice-spin mass at least two.  Thus
the two displayed edges are paid exactly by the endpoint mass drop to the
vacuum.

This gives a constructive cutoff-two inhabitant of the mass-amortized
macro-step interface and demonstrates that it genuinely escapes the strict
edgewise descent obstruction.  It is finite cutoff-two evidence only; no
cofinal hub, uniform sharing, uniform load, continuum, or Clay conclusion is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingCutoffTwoObstruction
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

/-! ## 1. A constructive finite-carrier coordinate for the table hub -/

def cutoffTwoHubIndex : Nat :=
  centralPhysicalFiniteIndexOfState cutoffTwoHalfCoupling (by decide) 2 0
    (cutoffTwoSectorStateAt 0)

theorem cutoffTwoHubIndex_lt :
    cutoffTwoHubIndex < centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) 2 0 := by
  apply centralPhysicalFiniteIndexOfState_lt
  exact cutoffTwoCubeSectorState_mem_positive
    (cutoffTwoSectorStateAt_mem (by omega))

theorem cutoffTwoHubIndex_stateAt :
    centralPhysicalFiniteStateAt cutoffTwoHalfCoupling (by decide) 2 0
        cutoffTwoHubIndex = cutoffTwoSectorStateAt 0 := by
  exact centralPhysicalFiniteStateAt_indexOfState_eq
    (cutoffTwoCubeSectorState_mem_positive
      (cutoffTwoSectorStateAt_mem (by omega)))

theorem cutoffTwoHubIndex_mem_vacuumSector :
    cutoffTwoHubIndex ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0 := by
  have hstate : cutoffTwoSectorStateAt 0 ∈
      centralPhysicalFiniteVacuumSectorStates
        cutoffTwoHalfCoupling (by decide) 2 0 :=
    cutoffTwoCubeSectorState_mem_canonicalVacuumSector
      (cutoffTwoSectorStateAt_mem (by omega))
  unfold centralPhysicalFiniteVacuumSectorStates at hstate
  obtain ⟨prior, hpriorMem, hpriorState⟩ := List.mem_map.mp hstate
  have hpriorLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hpriorMem
  have hindexEq : cutoffTwoHubIndex = prior :=
    centralPhysicalFiniteStateAt_injective_of_lt
      cutoffTwoHubIndex_lt hpriorLt
      (cutoffTwoHubIndex_stateAt.trans hpriorState.symm)
  rw [hindexEq]
  exact hpriorMem

/-! ## 2. Positive state-hub and hub-vacuum edges -/

theorem cutoffTwo_hub_sector_normalizedKernel_pos
    {state : EdgeLabelling} (hstate : state ∈ cutoffTwoCubeSectorStates) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      cutoffTwoHalfCoupling (by decide) 2 0
      (cutoffTwoSectorStateAt 0) state := by
  obtain ⟨column, hcolumn, hcolumnAt⟩ :=
    cutoffTwoCubeSectorState_exists_tableIndex hstate
  have hraw : (0 : Q') < centralPhysicalReflectedKernel
      cutoffTwoHalfCoupling 2 0 (cutoffTwoSectorStateAt 0) state := by
    rw [← hcolumnAt]
    exact centralPhysicalReflectedKernel_cutoffTwo_stateAt_zero_sectorStateAt_pos
      hcolumn
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos hraw (Q'.recipPos_pos _ _)

theorem cutoffTwo_sector_hub_normalizedKernel_pos
    {state : EdgeLabelling} (hstate : state ∈ cutoffTwoCubeSectorStates) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      cutoffTwoHalfCoupling (by decide) 2 0
      state (cutoffTwoSectorStateAt 0) := by
  have hforward := cutoffTwo_hub_sector_normalizedKernel_pos hstate
  have hstateHalf := cutoffTwoCubeSectorState_mem_halfStates hstate
  have hhubHalf := cutoffTwoCubeSectorState_mem_halfStates
    (cutoffTwoSectorStateAt_mem (by omega : 0 < 65))
  have hsymm := centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
    hstateHalf hhubHalf
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos at hforward ⊢
  exact Q'.pos_of_lt_of_le hforward
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.ge_of_eqv hsymm)
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))

theorem cutoffTwo_source_hub_finiteKernel_pos
    {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0) :
    (0 : Q') < centralPhysicalFiniteKernel cutoffTwoHalfCoupling
      (by decide) 2 0 source cutoffTwoHubIndex := by
  have hsourceSector : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 source ∈ cutoffTwoCubeSectorStates := by
    apply (centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _).mp
    unfold centralPhysicalFiniteVacuumSectorStates
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  unfold centralPhysicalFiniteKernel
  rw [cutoffTwoHubIndex_stateAt]
  exact cutoffTwo_sector_hub_normalizedKernel_pos hsourceSector

theorem cutoffTwo_hub_root_finiteKernel_pos :
    (0 : Q') < centralPhysicalFiniteKernel cutoffTwoHalfCoupling
      (by decide) 2 0 cutoffTwoHubIndex 0 := by
  unfold centralPhysicalFiniteKernel
  rw [cutoffTwoHubIndex_stateAt,
    centralPhysicalFiniteStateAt_zero_eq_vacuum]
  exact cutoffTwo_hub_sector_normalizedKernel_pos
    zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates

/-! ## 3. The two-edge positive macro-path -/

def cutoffTwoStateHubVacuumPath
    (source : Nat)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel cutoffTwoHalfCoupling (by decide) 2 0)
      (centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0)
      source 0 :=
  PositiveKernelChainIn.step
    (cutoffTwo_source_hub_finiteKernel_pos hsource)
    cutoffTwoHubIndex_mem_vacuumSector
    (PositiveKernelChainIn.step
      cutoffTwo_hub_root_finiteKernel_pos
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0)
      (PositiveKernelChainIn.refl 0))

theorem cutoffTwoStateHubVacuumPath_edgeLength
    (source : Nat)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0) :
    PositiveKernelChainIn.edgeLength
      (cutoffTwoStateHubVacuumPath source hsource) = 2 :=
  rfl

/-! ## 4. Every non-root sector state pays the two edges -/

theorem cutoffTwoSectorStateAt_one_eq_zeroEdgeLabelling :
    cutoffTwoSectorStateAt 1 = zeroEdgeLabelling := by
  obtain ⟨tail, hstates⟩ := boundedEdgeLabellings_starts_vacuum
    1 centralLowerCubeFaceIds
  have hdouble : doubleEdgeLabelling zeroEdgeLabelling =
      zeroEdgeLabelling := by
    funext id
    simp [doubleEdgeLabelling, zeroEdgeLabelling]
  unfold cutoffTwoSectorStateAt cutoffTwoCubeSectorStates
    cutoffTwoDoubledCubeSubsetStates
  rw [hstates]
  simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
    hdouble]

def cutoffTwoNonvacuumPhysicalMassFloorCheck : Bool :=
  (List.range 65).all fun column =>
    decide (column ≠ 1 → 2 ≤ cutoffTwoSectorPhysicalMass column)

theorem cutoffTwoNonvacuumPhysicalMassFloorCheck_eq_true :
    cutoffTwoNonvacuumPhysicalMassFloorCheck = true := by
  decide

theorem cutoffTwo_nonroot_physicalMass_ge_two
    {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0)
    (hsourceNonzero : source ≠ 0) :
    2 ≤ centralPhysicalFiniteVacuumSectorStatePhysicalMass
      cutoffTwoHalfCoupling (by decide) 2 source := by
  have hsourceSector : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 source ∈ cutoffTwoCubeSectorStates := by
    apply (centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _).mp
    unfold centralPhysicalFiniteVacuumSectorStates
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  obtain ⟨column, hcolumn, hcolumnAt⟩ :=
    cutoffTwoCubeSectorState_exists_tableIndex hsourceSector
  have hcolumnNe : column ≠ 1 := by
    intro hcolumnOne
    have hsourceStateEqRoot :
        centralPhysicalFiniteStateAt cutoffTwoHalfCoupling (by decide) 2 0
            source =
          centralPhysicalFiniteStateAt cutoffTwoHalfCoupling (by decide) 2 0
            0 := by
      rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
      rw [← cutoffTwoSectorStateAt_one_eq_zeroEdgeLabelling,
        ← hcolumnOne, hcolumnAt]
    have hsourceLt := centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) 2 0 hsource
    have hrootLt := centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) 2 0
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0)
    exact hsourceNonzero
      (centralPhysicalFiniteStateAt_injective_of_lt
        hsourceLt hrootLt hsourceStateEqRoot)
  have hentry := List.all_eq_true.mp
    cutoffTwoNonvacuumPhysicalMassFloorCheck_eq_true
      column (List.mem_range.mpr hcolumn)
  have htableMass : 2 ≤ cutoffTwoSectorPhysicalMass column :=
    (of_decide_eq_true hentry) hcolumnNe
  unfold centralPhysicalFiniteVacuumSectorStatePhysicalMass
    centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
  rw [← hcolumnAt]
  simpa only [cutoffTwoSectorPhysicalMass,
    cutoffTwoSectorLocalZeroStateAt, cutoffTwoSectorStateAt] using htableMass

theorem cutoffTwo_root_physicalMass_eq_zero :
    centralPhysicalFiniteVacuumSectorStatePhysicalMass
      cutoffTwoHalfCoupling (by decide) 2 0 = 0 := by
  unfold centralPhysicalFiniteVacuumSectorStatePhysicalMass
    centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
  exact cutoffTwoSectorPhysicalMass_zeroEdgeLabelling

/-! ## 5. Cutoff-two inhabitant and compiled routing -/

def cutoffTwoMassAmortizedHubMacroStep :
    CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
      cutoffTwoHalfCoupling (by decide) 2 where
  next := fun _ _ _ => 0
  next_mem := by
    intro _ _ _
    exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0
  macroPath := by
    intro source hsource _
    exact cutoffTwoStateHubVacuumPath source hsource
  physicalMass_lt := by
    intro source hsource hsourceNonzero
    rw [cutoffTwo_root_physicalMass_eq_zero]
    have hfloor := cutoffTwo_nonroot_physicalMass_ge_two
      hsource hsourceNonzero
    omega
  macroPath_edgeLength_le_massDrop := by
    intro source hsource hsourceNonzero
    rw [cutoffTwoStateHubVacuumPath_edgeLength,
      cutoffTwo_root_physicalMass_eq_zero, Nat.sub_zero]
    exact cutoffTwo_nonroot_physicalMass_ge_two hsource hsourceNonzero

def cutoffTwoPhysicalMassAmortizedHubRootRouting :
    CentralPhysicalFiniteVacuumSectorPhysicalMassAmortizedRootRoutingAt
      cutoffTwoHalfCoupling (by decide) 2 :=
  cutoffTwoMassAmortizedHubMacroStep.toPhysicalMassAmortizedRootRoutingAt

end YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep.cutoffTwoHubIndex_mem_vacuumSector
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep.cutoffTwoStateHubVacuumPath
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep.cutoffTwo_nonroot_physicalMass_ge_two
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep.cutoffTwoMassAmortizedHubMacroStep
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCutoffTwoMassAmortizedHubMacroStep.cutoffTwoPhysicalMassAmortizedHubRootRouting
