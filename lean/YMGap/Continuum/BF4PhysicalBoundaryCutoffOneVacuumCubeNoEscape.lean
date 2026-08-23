/-
# One-step no-escape for the cutoff-one vacuum/cube block

The exact cutoff-one reflected Gram rows at the vacuum and central cube are
supported on those same two states.  This module converts that state-level
row closure into one-step closure for the symmetrized production-kernel
support graph.

This is finite cutoff one only.  It supplies neither a cofinal sector family
nor a thermodynamic or continuum limit.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-- Both exact cutoff-one rows in the vacuum/cube block vanish at every
retained target outside that block. -/
theorem centralPhysicalReflectedKernel_cutoffOne_vacuumCube_eqv_zero_of_outside
    {w : Q'} (hw : (0 : Q') < w)
    (source target : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources)
    (htarget : target ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0)
    (htargetVacuum : target ≠ zeroEdgeLabelling)
    (htargetCube : target ≠ centralLowerCubeState) :
    centralPhysicalReflectedKernel w 1 0 source target ≈ 0 := by
  have hmarkovZero :=
    cutoffOneVacuumCubePhysicalGramMarkov_eqv_zero_of_outside_block
      hw source hsource target htarget htargetVacuum htargetCube
  simp only [cutoffOneVacuumCubePhysicalSources,
    List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with hsourceVacuum | hsourceCube
  · subst source
    unfold cutoffOneVacuumCubePhysicalGramMarkov at hmarkovZero
    rw [if_neg cutoffOne_vacuum_cube_code_ne] at hmarkovZero
    unfold cutoffOneVacuumPhysicalGramMarkov at hmarkovZero
    refine Q'.eqv_trans _
      (Q'.divPos
          (centralPhysicalReflectedKernel
            w 1 0 zeroEdgeLabelling target)
          (cutoffOneVacuumPhysicalGramRowMass w hw)
          (cutoffOneVacuumPhysicalGramRowMass_pos hw) *
        cutoffOneVacuumPhysicalGramRowMass w hw) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.divPos_mul_eqv
          (centralPhysicalReflectedKernel
            w 1 0 zeroEdgeLabelling target)
          (cutoffOneVacuumPhysicalGramRowMass w hw)
          (cutoffOneVacuumPhysicalGramRowMass_pos hw))
    refine Q'.eqv_trans _
      (0 * cutoffOneVacuumPhysicalGramRowMass w hw) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hmarkovZero
    exact Q'.zero_mul_eqv _
  · subst source
    unfold cutoffOneVacuumCubePhysicalGramMarkov at hmarkovZero
    rw [if_pos rfl] at hmarkovZero
    unfold cutoffOneCubePhysicalGramMarkov at hmarkovZero
    refine Q'.eqv_trans _
      (Q'.divPos
          (centralPhysicalReflectedKernel
            w 1 0 centralLowerCubeState target)
          (cutoffOneCubePhysicalGramRowMass w hw)
          (cutoffOneCubePhysicalGramRowMass_pos hw) *
        cutoffOneCubePhysicalGramRowMass w hw) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.divPos_mul_eqv
          (centralPhysicalReflectedKernel
            w 1 0 centralLowerCubeState target)
          (cutoffOneCubePhysicalGramRowMass w hw)
          (cutoffOneCubePhysicalGramRowMass_pos hw))
    refine Q'.eqv_trans _
      (0 * cutoffOneCubePhysicalGramRowMass w hw) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hmarkovZero
    exact Q'.zero_mul_eqv _

/-- A single support-graph edge whose source is the vacuum or central cube
cannot end outside that two-state block. -/
theorem next_state_mem_cutoffOneVacuumCubeBlock_of_adjacent
    {w : Q'} (hw : (0 : Q') < w)
    {sourceIndex targetIndex : Nat}
    (hsourceIndex : sourceIndex < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw) 1 0)
    (htargetIndex : targetIndex < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw) 1 0)
    (hsource : centralPhysicalFiniteStateAt w (Q'.le_of_lt hw)
      1 0 sourceIndex ∈ cutoffOneVacuumCubePhysicalSources)
    (hadj : centralPhysicalFiniteSupportAdjacentB w (Q'.le_of_lt hw)
      1 0 sourceIndex targetIndex = true) :
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw)
      1 0 targetIndex ∈ cutoffOneVacuumCubePhysicalSources := by
  let source := centralPhysicalFiniteStateAt w (Q'.le_of_lt hw)
    1 0 sourceIndex
  let target := centralPhysicalFiniteStateAt w (Q'.le_of_lt hw)
    1 0 targetIndex
  have hsourcePositive : source ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0 :=
    centralPhysicalFiniteStateAt_mem_positive
      w (Q'.le_of_lt hw) 1 0 hsourceIndex
  have htargetPositive : target ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0 :=
    centralPhysicalFiniteStateAt_mem_positive
      w (Q'.le_of_lt hw) 1 0 htargetIndex
  have hsourceHalf : source ∈ centralHalfStates 1 0 :=
    (mem_centralPositiveHalfStates_iff.mp hsourcePositive).1
  have htargetHalf : target ∈ centralHalfStates 1 0 :=
    (mem_centralPositiveHalfStates_iff.mp htargetPositive).1
  have hvacuumPositive := zeroEdgeLabelling_mem_centralPositiveHalfStates
    (Q'.le_of_lt hw) 1 0
  have hcubePositive := centralLowerCubeState_mem_centralPositiveHalfStates
    hw (by decide : 1 ≤ 1)
  by_cases htargetVacuumCode :
      bf4StateCode 1 0 target =
        bf4StateCode 1 0 zeroEdgeLabelling
  · have htargetVacuum := bf4StateCode_injective_on_positive
      htargetPositive hvacuumPositive htargetVacuumCode
    simp only [cutoffOneVacuumCubePhysicalSources,
      List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl htargetVacuum
  · by_cases htargetCubeCode :
        bf4StateCode 1 0 target =
          bf4StateCode 1 0 centralLowerCubeState
    · simp only [cutoffOneVacuumCubePhysicalSources,
        List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr
        (bf4StateCode_injective_on_positive
          htargetPositive hcubePositive htargetCubeCode)
    · have htargetVacuum : target ≠ zeroEdgeLabelling := by
        intro htarget
        exact htargetVacuumCode
          (congrArg (bf4StateCode 1 0) htarget)
      have htargetCube : target ≠ centralLowerCubeState := by
        intro htarget
        exact htargetCubeCode
          (congrArg (bf4StateCode 1 0) htarget)
      have hforward :
          centralPhysicalReflectedKernel w 1 0 source target ≈ 0 :=
        centralPhysicalReflectedKernel_cutoffOne_vacuumCube_eqv_zero_of_outside
          hw source target hsource htargetPositive
          htargetVacuum htargetCube
      have hreverse :
          centralPhysicalReflectedKernel w 1 0 target source ≈ 0 :=
        Q'.eqv_trans _ _ _
          (centralPhysicalReflectedKernel_symm w htargetHalf hsourceHalf)
          hforward
      have hforwardRaw :
          centralPhysicalFiniteRawKernel w (Q'.le_of_lt hw)
            1 0 sourceIndex targetIndex ≈ 0 := by
        unfold centralPhysicalFiniteRawKernel
        exact hforward
      have hreverseRaw :
          centralPhysicalFiniteRawKernel w (Q'.le_of_lt hw)
            1 0 targetIndex sourceIndex ≈ 0 := by
        unfold centralPhysicalFiniteRawKernel
        exact hreverse
      have hfalse :=
        centralPhysicalFiniteSupportAdjacentB_false_of_rawKernel_eqv_zero
          w (Q'.le_of_lt hw) 1 0 sourceIndex targetIndex
          hforwardRaw hreverseRaw
      rw [hadj] at hfalse
      cases hfalse

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape.centralPhysicalReflectedKernel_cutoffOne_vacuumCube_eqv_zero_of_outside
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape.next_state_mem_cutoffOneVacuumCubeBlock_of_adjacent
