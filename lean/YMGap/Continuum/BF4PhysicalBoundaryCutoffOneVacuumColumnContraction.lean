/-
# Exact two-term contraction of the cutoff-one vacuum column

The preceding support and annihilation theorems show that the genuine
source-to-vacuum half amplitude is supported only at the vacuum source and
the central lower cube.  This file performs the finite source sum over the
actual retained positive carrier.  A faithful mixed-radix state code supplies
constructive Dirac kernels, so the sum is evaluated without decidable
equality on function-valued labellings.

For positive coupling the exact result is

  columnMass(vacuum) = 1 + (coeffW w 1)^6.

This is a finite `K = 1`, half-extent-zero identity.  It does not provide a
cutoff-uniform, volume-uniform, or continuum estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Faithful source Dirac kernels -/

/-- Code-based Dirac mass on the cutoff-one lower-half carrier. -/
def cutoffOneSourceCodeDelta
    (source selected : EdgeLabelling) : Q' :=
  if bf4StateCode 1 0 source = bf4StateCode 1 0 selected then 1 else 0

theorem cutoffOne_vacuum_cube_code_ne :
    bf4StateCode 1 0 zeroEdgeLabelling ≠
      bf4StateCode 1 0 centralLowerCubeState := by
  decide

private theorem listQSum_sourceCodeDelta_zero_of_not_mem
    {w : Q'} (hw : (0 : Q') ≤ w)
    (selected : EdgeLabelling)
    (hselected : selected ∈ centralPositiveHalfStates w hw 1 0)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items →
        item ∈ centralPositiveHalfStates w hw 1 0) →
      selected ∉ items →
      listQSum
          (fun item => cutoffOneSourceCodeDelta item selected * value item)
          items ≈
        0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hcarrier, hnot => by
      have hhead := hcarrier head List.mem_cons_self
      have htail :
          ∀ item, item ∈ tail →
            item ∈ centralPositiveHalfStates w hw 1 0 :=
        fun item hitem =>
          hcarrier item (List.mem_cons_of_mem head hitem)
      have hselectedTail : selected ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hcode :
          bf4StateCode 1 0 head ≠ bf4StateCode 1 0 selected := by
        intro heq
        have hsame :=
          bf4StateCode_injective_on_positive hhead hselected heq
        subst head
        exact hnot List.mem_cons_self
      simp only [listQSum, cutoffOneSourceCodeDelta, if_neg hcode]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv (value head))
          (listQSum_sourceCodeDelta_zero_of_not_mem
            hw selected hselected value tail htail hselectedTail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_sourceCodeDelta_of_mem_nodup
    {w : Q'} (hw : (0 : Q') ≤ w)
    (selected : EdgeLabelling)
    (hselected : selected ∈ centralPositiveHalfStates w hw 1 0)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items →
        item ∈ centralPositiveHalfStates w hw 1 0) →
      items.Nodup →
      selected ∈ items →
      listQSum
          (fun item => cutoffOneSourceCodeDelta item selected * value item)
          items ≈
        value selected
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hcarrier, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, cutoffOneSourceCodeDelta, if_true]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr'
            (Q'.one_mul_eqv (value selected))
            (listQSum_sourceCodeDelta_zero_of_not_mem
              hw selected hselected value tail
              (fun item hitem =>
                hcarrier item
                  (List.mem_cons_of_mem selected hitem))
              hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' (value selected)))
      · have hheadCarrier := hcarrier head List.mem_cons_self
        have hcode :
            bf4StateCode 1 0 head ≠ bf4StateCode 1 0 selected := by
          intro heq
          have hsame :=
            bf4StateCode_injective_on_positive
              hheadCarrier hselected heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, cutoffOneSourceCodeDelta, if_neg hcode]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv (value head))
            (listQSum_sourceCodeDelta_of_mem_nodup
              hw selected hselected value tail
              (fun item hitem =>
                hcarrier item
                  (List.mem_cons_of_mem head hitem))
              hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' (value selected)))

/-- A code Dirac action evaluates any rational source function on the exact
retained cutoff-one carrier. -/
theorem cutoffOneSourceCodeDelta_action_eqv
    {w : Q'} (hw : (0 : Q') ≤ w)
    (selected : EdgeLabelling)
    (hselected : selected ∈ centralPositiveHalfStates w hw 1 0)
    (value : EdgeLabelling → Q') :
    listQSum
        (fun source =>
          cutoffOneSourceCodeDelta source selected * value source)
        (centralPositiveHalfStates w hw 1 0) ≈
      value selected := by
  exact listQSum_sourceCodeDelta_of_mem_nodup
    hw selected hselected value
    (centralPositiveHalfStates w hw 1 0)
    (fun item hitem => hitem)
    (centralPositiveHalfStates_nodup w hw 1 0)
    hselected

/-! ## 2. Pointwise two-Dirac decomposition -/

/-- On every retained source, the vacuum-column amplitude is exactly the
sum of its vacuum and cube Dirac components. -/
theorem centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_twoDirac
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0) :
    centralHalfAmplitude w 1 0 source zeroEdgeLabelling ≈
      cutoffOneSourceCodeDelta source zeroEdgeLabelling * 1 +
        cutoffOneSourceCodeDelta source centralLowerCubeState *
          (coeffW w 1) ^ 6 := by
  have hsourceHalf := (mem_centralPositiveHalfStates_iff.mp hsource).1
  have hvacuumMem := zeroEdgeLabelling_mem_centralPositiveHalfStates
    (Q'.le_of_lt hw) 1 0
  have hcubeMem := centralLowerCubeState_mem_centralPositiveHalfStates
    hw (by decide : 1 ≤ 1)
  by_cases hvacuumCode :
      bf4StateCode 1 0 source =
        bf4StateCode 1 0 zeroEdgeLabelling
  · have hsourceEq := bf4StateCode_injective_on_positive
      hsource hvacuumMem hvacuumCode
    subst source
    unfold cutoffOneSourceCodeDelta
    rw [if_pos rfl, if_neg cutoffOne_vacuum_cube_code_ne]
    refine Q'.eqv_trans _ 1 _
      (centralHalfAmplitude_cutoffOne_vacuum_vacuum_eqv_one w) ?_
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (1 + 0) _
        (Q'.add_eqv_congr'
          (Q'.one_mul_eqv 1)
          (Q'.zero_mul_eqv ((coeffW w 1) ^ 6)))
        (Q'.eqv_of_eq (Q'.add_zero' 1)))
  · by_cases hcubeCode :
        bf4StateCode 1 0 source =
          bf4StateCode 1 0 centralLowerCubeState
    · have hsourceEq := bf4StateCode_injective_on_positive
        hsource hcubeMem hcubeCode
      subst source
      unfold cutoffOneSourceCodeDelta
      rw [if_neg (Ne.symm cutoffOne_vacuum_cube_code_ne), if_pos rfl]
      refine Q'.eqv_trans _ ((coeffW w 1) ^ 6) _
        (centralHalfAmplitude_cutoffOne_cube_vacuum_eqv w) ?_
      exact Q'.eqv_symm
        (Q'.eqv_trans _ (0 + (coeffW w 1) ^ 6) _
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv 1)
            (Q'.one_mul_eqv ((coeffW w 1) ^ 6)))
          (Q'.eqv_of_eq (Q'.zero_add' ((coeffW w 1) ^ 6))))
    · have hneVacuum : source ≠ zeroEdgeLabelling := by
        intro heq
        subst source
        exact hvacuumCode rfl
      have hneCube : source ≠ centralLowerCubeState := by
        intro heq
        subst source
        exact hcubeCode rfl
      unfold cutoffOneSourceCodeDelta
      rw [if_neg hvacuumCode, if_neg hcubeCode]
      refine Q'.eqv_trans _ 0 _
        (centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_ne
          w source hsourceHalf hneVacuum hneCube) ?_
      exact Q'.eqv_symm
        (Q'.eqv_trans _ (0 + 0) _
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv 1)
            (Q'.zero_mul_eqv ((coeffW w 1) ^ 6)))
          (Q'.eqv_of_eq (Q'.zero_add' 0)))

/-! ## 3. Exact contraction of the genuine retained column -/

/-- The full genuine vacuum column on the retained positive cutoff-one
carrier contracts to precisely the vacuum and central-cube terms. -/
theorem centralBoundaryColumnMass_cutoffOne_vacuum_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    centralBoundaryColumnMass
        w (Q'.le_of_lt hw) 1 0 zeroEdgeLabelling ≈
      1 + (coeffW w 1) ^ 6 := by
  let states :=
    centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0
  let vacuumTerm : EdgeLabelling → Q' := fun source =>
    cutoffOneSourceCodeDelta source zeroEdgeLabelling * 1
  let cubeTerm : EdgeLabelling → Q' := fun source =>
    cutoffOneSourceCodeDelta source centralLowerCubeState *
      (coeffW w 1) ^ 6
  unfold centralBoundaryColumnMass
  change
    listQSum
        (fun source => centralHalfAmplitude w 1 0 source zeroEdgeLabelling)
        states ≈
      1 + (coeffW w 1) ^ 6
  refine Q'.eqv_trans _
    (listQSum (fun source => vacuumTerm source + cubeTerm source) states) _
    ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_twoDirac
      hw source hsource
  · refine Q'.eqv_trans _
      (listQSum vacuumTerm states + listQSum cubeTerm states) _
      (listQSum_add vacuumTerm cubeTerm states) ?_
    apply Q'.add_eqv_congr'
    · exact cutoffOneSourceCodeDelta_action_eqv
        (Q'.le_of_lt hw) zeroEdgeLabelling
        (zeroEdgeLabelling_mem_centralPositiveHalfStates
          (Q'.le_of_lt hw) 1 0)
        (fun _ => 1)
    · exact cutoffOneSourceCodeDelta_action_eqv
        (Q'.le_of_lt hw) centralLowerCubeState
        (centralLowerCubeState_mem_centralPositiveHalfStates
          hw (by decide : 1 ≤ 1))
        (fun _ => (coeffW w 1) ^ 6)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction.cutoffOne_vacuum_cube_code_ne
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction.cutoffOneSourceCodeDelta_action_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction.centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_twoDirac
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction.centralBoundaryColumnMass_cutoffOne_vacuum_eqv
