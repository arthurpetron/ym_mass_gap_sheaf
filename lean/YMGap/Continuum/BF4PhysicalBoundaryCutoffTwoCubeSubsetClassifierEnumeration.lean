/-
# Identification of the cutoff-two classifier with the exact 65-state list

For bounded lower-half states, the executable DFA accepts exactly the literal
65-state enumeration: the fundamental cube or one of the 64 doubled-spin
subsets.  The forward direction uses the proved DFA prefix semantics and the
support theorem for `centralHalfStates`; the reverse direction is a finite
kernel computation on the duplicate-free 65-element list.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

private theorem tailFace_getD_complete {id : Nat}
    (hid : id ∈ cutoffTwoCubeSubsetClassifierTailFaceIds) :
    ∃ index, index < 23 ∧
      cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0 = id := by
  simp only [cutoffTwoCubeSubsetClassifierTailFaceIds, List.mem_cons,
    List.not_mem_nil, or_false] at hid
  rcases hid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩
  · exact ⟨7, by decide, by decide⟩
  · exact ⟨8, by decide, by decide⟩
  · exact ⟨9, by decide, by decide⟩
  · exact ⟨10, by decide, by decide⟩
  · exact ⟨11, by decide, by decide⟩
  · exact ⟨12, by decide, by decide⟩
  · exact ⟨13, by decide, by decide⟩
  · exact ⟨14, by decide, by decide⟩
  · exact ⟨15, by decide, by decide⟩
  · exact ⟨16, by decide, by decide⟩
  · exact ⟨17, by decide, by decide⟩
  · exact ⟨18, by decide, by decide⟩
  · exact ⟨19, by decide, by decide⟩
  · exact ⟨20, by decide, by decide⟩
  · exact ⟨21, by decide, by decide⟩
  · exact ⟨22, by decide, by decide⟩

/-- Constructive membership transport from the production lower-face order
to the classifier scan order.  This avoids the classical decision procedure
for the general `List.Perm` proposition. -/
private theorem lowerFace_mem_classifierScan {id : Nat}
    (hid : id ∈ centralLowerFaceIds 0) :
    id ∈ 0 :: cutoffTwoCubeSubsetClassifierTailFaceIds := by
  have hfaces : centralLowerFaceIds 0 =
      [0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30,
       36, 37, 39, 45, 46, 48, 54, 55, 57, 63, 64, 66] := by
    decide
  rw [hfaces] at hid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
  rcases hid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cutoffTwoCubeSubsetClassifierTailFaceIds]

private theorem tail_zero_run_agrees_cube
    (state : EdgeLabelling)
    (hprefix : ∀ index, index < 23 →
      if index < 5 then
        state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 1
      else
        state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 0)
    {id : Nat} (hid : id ∈ cutoffTwoCubeSubsetClassifierTailFaceIds) :
    state id = centralLowerCubeState id := by
  obtain ⟨index, hindex, heq⟩ := tailFace_getD_complete hid
  have hvalue := hprefix index hindex
  rw [← heq]
  have hcases :
      index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨
      index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨
      index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨
      index = 16 ∨ index = 17 ∨ index = 18 ∨ index = 19 ∨
      index = 20 ∨ index = 21 ∨ index = 22 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    simpa [cutoffTwoCubeSubsetClassifierTailFaceIds,
      centralLowerCubeState, componentLabel, centralLowerCubeFaceIds]
      using hvalue

private theorem tail_one_run_cube_or_zero
    (state : EdgeLabelling)
    (hprefix : ∀ index, index < 23 →
      if index < 5 then
        state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 0 ∨
          state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 2
      else
        state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 0)
    {id : Nat} (hid : id ∈ cutoffTwoCubeSubsetClassifierTailFaceIds) :
    if id ∈ centralLowerCubeFaceIds then
      state id = 0 ∨ state id = 2
    else
      state id = 0 := by
  obtain ⟨index, hindex, heq⟩ := tailFace_getD_complete hid
  have hvalue := hprefix index hindex
  rw [← heq]
  have hcases :
      index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨
      index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨
      index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨
      index = 16 ∨ index = 17 ∨ index = 18 ∨ index = 19 ∨
      index = 20 ∨ index = 21 ∨ index = 22 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    simpa [cutoffTwoCubeSubsetClassifierTailFaceIds,
      centralLowerCubeFaceIds] using hvalue

private theorem state_eq_cube_of_terminal_zero
    (state : EdgeLabelling)
    (hstate : state ∈ centralHalfStates 2 0)
    (hterminal : cutoffTwoCubeSubsetClassifierTerminal state = 0) :
    state = centralLowerCubeState := by
  have hprefix := cutoffTwoCubeSubsetClassifierState_eq_zero_prefix
    state 23 (by
      simpa only [cutoffTwoCubeSubsetClassifierTerminal] using hterminal)
  have hsound := boundedEdgeLabellings_sound 2
    (centralLowerFaceIds 0) state (by
      simpa only [centralHalfStates] using hstate)
  funext id
  have hlowerDecision : Decidable (id ∈ centralLowerFaceIds 0) :=
    List.instDecidableMemOfLawfulBEq id (centralLowerFaceIds 0)
  cases hlowerDecision with
  | isTrue hlower =>
    have hscan : id ∈
        0 :: cutoffTwoCubeSubsetClassifierTailFaceIds :=
      lowerFace_mem_classifierScan hlower
    rcases List.mem_cons.mp hscan with hzero | htail
    · subst id
      rw [hprefix.1]
      symm
      unfold centralLowerCubeState
      exact componentLabel_eq_one_iff.mpr (by decide)
    · exact tail_zero_run_agrees_cube state hprefix.2 htail
  | isFalse hlower =>
    have hstateZero := hsound.2 id hlower
    have hnotCube : id ∉ centralLowerCubeFaceIds := by
      intro hcube
      exact hlower (centralLowerCubeFaceIds_subset_lower id hcube)
    rw [hstateZero]
    symm
    unfold centralLowerCubeState
    exact componentLabel_eq_zero_of_not_mem hnotCube

private theorem state_mem_doubled_of_terminal_one
    (state : EdgeLabelling)
    (hstate : state ∈ centralHalfStates 2 0)
    (hterminal : cutoffTwoCubeSubsetClassifierTerminal state = 1) :
    state ∈ cutoffTwoDoubledCubeSubsetStates := by
  have hsound := boundedEdgeLabellings_sound 2
    (centralLowerFaceIds 0) state (by
      simpa only [centralHalfStates] using hstate)
  have hbounded : ∀ id, state id < 3 := by
    intro id
    have hlowerDecision : Decidable (id ∈ centralLowerFaceIds 0) :=
      List.instDecidableMemOfLawfulBEq id (centralLowerFaceIds 0)
    cases hlowerDecision with
    | isTrue hlower => exact hsound.1 id hlower
    | isFalse hlower =>
      rw [hsound.2 id hlower]
      decide
  have hprefix := cutoffTwoCubeSubsetClassifierState_eq_one_prefix
    state hbounded 23 (by
      simpa only [cutoffTwoCubeSubsetClassifierTerminal] using hterminal)
  apply (mem_cutoffTwoDoubledCubeSubsetStates_iff state).mpr
  constructor
  · intro id hcube
    have hzeroDecision : Decidable (id = 0) := instDecidableEqNat id 0
    cases hzeroDecision with
    | isTrue hzero =>
      subst id
      exact hprefix.1
    | isFalse hzero =>
      have hlower := centralLowerCubeFaceIds_subset_lower id hcube
      have hscan : id ∈
          0 :: cutoffTwoCubeSubsetClassifierTailFaceIds :=
        lowerFace_mem_classifierScan hlower
      have htail := (List.mem_cons.mp hscan).resolve_left hzero
      have hvalue := tail_one_run_cube_or_zero state hprefix.2 htail
      simpa [hcube] using hvalue
  · intro id hnotCube
    have hlowerDecision : Decidable (id ∈ centralLowerFaceIds 0) :=
      List.instDecidableMemOfLawfulBEq id (centralLowerFaceIds 0)
    cases hlowerDecision with
    | isTrue hlower =>
      have hscan : id ∈
          0 :: cutoffTwoCubeSubsetClassifierTailFaceIds :=
        lowerFace_mem_classifierScan hlower
      rcases List.mem_cons.mp hscan with hzero | htail
      · subst id
        exact False.elim (hnotCube (by decide))
      · have hvalue := tail_one_run_cube_or_zero state hprefix.2 htail
        simpa [hnotCube] using hvalue
    | isFalse hlower => exact hsound.2 id hlower

/-! ## Exact language/list equivalence -/

/-- Direct finite check of the easy direction on the exact 65-state list. -/
def cutoffTwoCubeSectorClassifierCheck : Bool :=
  cutoffTwoCubeSectorStates.all fun state =>
    decide (cutoffTwoCubeSubsetClassifierTerminal state ≠ 2)

theorem cutoffTwoCubeSectorClassifier_checked :
    cutoffTwoCubeSectorClassifierCheck = true := by
  decide

theorem cutoffTwoCubeSubsetState_of_mem_sector
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    CutoffTwoCubeSubsetState state := by
  unfold CutoffTwoCubeSubsetState
  exact of_decide_eq_true
    (List.all_eq_true.mp cutoffTwoCubeSectorClassifier_checked
      state hstate)

theorem mem_cutoffTwoCubeSectorStates_of_classifier
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates 2 0)
    (hclassifier : CutoffTwoCubeSubsetState state) :
    state ∈ cutoffTwoCubeSectorStates := by
  have hsound := boundedEdgeLabellings_sound 2
    (centralLowerFaceIds 0) state (by
      simpa only [centralHalfStates] using hstate)
  have hbounded : ∀ id, state id < 3 := by
    intro id
    have hlowerDecision : Decidable (id ∈ centralLowerFaceIds 0) :=
      List.instDecidableMemOfLawfulBEq id (centralLowerFaceIds 0)
    cases hlowerDecision with
    | isTrue hlower => exact hsound.1 id hlower
    | isFalse hlower =>
      rw [hsound.2 id hlower]
      decide
  rcases cutoffTwoCubeSubsetClassifierTerminal_accept_cases
      state hbounded hclassifier with hzero | hone
  · unfold cutoffTwoCubeSectorStates
    exact List.mem_cons.mpr
      (Or.inl (state_eq_cube_of_terminal_zero state hstate hzero))
  · unfold cutoffTwoCubeSectorStates
    exact List.mem_cons.mpr
      (Or.inr (state_mem_doubled_of_terminal_one state hstate hone))

theorem cutoffTwoCubeSubsetState_iff_mem_sector
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates 2 0) :
    CutoffTwoCubeSubsetState state ↔
      state ∈ cutoffTwoCubeSectorStates := by
  constructor
  · exact mem_cutoffTwoCubeSectorStates_of_classifier hstate
  · exact cutoffTwoCubeSubsetState_of_mem_sector

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration.cutoffTwoCubeSectorClassifier_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration.cutoffTwoCubeSubsetState_iff_mem_sector
