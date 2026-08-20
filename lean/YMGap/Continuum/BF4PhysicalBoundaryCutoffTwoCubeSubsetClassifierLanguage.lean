/-
# Executable language of the cutoff-two cube-subset classifier

The CSP classifier scans the six lower faces of the distinguished cube and
then the other eighteen lower-half faces.  State zero means that every cube
label seen so far is one; state one means that every cube label seen so far
is zero or two and every off-cube label seen so far is zero; state two is the
absorbing reject state.

This module defines the same deterministic run independently of the CSP
certificate.  Membership in the candidate finite sector is the constructive
statement that the terminal state is not reject.  The later physical bridge
uses the intermediate states as the auxiliary CSP assignment.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- After face zero, these are the remaining five cube coordinates followed
by the eighteen off-cube lower-half coordinates, in the exact CSP order. -/
def cutoffTwoCubeSubsetClassifierTailFaceIds : List Nat :=
  [1, 3, 9, 19, 39,
   10, 12, 18, 21, 27, 28, 30, 36, 37, 45, 46, 48, 54, 55, 57, 63, 64, 66]

theorem cutoffTwoCubeSubsetClassifierTailFaceIds_length :
    cutoffTwoCubeSubsetClassifierTailFaceIds.length = 23 := by
  decide

theorem cutoffTwoCubeSubsetClassifierFaceIds_checked :
    (0 :: cutoffTwoCubeSubsetClassifierTailFaceIds).Perm
      (centralLowerFaceIds 0) := by
  decide

theorem cutoffTwoCubeSubsetClassifierCubeFaceIds_checked :
    0 :: cutoffTwoCubeSubsetClassifierTailFaceIds.take 5 =
      centralLowerCubeFaceIds := by
  decide

/-- State after reading face zero and then the first `step` tail faces. -/
def cutoffTwoCubeSubsetClassifierState
    (state : EdgeLabelling) : Nat → Nat
  | 0 => if state 0 = 1 then 0 else 1
  | step + 1 =>
      cutoffTwoCubeSubsetClassifierNext (step < 5)
        (cutoffTwoCubeSubsetClassifierState state step)
        (state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD step 0))

/-- The terminal state after all twenty-four lower-half coordinates. -/
def cutoffTwoCubeSubsetClassifierTerminal
    (state : EdgeLabelling) : Nat :=
  cutoffTwoCubeSubsetClassifierState state 23

/-- Executable sector predicate.  A later enumeration theorem identifies
this language with the fundamental cube plus the 64 doubled-spin subsets. -/
def CutoffTwoCubeSubsetState (state : EdgeLabelling) : Prop :=
  cutoffTwoCubeSubsetClassifierTerminal state ≠ 2

private theorem cutoffTwoCubeSubsetClassifierNext_lt_three
    (cubeCoordinate : Bool) (previous label : Nat)
    (hprevious : previous < 3) :
    cutoffTwoCubeSubsetClassifierNext cubeCoordinate previous label < 3 := by
  unfold cutoffTwoCubeSubsetClassifierNext
  by_cases htwo : previous = 2
  · simp [htwo]
  · cases cubeCoordinate with
    | false =>
        by_cases hlabel : label = 0
        · simp [htwo, hlabel, hprevious]
        · simp [htwo, hlabel]
    | true =>
        by_cases hzero : previous = 0
        · by_cases hlabel : label = 1
          · simp [htwo, hzero, hlabel]
          · simp [htwo, hzero, hlabel]
        · by_cases hlabel : label = 0 ∨ label = 2
          · simp [htwo, hzero, hlabel]
          · simp [htwo, hzero, hlabel]

theorem cutoffTwoCubeSubsetClassifierState_lt_three
    (state : EdgeLabelling) : ∀ step,
    cutoffTwoCubeSubsetClassifierState state step < 3
  | 0 => by
      by_cases hlabel : state 0 = 1 <;>
        simp [cutoffTwoCubeSubsetClassifierState, hlabel]
  | step + 1 => by
      exact cutoffTwoCubeSubsetClassifierNext_lt_three
        (step < 5)
        (cutoffTwoCubeSubsetClassifierState state step)
        (state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD step 0))
        (cutoffTwoCubeSubsetClassifierState_lt_three state step)

theorem cutoffTwoCubeSubsetClassifierTerminal_lt_three
    (state : EdgeLabelling) :
    cutoffTwoCubeSubsetClassifierTerminal state < 3 := by
  exact cutoffTwoCubeSubsetClassifierState_lt_three state 23

theorem cutoffTwoCubeSubsetClassifierTerminal_eq_two_of_not_state
    {state : EdgeLabelling} (hstate : ¬ CutoffTwoCubeSubsetState state) :
    cutoffTwoCubeSubsetClassifierTerminal state = 2 := by
  unfold CutoffTwoCubeSubsetState at hstate
  exact Decidable.byContradiction fun hne => hstate hne

/-! ## Backward semantics of accepting runs -/

private theorem cutoffTwoCubeSubsetClassifierNext_eq_zero
    (cubeCoordinate : Bool) (previous label : Nat)
    (hprevious : previous < 3)
    (hzero : cutoffTwoCubeSubsetClassifierNext
      cubeCoordinate previous label = 0) :
    previous = 0 ∧
      (if cubeCoordinate then label = 1 else label = 0) := by
  unfold cutoffTwoCubeSubsetClassifierNext at hzero
  by_cases htwo : previous = 2
  · simp [htwo] at hzero
  · cases cubeCoordinate with
    | false =>
        by_cases hlabel : label = 0
        · simp [htwo, hlabel] at hzero ⊢
          exact hzero
        · simp [htwo, hlabel] at hzero
    | true =>
        by_cases hpreviousZero : previous = 0
        · by_cases hlabel : label = 1
          · simp [htwo, hpreviousZero, hlabel]
          · simp [htwo, hpreviousZero, hlabel] at hzero
        · have hpreviousOne : previous = 1 := by omega
          subst previous
          by_cases hlabel : label = 0 ∨ label = 2 <;>
            simp [htwo, hpreviousZero, hlabel] at hzero

private theorem cutoffTwoCubeSubsetClassifierNext_eq_one
    (cubeCoordinate : Bool) (previous label : Nat)
    (hprevious : previous < 3)
    (hone : cutoffTwoCubeSubsetClassifierNext
      cubeCoordinate previous label = 1) :
    previous = 1 ∧
      (if cubeCoordinate then label = 0 ∨ label = 2 else label = 0) := by
  unfold cutoffTwoCubeSubsetClassifierNext at hone
  by_cases htwo : previous = 2
  · simp [htwo] at hone
  · cases cubeCoordinate with
    | false =>
        by_cases hlabel : label = 0
        · have hpreviousOne : previous = 1 := by
            simpa [htwo, hlabel] using hone
          exact ⟨hpreviousOne, hlabel⟩
        · simp [htwo, hlabel] at hone
    | true =>
        by_cases hpreviousZero : previous = 0
        · by_cases hlabel : label = 1 <;>
            simp [htwo, hpreviousZero, hlabel] at hone
        · have hpreviousOne : previous = 1 := by omega
          subst previous
          by_cases hlabel : label = 0 ∨ label = 2
          · exact ⟨rfl, hlabel⟩
          · simp [htwo, hpreviousZero, hlabel] at hone

theorem cutoffTwoCubeSubsetClassifierState_eq_zero_prefix
    (state : EdgeLabelling) : ∀ step,
    cutoffTwoCubeSubsetClassifierState state step = 0 →
      state 0 = 1 ∧
      ∀ index, index < step →
        if index < 5 then
          state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 1
        else
          state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 0
  | 0, hzero => by
      simp only [cutoffTwoCubeSubsetClassifierState] at hzero
      split at hzero <;> simp_all
  | step + 1, hzero => by
      have hnext := cutoffTwoCubeSubsetClassifierNext_eq_zero
        (decide (step < 5))
        (cutoffTwoCubeSubsetClassifierState state step)
        (state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD step 0))
        (cutoffTwoCubeSubsetClassifierState_lt_three state step)
        (by simpa only [cutoffTwoCubeSubsetClassifierState] using hzero)
      have ih := cutoffTwoCubeSubsetClassifierState_eq_zero_prefix
        state step hnext.1
      refine ⟨ih.1, ?_⟩
      intro index hindex
      by_cases hlt : index < step
      · exact ih.2 index hlt
      · have heq : index = step := by omega
        subst index
        by_cases hcube : step < 5
        · simpa [hcube] using hnext.2
        · simpa [hcube] using hnext.2

theorem cutoffTwoCubeSubsetClassifierState_eq_one_prefix
    (state : EdgeLabelling) (hstateBounded : ∀ id, state id < 3) :
    ∀ step,
    cutoffTwoCubeSubsetClassifierState state step = 1 →
      (state 0 = 0 ∨ state 0 = 2) ∧
      ∀ index, index < step →
        if index < 5 then
          state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 0 ∨
            state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 2
        else
          state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD index 0) = 0
  | 0, hone => by
      simp only [cutoffTwoCubeSubsetClassifierState] at hone
      split at hone
      · simp_all
      · have hbound := hstateBounded 0
        constructor
        · omega
        · intro index hindex
          omega
  | step + 1, hone => by
      have hnext := cutoffTwoCubeSubsetClassifierNext_eq_one
        (decide (step < 5))
        (cutoffTwoCubeSubsetClassifierState state step)
        (state (cutoffTwoCubeSubsetClassifierTailFaceIds.getD step 0))
        (cutoffTwoCubeSubsetClassifierState_lt_three state step)
        (by simpa only [cutoffTwoCubeSubsetClassifierState] using hone)
      have ih := cutoffTwoCubeSubsetClassifierState_eq_one_prefix
        state hstateBounded step hnext.1
      refine ⟨ih.1, ?_⟩
      intro index hindex
      by_cases hlt : index < step
      · exact ih.2 index hlt
      · have heq : index = step := by omega
        subst index
        by_cases hcube : step < 5
        · simpa [hcube] using hnext.2
        · simpa [hcube] using hnext.2

theorem cutoffTwoCubeSubsetClassifierTerminal_accept_cases
    (state : EdgeLabelling) (hstateBounded : ∀ id, state id < 3)
    (haccept : CutoffTwoCubeSubsetState state) :
    cutoffTwoCubeSubsetClassifierTerminal state = 0 ∨
      cutoffTwoCubeSubsetClassifierTerminal state = 1 := by
  have hbound := cutoffTwoCubeSubsetClassifierTerminal_lt_three state
  unfold CutoffTwoCubeSubsetState at haccept
  omega

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage.cutoffTwoCubeSubsetClassifierTerminal_lt_three
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage.cutoffTwoCubeSubsetClassifierTerminal_accept_cases
