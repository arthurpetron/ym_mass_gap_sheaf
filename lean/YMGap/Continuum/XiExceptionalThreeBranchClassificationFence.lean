/-
# Three-branch exceptional classification fence

The routed path-safe branch and the two whole-component orientations do not
exhaust the exceptional source.  This file makes all three tests Boolean,
partitions the source into three exclusive covered regions plus an exact
residual, and banks the six-cycle counterexample.  The residual carries the
strictly stronger certificate needed by the next attack: both residual sides
contain a path-unsafe occurrence, and an unsafe-left occurrence has a genuine
cross conflict with the routed right side.
-/

import YMGap.Continuum.XiExceptionalMixedComponentFence
import YMGap.Continuum.XiExceptionalMixedEarAbsorption
import YMGap.Continuum.XiExceptionalRoutedExternalSplit
import YMGap.Continuum.XiExceptionalParallelComponentMismatchFence

namespace YMGap.Continuum.XiExceptionalThreeBranchClassificationFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalComponentCarrier
open YMGap.Continuum.XiExceptionalRoutedExternalSplit

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Boolean component-safety tests -/

def routedResidualPathSafeB
    (Gamma : List (Polymer L))
    (safe : Nat → Bool) (residual : OccBitVec Gamma.length) : Bool :=
  (occurrenceIndices Gamma.length).all (fun i =>
    !residual.at i || safe i)

def componentRightSafeB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  routedResidualPathSafeB Gamma
    (exceptionalPathSafe Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry)

def componentLeftSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  ∀ i, i < Gamma.length →
    (routedLeftResidual Gamma qP b1 b2 entry).at i = true →
    exceptionalPathSafe Gamma qP b1 b2 entry i = true

def componentLeftSafeB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  routedResidualPathSafeB Gamma
    (exceptionalPathSafe Gamma qP b1 b2 entry)
    (routedLeftResidual Gamma qP b1 b2 entry)

private theorem occurrenceIndices_sound : ∀ {n i : Nat},
    i ∈ occurrenceIndices n → i < n
  | 0, _, hi => by cases hi
  | n + 1, 0, _ => by omega
  | n + 1, i + 1, hi => by
      have ht : i ∈ occurrenceIndices n := by
        rcases List.mem_cons.mp hi with hzero | htail
        · cases hzero
        · obtain ⟨j, hj, hji⟩ := List.mem_map.mp htail
          injection hji with h
          subst j
          exact hj
      have := occurrenceIndices_sound ht
      omega

private theorem exists_false_of_all_false (f : a → Bool) :
    ∀ xs : List a, xs.all f = false → ∃ x, x ∈ xs ∧ f x = false
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : f x with
      | false => exact ⟨x, List.mem_cons_self, hx⟩
      | true =>
          have ht : xs.all f = false := by
            simp only [List.all_cons, hx, Bool.true_and] at h
            exact h
          obtain ⟨y, hy, hfy⟩ := exists_false_of_all_false f xs ht
          exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩

theorem routedResidualPathSafeB_true
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (residual : OccBitVec Gamma.length)
    (hcheck : routedResidualPathSafeB Gamma safe residual = true) :
    ∀ i, i < Gamma.length → residual.at i = true → safe i = true := by
  intro i hi hres
  have hall := List.all_eq_true.mp hcheck i (occurrenceIndices_complete hi)
  cases hs : safe i <;> simp_all [routedResidualPathSafeB]

theorem routedResidualPathSafeB_false
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (residual : OccBitVec Gamma.length)
    (hcheck : routedResidualPathSafeB Gamma safe residual = false) :
    ∃ i, i < Gamma.length ∧ residual.at i = true ∧ safe i = false := by
  unfold routedResidualPathSafeB at hcheck
  obtain ⟨i, himem, hfalse⟩ := exists_false_of_all_false _ _ hcheck
  have hi : i < Gamma.length := occurrenceIndices_sound himem
  refine ⟨i, hi, ?_, ?_⟩
  · cases hr : residual.at i <;> cases hs : safe i <;> simp_all
  · cases hr : residual.at i <;> cases hs : safe i <;> simp_all

theorem componentRightSafeB_true
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hsafe : componentRightSafeB Gamma qP b1 b2 entry = true) :
    componentRightSafe Gamma qP b1 b2 entry := by
  simpa [componentRightSafeB, componentRightSafe, routedRightResidual] using
    routedResidualPathSafeB_true Gamma
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedRightResidual Gamma qP b1 b2 entry) hsafe

theorem componentLeftSafeB_true
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hsafe : componentLeftSafeB Gamma qP b1 b2 entry = true) :
    componentLeftSafe Gamma qP b1 b2 entry := by
  exact routedResidualPathSafeB_true Gamma
    (exceptionalPathSafe Gamma qP b1 b2 entry)
    (routedLeftResidual Gamma qP b1 b2 entry) hsafe

/-! ## Exclusive source partition -/

def threeBranchCoveredB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  routedExternalCompatibleB Gamma qP b1 b2 entry ||
    componentRightSafeB Gamma qP b1 b2 entry ||
      componentLeftSafeB Gamma qP b1 b2 entry

def routedPathSafeBranchSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (routedExternalCompatibleB Gamma qP b1 b2)

def afterRoutedPathSafeSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (fun entry => !(routedExternalCompatibleB Gamma qP b1 b2 entry))

def componentRightOnlySource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (afterRoutedPathSafeSource Gamma qP b1 b2).filter
    (componentRightSafeB Gamma qP b1 b2)

def afterComponentRightSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (afterRoutedPathSafeSource Gamma qP b1 b2).filter
    (fun entry => !(componentRightSafeB Gamma qP b1 b2 entry))

def componentLeftOnlySource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (afterComponentRightSource Gamma qP b1 b2).filter
    (componentLeftSafeB Gamma qP b1 b2)

def threeBranchResidualSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (afterComponentRightSource Gamma qP b1 b2).filter
    (fun entry => !(componentLeftSafeB Gamma qP b1 b2 entry))

/-- The nested filters allocate every source occurrence exactly once. -/
theorem exceptionalSource_threeBranch_residual_partition
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≈
      qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (routedPathSafeBranchSource Gamma qP b1 b2) +
        (qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
            entry.1) (componentRightOnlySource Gamma qP b1 b2) +
          (qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
              entry.1) (componentLeftOnlySource Gamma qP b1 b2) +
            qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
              entry.1) (threeBranchResidualSource Gamma qP b1 b2))) := by
  let weight := fun entry : ExceptionalSourceEntry Gamma qP b1 b2 =>
    occurrencePairWeight w qP b1 b2 Gamma label entry.1
  have hpath := qListSum_filter_partition weight
    (routedExternalCompatibleB Gamma qP b1 b2)
    (fullExceptionalSource Gamma qP b1 b2)
  have hright := qListSum_filter_partition weight
    (componentRightSafeB Gamma qP b1 b2)
    (afterRoutedPathSafeSource Gamma qP b1 b2)
  have hleft := qListSum_filter_partition weight
    (componentLeftSafeB Gamma qP b1 b2)
    (afterComponentRightSource Gamma qP b1 b2)
  change qListSum weight (fullExceptionalSource Gamma qP b1 b2) ≈
    qListSum weight (routedPathSafeBranchSource Gamma qP b1 b2) +
      qListSum weight (afterRoutedPathSafeSource Gamma qP b1 b2) at hpath
  change qListSum weight (afterRoutedPathSafeSource Gamma qP b1 b2) ≈
    qListSum weight (componentRightOnlySource Gamma qP b1 b2) +
      qListSum weight (afterComponentRightSource Gamma qP b1 b2) at hright
  change qListSum weight (afterComponentRightSource Gamma qP b1 b2) ≈
    qListSum weight (componentLeftOnlySource Gamma qP b1 b2) +
      qListSum weight (threeBranchResidualSource Gamma qP b1 b2) at hleft
  have htail := Q'.eqv_trans _ _ _ hright
    (Q'.add_eqv_congr_left _ _ _ hleft)
  exact Q'.eqv_trans _ _ _ hpath
    (Q'.add_eqv_congr_left _ _ _ htail)

theorem threeBranchResidualSource_tests
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ threeBranchResidualSource Gamma qP b1 b2) :
    routedExternalCompatibleB Gamma qP b1 b2 entry = false ∧
      componentRightSafeB Gamma qP b1 b2 entry = false ∧
      componentLeftSafeB Gamma qP b1 b2 entry = false := by
  have hleft := (List.mem_filter.mp hentry).2
  have hafterRight := (List.mem_filter.mp hentry).1
  have hright := (List.mem_filter.mp hafterRight).2
  have hafterPath := (List.mem_filter.mp hafterRight).1
  have hpath := (List.mem_filter.mp hafterPath).2
  cases hp : routedExternalCompatibleB Gamma qP b1 b2 entry <;>
    cases hr : componentRightSafeB Gamma qP b1 b2 entry <;>
    cases hl : componentLeftSafeB Gamma qP b1 b2 entry <;>
    simp_all

/-! ## The exact residual invariant -/

def RoutedResidualUnsafe
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (residual : OccBitVec Gamma.length) : Prop :=
  ∃ i, i < Gamma.length ∧ residual.at i = true ∧ safe i = false

def ThreeBranchResidualInvariant
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  (∃ i, i < Gamma.length ∧
      (routedLeftResidual Gamma qP b1 b2 entry).at i = true ∧
      exceptionalPathSafe Gamma qP b1 b2 entry i = false ∧
      ∃ j, j < Gamma.length ∧
        (routedRightResidual Gamma qP b1 b2 entry).at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false) ∧
    RoutedResidualUnsafe Gamma
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedRightResidual Gamma qP b1 b2 entry) ∧
    RoutedResidualUnsafe Gamma
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedLeftResidual Gamma qP b1 b2 entry)

theorem threeBranchResidualSource_invariant
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ threeBranchResidualSource Gamma qP b1 b2) :
    ThreeBranchResidualInvariant Gamma qP b1 b2 entry := by
  obtain ⟨hpath, hright, hleft⟩ :=
    threeBranchResidualSource_tests Gamma qP b1 b2 entry hentry
  refine ⟨routedExternal_incompatible_cross_witness
      Gamma qP b1 b2 entry hpath, ?_, ?_⟩
  · exact routedResidualPathSafeB_false Gamma
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedRightResidual Gamma qP b1 b2 entry) hright
  · exact routedResidualPathSafeB_false Gamma
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedLeftResidual Gamma qP b1 b2 entry) hleft

/-! ## Four-occurrence control computation -/

namespace FourOccurrenceControl

/-- The four-occurrence star is accepted by the switched-right component
branch.  This is a closed small-`Gamma` check of the classifier before the
six-cycle refutation below. -/
theorem component_right_branch_accepts : componentRightSafeB _ _ _ _
    YMGap.Continuum.XiExceptionalParallelComponentMismatchFence.entry =
      true := by
  unfold componentRightSafeB routedResidualPathSafeB routedRightResidual
  unfold YMGap.Continuum.XiExceptionalParallelComponentMismatchFence.entry
  dsimp only
  rw [YMGap.Continuum.XiExceptionalParallelComponentMismatchFence.source_path_vertices]
  rfl

end FourOccurrenceControl

/-! ## Machine-checked six-occurrence counterexample -/

namespace SixCycle

open YMGap.Continuum.XiExceptionalMixedEarAbsorption

def entry : ExceptionalSourceEntry Gamma qAll markV0 badV3 :=
  ⟨pair, pair_mem⟩

theorem entry_eq_mixed_component_fence :
    entry = YMGap.Continuum.XiExceptionalMixedComponentFence.entry := by
  rfl

theorem entry_mem_full : entry ∈ fullExceptionalSource
    Gamma qAll markV0 badV3 := by
  exact List.mem_attach _ entry

theorem gamma_length : Gamma.length = 6 := by rfl

theorem routed_path_safe_fails :
    routedExternalCompatibleB Gamma qAll markV0 badV3 entry = false := by
  have hmixed : routedExternalCompatibleB _ _ _ _
      YMGap.Continuum.XiExceptionalMixedComponentFence.entry = false := by
    unfold routedExternalCompatibleB entryRoutedExternal
      routedLeftResidual routedRightResidual exceptionalPathSafe
    unfold YMGap.Continuum.XiExceptionalMixedComponentFence.entry
    dsimp only
    rcases
        YMGap.Continuum.XiExceptionalMixedComponentFence.source_path_is_cycle_arc
      with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  simpa [entry_eq_mixed_component_fence] using hmixed

theorem component_right_safeB_fails :
    componentRightSafeB Gamma qAll markV0 badV3 entry = false := by
  cases h : componentRightSafeB Gamma qAll markV0 badV3 entry with
  | false => rfl
  | true =>
      exact False.elim
        (YMGap.Continuum.XiExceptionalMixedComponentFence.component_right_safe_fails
          (entry_eq_mixed_component_fence ▸
            componentRightSafeB_true Gamma qAll markV0 badV3 entry h))

theorem component_left_safeB_fails :
    componentLeftSafeB Gamma qAll markV0 badV3 entry = false := by
  cases h : componentLeftSafeB Gamma qAll markV0 badV3 entry with
  | false => rfl
  | true =>
      have hsafe := componentLeftSafeB_true Gamma qAll markV0 badV3 entry h
      exact False.elim
        (YMGap.Continuum.XiExceptionalMixedComponentFence.component_left_safe_fails
          (by simpa [componentLeftSafe,
            YMGap.Continuum.XiExceptionalMixedComponentFence.componentLeftSafe,
            routedLeftResidual] using hsafe))

theorem three_branch_covered_fails :
    threeBranchCoveredB Gamma qAll markV0 badV3 entry = false := by
  simp [threeBranchCoveredB, routed_path_safe_fails,
    component_right_safeB_fails, component_left_safeB_fails]

theorem three_branch_exhaustiveness_refuted :
    ¬ ∀ e : ExceptionalSourceEntry Gamma qAll markV0 badV3,
      e ∈ fullExceptionalSource Gamma qAll markV0 badV3 →
        threeBranchCoveredB Gamma qAll markV0 badV3 e = true := by
  intro hall
  have h := hall entry entry_mem_full
  rw [three_branch_covered_fails] at h
  cases h

theorem entry_mem_residual :
    entry ∈ threeBranchResidualSource Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [component_left_safeB_fails]⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [component_right_safeB_fails]⟩
  apply List.mem_filter.mpr
  exact ⟨entry_mem_full, by simp [routed_path_safe_fails]⟩

theorem residual_invariant :
    ThreeBranchResidualInvariant Gamma qAll markV0 badV3 entry :=
  threeBranchResidualSource_invariant Gamma qAll markV0 badV3
    entry entry_mem_residual

end SixCycle

#print axioms routedResidualPathSafeB_true
#print axioms routedResidualPathSafeB_false
#print axioms componentRightSafeB_true
#print axioms componentLeftSafeB_true
#print axioms exceptionalSource_threeBranch_residual_partition
#print axioms threeBranchResidualSource_tests
#print axioms threeBranchResidualSource_invariant
#print axioms FourOccurrenceControl.component_right_branch_accepts
#print axioms SixCycle.entry_eq_mixed_component_fence
#print axioms SixCycle.routed_path_safe_fails
#print axioms SixCycle.component_right_safeB_fails
#print axioms SixCycle.component_left_safeB_fails
#print axioms SixCycle.three_branch_exhaustiveness_refuted
#print axioms SixCycle.entry_mem_residual
#print axioms SixCycle.residual_invariant

end YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
