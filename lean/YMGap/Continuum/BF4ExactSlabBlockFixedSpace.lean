/-
# Exact original block fixed spaces, at every positive nome

The original block conditional fixes a completed state exactly when all
original singleton updates in that block fix it. The proof transports only
the auxiliary Haar fixed spaces through an explicit norm equivalence; it
does not identify the raw Haar map with the interacting orthogonal map.
This supplies the same-object subsystem fixed space for collective methods,
without assuming or establishing a quantitative subsystem gap.
-/

import YMGap.Continuum.BF4ExactSlabBlockReferenceProjection
import YMGap.Continuum.BF4ExactSlabBlockTower
import YMGap.Continuum.BF4ExactSlabBlockSingletonProjection
import YMGap.Continuum.BF4ExactSlabConditionalSweep
import YMGap.Continuum.GNSProjectionGeneratorKernel

namespace YMGap.Continuum.BF4ExactSlabBlockFixedSpace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionGeneratorKernel
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletionComparison
open YMGap.Continuum.BF4ExactSlabBlockReferenceProjection
open YMGap.Continuum.BF4ExactSlabBlockTower
open YMGap.Continuum.BF4ExactSlabBlockSingletonProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (S : List Z4Link)
  (hS : ∀ link, link ∈ S → link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => backgroundData hw0 hw1 K extent hK S
local notation "W" => background w K extent S
local notation "HC" => background_certificate hw0 hw1 K extent hK S
local notation "J" => toBackground hw0 hw1 K extent hK S hS
local notation "I" => toFull hw0 hw1 K extent hK S hS
local notation "CS" => BF4ExactSlabBlockConditionalProjection.conditionalProjection
  hw0 hw1 K extent hK S hS

/-- No small-nome, distinctness, exterior boundary condition, or patch-gap
hypothesis. All operators act on the SAME full original completion. -/
theorem fixed_iff_singletons (x : GNSCompletionSpace F) :
    CS x = x ↔ ∀ link (hi : link ∈ S),
      BF4ExactSlabStarConditionalProjection.conditionalProjection
        hw0 hw1 K extent hK link (hS link hi) x = x := by
  constructor
  · intro hx link hi
    have hsub : ∀ j, j ∈ [link] → j ∈ S :=
      fun j hj => (List.mem_singleton.mp hj) ▸ hi
    have ht := tower hw0 hw1 K extent hK [link] S
      (fun j hj => (List.mem_singleton.mp hj) ▸ (hS link hi)) hS
      (slots_subset_of_links_subset extent [link] S hsub) x
    rw [hx, conditionalProjection_singleton] at ht
    exact ht
  · intro hx
    have hraw (link : Z4Link) (hi : link ∈ S) :
        reference hw0 hw1 K extent hK S [link] hS
          (fun j hj => (List.mem_singleton.mp hj) ▸ hi) x = x := by
      have hp : BF4ExactSlabBlockConditionalProjection.conditionalProjection
          hw0 hw1 K extent hK [link]
          (fun j hj => (List.mem_singleton.mp hj) ▸ (hS link hi)) x = x :=
        (conditionalProjection_singleton hw0 hw1 K extent hK link (hS link hi) x).trans
          (hx link hi)
      have hr := reference_conditional hw0 hw1 K extent hK S [link] hS
        (fun j hj => (List.mem_singleton.mp hj) ▸ hi) x
      rw [hp] at hr
      exact hr
    have hall : familyProjection (boundaryCompleteSlabLinks extent).length W HC
        (slots extent S) (slots_valid extent S hS)
        (background_independent w K extent S hS) (J x) = J x := by
      apply familyProjection_fixed_of_singletons
      intro i hi
      obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hi
      exact (background_reference_singleton hw0 hw1 K extent hK S hS
        link hlink x).symm.trans (congrArg J (hraw link hlink))
    have href : reference hw0 hw1 K extent hK S S hS (fun _ h => h) x = x := by
      change I (familyProjection (boundaryCompleteSlabLinks extent).length W HC
        (slots extent S) (slots_valid extent S hS)
        (background_independent w K extent S hS) (J x)) = x
      rw [hall]
      exact toFull_toBackground hw0 hw1 K extent hK S hS x
    have ht := conditional_reference hw0 hw1 K extent hK S S hS (fun _ h => h) x
    rw [href] at ht
    exact ht

/-- The range of the union block is the intersection of the two actual
fixed spaces. The two interacting projections need NOT commute. -/
theorem union_fixed_iff (A B : List Z4Link)
    (hA : ∀ link, link ∈ A → link ∈ boundaryCompleteSlabLinks extent)
    (hB : ∀ link, link ∈ B → link ∈ boundaryCompleteSlabLinks extent)
    (x : GNSCompletionSpace F) :
    BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK
      (A ++ B) (fun link h => (List.mem_append.mp h).elim (hA link) (hB link)) x = x ↔
    BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK A hA x = x ∧
    BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK B hB x = x := by
  rw [fixed_iff_singletons, fixed_iff_singletons, fixed_iff_singletons]
  constructor
  · intro h
    exact ⟨fun link hi => h link (List.mem_append_left B hi),
      fun link hi => h link (List.mem_append_right A hi)⟩
  · intro h link hi
    exact (List.mem_append.mp hi).elim (h.1 link) (h.2 link)

/-- Literal physical links of a patch schedule, preserving multiplicity. -/
def testLinks (tests : List (PhysicalLink extent)) : List Z4Link :=
  tests.map Subtype.val

theorem testLinks_valid (tests : List (PhysicalLink extent)) :
    ∀ link, link ∈ testLinks extent tests → link ∈ boundaryCompleteSlabLinks extent := by
  intro link h
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
  exact i.property

local notation "P" => projections hw0 hw1 K extent hK

/-- This is the fixed space of the EXISTING patch residuals, not those of
an isolated action with exterior factors deleted. -/
theorem fixed_iff_jointFixed (tests : List (PhysicalLink extent))
    (x : GNSCompletionSpace F) :
    BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK
      (testLinks extent tests) (testLinks_valid extent tests) x = x ↔
      (P).JointFixed tests x := by
  rw [fixed_iff_singletons]
  constructor
  · intro h i hi
    exact h i.val (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro h link hi
    obtain ⟨i, hmem, rfl⟩ := List.mem_map.mp hi
    exact h i hmem

/-- The already constructed original block projection is the exact
groundspace projection for the actual completed patch generator. -/
theorem fixed_iff_generator_zero (tests : List (PhysicalLink extent))
    (x : GNSCompletionSpace F) :
    BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK
      (testLinks extent tests) (testLinks_valid extent tests) x = x ↔
      (P).residualSum tests x = embedV F (F).zero :=
  (fixed_iff_jointFixed hw0 hw1 K extent hK tests x).trans
    (residualSum_zero_iff_jointFixed P tests x).symm

theorem fixed_iff_energy_zero (tests : List (PhysicalLink extent))
    (x : GNSCompletionSpace F) :
    BF4ExactSlabBlockConditionalProjection.conditionalProjection hw0 hw1 K extent hK
      (testLinks extent tests) (testLinks_valid extent tests) x = x ↔
      (P).finalEnergy tests x = RCzero :=
  (fixed_iff_jointFixed hw0 hw1 K extent hK tests x).trans
    (finalEnergy_zero_iff_jointFixed P tests x).symm

#print axioms fixed_iff_singletons
#print axioms union_fixed_iff
#print axioms testLinks
#print axioms testLinks_valid
#print axioms fixed_iff_jointFixed
#print axioms fixed_iff_generator_zero
#print axioms fixed_iff_energy_zero

end YMGap.Continuum.BF4ExactSlabBlockFixedSpace
