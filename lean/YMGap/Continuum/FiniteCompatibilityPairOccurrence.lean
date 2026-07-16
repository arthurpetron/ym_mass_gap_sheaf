/-
# Weighted occurrence of a compatible pair in a finite gas

Two distinct compatible atoms in the ambient enumeration form a genuine
two-atom compatible family.  Restoring the ambient order gives a canonical
representative, whose weight is the product of the two atom weights.  Since
that representative occurs in the joint-event filter, its weight is bounded
by the joint occurrence numerator.

This is a finite constructive statement.  It does not assert correlation,
positive association, or reflection positivity.
-/

import YMGap.Continuum.FiniteCompatibilityRootInsertion
import YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

namespace YMGap.Continuum.FiniteCompatibilityPairOccurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityRootInsertion
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CutoffOneSupportBijection

local infix:50 " ≈ " => Q'.eqv

variable {A : Type} [DecidableEq A]

/-- Two distinct ambient atoms, compatible in the stated order, contribute
their product weight to the numerator of their joint occurrence event. -/
theorem pair_weight_le_jointOccurrenceNumerator
    (compat : A → A → Bool)
    (hsymm : ∀ left right, compat left right = compat right left)
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (ambient : List A) (first second : A)
    (hambient : ambient.Nodup)
    (hfirst : first ∈ ambient) (hsecond : second ∈ ambient)
    (hne : first ≠ second) (hcompat : compat first second = true) :
    weight first * weight second ≤
      eventNumerator compat weight ambient
        (fun family => memberB family first && memberB family second) := by
  let pair := orderedRootInsertion ambient first [second]
  have hpairNodup : pair.Nodup := by
    unfold pair orderedRootInsertion
    exact List.filter_sublist.nodup hambient
  have hfirstPair : first ∈ pair := by
    exact (mem_orderedRootInsertion_iff ambient first [second] first).2
      ⟨hfirst, Or.inl rfl⟩
  have hsecondPair : second ∈ pair := by
    exact (mem_orderedRootInsertion_iff ambient first [second] second).2
      ⟨hsecond, Or.inr List.mem_cons_self⟩
  have hpairCompat : familyCompatibleB compat pair = true := by
    apply familyCompatibleB_of_pairwise compat hpairNodup
    intro left hleft right hright hleftRight
    have hleftRaw :=
      (mem_orderedRootInsertion_iff ambient first [second] left).1 hleft
    have hrightRaw :=
      (mem_orderedRootInsertion_iff ambient first [second] right).1 hright
    rcases hleftRaw.2 with hleftFirst | hleftSecond
    · subst left
      rcases hrightRaw.2 with hrightFirst | hrightSecond
      · subst right
        exact False.elim (hleftRight rfl)
      · have hrightEq : right = second := by
          simpa only [List.mem_singleton] using hrightSecond
        subst right
        exact hcompat
    · have hleftEq : left = second := by
        simpa only [List.mem_singleton] using hleftSecond
      subst left
      rcases hrightRaw.2 with hrightFirst | hrightSecond
      · subst right
        rw [hsymm]
        exact hcompat
      · have hrightEq : right = second := by
          simpa only [List.mem_singleton] using hrightSecond
        subst right
        exact False.elim (hleftRight rfl)
  have hpairFamily : pair ∈ compatibleFamilies compat ambient := by
    unfold compatibleFamilies
    apply List.mem_filter.mpr
    exact ⟨filter_mem_sublists _ _, hpairCompat⟩
  have hpairTarget : pair ∈
      (compatibleFamilies compat ambient).filter
        (fun family => memberB family first && memberB family second) := by
    apply List.mem_filter.mpr
    refine ⟨hpairFamily, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(memberB_eq_true_iff pair first).2 hfirstPair,
      (memberB_eq_true_iff pair second).2 hsecondPair⟩
  have hrawNodup : [first, second].Nodup := by
    simp [hne]
  have hpairPerm : [first, second].Perm pair := by
    apply perm_of_nodup_mem_iff [first, second] pair
      hrawNodup hpairNodup
    intro atom
    constructor
    · intro hraw
      apply (mem_orderedRootInsertion_iff
        ambient first [second] atom).2
      refine ⟨?_, List.mem_cons.mp hraw⟩
      rcases List.mem_cons.mp hraw with hfirstEq | hsecondMem
      · subst atom
        exact hfirst
      · have hsecondEq : atom = second := by
          simpa only [List.mem_singleton] using hsecondMem
        subst atom
        exact hsecond
    · intro hencoded
      exact List.mem_cons.mpr
        ((mem_orderedRootInsertion_iff
          ambient first [second] atom).1 hencoded |>.2)
  have hrawWeight :
      weight first * weight second ≈
        familyWeight weight [first, second] := by
    change weight first * weight second ≈
      weight first * (weight second * 1)
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv (weight second)))
  have hpairWeight :
      weight first * weight second ≈ familyWeight weight pair :=
    Q'.eqv_trans _ _ _ hrawWeight
      (familyWeight_perm weight hpairPerm)
  have hmember : familyWeight weight pair ≤
      listQSum (familyWeight weight)
        ((compatibleFamilies compat ambient).filter
          (fun family => memberB family first && memberB family second)) :=
    listQSum_member_le (familyWeight weight)
      (familyWeight_nonnegative weight hweight) _ hpairTarget
  unfold eventNumerator
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpairWeight) hmember

end YMGap.Continuum.FiniteCompatibilityPairOccurrence

#print axioms YMGap.Continuum.FiniteCompatibilityPairOccurrence.pair_weight_le_jointOccurrenceNumerator
