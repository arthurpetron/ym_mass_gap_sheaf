/-
# Exact split at routed-external compatibility

The path-safe carrier is valid exactly when its routed external family is
internally compatible.  This file partitions the full exceptional source by
that actual Boolean target check and closes the true branch globally.

On the false branch, the external mask is the disjoint Boolean union of the
unsafe part of the switched-left residual and the complete switched-right
residual.  Both pieces are separately compatible, so finite failure
extraction returns a genuine cross edge from an unsafe-left occurrence to a
right occurrence.  This is the canonical local input for the next detour
allocator.
-/

import YMGap.Continuum.XiExceptionalMergedIncompatibleSplit
import YMGap.Continuum.XiPathSafeFactsClosure

namespace YMGap.Continuum.XiExceptionalRoutedExternalSplit

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalPathSafeSummation
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiAdmissibleSourceSwitch
open YMGap.Continuum.XiNonexceptionalTargetValidity
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalMergedIncompatibleSplit
open YMGap.Continuum.XiPathSafeFactsClosure

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Source-specific routed masks -/

def routedLeftResidual
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 entry.1
  residualBits pathBits switched.1

def routedRightResidual
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 entry.1
  residualBits pathBits switched.2

def unsafeLeftBits (safe : Nat → Bool) (left : OccBitVec n) :
    OccBitVec n :=
  bitsFromMask n (fun i => (!safe i) && left.at i) 0

theorem unsafeLeftBits_at (safe : Nat → Bool) (left : OccBitVec n)
    (i : Nat) (hi : i < n) :
    (unsafeLeftBits safe left).at i = ((!safe i) && left.at i) := by
  unfold unsafeLeftBits
  simpa using bitsFromMask_at n (fun j => (!safe j) && left.at j) 0 i hi

def entryUnsafeLeftBits
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  unsafeLeftBits (exceptionalPathSafe Gamma qP b1 b2 entry)
    (routedLeftResidual Gamma qP b1 b2 entry)

def entryRoutedExternal
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  routedExternal (exceptionalPathSafe Gamma qP b1 b2 entry)
    (routedLeftResidual Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry)

theorem routedExternal_eq_union_unsafeLeft
    (safe : Nat → Bool) (left right : OccBitVec n) :
    routedExternal safe left right = unionBits (unsafeLeftBits safe left) right := by
  apply BitVec.ext
  intro i
  by_cases hi : i < n
  · rw [routedExternal_at safe left right i hi, unionBits_at,
      unsafeLeftBits_at safe left i hi]
  · have hge : n ≤ i := by omega
    exact (bitVec_at_false_of_ge (routedExternal safe left right) i hge).trans
      (bitVec_at_false_of_ge (unionBits (unsafeLeftBits safe left) right)
        i hge).symm

theorem entryRoutedExternal_eq_union
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entryRoutedExternal Gamma qP b1 b2 entry =
      unionBits (entryUnsafeLeftBits Gamma qP b1 b2 entry)
        (routedRightResidual Gamma qP b1 b2 entry) := by
  exact routedExternal_eq_union_unsafeLeft _ _ _

/-! ## Exact source partition and the globally paid branch -/

def routedExternalCompatibleB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  familyCompatibleB
    (selectByBits Gamma (entryRoutedExternal Gamma qP b1 b2 entry))

def routedExternalCompatibleSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (routedExternalCompatibleB Gamma qP b1 b2)

def routedExternalIncompatibleSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (fun entry => !(routedExternalCompatibleB Gamma qP b1 b2 entry))

theorem exceptionalSource_routedExternal_partition
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≈
      qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (routedExternalCompatibleSource Gamma qP b1 b2) +
        qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (routedExternalIncompatibleSource Gamma qP b1 b2) := by
  exact qListSum_filter_partition
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (routedExternalCompatibleB Gamma qP b1 b2)
    (fullExceptionalSource Gamma qP b1 b2)

def routedExternalCompatibleFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcompatible : routedExternalCompatibleB Gamma qP b1 b2 entry = true) :
    PathSafeRoutedFacts Gamma qP b1 b2 entry :=
  pathSafeRoutedFactsOfExternalCompatibility Gamma qP b1 b2 entry
    ⟨by simpa [routedExternalCompatibleB, entryRoutedExternal,
      routedLeftResidual, routedRightResidual] using hcompatible⟩

theorem routedExternalCompatibleSource_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (routedExternalCompatibleSource Gamma qP b1 b2) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply pathSafe_region_global_bound hw Gamma qP b1 b2 label
    (routedExternalCompatibleSource Gamma qP b1 b2)
    (nodup_filter_bool _ _ (fullExceptionalSource_nodup Gamma qP b1 b2))
  intro entry hentry
  exact routedExternalCompatibleFacts Gamma qP b1 b2 entry
    (List.mem_filter.mp hentry).2

/-! ## Separate compatibility of the two routed pieces -/

private theorem residual_select_sublist
    (Gamma : List (Polymer L)) (path bits : OccBitVec Gamma.length) :
    (selectByBits Gamma (residualBits path bits)).Sublist
      (selectByBits Gamma bits) := by
  rw [← maskFamily_toMask_eq_selectByBits]
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_sublist_of_submask
  intro i hres
  by_cases hi : i < Gamma.length
  · change (residualBits path bits).at i = true at hres
    rw [residualBits_at path bits i hi] at hres
    exact ((Bool.and_eq_true _ _).mp hres).2
  · have hge : Gamma.length ≤ i := by omega
    change (residualBits path bits).at i = true at hres
    rw [bitVec_at_false_of_ge (residualBits path bits) i hge] at hres
    cases hres

theorem routedResiduals_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB (selectByBits Gamma
        (routedLeftResidual Gamma qP b1 b2 entry)) = true ∧
      familyCompatibleB (selectByBits Gamma
        (routedRightResidual Gamma qP b1 b2 entry)) = true := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let afacts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    facts.source_admissible
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  change familyCompatibleB
      (selectByBits Gamma (residualBits pathBits switched.1)) = true ∧
    familyCompatibleB
      (selectByBits Gamma (residualBits pathBits switched.2)) = true
  exact ⟨familyCompatibleB_of_sublist
      (residual_select_sublist Gamma pathBits switched.1)
      (switched_left_family_compatible Gamma qP b1 b2 pair afacts),
    familyCompatibleB_of_sublist
      (residual_select_sublist Gamma pathBits switched.2)
      (switched_right_family_compatible Gamma qP b1 b2 pair afacts)⟩

private theorem unsafeLeft_select_sublist
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left : OccBitVec Gamma.length) :
    (selectByBits Gamma (unsafeLeftBits safe left)).Sublist
      (selectByBits Gamma left) := by
  rw [← maskFamily_toMask_eq_selectByBits]
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_sublist_of_submask
  intro i hunsafe
  by_cases hi : i < Gamma.length
  · change (unsafeLeftBits safe left).at i = true at hunsafe
    rw [unsafeLeftBits_at safe left i hi] at hunsafe
    exact ((Bool.and_eq_true _ _).mp hunsafe).2
  · have hge : Gamma.length ≤ i := by omega
    change (unsafeLeftBits safe left).at i = true at hunsafe
    rw [bitVec_at_false_of_ge (unsafeLeftBits safe left) i hge] at hunsafe
    cases hunsafe

theorem entryUnsafeLeftBits_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB (selectByBits Gamma
      (entryUnsafeLeftBits Gamma qP b1 b2 entry)) = true := by
  apply familyCompatibleB_of_sublist
    (unsafeLeft_select_sublist Gamma
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedLeftResidual Gamma qP b1 b2 entry))
  exact (routedResiduals_compatible Gamma qP b1 b2 entry).1

/-! ## Failure gives an unsafe-left/right cross edge -/

theorem crossResidualCompatibleB_false_of_union_incompatible
    (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (hleft : familyCompatibleB (selectByBits Gamma left) = true)
    (hright : familyCompatibleB (selectByBits Gamma right) = true)
    (hunion : familyCompatibleB
      (selectByBits Gamma (unionBits left right)) = false) :
    crossResidualCompatibleB Gamma left right = false := by
  cases hcross : crossResidualCompatibleB Gamma left right with
  | false => rfl
  | true =>
      have hcompatible := unionBits_compatible_of_cross Gamma left right
        hleft hright hcross
      rw [hunion] at hcompatible
      cases hcompatible

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

private theorem crossResidualCompatibleB_false_witness
    (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (hcross : crossResidualCompatibleB Gamma left right = false) :
    ∃ i, i < Gamma.length ∧ left.at i = true ∧
      ∃ j, j < Gamma.length ∧ right.at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  unfold crossResidualCompatibleB at hcross
  obtain ⟨i, hiMem, hiFalse⟩ := exists_false_of_all_false _ _ hcross
  have hi : i < Gamma.length := occurrenceIndices_sound hiMem
  have hleft : left.at i = true := by
    cases hl : left.at i with
    | true => rfl
    | false =>
        simp only [hl, Bool.not_false, Bool.true_or] at hiFalse
        cases hiFalse
  have hinner : (occurrenceIndices Gamma.length).all (fun j =>
      (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) =
      false := by
    simpa only [hleft, Bool.not_true, Bool.false_or] using hiFalse
  obtain ⟨j, hjMem, hjFalse⟩ := exists_false_of_all_false _ _ hinner
  have hj : j < Gamma.length := occurrenceIndices_sound hjMem
  have hright : right.at j = true := by
    cases hr : right.at j with
    | true => rfl
    | false =>
        simp only [hr, Bool.not_false, Bool.true_or] at hjFalse
        cases hjFalse
  have hconflict : compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
    simpa only [hright, Bool.not_true, Bool.false_or] using hjFalse
  exact ⟨i, hi, hleft, j, hj, hright, hconflict⟩

/-- Exact local certificate on the failed target-validity branch. -/
theorem routedExternal_incompatible_cross_witness
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hincompatible : routedExternalCompatibleB Gamma qP b1 b2 entry = false) :
    ∃ i, i < Gamma.length ∧
      (routedLeftResidual Gamma qP b1 b2 entry).at i = true ∧
      exceptionalPathSafe Gamma qP b1 b2 entry i = false ∧
      ∃ j, j < Gamma.length ∧
        (routedRightResidual Gamma qP b1 b2 entry).at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  let unsafeLeft := entryUnsafeLeftBits Gamma qP b1 b2 entry
  let right := routedRightResidual Gamma qP b1 b2 entry
  have hunion : familyCompatibleB
      (selectByBits Gamma (unionBits unsafeLeft right)) = false := by
    rw [← entryRoutedExternal_eq_union Gamma qP b1 b2 entry]
    simpa [routedExternalCompatibleB] using hincompatible
  have hcross : crossResidualCompatibleB Gamma unsafeLeft right = false :=
    crossResidualCompatibleB_false_of_union_incompatible Gamma
      unsafeLeft right
      (by simpa [unsafeLeft] using
        entryUnsafeLeftBits_compatible Gamma qP b1 b2 entry)
      (by simpa [right] using
        (routedResiduals_compatible Gamma qP b1 b2 entry).2)
      hunion
  obtain ⟨i, hi, hiUnsafe, j, hj, hjRight, hij⟩ :=
    crossResidualCompatibleB_false_witness Gamma unsafeLeft right hcross
  have hiParts :
      ((!exceptionalPathSafe Gamma qP b1 b2 entry i) &&
        (routedLeftResidual Gamma qP b1 b2 entry).at i) = true := by
    rw [← unsafeLeftBits_at
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedLeftResidual Gamma qP b1 b2 entry) i hi]
    simpa [unsafeLeft, entryUnsafeLeftBits] using hiUnsafe
  have hiSafe : exceptionalPathSafe Gamma qP b1 b2 entry i = false := by
    have hnot := ((Bool.and_eq_true _ _).mp hiParts).1
    cases hs : exceptionalPathSafe Gamma qP b1 b2 entry i <;> simp_all
  have hiLeft : (routedLeftResidual Gamma qP b1 b2 entry).at i = true :=
    ((Bool.and_eq_true _ _).mp hiParts).2
  exact ⟨i, hi, hiLeft, hiSafe, j, hj, by simpa [right] using hjRight, hij⟩

theorem routedExternalIncompatibleSource_cross_witness
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ routedExternalIncompatibleSource Gamma qP b1 b2) :
    ∃ i, i < Gamma.length ∧
      (routedLeftResidual Gamma qP b1 b2 entry).at i = true ∧
      exceptionalPathSafe Gamma qP b1 b2 entry i = false ∧
      ∃ j, j < Gamma.length ∧
        (routedRightResidual Gamma qP b1 b2 entry).at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  apply routedExternal_incompatible_cross_witness Gamma qP b1 b2 entry
  simpa [routedExternalIncompatibleSource] using (List.mem_filter.mp hentry).2

#print axioms unsafeLeftBits_at
#print axioms routedExternal_eq_union_unsafeLeft
#print axioms entryRoutedExternal_eq_union
#print axioms exceptionalSource_routedExternal_partition
#print axioms routedExternalCompatibleFacts
#print axioms routedExternalCompatibleSource_global_bound
#print axioms routedResiduals_compatible
#print axioms entryUnsafeLeftBits_compatible
#print axioms crossResidualCompatibleB_false_of_union_incompatible
#print axioms routedExternal_incompatible_cross_witness
#print axioms routedExternalIncompatibleSource_cross_witness

end YMGap.Continuum.XiExceptionalRoutedExternalSplit
