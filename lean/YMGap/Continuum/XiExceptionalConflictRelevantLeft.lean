/-
# Conflict-relevant unsafe-left residual

The routed-external failure is cross-sided.  It is therefore unnecessary to
charge every path-unsafe left residual occurrence: only those left
occurrences that actually conflict with the routed-right residual obstruct
target compatibility.

This file makes that pruning exact.  The unsafe-left mask is partitioned into
cross-safe and cross-bad masks.  The cross-safe mask together with the entire
right residual is compatible, while every cross-bad bit carries a bounded
right-residual conflict witness.  Thus the remaining allocator need consume
only genuine cross-conflict left occurrences.
-/

import YMGap.Continuum.XiExceptionalRoutedExternalSplit

namespace YMGap.Continuum.XiExceptionalConflictRelevantLeft

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalParallelSourceSide
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalMergedIncompatibleSplit
open YMGap.Continuum.XiNonexceptionalTargetValidity

variable {L : Lattice} [DecidableEq L.Plaquette]

private theorem occurrenceIndices_sound : forall {n i : Nat},
    i ∈ occurrenceIndices n -> i < n
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

/-! ## The exact finite cross partition -/

def crossSafeLeftBits (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) : OccBitVec Gamma.length :=
  bitsFromMask Gamma.length (fun i =>
    left.at i &&
      (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j))) 0

def crossBadLeftBits (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) : OccBitVec Gamma.length :=
  bitsFromMask Gamma.length (fun i =>
    left.at i &&
      !(occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j))) 0

theorem crossSafeLeftBits_at (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) (i : Nat)
    (hi : i < Gamma.length) :
    (crossSafeLeftBits Gamma left right).at i =
      (left.at i &&
        (occurrenceIndices Gamma.length).all (fun j =>
          (!right.at j) ||
            compatibleB (polyAt Gamma i) (polyAt Gamma j))) := by
  unfold crossSafeLeftBits
  simpa using bitsFromMask_at Gamma.length (fun k =>
    left.at k &&
      (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma k) (polyAt Gamma j)))
    0 i hi

theorem crossBadLeftBits_at (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) (i : Nat)
    (hi : i < Gamma.length) :
    (crossBadLeftBits Gamma left right).at i =
      (left.at i &&
        !(occurrenceIndices Gamma.length).all (fun j =>
          (!right.at j) ||
            compatibleB (polyAt Gamma i) (polyAt Gamma j))) := by
  unfold crossBadLeftBits
  simpa using bitsFromMask_at Gamma.length (fun k =>
    left.at k &&
      !(occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma k) (polyAt Gamma j)))
    0 i hi

theorem crossSafeLeftBits_submask (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) :
    forall i, (crossSafeLeftBits Gamma left right).at i = true ->
      left.at i = true := by
  intro i hsafe
  by_cases hi : i < Gamma.length
  · rw [crossSafeLeftBits_at Gamma left right i hi] at hsafe
    exact ((Bool.and_eq_true _ _).mp hsafe).1
  · have hge : Gamma.length <= i := by omega
    rw [bitVec_at_false_of_ge (crossSafeLeftBits Gamma left right) i hge]
      at hsafe
    cases hsafe

theorem crossBadLeftBits_submask (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) :
    forall i, (crossBadLeftBits Gamma left right).at i = true ->
      left.at i = true := by
  intro i hbad
  by_cases hi : i < Gamma.length
  · rw [crossBadLeftBits_at Gamma left right i hi] at hbad
    exact ((Bool.and_eq_true _ _).mp hbad).1
  · have hge : Gamma.length <= i := by omega
    rw [bitVec_at_false_of_ge (crossBadLeftBits Gamma left right) i hge]
      at hbad
    cases hbad

theorem left_eq_union_crossSafe_crossBad (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) :
    left = unionBits (crossSafeLeftBits Gamma left right)
      (crossBadLeftBits Gamma left right) := by
  apply BitVec.ext
  intro i
  by_cases hi : i < Gamma.length
  · rw [unionBits_at, crossSafeLeftBits_at Gamma left right i hi,
      crossBadLeftBits_at Gamma left right i hi]
    cases hl : left.at i <;>
      cases hc : (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) <;>
      simp
  · have hge : Gamma.length <= i := by omega
    rw [bitVec_at_false_of_ge left i hge,
      bitVec_at_false_of_ge
        (unionBits (crossSafeLeftBits Gamma left right)
          (crossBadLeftBits Gamma left right)) i hge]

theorem crossSafe_crossBad_disjoint (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) (i : Nat) :
    !((crossSafeLeftBits Gamma left right).at i &&
      (crossBadLeftBits Gamma left right).at i) = true := by
  by_cases hi : i < Gamma.length
  · rw [crossSafeLeftBits_at Gamma left right i hi,
      crossBadLeftBits_at Gamma left right i hi]
    cases left.at i <;>
      cases (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) <;>
      rfl
  · have hge : Gamma.length <= i := by omega
    rw [bitVec_at_false_of_ge (crossSafeLeftBits Gamma left right) i hge]
    rfl

theorem crossSafeLeftBits_cross_compatible (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) :
    crossResidualCompatibleB Gamma
      (crossSafeLeftBits Gamma left right) right = true := by
  unfold crossResidualCompatibleB
  apply List.all_eq_true.mpr
  intro i hiMem
  have hi : i < Gamma.length := by
    exact occurrenceIndices_sound hiMem
  rw [crossSafeLeftBits_at Gamma left right i hi]
  cases hl : left.at i <;>
    cases hc : (occurrenceIndices Gamma.length).all (fun j =>
      (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) <;>
    simp

private theorem exists_false_of_all_false (f : a -> Bool) :
    forall xs : List a, xs.all f = false -> exists x, x ∈ xs ∧ f x = false
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

/-- Every marked cross-bad occurrence has an actual bounded conflict on the
right. -/
theorem crossBadLeftBits_conflict_witness (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) (i : Nat)
    (hi : i < Gamma.length)
    (hbad : (crossBadLeftBits Gamma left right).at i = true) :
    left.at i = true ∧
      exists j, j < Gamma.length ∧ right.at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  rw [crossBadLeftBits_at Gamma left right i hi] at hbad
  have hparts := (Bool.and_eq_true _ _).mp hbad
  have hall : (occurrenceIndices Gamma.length).all (fun j =>
      (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) =
      false := by
    cases h : (occurrenceIndices Gamma.length).all (fun j =>
      (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j))
    · rfl
    · simp only [h, Bool.not_true] at hparts
      cases hparts.2
  obtain ⟨j, hjMem, hjFalse⟩ := exists_false_of_all_false _ _ hall
  have hj : j < Gamma.length := occurrenceIndices_sound hjMem
  have hright : right.at j = true := by
    cases hr : right.at j with
    | true => rfl
    | false =>
        simp only [hr, Bool.not_false, Bool.true_or] at hjFalse
        cases hjFalse
  have hconflict : compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
    simpa only [hright, Bool.not_true, Bool.false_or] using hjFalse
  exact ⟨hparts.1, j, hj, hright, hconflict⟩

/-! ## Source-specific pruning -/

def entryCrossSafeUnsafeLeft
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  crossSafeLeftBits Gamma
    (entryUnsafeLeftBits Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry)

def entryCrossBadUnsafeLeft
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  crossBadLeftBits Gamma
    (entryUnsafeLeftBits Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry)

def entryConflictPrunedExternal
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  unionBits (entryCrossSafeUnsafeLeft Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry)

theorem entryUnsafeLeft_partition
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entryUnsafeLeftBits Gamma qP b1 b2 entry =
      unionBits (entryCrossSafeUnsafeLeft Gamma qP b1 b2 entry)
        (entryCrossBadUnsafeLeft Gamma qP b1 b2 entry) := by
  exact left_eq_union_crossSafe_crossBad Gamma
    (entryUnsafeLeftBits Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry)

theorem entryCrossSafeUnsafeLeft_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB (selectByBits Gamma
      (entryCrossSafeUnsafeLeft Gamma qP b1 b2 entry)) = true := by
  apply selectByBits_compatible_of_submask Gamma _
    (entryUnsafeLeftBits Gamma qP b1 b2 entry)
  · exact crossSafeLeftBits_submask Gamma _ _
  · exact entryUnsafeLeftBits_compatible Gamma qP b1 b2 entry

theorem entryConflictPrunedExternal_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB (selectByBits Gamma
      (entryConflictPrunedExternal Gamma qP b1 b2 entry)) = true := by
  apply unionBits_compatible_of_cross Gamma
  · exact entryCrossSafeUnsafeLeft_compatible Gamma qP b1 b2 entry
  · exact (routedResiduals_compatible Gamma qP b1 b2 entry).2
  · exact crossSafeLeftBits_cross_compatible Gamma
      (entryUnsafeLeftBits Gamma qP b1 b2 entry)
      (routedRightResidual Gamma qP b1 b2 entry)

/-- A source-specific bad bit is simultaneously an unsafe routed-left bit and
has a bounded routed-right conflict witness. -/
theorem entryCrossBadUnsafeLeft_certificate
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbad : (entryCrossBadUnsafeLeft Gamma qP b1 b2 entry).at i = true) :
    (routedLeftResidual Gamma qP b1 b2 entry).at i = true ∧
      exceptionalPathSafe Gamma qP b1 b2 entry i = false ∧
      exists j, j < Gamma.length ∧
        (routedRightResidual Gamma qP b1 b2 entry).at j = true ∧
        compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  obtain ⟨hiUnsafe, j, hj, hjRight, hij⟩ :=
    crossBadLeftBits_conflict_witness Gamma
      (entryUnsafeLeftBits Gamma qP b1 b2 entry)
      (routedRightResidual Gamma qP b1 b2 entry) i hi hbad
  have hiParts :
      ((!exceptionalPathSafe Gamma qP b1 b2 entry i) &&
        (routedLeftResidual Gamma qP b1 b2 entry).at i) = true := by
    rw [← unsafeLeftBits_at
      (exceptionalPathSafe Gamma qP b1 b2 entry)
      (routedLeftResidual Gamma qP b1 b2 entry) i hi]
    exact hiUnsafe
  have hiSafe : exceptionalPathSafe Gamma qP b1 b2 entry i = false := by
    have hnot := ((Bool.and_eq_true _ _).mp hiParts).1
    cases hs : exceptionalPathSafe Gamma qP b1 b2 entry i <;> simp_all
  exact ⟨((Bool.and_eq_true _ _).mp hiParts).2, hiSafe,
    j, hj, hjRight, hij⟩

theorem entryRoutedExternal_eq_bad_union_pruned
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entryRoutedExternal Gamma qP b1 b2 entry =
      unionBits (entryCrossBadUnsafeLeft Gamma qP b1 b2 entry)
        (entryConflictPrunedExternal Gamma qP b1 b2 entry) := by
  rw [entryRoutedExternal_eq_union, entryUnsafeLeft_partition]
  unfold entryConflictPrunedExternal
  apply BitVec.ext
  intro i
  repeat' rw [unionBits_at]
  cases (entryCrossSafeUnsafeLeft Gamma qP b1 b2 entry).at i <;>
    cases (entryCrossBadUnsafeLeft Gamma qP b1 b2 entry).at i <;>
    cases (routedRightResidual Gamma qP b1 b2 entry).at i <;> rfl

#print axioms crossSafeLeftBits_at
#print axioms crossBadLeftBits_at
#print axioms crossSafeLeftBits_submask
#print axioms crossBadLeftBits_submask
#print axioms left_eq_union_crossSafe_crossBad
#print axioms crossSafe_crossBad_disjoint
#print axioms crossSafeLeftBits_cross_compatible
#print axioms crossBadLeftBits_conflict_witness
#print axioms entryUnsafeLeft_partition
#print axioms entryCrossSafeUnsafeLeft_compatible
#print axioms entryConflictPrunedExternal_compatible
#print axioms entryCrossBadUnsafeLeft_certificate
#print axioms entryRoutedExternal_eq_bad_union_pruned

end YMGap.Continuum.XiExceptionalConflictRelevantLeft
