/-
# Data-valued first-unsafe selector and entry splice

The existence theorem for an unsafe residual occurrence lives in `Prop` and
therefore cannot construct a carrier walk in `Type`.  This successor performs
the finite search directly on `occurrenceIndices`: the selected occurrence is
data, while separate theorems certify its bound, residual bit, and path
conflict.  The entry-level first-conflict splice is built only from this
Boolean selector.
-/

import YMGap.Continuum.XiExceptionalFirstConflictSplice

namespace YMGap.Continuum.XiExceptionalEntryFirstConflictSplice

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictSplice

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Finite Boolean first-unsafe occurrence -/

def unsafeResidualOccurrenceB (Gamma : List (Polymer L))
    (vertices : List Nat) (residual : OccBitVec Gamma.length)
    (i : Nat) : Bool :=
  residual.at i && Bool.not (pathSafe Gamma vertices i)

def firstUnsafeOccurrence (Gamma : List (Polymer L))
    (vertices : List Nat) (residual : OccBitVec Gamma.length) : Nat :=
  firstTrueOn 0 (unsafeResidualOccurrenceB Gamma vertices residual)
    (occurrenceIndices Gamma.length)

private theorem bool_not_and_not (a b : Bool) :
    Bool.not (a && Bool.not b) = (Bool.not a || b) := by
  cases a <;> cases b <;> rfl

private theorem occurrenceIndices_sound : ∀ {n i : Nat},
    i ∈ occurrenceIndices n → i < n
  | 0, _, hi => by cases hi
  | n + 1, 0, _ => by omega
  | n + 1, i + 1, hi => by
      rcases List.mem_cons.mp hi with hzero | htail
      · cases hzero
      · obtain ⟨j, hj, hji⟩ := List.mem_map.mp htail
        injection hji with h
        subst j
        have := occurrenceIndices_sound hj
        omega

theorem firstUnsafeOccurrence_spec
    (Gamma : List (Polymer L)) (vertices : List Nat)
    (residual : OccBitVec Gamma.length)
    (hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      Bool.not (residual.at i) || pathSafe Gamma vertices i) = false) :
    firstUnsafeOccurrence Gamma vertices residual < Gamma.length ∧
      residual.at (firstUnsafeOccurrence Gamma vertices residual) = true ∧
      pathSafe Gamma vertices
        (firstUnsafeOccurrence Gamma vertices residual) = false := by
  let p := unsafeResidualOccurrenceB Gamma vertices residual
  have hfun : (fun i => Bool.not (p i)) =
      (fun i => Bool.not (residual.at i) || pathSafe Gamma vertices i) := by
    funext i
    simpa only [p, unsafeResidualOccurrenceB] using
      bool_not_and_not (residual.at i) (pathSafe Gamma vertices i)
  have hall : (occurrenceIndices Gamma.length).all
      (fun i => Bool.not (p i)) = false := by
    rw [hfun]
    exact hcheck
  have hfirst := firstTrueOn_mem_and_true 0 p
    (occurrenceIndices Gamma.length) hall
  have hp := (Bool.and_eq_true _ _).mp hfirst.2
  refine ⟨occurrenceIndices_sound hfirst.1, hp.1, ?_⟩
  exact eq_false_of_not_true hp.2

/-! ## Entry-level data and specifications -/

def entryLeftFirstUnsafeOccurrence
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Nat :=
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  firstUnsafeOccurrence Gamma path.indexWalk.vertices
    (leftPathResidual Gamma qP b1 b2 entry)

theorem entryLeftFirstUnsafeOccurrence_spec
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = false) :
    entryLeftFirstUnsafeOccurrence Gamma qP b1 b2 entry < Gamma.length ∧
      (leftPathResidual Gamma qP b1 b2 entry).at
        (entryLeftFirstUnsafeOccurrence Gamma qP b1 b2 entry) = true ∧
      let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
      let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
      pathSafe Gamma path.indexWalk.vertices
        (entryLeftFirstUnsafeOccurrence Gamma qP b1 b2 entry) = false := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      Bool.not ((leftPathResidual Gamma qP b1 b2 entry).at i) ||
        pathSafe Gamma path.indexWalk.vertices i) = false := by
    simpa only [leftResidualPathSafeB] using hunsafe
  exact firstUnsafeOccurrence_spec Gamma path.indexWalk.vertices
    (leftPathResidual Gamma qP b1 b2 entry) hcheck

/-! ## The entry-level Type-valued splice -/

def entryLeftFirstConflictSplice
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = false) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    CWalk (incAtDistinct Gamma)
      (exceptionalMarkedIndex Gamma b1 b2 entry.1) path.seed := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  let base := conflictWalkOfDisagreement Gamma
    (bitMask entry.1.1) (bitMask entry.1.2) path.indexWalk
  let u := entryLeftFirstUnsafeOccurrence Gamma qP b1 b2 entry
  have hu := entryLeftFirstUnsafeOccurrence_spec
    Gamma qP b1 b2 entry hunsafe
  have hbaseUnsafe : pathSafe Gamma base.vertices u = false := by
    rw [conflictWalkOfDisagreement_vertices]
    exact hu.2.2
  exact YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictEndpointDetour
    Gamma base u hbaseUnsafe

theorem entryLeftFirstConflictSplice_length
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = false) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (entryLeftFirstConflictSplice Gamma qP b1 b2 entry hunsafe).vertices.length =
      path.indexWalk.vertices.length + 2 := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  let base := conflictWalkOfDisagreement Gamma
    (bitMask entry.1.1) (bitMask entry.1.2) path.indexWalk
  let u := entryLeftFirstUnsafeOccurrence Gamma qP b1 b2 entry
  have hu := entryLeftFirstUnsafeOccurrence_spec
    Gamma qP b1 b2 entry hunsafe
  have hbaseUnsafe : pathSafe Gamma base.vertices u = false := by
    rw [conflictWalkOfDisagreement_vertices]
    exact hu.2.2
  have hlen :=
    YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictEndpointDetour_length
      Gamma base u hbaseUnsafe
  change (entryLeftFirstConflictSplice Gamma qP b1 b2 entry hunsafe).vertices.length =
    path.indexWalk.vertices.length + 2
  rw [show entryLeftFirstConflictSplice Gamma qP b1 b2 entry hunsafe =
      YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictEndpointDetour
        Gamma base u hbaseUnsafe by rfl]
  rw [hlen, conflictWalkOfDisagreement_vertices]

#print axioms firstUnsafeOccurrence_spec
#print axioms entryLeftFirstUnsafeOccurrence_spec
#print axioms entryLeftFirstConflictSplice
#print axioms entryLeftFirstConflictSplice_length

end YMGap.Continuum.XiExceptionalEntryFirstConflictSplice
