/-
# Endpoint-preserving ear for one routed cross conflict

A cross-bad unsafe-left occurrence `u` has two certified edges: an old path
pivot `p -- u`, and a routed-right conflict `u -- v`.  The shortest walk that
absorbs both endpoints while preserving the old marked endpoints is the
four-edge ear `p -- u -- v -- u -- p`.

This file constructs that ear, proves its exact four-vertex fuel cost, and
computes its exact activity normalization.  It also gives a constructive
first-right-conflict selector for the conflict-relevant mask.
-/

import YMGap.Continuum.XiExceptionalConflictRelevantLeft
import YMGap.Continuum.XiExceptionalFirstConflictSplice

namespace YMGap.Continuum.XiExceptionalCrossConflictEar

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalConflictRelevantLeft
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictSplice
open YMGap.Continuum.XiExceptionalCrossSpineCarrier

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## The generic four-edge ear -/

namespace CWalk

variable {a : Type} {edge : a -> a -> Bool}

private theorem append_vertices_length :
    forall {x y z : a} (first : CWalk edge x y)
      (second : CWalk edge y z),
      (first.append second).vertices.length + 1 =
        first.vertices.length + second.vertices.length
  | _, _, _, .single _, second => by
      simp only [CWalk.append, CWalk.vertices, List.length_cons,
        List.length_nil]
      omega
  | _, _, _, .cons _ rest, second => by
      simp only [CWalk.append, CWalk.vertices, List.length_cons]
      rw [append_vertices_length rest second]
      omega

/-- Insert `pivot -- u -- v -- u -- pivot` between a factored prefix and
suffix.  The indexed return type preserves the original endpoints. -/
def endpointCrossEar {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (hvu : edge v u = true) (hup : edge u pivot = true) :
    CWalk edge x y :=
  pre.append (.cons hpu (.cons huv (.cons hvu (.cons hup suf))))

theorem endpointCrossEar_vertices_length {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (hvu : edge v u = true) (hup : edge u pivot = true) :
    (endpointCrossEar pre suf u v hpu huv hvu hup).vertices.length =
      (pre.append suf).vertices.length + 4 := by
  have hplain := append_vertices_length pre suf
  have hear := append_vertices_length pre
    (.cons hpu (.cons huv (.cons hvu (.cons hup suf))))
  unfold endpointCrossEar
  simp only [CWalk.vertices, List.length_cons] at hear
  omega

variable {L : Lattice} [DecidableEq L.Plaquette]

/-- Exact normalization of the four-edge ear.  Relative to the original
walk it introduces one extra pivot, two extra copies of `U`, and one copy of
`V`. -/
theorem endpointCrossEar_activityWeight_eqv
    (w : Q') (label : L.Plaquette -> Rep)
    {X P Y : Polymer L}
    (pre : CWalk (fun A B : Polymer L => !(compatibleB A B)) X P)
    (suf : CWalk (fun A B : Polymer L => !(compatibleB A B)) P Y)
    (U V : Polymer L)
    (hpu : (!(compatibleB P U)) = true)
    (huv : (!(compatibleB U V)) = true)
    (hvu : (!(compatibleB V U)) = true)
    (hup : (!(compatibleB U P)) = true) :
    (endpointCrossEar pre suf U V hpu huv hvu hup).activityWeight w label ≈
      ((((pre.append suf).activityWeight w label * activity w P label) *
          activity w U label) * activity w V label) *
        activity w U label := by
  have hear := CWalk.append_activityWeight_eqv w label pre
    (.cons hpu (.cons huv (.cons hvu (.cons hup suf))))
  have hplain := CWalk.append_activityWeight_eqv w label pre suf
  unfold endpointCrossEar
  refine Q'.eqv_trans _
    (prefixActivityWeight w label pre *
      (activity w P label *
        (activity w U label *
          (activity w V label *
            (activity w U label * suf.activityWeight w label))))) _
    hear ?_
  refine Q'.eqv_trans _
    (((((prefixActivityWeight w label pre * suf.activityWeight w label) *
      activity w P label) * activity w U label) *
        activity w V label) * activity w U label) _ ?_ ?_
  · ring_qeqv
  · exact Q'.mul_eqv_congr_right _ _ (activity w U label)
      (Q'.mul_eqv_congr_right _ _ (activity w V label)
        (Q'.mul_eqv_congr_right _ _ (activity w U label)
          (Q'.mul_eqv_congr_right _ _ (activity w P label)
            (Q'.eqv_symm hplain))))

end CWalk

/-! ## A constructive right-conflict selector -/

variable {L : Lattice} [DecidableEq L.Plaquette]

def firstRightConflictIndex (Gamma : List (Polymer L))
    (right : OccBitVec Gamma.length) (i : Nat) : Nat :=
  firstTrueOn i (fun j =>
    !((!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)))
    (occurrenceIndices Gamma.length)

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

private theorem all_not_not_eq (f : a -> Bool) : forall xs : List a,
    xs.all (fun x => !(!(f x))) = xs.all f
  | [] => rfl
  | x :: xs => by
      simp only [List.all_cons]
      rw [all_not_not_eq f xs]
      cases f x <;> rfl

theorem firstRightConflictIndex_spec (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) (i : Nat)
    (hi : i < Gamma.length)
    (hbad : (crossBadLeftBits Gamma left right).at i = true) :
    let j := firstRightConflictIndex Gamma right i
    j < Gamma.length ∧ right.at j = true ∧
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
  have hfirst := firstTrueOn_mem_and_true i
    (fun j =>
      !((!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)))
    (occurrenceIndices Gamma.length) (by
      rw [all_not_not_eq]
      exact hall)
  let j := firstRightConflictIndex Gamma right i
  have hjMem : j ∈ occurrenceIndices Gamma.length := by
    simpa [j, firstRightConflictIndex] using hfirst.1
  have hj : j < Gamma.length := occurrenceIndices_sound hjMem
  have hjTrue :
      !((!right.at j) ||
        compatibleB (polyAt Gamma i) (polyAt Gamma j)) = true := by
    simpa [j, firstRightConflictIndex] using hfirst.2
  have hright : right.at j = true := by
    cases hr : right.at j with
    | true => rfl
    | false => simp [hr] at hjTrue
  have hconflict :
      compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
    cases hc : compatibleB (polyAt Gamma i) (polyAt Gamma j) with
    | false => rfl
    | true => simp [hc] at hjTrue
  exact ⟨hj, hright, hconflict⟩

theorem incAtDistinct_of_distinct_incompatible
    (Gamma : List (Polymer L)) (i j : Nat)
    (hij : i ≠ j)
    (hconflict : compatibleB (polyAt Gamma i) (polyAt Gamma j) = false) :
    incAtDistinct Gamma i j = true := by
  unfold incAtDistinct
  simp [hij, hconflict]

/-- In a genuine exceptional entry, an unsafe routed-left occurrence and a
routed-right occurrence cannot be the same ambient occurrence. -/
theorem entry_unsafeLeft_right_distinct
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i j : Nat) (hi : i < Gamma.length)
    (hiLeft : (routedLeftResidual Gamma qP b1 b2 entry).at i = true)
    (hiUnsafe : exceptionalPathSafe Gamma qP b1 b2 entry i = false)
    (hjRight : (routedRightResidual Gamma qP b1 b2 entry).at j = true) :
    i ≠ j := by
  intro hij
  subst j
  exact exceptional_unsafe_cross_side_impossible
    Gamma qP b1 b2 entry entry rfl i hi
      (by simpa [exceptionalPathSafe] using hiUnsafe) hiLeft hjRight

/-! ## The source-specific ear certificate -/

structure EntryCrossEarCertificate
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) (i : Nat) : Type where
  left_lt : i < Gamma.length
  left_residual : (routedLeftResidual Gamma qP b1 b2 entry).at i = true
  left_unsafe : exceptionalPathSafe Gamma qP b1 b2 entry i = false
  rightIndex : Nat
  right_lt : rightIndex < Gamma.length
  right_residual :
    (routedRightResidual Gamma qP b1 b2 entry).at rightIndex = true
  cross_conflict :
    compatibleB (polyAt Gamma i) (polyAt Gamma rightIndex) = false
  indices_ne : i ≠ rightIndex

def entryCrossEarCertificate
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbad : (entryCrossBadUnsafeLeft Gamma qP b1 b2 entry).at i = true) :
    EntryCrossEarCertificate Gamma qP b1 b2 entry i := by
  have hcert := entryCrossBadUnsafeLeft_certificate
    Gamma qP b1 b2 entry i hi hbad
  have hiLeft := hcert.1
  have hiUnsafe := hcert.2.1
  let j := firstRightConflictIndex Gamma
    (routedRightResidual Gamma qP b1 b2 entry) i
  have hspec := firstRightConflictIndex_spec Gamma
    (entryUnsafeLeftBits Gamma qP b1 b2 entry)
    (routedRightResidual Gamma qP b1 b2 entry) i hi
    (by simpa [entryCrossBadUnsafeLeft] using hbad)
  have hj : j < Gamma.length := by simpa [j] using hspec.1
  have hjRight :
      (routedRightResidual Gamma qP b1 b2 entry).at j = true := by
    simpa [j] using hspec.2.1
  have hij : compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
    simpa [j] using hspec.2.2
  exact
    { left_lt := hi
      left_residual := hiLeft
      left_unsafe := hiUnsafe
      rightIndex := j
      right_lt := hj
      right_residual := hjRight
      cross_conflict := hij
      indices_ne := entry_unsafeLeft_right_distinct Gamma qP b1 b2 entry
        i j hi hiLeft hiUnsafe hjRight }

#print axioms CWalk.endpointCrossEar_vertices_length
#print axioms CWalk.endpointCrossEar_activityWeight_eqv
#print axioms firstRightConflictIndex_spec
#print axioms incAtDistinct_of_distinct_incompatible
#print axioms entry_unsafeLeft_right_distinct
#print axioms entryCrossEarCertificate

end YMGap.Continuum.XiExceptionalCrossConflictEar
