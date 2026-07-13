/-
# First-conflict endpoint-preserving detours

An unsafe residual occurrence conflicts with a computably selected first
canonical-path vertex.  Inserting the two edges `j -> u -> j` at that vertex
preserves both endpoints and adds exactly two vertices to the carrier walk.
This file isolates that constructive walk operation and the Boolean first-
conflict selector.  The endpoint statement is carried by the dependent type;
the explicit length theorem records its finite-target cost.
-/

import YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit

namespace YMGap.Continuum.XiExceptionalFirstConflictDetour

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
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit

/-! ## A constructive first-true selector on a list -/

def firstTrueOn (fallback : a) (p : a → Bool) : List a → a
  | [] => fallback
  | x :: xs => if p x then x else firstTrueOn fallback p xs

theorem firstTrueOn_mem_and_true (fallback : a) (p : a → Bool) :
    ∀ xs : List a, xs.all (fun x => !(p x)) = false →
      firstTrueOn fallback p xs ∈ xs ∧
        p (firstTrueOn fallback p xs) = true
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : p x with
      | true =>
          simp [firstTrueOn, hx]
      | false =>
          have ht : xs.all (fun y => !(p y)) = false := by
            simpa only [List.all_cons, hx, Bool.not_false,
              Bool.true_and] using h
          have ih := firstTrueOn_mem_and_true fallback p xs ht
          simp only [firstTrueOn, hx, Bool.false_eq_true, ↓reduceIte]
          exact ⟨List.mem_cons_of_mem x ih.1, ih.2⟩

variable {L : Lattice} [DecidableEq L.Plaquette]

def firstConflictIndex (Gamma : List (Polymer L))
    (vertices : List Nat) (i : Nat) : Nat :=
  firstTrueOn i (fun j => symConflict (incAtDistinct Gamma) j i) vertices

theorem firstConflictIndex_mem_and_conflict
    (Gamma : List (Polymer L)) (vertices : List Nat) (i : Nat)
    (hunsafe : pathSafe Gamma vertices i = false) :
    firstConflictIndex Gamma vertices i ∈ vertices ∧
      symConflict (incAtDistinct Gamma)
        (firstConflictIndex Gamma vertices i) i = true := by
  unfold pathSafe at hunsafe
  exact firstTrueOn_mem_and_true i
    (fun j => symConflict (incAtDistinct Gamma) j i) vertices hunsafe

/-! ## Endpoint-preserving detour insertion -/

namespace CWalk

variable {a : Type}
variable {edge : a → a → Bool}

private theorem append_vertices_length :
    ∀ {x y z : a} (first : CWalk edge x y) (second : CWalk edge y z),
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

/-- Given a prefix ending at a conflict vertex and the remaining suffix,
insert the excursion `pivot -> detour -> pivot`.  Both endpoints are
preserved by the indexed return type. -/
def endpointDetour {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (detour : a) (hout : edge pivot detour = true)
    (hin : edge detour pivot = true) : CWalk edge x y :=
  pre.append (.cons hout (.cons hin suf))

/-- The endpoint-preserving excursion costs exactly two vertices relative to
the same prefix/suffix concatenation without the excursion. -/
theorem endpointDetour_vertices_length {x pivot y : a}
    (pre : CWalk edge x pivot) (suf : CWalk edge pivot y)
    (detour : a) (hout : edge pivot detour = true)
    (hin : edge detour pivot = true) :
    (endpointDetour pre suf detour hout hin).vertices.length =
      (pre.append suf).vertices.length + 2 := by
  have hplain := append_vertices_length pre suf
  have hdetour := append_vertices_length pre
    (.cons hout (.cons hin suf))
  unfold endpointDetour
  simp only [CWalk.vertices, List.length_cons] at hdetour
  omega

end CWalk

/-! ## The conflict relation supplies both detour edges -/

theorem incAtDistinct_symm (Gamma : List (Polymer L)) (i j : Nat) :
    incAtDistinct Gamma i j = incAtDistinct Gamma j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    unfold incAtDistinct
    simp only [decide_eq_true hij, decide_eq_true hji, Bool.true_and]
    exact congrArg Bool.not (compatibleB_symm (polyAt Gamma i) (polyAt Gamma j))

theorem incAtDistinct_of_symConflict_true
    (Gamma : List (Polymer L)) (i j : Nat)
    (hconflict : symConflict (incAtDistinct Gamma) i j = true) :
    incAtDistinct Gamma i j = true := by
  unfold symConflict at hconflict
  rcases (Bool.or_eq_true _ _).mp hconflict with hij | hji
  · exact hij
  · rw [incAtDistinct_symm Gamma i j]
    exact hji

def conflictWalkOfDisagreement
    (Gamma : List (Polymer L)) (left right : Nat → Bool) {i j : Nat}
    (walk : CWalk
      (disagreementEdge Gamma.length (incAtDistinct Gamma) left right)
      i j) : CWalk (incAtDistinct Gamma) i j :=
  mapCWalk id (fun x y h => by
    have hbits := ((Bool.and_eq_true _ _).mp h).2
    have hconflict := ((Bool.and_eq_true _ _).mp hbits).2
    exact incAtDistinct_of_symConflict_true Gamma x y hconflict) walk

theorem conflictWalkOfDisagreement_vertices
    (Gamma : List (Polymer L)) (left right : Nat → Bool) {i j : Nat}
    (walk : CWalk
      (disagreementEdge Gamma.length (incAtDistinct Gamma) left right)
      i j) :
    (conflictWalkOfDisagreement Gamma left right walk).vertices =
      walk.vertices := by
  let hedge : ∀ x y,
      disagreementEdge Gamma.length (incAtDistinct Gamma) left right x y =
        true → incAtDistinct Gamma x y = true := fun x y h => by
    have hbits := ((Bool.and_eq_true _ _).mp h).2
    have hconflict := ((Bool.and_eq_true _ _).mp hbits).2
    exact incAtDistinct_of_symConflict_true Gamma x y hconflict
  change (mapCWalk id hedge walk).vertices = walk.vertices
  rw [vertices_mapCWalk]
  simpa only [List.map_id]

/-! ## Unsafe residuals expose a computable first conflict -/

theorem leftUnsafe_firstConflict_witness
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = false) :
    ∃ u, u < Gamma.length ∧
      (leftPathResidual Gamma qP b1 b2 entry).at u = true ∧
      let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
      let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
      firstConflictIndex Gamma path.indexWalk.vertices u ∈
          path.indexWalk.vertices ∧
        incAtDistinct Gamma
          (firstConflictIndex Gamma path.indexWalk.vertices u) u = true ∧
        incAtDistinct Gamma u
          (firstConflictIndex Gamma path.indexWalk.vertices u) = true := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  obtain ⟨u, hu, hres, hpathUnsafe⟩ :=
    leftResidualPathSafeB_false Gamma qP b1 b2 entry hunsafe
  change pathSafe Gamma path.indexWalk.vertices u = false at hpathUnsafe
  have hfirst := firstConflictIndex_mem_and_conflict Gamma
    path.indexWalk.vertices u hpathUnsafe
  have hout := incAtDistinct_of_symConflict_true Gamma
    (firstConflictIndex Gamma path.indexWalk.vertices u) u hfirst.2
  refine ⟨u, hu, hres, hfirst.1, hout, ?_⟩
  rw [← incAtDistinct_symm Gamma]
  exact hout

#print axioms firstTrueOn_mem_and_true
#print axioms firstConflictIndex_mem_and_conflict
#print axioms CWalk.endpointDetour_vertices_length
#print axioms incAtDistinct_symm
#print axioms incAtDistinct_of_symConflict_true
#print axioms conflictWalkOfDisagreement_vertices
#print axioms leftUnsafe_firstConflict_witness

end YMGap.Continuum.XiExceptionalFirstConflictDetour
