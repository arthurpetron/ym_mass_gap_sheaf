/-
# Decoding cleared path sides

The residual routed code clears both switched masks on path occurrences.
Those bits are nevertheless recoverable: the carrier chain records the
ordered occurrence path, its first vertex is switched-left, and every
disagreement edge alternates the exclusive occupied side.
-/

import YMGap.Continuum.XiExceptionalRoutedExactWeight

namespace YMGap.Continuum.XiExceptionalPathSideDecoder

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

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. The occurrence list stored by a chain code -/

def occurrenceChainVertices (start : Nat) : OccChainCode n → List Nat
  | .terminal _ => [start]
  | .step next rest => start :: occurrenceChainVertices next rest

theorem occurrenceChainVertices_ofWalk
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec n) :
    occurrenceChainVertices i
      (occurrenceChainCodeOfWalk walk background) = walk.vertices := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simp only [occurrenceChainCodeOfWalk, occurrenceChainVertices,
        CWalk.vertices, CWalk.start_eq]
      rw [ih]

/-! ## 2. Alternating exclusive sides -/

def OppositeSides (li ri lj rj : Bool) : Prop :=
  (li = true ∧ ri = false ∧ lj = false ∧ rj = true) ∨
    (li = false ∧ ri = true ∧ lj = true ∧ rj = false)

def AlternatingSides (left right : Nat → Bool) : List Nat → Prop
  | [] => True
  | [_] => True
  | i :: j :: rest =>
      OppositeSides (left i) (right i) (left j) (right j) ∧
        AlternatingSides left right (j :: rest)

theorem oppositeSides_of_disagreementBits
    (li ri lj rj conflict : Bool)
    (h : disagreementBits li ri lj rj conflict = true) :
    OppositeSides li ri lj rj := by
  cases li <;> cases ri <;> cases lj <;> cases rj <;> cases conflict <;>
    simp_all [disagreementBits, leftOnly, rightOnly, OppositeSides]

theorem alternatingSides_of_disagreementWalk
    (N : Nat) (inc : Nat → Nat → Bool)
    (left right : Nat → Bool) :
    ∀ {i j : Nat}
      (walk : CWalk (disagreementEdge N inc left right) i j),
      AlternatingSides left right walk.vertices
  | _, _, .single _ => by simp [CWalk.vertices, AlternatingSides]
  | _, _, .cons hedge rest => by
      have hop := oppositeSides_of_disagreementBits _ _ _ _ _
        ((Bool.and_eq_true _ _).mp hedge).2
      cases rest with
      | single _ => exact ⟨hop, True.intro⟩
      | cons hnext tail =>
          have ih := alternatingSides_of_disagreementWalk N inc left right
            (.cons hnext tail)
          exact ⟨hop, ih⟩

private theorem opposite_target_unique
    (li1 ri1 li2 ri2 lj1 rj1 lj2 rj2 : Bool)
    (hsource : li1 = li2 ∧ ri1 = ri2)
    (hop1 : OppositeSides li1 ri1 lj1 rj1)
    (hop2 : OppositeSides li2 ri2 lj2 rj2) :
    lj1 = lj2 ∧ rj1 = rj2 := by
  cases li1 <;> cases ri1 <;> cases li2 <;> cases ri2 <;>
    cases lj1 <;> cases rj1 <;> cases lj2 <;> cases rj2 <;>
    simp_all [OppositeSides]

theorem alternatingSides_unique
    (left1 right1 left2 right2 : Nat → Bool) :
    ∀ (vertices : List Nat),
      AlternatingSides left1 right1 vertices →
      AlternatingSides left2 right2 vertices →
      (match vertices with
        | [] => True
        | i :: _ => left1 i = left2 i ∧ right1 i = right2 i) →
      ∀ i, i ∈ vertices →
        left1 i = left2 i ∧ right1 i = right2 i
  | [], _, _, _, _, hi => by cases hi
  | [x], _, _, hfirst, i, hi => by
      rw [List.mem_singleton.mp hi]
      exact hfirst
  | x :: y :: rest, halt1, halt2, hfirst, i, hi => by
      have hnext := opposite_target_unique _ _ _ _ _ _ _ _ hfirst
        halt1.1 halt2.1
      rcases List.mem_cons.mp hi with hix | hitail
      · rw [hix]
        exact hfirst
      · exact alternatingSides_unique left1 right1 left2 right2
          (y :: rest) halt1.2 halt2.2 hnext i hitail

/-! ## 3. The exceptional switched path has the canonical side pattern -/

theorem exceptional_switched_path_alternating
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    AlternatingSides
      (switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2))
      (switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2))
      path.indexWalk.vertices := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let switchedLeftF := switchedLeft Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
  let switchedRightF := switchedRight Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
  have hedgeSwitched : ∀ i j,
      disagreementEdge Gamma.length (incAtDistinct Gamma)
          (bitMask pair.1) (bitMask pair.2) i j = true →
        disagreementEdge Gamma.length (incAtDistinct Gamma)
          switchedLeftF switchedRightF i j = true := by
    intro i j h
    rw [disagreementEdge_switch_invariant Gamma.length
      (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2)
      (sameSide_guard_incAtDistinct Gamma (bitMask pair.1)
        facts.left_pairwise)
      (sameSide_guard_incAtDistinct Gamma (bitMask pair.2)
        facts.right_pairwise) i j]
    exact h
  let switchedWalk := mapCWalk
    (edgeB := disagreementEdge Gamma.length (incAtDistinct Gamma)
      switchedLeftF switchedRightF)
    (fun i => i)
    hedgeSwitched
    path.indexWalk
  have halt := alternatingSides_of_disagreementWalk Gamma.length
    (incAtDistinct Gamma) switchedLeftF switchedRightF switchedWalk
  have hvertices := vertices_mapCWalk (fun i : Nat => i)
    hedgeSwitched
    path.indexWalk
  have hvertices' : switchedWalk.vertices = path.indexWalk.vertices := by
    dsimp only [switchedWalk]
    simpa using hvertices
  rw [hvertices'] at halt
  exact halt

theorem exceptional_switched_path_start_left
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let marked := exceptionalMarkedIndex Gamma b1 b2 pair
    switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) marked = true ∧
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) marked = false := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let marked := exceptionalMarkedIndex Gamma b1 b2 pair
  unfold switchedLeft switchedRight swapLeftMask swapRightMask
  rw [facts.marked_reached]
  exact ⟨facts.marked_right_true, facts.marked_left_false⟩

#print axioms occurrenceChainVertices_ofWalk
#print axioms alternatingSides_of_disagreementWalk
#print axioms alternatingSides_unique
#print axioms exceptional_switched_path_alternating
#print axioms exceptional_switched_path_start_left

end YMGap.Continuum.XiExceptionalPathSideDecoder
