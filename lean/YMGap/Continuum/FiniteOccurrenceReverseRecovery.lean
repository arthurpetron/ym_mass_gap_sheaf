/-
# Reverse recovery for an ambient occurrence-component switch

This module isolates the graph-theoretic recovery mechanism needed by the
canonical boundary switch.  A duplicate-free ambient atom list carries two
Boolean occupation masks.  Only disagreement occurrences (left-only or
right-only) are vertices; compatible cross-replica conflicts are the edges.

The occurrence universe is interleaved in ambient order.  Swapping a Boolean
component therefore conjugates the universe literally by a side-tag swapping
involution.  This avoids any unproved permutation invariance of the finite
Warshall computation.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching
import YMGap.Continuum.Z4CanonicalBipartitePath

namespace YMGap.Continuum.FiniteOccurrenceReverseRecovery

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.Z4CanonicalBipartitePath

variable {A : Type} [DecidableEq A]

/-! ## 1. Exclusive occurrences and their interleaved universe -/

def leftOnlyB (left right : A → Bool) (atom : A) : Bool :=
  left atom && !(right atom)

def rightOnlyB (left right : A → Bool) (atom : A) : Bool :=
  !(left atom) && right atom

inductive OccurrenceVertex (A : Type)
  | root
  | left : A → OccurrenceVertex A
  | right : A → OccurrenceVertex A
deriving DecidableEq

def occurrenceVertices (left right : A → Bool)
    (atom : A) : List (OccurrenceVertex A) :=
  if leftOnlyB left right atom then [.left atom]
  else if rightOnlyB left right atom then [.right atom]
  else []

def occurrenceTail (ambient : List A)
    (left right : A → Bool) : List (OccurrenceVertex A) :=
  ambient.flatMap (occurrenceVertices left right)

def occurrenceUniverse (ambient : List A)
    (left right : A → Bool) : List (OccurrenceVertex A) :=
  .root :: occurrenceTail ambient left right

def swapOccurrenceVertex (cut : A → Bool) :
    OccurrenceVertex A → OccurrenceVertex A
  | .root => .root
  | .left atom =>
      if cut atom then .right atom else .left atom
  | .right atom =>
      if cut atom then .left atom else .right atom

theorem swapOccurrenceVertex_involutive (cut : A → Bool)
    (vertex : OccurrenceVertex A) :
    swapOccurrenceVertex cut (swapOccurrenceVertex cut vertex) =
      vertex := by
  cases vertex with
  | root => rfl
  | left atom => cases hcut : cut atom <;>
      simp [swapOccurrenceVertex, hcut]
  | right atom => cases hcut : cut atom <;>
      simp [swapOccurrenceVertex, hcut]

theorem swapOccurrenceVertex_injective (cut : A → Bool) :
    Function.Injective (swapOccurrenceVertex cut) := by
  intro left right hsame
  have := congrArg (swapOccurrenceVertex cut) hsame
  simpa [swapOccurrenceVertex_involutive] using this

/-- Per ambient atom, occupation-bit swapping and side-tag swapping produce
the same exclusive-occurrence block. -/
theorem occurrenceVertices_switch
    (cut left right : A → Bool) (atom : A) :
    occurrenceVertices
        (swapLeftMask cut left right)
        (swapRightMask cut left right) atom =
      (occurrenceVertices left right atom).map
        (swapOccurrenceVertex cut) := by
  cases hcut : cut atom <;>
    cases hleft : left atom <;>
    cases hright : right atom <;>
    simp [occurrenceVertices, leftOnlyB, rightOnlyB,
      swapLeftMask, swapRightMask, swapOccurrenceVertex,
      hcut, hleft, hright]

private theorem occurrenceTail_switch
    (cut left right : A → Bool) :
    ∀ ambient : List A,
      occurrenceTail ambient
          (swapLeftMask cut left right)
          (swapRightMask cut left right) =
        (occurrenceTail ambient left right).map
          (swapOccurrenceVertex cut)
  | [] => rfl
  | atom :: rest => by
      unfold occurrenceTail
      simp only [List.flatMap_cons, List.map_append]
      rw [occurrenceVertices_switch]
      exact congrArg
        (fun tail =>
          (occurrenceVertices left right atom).map
              (swapOccurrenceVertex cut) ++ tail)
        (occurrenceTail_switch cut left right rest)

/-- The switched occurrence universe is literally the image of the original
universe under the side-swap involution. -/
theorem occurrenceUniverse_switch
    (ambient : List A) (cut left right : A → Bool) :
    occurrenceUniverse ambient
        (swapLeftMask cut left right)
        (swapRightMask cut left right) =
      (occurrenceUniverse ambient left right).map
        (swapOccurrenceVertex cut) := by
  unfold occurrenceUniverse
  simp only [List.map_cons, swapOccurrenceVertex]
  rw [occurrenceTail_switch]

/-! ## 2. Forward and reverse occurrence graphs -/

def forwardEdge (ambient : List A)
    (compat : A → A → Bool) (bad : A → Bool)
    (left right : A → Bool) :
    OccurrenceVertex A → OccurrenceVertex A → Bool
  | .root, .left atom =>
      memberB ambient atom &&
        (leftOnlyB left right atom && bad atom)
  | .left leftAtom, .right rightAtom =>
      (memberB ambient leftAtom && memberB ambient rightAtom) &&
        ((leftOnlyB left right leftAtom &&
          rightOnlyB left right rightAtom) &&
            !(compat leftAtom rightAtom))
  | .right rightAtom, .left leftAtom =>
      (memberB ambient rightAtom && memberB ambient leftAtom) &&
        ((rightOnlyB left right rightAtom &&
          leftOnlyB left right leftAtom) &&
            !(compat leftAtom rightAtom))
  | _, _ => false

def reverseEdge (ambient : List A)
    (compat : A → A → Bool) (bad : A → Bool)
    (left right : A → Bool) :
    OccurrenceVertex A → OccurrenceVertex A → Bool
  | .root, .right atom =>
      memberB ambient atom &&
        (rightOnlyB left right atom && bad atom)
  | .left leftAtom, .right rightAtom =>
      (memberB ambient leftAtom && memberB ambient rightAtom) &&
        ((leftOnlyB left right leftAtom &&
          rightOnlyB left right rightAtom) &&
            !(compat leftAtom rightAtom))
  | .right rightAtom, .left leftAtom =>
      (memberB ambient rightAtom && memberB ambient leftAtom) &&
        ((rightOnlyB left right rightAtom &&
          leftOnlyB left right leftAtom) &&
            !(compat leftAtom rightAtom))
  | _, _ => false

def forwardReach (ambient : List A)
    (compat : A → A → Bool) (bad : A → Bool)
    (left right : A → Bool) (vertex : OccurrenceVertex A) : Bool :=
  warshall (forwardEdge ambient compat bad left right)
    (occurrenceUniverse ambient left right) .root vertex

def reverseReach (ambient : List A)
    (compat : A → A → Bool) (bad : A → Bool)
    (left right : A → Bool) (vertex : OccurrenceVertex A) : Bool :=
  warshall (reverseEdge ambient compat bad left right)
    (occurrenceUniverse ambient left right) .root vertex

def forwardCut (ambient : List A)
    (compat : A → A → Bool) (bad : A → Bool)
    (left right : A → Bool) (atom : A) : Bool :=
  if leftOnlyB left right atom then
    forwardReach ambient compat bad left right (.left atom)
  else if rightOnlyB left right atom then
    forwardReach ambient compat bad left right (.right atom)
  else false

def reverseCut (ambient : List A)
    (compat : A → A → Bool) (bad : A → Bool)
    (left right : A → Bool) (atom : A) : Bool :=
  if rightOnlyB left right atom then
    reverseReach ambient compat bad left right (.right atom)
  else if leftOnlyB left right atom then
    reverseReach ambient compat bad left right (.left atom)
  else false

theorem leftOccurrence_mem_universe
    (ambient : List A) (left right : A → Bool)
    {atom : A} (hatom : atom ∈ ambient)
    (hleftOnly : leftOnlyB left right atom = true) :
    OccurrenceVertex.left atom ∈
      occurrenceUniverse ambient left right := by
  unfold occurrenceUniverse occurrenceTail
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨atom, hatom, ?_⟩
  simp [occurrenceVertices, hleftOnly]

theorem rightOccurrence_mem_universe
    (ambient : List A) (left right : A → Bool)
    {atom : A} (hatom : atom ∈ ambient)
    (hrightOnly : rightOnlyB left right atom = true) :
    OccurrenceVertex.right atom ∈
      occurrenceUniverse ambient left right := by
  unfold occurrenceUniverse occurrenceTail
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨atom, hatom, ?_⟩
  have hleftFalse : leftOnlyB left right atom = false := by
    unfold leftOnlyB rightOnlyB at *
    cases hleft : left atom <;> cases hright : right atom <;>
      simp_all
  simp [occurrenceVertices, hleftFalse, hrightOnly]

theorem forwardSeed_reached
    (ambient : List A) (compat : A → A → Bool)
    (bad left right : A → Bool) {atom : A}
    (hatom : atom ∈ ambient)
    (hseed : (leftOnlyB left right atom && bad atom) = true) :
    forwardReach ambient compat bad left right (.left atom) = true := by
  unfold forwardReach
  apply warshall_edge
  simp [forwardEdge, memberB, hatom, hseed]

theorem forwardSeed_cut_true
    (ambient : List A) (compat : A → A → Bool)
    (bad left right : A → Bool) {atom : A}
    (hatom : atom ∈ ambient)
    (hseed : (leftOnlyB left right atom && bad atom) = true) :
    forwardCut ambient compat bad left right atom = true := by
  have hparts := (Bool.and_eq_true _ _).mp hseed
  unfold forwardCut
  simp [hparts.1,
    forwardSeed_reached ambient compat bad left right hatom hseed]

theorem forwardReach_right_of_left_edge
    (ambient : List A) (compat : A → A → Bool)
    (bad left right : A → Bool)
    {leftAtom rightAtom : A}
    (hleftAmbient : leftAtom ∈ ambient)
    (hrightAmbient : rightAtom ∈ ambient)
    (hleftOnly : leftOnlyB left right leftAtom = true)
    (hrightOnly : rightOnlyB left right rightAtom = true)
    (hconflict : (!(compat leftAtom rightAtom)) = true)
    (hreach : forwardReach ambient compat bad left right
      (.left leftAtom) = true) :
    forwardReach ambient compat bad left right
      (.right rightAtom) = true := by
  unfold forwardReach at hreach ⊢
  apply warshall_trans_of_mem
    (forwardEdge ambient compat bad left right)
    (occurrenceUniverse ambient left right)
    .root (.left leftAtom) (.right rightAtom)
    (leftOccurrence_mem_universe ambient left right
      hleftAmbient hleftOnly) hreach
  apply warshall_edge
  simp [forwardEdge, memberB, hleftAmbient, hrightAmbient,
    hleftOnly, hrightOnly, hconflict]

theorem forwardReach_left_of_right_edge
    (ambient : List A) (compat : A → A → Bool)
    (bad left right : A → Bool)
    {leftAtom rightAtom : A}
    (hleftAmbient : leftAtom ∈ ambient)
    (hrightAmbient : rightAtom ∈ ambient)
    (hleftOnly : leftOnlyB left right leftAtom = true)
    (hrightOnly : rightOnlyB left right rightAtom = true)
    (hconflict : (!(compat leftAtom rightAtom)) = true)
    (hreach : forwardReach ambient compat bad left right
      (.right rightAtom) = true) :
    forwardReach ambient compat bad left right
      (.left leftAtom) = true := by
  unfold forwardReach at hreach ⊢
  apply warshall_trans_of_mem
    (forwardEdge ambient compat bad left right)
    (occurrenceUniverse ambient left right)
    .root (.right rightAtom) (.left leftAtom)
    (rightOccurrence_mem_universe ambient left right
      hrightAmbient hrightOnly) hreach
  apply warshall_edge
  simp [forwardEdge, memberB, hleftAmbient, hrightAmbient,
    hleftOnly, hrightOnly, hconflict]

/-- The reached cut is constant across every occupied disagreement edge. -/
theorem forwardCut_closed
    (ambient : List A) (compat : A → A → Bool)
    (bad left right : A → Bool)
    {leftAtom rightAtom : A}
    (hleftAmbient : leftAtom ∈ ambient)
    (hrightAmbient : rightAtom ∈ ambient)
    (hleftOnly : leftOnlyB left right leftAtom = true)
    (hrightOnly : rightOnlyB left right rightAtom = true)
    (hconflict : (!(compat leftAtom rightAtom)) = true) :
    forwardCut ambient compat bad left right leftAtom =
      forwardCut ambient compat bad left right rightAtom := by
  have hleftRightFalse : rightOnlyB left right leftAtom = false := by
    unfold leftOnlyB rightOnlyB at *
    cases hl : left leftAtom <;> cases hr : right leftAtom <;>
      simp_all
  have hrightLeftFalse : leftOnlyB left right rightAtom = false := by
    unfold leftOnlyB rightOnlyB at *
    cases hl : left rightAtom <;> cases hr : right rightAtom <;>
      simp_all
  simp only [forwardCut, hleftOnly, hrightLeftFalse,
    hrightOnly, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hreach => forwardReach_right_of_left_edge
      ambient compat bad left right hleftAmbient hrightAmbient hleftOnly
        hrightOnly hconflict hreach
  · exact fun hreach => forwardReach_left_of_right_edge
      ambient compat bad left right hleftAmbient hrightAmbient hleftOnly
        hrightOnly hconflict hreach

end YMGap.Continuum.FiniteOccurrenceReverseRecovery

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteOccurrenceReverseRecovery.swapOccurrenceVertex_involutive
#print axioms YMGap.Continuum.FiniteOccurrenceReverseRecovery.occurrenceUniverse_switch
#print axioms YMGap.Continuum.FiniteOccurrenceReverseRecovery.forwardCut_closed
