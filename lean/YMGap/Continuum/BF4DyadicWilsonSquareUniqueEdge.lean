/-
# A unique selected link in the literal dyadic Wilson square

The first east edge of every positive-side square is retained literally and
its underlying positive link does not occur in the remaining ordered word.
The statement deliberately ignores orientation when testing uniqueness.  It
is finite list geometry only, intended as an input to a later one-link Haar
extraction; it proves no variance, response, or scaling assertion.
-/

import YMGap.Continuum.BF4DyadicWilsonSquare

namespace YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquare

/-- The selected positive edge at the southwest corner. -/
def selectedEdge : OrientedBF4Link :=
  ⟨(((0,0,0,0), .x0)), false⟩

/-- Its underlying positive link; orientations are forgotten against this
value in the uniqueness statements below. -/
def selectedLink : Z4Link := ((0,0,0,0), .x0)

/-- The literal remainder after removing the first east edge from a square
of side `n+1`. -/
def squareTail (n : Nat) : List OrientedBF4Link :=
  eastFrom 1 0 n ++ (northFrom (n+1) 0 (n+1) ++
    (westTo 0 (n+1) (n+1) ++ southTo 0 0 (n+1)))

/-- The canonical tail of the positive-side dyadic square.  Positivity of
`side scale` ensures that subtracting its literal head leaves this predecessor
index without truncation ambiguity. -/
def dyadicTail (scale : Nat) : List OrientedBF4Link :=
  squareTail (side scale - 1)

/-- The square word exposes the selected edge as its literal head. -/
theorem squareEdges_succ (n : Nat) :
    squareEdges (n+1) = selectedEdge :: squareTail n := by
  rfl

private theorem eastFrom_selected_absent (x n : Nat) (hx : 0 < x) :
    ∀ e, e ∈ eastFrom x 0 n → e.link ≠ selectedLink := by
  induction n generalizing x with
  | zero =>
      intro e he
      exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [eastFrom, List.mem_cons] at he
      rcases he with rfl | he
      · intro h
        change (((x,0,0,0), .x0) : Z4Link) = ((0,0,0,0), .x0) at h
        have hx0 : x = 0 := congrArg (fun link : Z4Link => link.1.1) h
        omega
      · exact ih (x+1) (by omega) e he

private theorem northFrom_selected_absent (x y n : Nat) :
    ∀ e, e ∈ northFrom x y n → e.link ≠ selectedLink := by
  induction n generalizing y with
  | zero =>
      intro e he
      exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [northFrom, List.mem_cons] at he
      rcases he with rfl | he
      · intro h
        change (((x,y,0,0), .x1) : Z4Link) = ((0,0,0,0), .x0) at h
        have := congrArg (fun link : Z4Link => link.2) h
        contradiction
      · exact ih (y+1) e he

private theorem westTo_selected_absent (x y n : Nat) (hy : 0 < y) :
    ∀ e, e ∈ westTo x y n → e.link ≠ selectedLink := by
  induction n with
  | zero =>
      intro e he
      exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [westTo, List.mem_cons] at he
      rcases he with rfl | he
      · intro h
        change (((x+n,y,0,0), .x0) : Z4Link) = ((0,0,0,0), .x0) at h
        have hy0 : y = 0 := congrArg (fun link : Z4Link => link.1.2.1) h
        omega
      · exact ih e he

private theorem southTo_selected_absent (x y n : Nat) :
    ∀ e, e ∈ southTo x y n → e.link ≠ selectedLink := by
  induction n with
  | zero =>
      intro e he
      exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [southTo, List.mem_cons] at he
      rcases he with rfl | he
      · intro h
        change (((x,y+n,0,0), .x1) : Z4Link) = ((0,0,0,0), .x0) at h
        have := congrArg (fun link : Z4Link => link.2) h
        contradiction
      · exact ih e he

/-- After the literal head is removed, no orientation of its underlying link
occurs in the remaining square word. -/
theorem selectedLink_not_mem_squareTail (n : Nat) :
    ∀ e, e ∈ squareTail n → e.link ≠ selectedLink := by
  intro e he
  simp only [squareTail, List.mem_append] at he
  rcases he with he | he
  · exact eastFrom_selected_absent 1 n (by omega) e he
  · rcases he with he | he
    · exact northFrom_selected_absent (n+1) 0 (n+1) e he
    · rcases he with he | he
      · exact westTo_selected_absent 0 (n+1) (n+1) (by omega) e he
      · exact southTo_selected_absent 0 0 (n+1) e he

/-- Any occurrence of this underlying link has the selected orientation.
Exact occurrence count additionally uses the head-tail equality and absence
from the tail, rather than this membership implication alone. -/
theorem squareEdges_selectedLink_unique {side : Nat} (hside : 0 < side)
    (e : OrientedBF4Link) :
    e ∈ squareEdges side → e.link = selectedLink → e = selectedEdge := by
  cases side with
  | zero => exact False.elim (Nat.not_lt_zero 0 hside)
  | succ n =>
      rw [squareEdges_succ]
      intro he hlink
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · exact False.elim ((selectedLink_not_mem_squareTail n e he) hlink)

/-- The selected oriented edge actually occurs in every positive-side square. -/
theorem selectedEdge_mem_squareEdges {side : Nat} (hside : 0 < side) :
    selectedEdge ∈ squareEdges side := by
  cases side with
  | zero => exact False.elim (Nat.not_lt_zero 0 hside)
  | succ n =>
      rw [squareEdges_succ]
      exact List.mem_cons_self

/-- The padded dyadic loop retains the same exact-once selected underlying
link.  Padding changes only the room witness, not the word. -/
theorem paddedSquare_selectedLink_unique (scale width : Nat)
    (hwidth : side scale < width) (e : OrientedBF4Link) :
    e ∈ (paddedSquare scale width hwidth).edges →
      e.link = selectedLink → e = selectedEdge := by
  rw [paddedSquare_edges]
  exact squareEdges_selectedLink_unique (side_positive scale) e

/-- The exact selected edge is present in the padded dyadic word. -/
theorem selectedEdge_mem_paddedSquare (scale width : Nat)
    (hwidth : side scale < width) :
    selectedEdge ∈ (paddedSquare scale width hwidth).edges := by
  rw [paddedSquare_edges]
  exact selectedEdge_mem_squareEdges (side_positive scale)

/-- Exact head-tail decomposition of the padded dyadic word.  This is the
direct list shape needed to isolate the selected link in a later Haar
factorization. -/
theorem paddedSquare_edges_split (scale width : Nat)
    (hwidth : side scale < width) :
    (paddedSquare scale width hwidth).edges = selectedEdge :: dyadicTail scale := by
  rw [paddedSquare_edges]
  unfold dyadicTail
  have hs : side scale = (side scale - 1) + 1 := by
    have hp := side_positive scale
    omega
  exact (congrArg squareEdges hs).trans (squareEdges_succ (side scale - 1))

/-- No orientation of the selected underlying link occurs in the canonical
tail of the padded dyadic word. -/
theorem selectedLink_not_mem_dyadicTail (scale : Nat) :
    ∀ e, e ∈ dyadicTail scale → e.link ≠ selectedLink := by
  exact selectedLink_not_mem_squareTail (side scale - 1)

#print axioms selectedEdge
#print axioms selectedLink
#print axioms squareTail
#print axioms dyadicTail
#print axioms squareEdges_succ
#print axioms selectedLink_not_mem_squareTail
#print axioms squareEdges_selectedLink_unique
#print axioms selectedEdge_mem_squareEdges
#print axioms paddedSquare_selectedLink_unique
#print axioms selectedEdge_mem_paddedSquare
#print axioms paddedSquare_edges_split
#print axioms selectedLink_not_mem_dyadicTail

end YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
