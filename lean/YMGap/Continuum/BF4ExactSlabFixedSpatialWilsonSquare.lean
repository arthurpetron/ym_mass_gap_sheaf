/-
# Literal axis-aligned spatial Wilson squares

For every natural side length, this file constructs the closed ordered word
around the square `[0,side] x [0,side]` in the `x0`--`x1` plane.  The word is
an actual `SourceLoop side`: every underlying positive link belongs to the
existing width-`side` spatial carrier.  This is finite lattice geometry only;
no spacing assignment, cross-scale carrier identification, or analytic claim
is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)

/-- Positive `x0` traversal, starting at `(x,y,0,0)`. -/
def eastFrom (x y : Nat) : Nat → List OrientedBF4Link
  | 0 => []
  | n+1 => ⟨((x,y,0,0), .x0), false⟩ :: eastFrom (x+1) y n

/-- Positive `x1` traversal, starting at `(x,y,0,0)`. -/
def northFrom (x y : Nat) : Nat → List OrientedBF4Link
  | 0 => []
  | n+1 => ⟨((x,y,0,0), .x1), false⟩ :: northFrom x (y+1) n

/-- Negative `x0` traversal from `(x+n,y,0,0)` to `(x,y,0,0)`. -/
def westTo (x y : Nat) : Nat → List OrientedBF4Link
  | 0 => []
  | n+1 => ⟨((x+n,y,0,0), .x0), true⟩ :: westTo x y n

/-- Negative `x1` traversal from `(x,y+n,0,0)` to `(x,y,0,0)`. -/
def southTo (x y : Nat) : Nat → List OrientedBF4Link
  | 0 => []
  | n+1 => ⟨((x,y+n,0,0), .x1), true⟩ :: southTo x y n

private theorem east_compatible (x y n : Nat) :
    Compatible (x,y,0,0) (eastFrom x y n) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
      change entryStart ⟨((x,y,0,0), .x0), false⟩ = (x,y,0,0) ∧
        Compatible (entryFinish ⟨((x,y,0,0), .x0), false⟩) (eastFrom (x+1) y n)
      constructor
      · simp [entryStart]
      · simpa [entryFinish, addE] using ih (x+1)

private theorem north_compatible (x y n : Nat) :
    Compatible (x,y,0,0) (northFrom x y n) := by
  induction n generalizing y with
  | zero => trivial
  | succ n ih =>
      change entryStart ⟨((x,y,0,0), .x1), false⟩ = (x,y,0,0) ∧
        Compatible (entryFinish ⟨((x,y,0,0), .x1), false⟩) (northFrom x (y+1) n)
      constructor
      · simp [entryStart]
      · simpa [entryFinish, addE] using ih (y+1)

private theorem west_compatible (x y n : Nat) :
    Compatible (x+n,y,0,0) (westTo x y n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      simp only [westTo, Compatible, entryStart, entryFinish, if_pos, addE]
      constructor
      · congr 1 <;> omega
      · exact ih

private theorem south_compatible (x y n : Nat) :
    Compatible (x,y+n,0,0) (southTo x y n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      simp only [southTo, Compatible, entryStart, entryFinish, if_pos, addE]
      constructor
      · congr 1 <;> omega
      · exact ih

private theorem east_finish (x y n : Nat) :
    pathFinish (x,y,0,0) (eastFrom x y n) = (x+n,y,0,0) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [eastFrom, pathFinish, entryFinish,
        if_neg (by decide : ¬ false = true), addE]
      rw [ih (x+1)]
      congr 1 <;> omega

private theorem north_finish (x y n : Nat) :
    pathFinish (x,y,0,0) (northFrom x y n) = (x,y+n,0,0) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      simp only [northFrom, pathFinish, entryFinish,
        if_neg (by decide : ¬ false = true), addE]
      rw [ih (y+1)]
      rw [show y+1+n = y+(n+1) by omega]

private theorem west_finish (x y n : Nat) :
    pathFinish (x+n,y,0,0) (westTo x y n) = (x,y,0,0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [westTo, pathFinish, entryFinish, if_pos]
      exact ih

private theorem south_finish (x y n : Nat) :
    pathFinish (x,y+n,0,0) (southTo x y n) = (x,y,0,0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [southTo, pathFinish, entryFinish, if_pos]
      exact ih

private theorem pathFinish_append (start : Z4Vertex) (xs ys : List OrientedBF4Link) :
    pathFinish start (xs ++ ys) = pathFinish (pathFinish start xs) ys := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, pathFinish]
      exact ih (entryFinish x)

private theorem compatible_append (start : Z4Vertex) (xs ys : List OrientedBF4Link)
    (hx : Compatible start xs) (hy : Compatible (pathFinish start xs) ys) :
    Compatible start (xs ++ ys) := by
  induction xs generalizing start with
  | nil => exact hy
  | cons x xs ih =>
      exact ⟨hx.1, ih (entryFinish x) hx.2 hy⟩

/-- The ordered four-side boundary of the corner-anchored square. -/
def squareEdges (side : Nat) : List OrientedBF4Link :=
  eastFrom 0 0 side ++ (northFrom side 0 side ++
    (westTo 0 side side ++ southTo 0 0 side))

theorem squareEdges_length (side : Nat) :
    (squareEdges side).length = 4*side := by
  have he : ∀ x y n, (eastFrom x y n).length = n := by
    intro x y n
    induction n generalizing x with
    | zero => rfl
    | succ n ih => simp [eastFrom, ih]
  have hn : ∀ x y n, (northFrom x y n).length = n := by
    intro x y n
    induction n generalizing y with
    | zero => rfl
    | succ n ih => simp [northFrom, ih]
  have hw : ∀ x y n, (westTo x y n).length = n := by
    intro x y n
    induction n with
    | zero => rfl
    | succ n ih => simp [westTo, ih]
  have hs : ∀ x y n, (southTo x y n).length = n := by
    intro x y n
    induction n with
    | zero => rfl
    | succ n ih => simp [southTo, ih]
  simp [squareEdges, he, hn, hw, hs]
  omega

/-- Coordinate box for the underlying positive representative of an edge. -/
def InSquare (side : Nat) (link : Z4Link) : Prop :=
  ((link.2 = .x0 ∧ link.1.1 < side) ∨
    (link.2 = .x1 ∧ link.1.2.1 < side)) ∧
    link.1.1 ≤ side ∧ link.1.2.1 ≤ side ∧
    link.1.2.2.1 = 0 ∧ link.1.2.2.2 = 0

/-- Vertex version of the same closed coordinate rectangle. -/
def VertexInSquare (side : Nat) (v : Z4Vertex) : Prop :=
  v.1 ≤ side ∧ v.2.1 ≤ side ∧ v.2.2.1 = 0 ∧ v.2.2.2 = 0

private theorem east_bound {side x y n : Nat} (hx : x+n ≤ side) (hy : y ≤ side) :
    ∀ e, e ∈ eastFrom x y n → InSquare side e.link := by
  induction n generalizing x with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [eastFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨Or.inl ⟨rfl, by change x < side; omega⟩,
          by change x ≤ side; omega, hy, rfl, rfl⟩
      · exact ih (x := x+1) (by omega) e he

private theorem north_bound {side x y n : Nat} (hx : x ≤ side) (hy : y+n ≤ side) :
    ∀ e, e ∈ northFrom x y n → InSquare side e.link := by
  induction n generalizing y with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [northFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨Or.inr ⟨rfl, by change y < side; omega⟩,
          hx, by change y ≤ side; omega, rfl, rfl⟩
      · exact ih (y := y+1) (by omega) e he

private theorem west_bound {side x y n : Nat} (hx : x+n ≤ side) (hy : y ≤ side) :
    ∀ e, e ∈ westTo x y n → InSquare side e.link := by
  induction n with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [westTo, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨Or.inl ⟨rfl, by change x+n < side; omega⟩,
          by change x+n ≤ side; omega, hy, rfl, rfl⟩
      · exact ih (by omega) e he

private theorem south_bound {side x y n : Nat} (hx : x ≤ side) (hy : y+n ≤ side) :
    ∀ e, e ∈ southTo x y n → InSquare side e.link := by
  induction n with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [southTo, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨Or.inr ⟨rfl, by change y+n < side; omega⟩,
          hx, by change y+n ≤ side; omega, rfl, rfl⟩
      · exact ih (by omega) e he

/-- Every positive link representative lies in the displayed square. -/
theorem squareEdges_inSquare (side : Nat) (e : OrientedBF4Link)
    (he : e ∈ squareEdges side) : InSquare side e.link := by
  simp only [squareEdges, List.mem_append] at he
  rcases he with he | he
  · exact east_bound (side := side) (by omega) (by omega) e he
  · rcases he with he | he
    · exact north_bound (side := side) (by omega) (by omega) e he
    · rcases he with he | he
      · exact west_bound (side := side) (by omega) (by omega) e he
      · exact south_bound (side := side) (by omega) (by omega) e he

/-- Both oriented endpoints stay inside the same displayed rectangle. -/
theorem squareEdges_endpoints_inSquare (side : Nat) (e : OrientedBF4Link)
    (he : e ∈ squareEdges side) :
    VertexInSquare side (entryStart e) ∧ VertexInSquare side (entryFinish e) := by
  have hb := squareEdges_inSquare side e he
  rcases e with ⟨⟨⟨x,y,z,t⟩,dir⟩,reverse⟩
  rcases hb with ⟨hstep,hx,hy,hz,ht⟩
  change ((dir = .x0 ∧ x < side) ∨ (dir = .x1 ∧ y < side)) at hstep
  change x ≤ side at hx
  change y ≤ side at hy
  change z = 0 at hz
  change t = 0 at ht
  subst z
  subst t
  have hbase : VertexInSquare side (x,y,0,0) := ⟨hx,hy,rfl,rfl⟩
  rcases hstep with ⟨hdir,hstrict⟩ | ⟨hdir,hstrict⟩
  · subst dir
    have hnext : VertexInSquare side (x+1,y,0,0) :=
      ⟨by change x+1 ≤ side; omega,hy,rfl,rfl⟩
    cases reverse
    · exact ⟨hbase,hnext⟩
    · exact ⟨hnext,hbase⟩
  · subst dir
    have hnext : VertexInSquare side (x,y+1,0,0) :=
      ⟨hx,by change y+1 ≤ side; omega,rfl,rfl⟩
    cases reverse
    · exact ⟨hbase,hnext⟩
    · exact ⟨hnext,hbase⟩

private theorem squareEdges_compatible (side : Nat) :
    Compatible (0,0,0,0) (squareEdges side) := by
  unfold squareEdges
  apply compatible_append
  · exact east_compatible 0 0 side
  · rw [east_finish]
    simp only [Nat.zero_add]
    apply compatible_append
    · exact north_compatible side 0 side
    · rw [north_finish]
      simp only [Nat.zero_add]
      apply compatible_append
      · simpa only [Nat.zero_add] using west_compatible 0 side side
      · have hw : pathFinish (side,side,0,0) (westTo 0 side side) =
            (0,side,0,0) := by
          simpa only [Nat.zero_add] using west_finish 0 side side
        rw [hw]
        simpa only [Nat.zero_add] using south_compatible 0 0 side

private theorem squareEdges_closed (side : Nat) :
    pathFinish (0,0,0,0) (squareEdges side) = (0,0,0,0) := by
  unfold squareEdges
  rw [pathFinish_append, east_finish]
  simp only [Nat.zero_add]
  rw [pathFinish_append, north_finish]
  simp only [Nat.zero_add]
  have hw : pathFinish (side,side,0,0) (westTo 0 side side) = (0,side,0,0) := by
    simpa only [Nat.zero_add] using west_finish 0 side side
  rw [pathFinish_append, hw]
  simpa only [Nat.zero_add] using south_finish 0 0 side

/-- The literal square as an actual source loop on the width-`side` carrier. -/
def squareLoop (side : Nat) : SourceLoop side where
  start := (0,0,0,0)
  edges := squareEdges side
  compatible := squareEdges_compatible side
  closed := squareEdges_closed side
  physical := by
    intro e he
    have hb := squareEdges_inSquare side e he
    apply (baseLinks_mem_iff side e.link).mpr
    have hdir : e.link.2 ≠ .x3 := by
      rcases hb.1 with ⟨h,_⟩ | ⟨h,_⟩ <;> rw [h] <;> decide
    have hz : e.link.1.2.2.1 = 0 := hb.2.2.2.1
    exact ⟨hdir, hb.2.1, hb.2.2.1, by rw [hz]; exact Nat.zero_le side, hb.2.2.2.2⟩

theorem squareLoop_length (side : Nat) :
    (squareLoop side).edges.length = 4*side :=
  squareEdges_length side

#print axioms squareEdges_inSquare
#print axioms squareEdges_endpoints_inSquare
#print axioms squareLoop
#print axioms squareLoop_length
#print axioms squareEdges_length

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare
