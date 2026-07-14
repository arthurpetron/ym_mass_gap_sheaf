/-
# Four comb-shaped fusion-tree coordinate bases

Four comb-shaped charts are obtained as cyclic presentations of the certified
four-factor left comb.  Each presentation keeps the fused pair adjacent and
transports its explicit synthesis back to the original coefficient box.  The
resulting charts share one semantic carrier and retain their genuinely
dependent channel types.

Exact scope: these are valid cyclic tensor-order coordinate bases.  This file
does not identify them with the repository's fixed ordered raw `triRight`/F
normalization.  In particular, the odd-outer sign exposed by the cyclic-right
normalization fence requires a separate derived bridge before that stronger
identification can be made.
-/

import YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Four cyclic comb charts; the balanced chart is added separately. -/
inductive Comb4Tree where
  | p0 | p1 | p2 | p3

def presentP1 (x : QuadForm) : QuadForm := fun j l i r => x i j l r
def restoreP1 (x : QuadForm) : QuadForm := fun i j l r => x j l i r

def presentP2 (x : QuadForm) : QuadForm := fun j l r i => x i j l r
def restoreP2 (x : QuadForm) : QuadForm := fun i j l r => x j l r i

def presentP3 (x : QuadForm) : QuadForm := fun l r j i => x i j l r
def restoreP3 (x : QuadForm) : QuadForm := fun i j l r => x l r j i

def p1Coordinates (a b c d : Nat) (x : QuadForm) :
    LeftComb4Channel b c a d → Q' :=
  leftComb4Coordinates b c a d (presentP1 x)

def p1Reconstruct (a b c d : Nat)
    (u : LeftComb4Channel b c a d → Q') : QuadForm :=
  restoreP1 (leftComb4Reconstruct b c a d u)

def p2Coordinates (a b c d : Nat) (x : QuadForm) :
    LeftComb4Channel b c d a → Q' :=
  leftComb4Coordinates b c d a (presentP2 x)

def p2Reconstruct (a b c d : Nat)
    (u : LeftComb4Channel b c d a → Q') : QuadForm :=
  restoreP2 (leftComb4Reconstruct b c d a u)

def p3Coordinates (a b c d : Nat) (x : QuadForm) :
    LeftComb4Channel c d b a → Q' :=
  leftComb4Coordinates c d b a (presentP3 x)

def p3Reconstruct (a b c d : Nat)
    (u : LeftComb4Channel c d b a → Q') : QuadForm :=
  restoreP3 (leftComb4Reconstruct c d b a u)

theorem p1Coordinates_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (q : LeftComb4Channel b c a d) :
    p1Coordinates a b c d x q ≈ p1Coordinates a b c d z q := by
  apply leftComb4Coordinates_congr b c a d
  intro j l i r hj hl hi hr
  exact hxz i j l r hi hj hl hr

theorem p1Coordinates_reconstruct (a b c d : Nat)
    (u : LeftComb4Channel b c a d → Q')
    (q : LeftComb4Channel b c a d) :
    p1Coordinates a b c d (p1Reconstruct a b c d u) q ≈ u q := by
  exact leftComb4Coordinates_reconstruct b c a d u q

theorem p1Reconstruct_coordinates (a b c d : Nat) (x : QuadForm)
    (i j l r : Nat) (hi : i ≤ a) (hj : j ≤ b)
    (hl : l ≤ c) (hr : r ≤ d) :
    p1Reconstruct a b c d (p1Coordinates a b c d x) i j l r ≈
      x i j l r := by
  exact leftComb4Reconstruct_coordinates b c a d (presentP1 x)
    j l i r hj hl hi hr

theorem p2Coordinates_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (q : LeftComb4Channel b c d a) :
    p2Coordinates a b c d x q ≈ p2Coordinates a b c d z q := by
  apply leftComb4Coordinates_congr b c d a
  intro j l r i hj hl hr hi
  exact hxz i j l r hi hj hl hr

theorem p2Coordinates_reconstruct (a b c d : Nat)
    (u : LeftComb4Channel b c d a → Q')
    (q : LeftComb4Channel b c d a) :
    p2Coordinates a b c d (p2Reconstruct a b c d u) q ≈ u q := by
  exact leftComb4Coordinates_reconstruct b c d a u q

theorem p2Reconstruct_coordinates (a b c d : Nat) (x : QuadForm)
    (i j l r : Nat) (hi : i ≤ a) (hj : j ≤ b)
    (hl : l ≤ c) (hr : r ≤ d) :
    p2Reconstruct a b c d (p2Coordinates a b c d x) i j l r ≈
      x i j l r := by
  exact leftComb4Reconstruct_coordinates b c d a (presentP2 x)
    j l r i hj hl hr hi

theorem p3Coordinates_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (q : LeftComb4Channel c d b a) :
    p3Coordinates a b c d x q ≈ p3Coordinates a b c d z q := by
  apply leftComb4Coordinates_congr c d b a
  intro l r j i hl hr hj hi
  exact hxz i j l r hi hj hl hr

theorem p3Coordinates_reconstruct (a b c d : Nat)
    (u : LeftComb4Channel c d b a → Q')
    (q : LeftComb4Channel c d b a) :
    p3Coordinates a b c d (p3Reconstruct a b c d u) q ≈ u q := by
  exact leftComb4Coordinates_reconstruct c d b a u q

theorem p3Reconstruct_coordinates (a b c d : Nat) (x : QuadForm)
    (i j l r : Nat) (hi : i ≤ a) (hj : j ≤ b)
    (hl : l ≤ c) (hr : r ≤ d) :
    p3Reconstruct a b c d (p3Coordinates a b c d x) i j l r ≈
      x i j l r := by
  exact leftComb4Reconstruct_coordinates c d b a (presentP3 x)
    l r j i hl hr hj hi

/-- **The four cyclic comb charts as coordinate bases of one four-form box.** -/
def fourCombCoordinateBases (a b c d : Nat) :
    CoordinateBases Comb4Tree QuadForm where
  Index := fun
    | .p0 => LeftComb4Channel a b c d
    | .p1 => LeftComb4Channel b c a d
    | .p2 => LeftComb4Channel b c d a
    | .p3 => LeftComb4Channel c d b a
  Rel := PhysicalQuadBoxEqv a b c d
  rel_refl := fun x i j l r hi hj hl hr => Q'.eqv_refl _
  rel_symm := fun h i j l r hi hj hl hr =>
    Q'.eqv_symm (h i j l r hi hj hl hr)
  rel_trans := fun h₁ h₂ i j l r hi hj hl hr =>
    Q'.eqv_trans _ _ _ (h₁ i j l r hi hj hl hr)
      (h₂ i j l r hi hj hl hr)
  synth := fun
    | .p0, u => leftComb4Reconstruct a b c d u
    | .p1, u => p1Reconstruct a b c d u
    | .p2, u => p2Reconstruct a b c d u
    | .p3, u => p3Reconstruct a b c d u
  coords := fun
    | .p0, x => leftComb4Coordinates a b c d x
    | .p1, x => p1Coordinates a b c d x
    | .p2, x => p2Coordinates a b c d x
    | .p3, x => p3Coordinates a b c d x
  coords_congr := by
    intro T x z hxz q
    cases T with
    | p0 => exact leftComb4Coordinates_congr a b c d x z hxz q
    | p1 => exact p1Coordinates_congr a b c d x z hxz q
    | p2 => exact p2Coordinates_congr a b c d x z hxz q
    | p3 => exact p3Coordinates_congr a b c d x z hxz q
  synth_coords := by
    intro T x
    cases T with
    | p0 =>
        intro i j l r hi hj hl hr
        exact leftComb4Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p1 =>
        intro i j l r hi hj hl hr
        exact p1Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p2 =>
        intro i j l r hi hj hl hr
        exact p2Reconstruct_coordinates a b c d x i j l r hi hj hl hr
    | p3 =>
        intro i j l r hi hj hl hr
        exact p3Reconstruct_coordinates a b c d x i j l r hi hj hl hr
  coords_synth := by
    intro T u q
    cases T with
    | p0 => exact leftComb4Coordinates_reconstruct a b c d u q
    | p1 => exact p1Coordinates_reconstruct a b c d u q
    | p2 => exact p2Coordinates_reconstruct a b c d u q
    | p3 => exact p3Coordinates_reconstruct a b c d u q

end YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p1Coordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p1Coordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p1Reconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p2Coordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p2Coordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p2Reconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p3Coordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p3Coordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.p3Reconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnFourCombTreeCoordinateBases.fourCombCoordinateBases
