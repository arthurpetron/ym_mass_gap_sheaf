/-
# The constructive all-label three-factor SU(2) associator

The left-nested coordinate basis can be transported cyclically to the
right-associated tree.  Both trees then become coordinate bases of the same
physical three-form box.  Their basis change is therefore the full dependent
all-label associator, with constructive inverse round trips supplied by the
common semantic carrier.
-/

import YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- The two binary bracketings of three ordered factors. -/
inductive AssocTree where
  | left
  | right

/-- Cyclically present `(m,n,p)` coefficients as `(n,p,m)` coefficients. -/
def rotateTri (x : TriForm) : TriForm :=
  fun j l i => x i j l

/-- Return cyclically presented coefficients to their original order. -/
def unrotateTri (x : TriForm) : TriForm :=
  fun i j l => x j l i

/-- The right-associated coordinate family is the left-nested family on the
cyclic presentation `(n,p,m)`. -/
def rightNestedCoordinates (m n p : Nat) (x : TriForm) :
    LeftNestedCGChannel n p m → Q' :=
  leftNestedCoordinates n p m (rotateTri x)

/-- Explicit synthesis for the right-associated tree. -/
def rightNestedReconstruct (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q') : TriForm :=
  unrotateTri (leftNestedReconstruct n p m c)

/-- Right-associated coordinates respect the common original coefficient
box. -/
theorem rightNestedCoordinates_congr (m n p : Nat) (x z : TriForm)
    (hxz : PhysicalBoxEqv m n p x z)
    (q : LeftNestedCGChannel n p m) :
    rightNestedCoordinates m n p x q ≈
      rightNestedCoordinates m n p z q := by
  apply leftNestedCoordinates_congr n p m
  intro j l i hj hl hi
  exact hxz i j l hi hj hl

/-- Right-associated synthesis followed by analysis is the identity. -/
theorem rightNestedCoordinates_reconstruct (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q')
    (q : LeftNestedCGChannel n p m) :
    rightNestedCoordinates m n p (rightNestedReconstruct m n p c) q ≈
      c q := by
  exact leftNestedCoordinates_reconstruct n p m c q

/-- Right-associated analysis followed by synthesis recovers the original
physical coefficient box. -/
theorem rightNestedReconstruct_coordinates (m n p : Nat) (x : TriForm)
    (i j l : Nat) (hi : i ≤ m) (hj : j ≤ n) (hl : l ≤ p) :
    rightNestedReconstruct m n p (rightNestedCoordinates m n p x) i j l ≈
      x i j l := by
  exact leftNestedReconstruct_coordinates n p m (rotateTri x)
    j l i hj hl hi

/-- **Both bracketings as coordinate bases of one physical three-form box.** -/
def associatorCoordinateBases (m n p : Nat) :
    CoordinateBases AssocTree TriForm where
  Index := fun
    | .left => LeftNestedCGChannel m n p
    | .right => LeftNestedCGChannel n p m
  Rel := PhysicalBoxEqv m n p
  rel_refl := fun x i j l hi hj hl => Q'.eqv_refl _
  rel_symm := fun h i j l hi hj hl => Q'.eqv_symm (h i j l hi hj hl)
  rel_trans := fun h₁ h₂ i j l hi hj hl =>
    Q'.eqv_trans _ _ _ (h₁ i j l hi hj hl) (h₂ i j l hi hj hl)
  synth := fun
    | .left, c => leftNestedReconstruct m n p c
    | .right, c => rightNestedReconstruct m n p c
  coords := fun
    | .left, x => leftNestedCoordinates m n p x
    | .right, x => rightNestedCoordinates m n p x
  coords_congr := by
    intro T x z hxz q
    cases T with
    | left => exact leftNestedCoordinates_congr m n p x z hxz q
    | right => exact rightNestedCoordinates_congr m n p x z hxz q
  synth_coords := by
    intro T x
    cases T with
    | left =>
        intro i j l hi hj hl
        exact leftNestedReconstruct_coordinates m n p x i j l hi hj hl
    | right =>
        intro i j l hi hj hl
        exact rightNestedReconstruct_coordinates m n p x i j l hi hj hl
  coords_synth := by
    intro T c q
    cases T with
    | left => exact leftNestedCoordinates_reconstruct m n p c q
    | right => exact rightNestedCoordinates_reconstruct m n p c q

/-- Full dependent all-label associator from `((m,n),p)` channels to
`(m,(n,p))` channels. -/
def allLabelAssociator (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q') :
    LeftNestedCGChannel n p m → Q' :=
  basisChange (associatorCoordinateBases m n p) .left .right c

/-- The reverse all-label associator. -/
def allLabelAssociatorInv (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q') :
    LeftNestedCGChannel m n p → Q' :=
  basisChange (associatorCoordinateBases m n p) .right .left c

/-- Right then left recoupling returns every left-associated coordinate. -/
theorem allLabelAssociator_left_roundtrip (m n p : Nat)
    (c : LeftNestedCGChannel m n p → Q') :
    ∀ q, allLabelAssociatorInv m n p (allLabelAssociator m n p c) q ≈ c q := by
  intro q
  exact Q'.eqv_trans _ _ _
    (basisChange_comp (associatorCoordinateBases m n p)
      .left .right .left c q)
    (basisChange_refl (associatorCoordinateBases m n p) .left c q)

/-- Left then right recoupling returns every right-associated coordinate. -/
theorem allLabelAssociator_right_roundtrip (m n p : Nat)
    (c : LeftNestedCGChannel n p m → Q') :
    ∀ q, allLabelAssociator m n p (allLabelAssociatorInv m n p c) q ≈ c q := by
  intro q
  exact Q'.eqv_trans _ _ _
    (basisChange_comp (associatorCoordinateBases m n p)
      .right .left .right c q)
    (basisChange_refl (associatorCoordinateBases m n p) .right c q)

end YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases.rightNestedCoordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases.rightNestedCoordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases.rightNestedReconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases.associatorCoordinateBases
#print axioms YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases.allLabelAssociator_left_roundtrip
#print axioms YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases.allLabelAssociator_right_roundtrip
