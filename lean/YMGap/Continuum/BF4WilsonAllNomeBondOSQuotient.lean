/-
# The fixed-width physical bond-null Wilson quotient

Finite signed Wilson sources are quotiented by the null relation of the
actual original odd-window bond form. Their state map is injective into the
ORIGINAL completion, preserves the physical pairing and forward time, and
has computed dense approximants for every supplied witnessed time-sector
state. The range witness remains with the sector state; it is not selected
from a quotient. This is not a completed source quotient, a time-zero
multiplier representation, or a canonical continuum OS root.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSRealization

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization
  (bondForm image image_pairing image_eq_iff_bond_null image_advance image_unit
    denseExpression denseExpression_bound denseSequence denseSequence_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Nullity is tested with the actual original odd-window bond expectation
of the signed difference, not with the ambient completion norm. -/
def nullSetoid : Setoid (IntrinsicExpression width) where
  r x y := bondForm hw0 hw1 (difference x y) (difference x y) = RCzero
  iseqv := by
    constructor
    · intro x
      exact (image_eq_iff_bond_null hw0 hw1 x x).mp rfl
    · intro x y h
      exact (image_eq_iff_bond_null hw0 hw1 y x).mp
        ((image_eq_iff_bond_null hw0 hw1 x y).mpr h).symm
    · intro x y z hxy hyz
      exact (image_eq_iff_bond_null hw0 hw1 x z).mp
        (((image_eq_iff_bond_null hw0 hw1 x y).mpr hxy).trans
          ((image_eq_iff_bond_null hw0 hw1 y z).mpr hyz))

def Observable : Type := Quotient (nullSetoid hw0 hw1 (width := width))

def ofSource (x : IntrinsicExpression width) : Observable hw0 hw1 (width := width) :=
  Quotient.mk (nullSetoid hw0 hw1) x

/-- The quotient lands in the unchanged original completion. A direct lift
into `TimeSector.State` would erase its Type-valued range-witness distinction. -/
def state : Observable hw0 hw1 (width := width) → V :=
  Quotient.lift (fun x => (image hw0 hw1 x).val)
    (fun x y h => (image_eq_iff_bond_null hw0 hw1 x y).mpr h)

theorem state_ofSource (x : IntrinsicExpression width) :
    state hw0 hw1 (ofSource hw0 hw1 x) = (image hw0 hw1 x).val := rfl

/-- This is exactly the physical bond-null relation, with no additional
kernel deletion or identification of ambient completion vectors. -/
theorem ofSource_eq_iff_bond_null (x y : IntrinsicExpression width) :
    ofSource hw0 hw1 x = ofSource hw0 hw1 y ↔
      bondForm hw0 hw1 (difference x y) (difference x y) = RCzero := by
  constructor
  · intro h
    exact (image_eq_iff_bond_null hw0 hw1 x y).mp
      (congrArg (state hw0 hw1) h)
  · intro h
    exact Quotient.sound h

theorem state_injective (x y : Observable hw0 hw1 (width := width))
    (h : state hw0 hw1 x = state hw0 hw1 y) : x = y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      exact Quotient.sound ((image_eq_iff_bond_null hw0 hw1 a b).mp h)

/-- The inner product is inherited from the ORIGINAL completion, not a
newly assumed Gram form. -/
def inner (x y : Observable hw0 hw1 (width := width)) : RC :=
  B (state hw0 hw1 x) (state hw0 hw1 y)

theorem inner_ofSource (x y : IntrinsicExpression width) :
    inner hw0 hw1 (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) =
      bondForm hw0 hw1 x y :=
  image_pairing hw0 hw1 x y

theorem distance_ofSource (x y : IntrinsicExpression width) :
    dist (state hw0 hw1 (ofSource hw0 hw1 x))
      (state hw0 hw1 (ofSource hw0 hw1 y)) =
      bondForm hw0 hw1 (difference x y) (difference x y) :=
  BF4WilsonAllNomeBondOSRealization.image_distance hw0 hw1 x y

/-- The same original one-step time advance descends to physical null
classes. No multiplier on those classes is asserted. -/
def forwardTime : Observable hw0 hw1 (width := width) →
    Observable hw0 hw1 (width := width) :=
  Quotient.lift
    (fun x => ofSource hw0 hw1 (advance 1 x))
    (fun x y h => Quotient.sound
      ((image_eq_iff_bond_null hw0 hw1 (advance 1 x) (advance 1 y)).mp (by
        have heq := (image_eq_iff_bond_null hw0 hw1 x y).mpr h
        have ht := congrArg (T 1) heq
        rwa [← image_advance hw0 hw1 x, ← image_advance hw0 hw1 y] at ht)))

theorem state_forwardTime (x : Observable hw0 hw1 (width := width)) :
    state hw0 hw1 (forwardTime hw0 hw1 x) = T 1 (state hw0 hw1 x) := by
  induction x using Quotient.inductionOn with
  | h a => exact image_advance hw0 hw1 a

def vacuum : Observable hw0 hw1 (width := width) := ofSource hw0 hw1 (unit width)

theorem state_vacuum :
    state hw0 hw1 (vacuum hw0 hw1 (width := width)) = unitState hw0 hw1 width :=
  image_unit hw0 hw1

/-- A Type-level approximant and its error proof, computed from the supplied
sector state's original time-range witness and two explicit moduli. -/
def approximationData (x : State hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' z : Observable hw0 hw1 (width := width),
      RCle (dist (state hw0 hw1 z) x.val) (rat epsilon) :=
  ⟨ofSource hw0 hw1 (denseExpression hw0 hw1 x epsilon),
    denseExpression_bound hw0 hw1 x epsilon he⟩

/-- A fixed computable approximation schedule, still in the physical
bond-null source quotient. -/
def denseObservable (x : State hw0 hw1 (width := width)) (n : Nat) :
    Observable hw0 hw1 (width := width) :=
  ofSource hw0 hw1 (denseSequence hw0 hw1 x n)

theorem denseObservable_bound (x : State hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : epsilon.den ≤ n) :
    RCle (dist (state hw0 hw1 (denseObservable hw0 hw1 x n)) x.val)
      (rat epsilon) :=
  denseSequence_bound hw0 hw1 x epsilon he n hn

#print axioms nullSetoid
#print axioms Observable
#print axioms state
#print axioms ofSource_eq_iff_bond_null
#print axioms state_injective
#print axioms inner_ofSource
#print axioms distance_ofSource
#print axioms forwardTime
#print axioms state_forwardTime
#print axioms state_vacuum
#print axioms approximationData
#print axioms denseObservable_bound

end YMGap.Continuum.BF4WilsonAllNomeBondOSQuotient
