/-
# Constructive pivot selection for finite Boolean events

If a Boolean event is true at one finite bit vector and false at another,
replace the coordinates one at a time.  Some consecutive pair must be the
first true-to-false transition.  This module retains that coordinate as
Type-level data; it is the root needed by a disagreement-component switch
for a general finite cylinder event.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching

namespace YMGap.Continuum.FiniteBooleanEventPivot

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Type-level witness to a true-to-false transition in a finite Boolean
path. -/
structure TrueToFalseTransition (state : Nat → Bool) (steps : Nat) where
  index : Nat
  index_lt : index < steps
  before_true : state index = true
  after_false : state (index + 1) = false

/-- A finite Boolean path starting at `true` and ending at `false` has a
constructively selected true-to-false transition. -/
def trueToFalseTransition (state : Nat → Bool) :
    ∀ steps : Nat, state 0 = true → state steps = false →
      TrueToFalseTransition state steps
  | 0, hstart, hend => by
      have hbad : true = false := hstart.symm.trans hend
      exact Bool.noConfusion hbad
  | steps + 1, hstart, hend => by
      cases hprevious : state steps with
      | false =>
          let previous :=
            trueToFalseTransition state steps hstart hprevious
          exact
            { index := previous.index
              index_lt := Nat.lt_trans previous.index_lt
                (Nat.lt_succ_self steps)
              before_true := previous.before_true
              after_false := previous.after_false }
      | true =>
          exact
            { index := steps
              index_lt := Nat.lt_succ_self steps
              before_true := hprevious
              after_false := hend }

/-- Replace the first `index` coordinates of `left` by those of `right`.
The endpoints are `left` and, for equally long lists, `right`. -/
def coordinateBlend {A : Type} (left right : List A) (index : Nat) :
    List A :=
  right.take index ++ left.drop index

@[simp] theorem coordinateBlend_zero {A : Type}
    (left right : List A) :
    coordinateBlend left right 0 = left := by
  rfl

theorem coordinateBlend_length {A : Type}
    (left right : List A) (index : Nat)
    (hlength : left.length = right.length) :
    (coordinateBlend left right index).length = left.length := by
  unfold coordinateBlend
  rw [List.length_append, List.length_take, List.length_drop, hlength]
  omega

@[simp] theorem coordinateBlend_all {A : Type}
    (left right : List A) (hlength : left.length = right.length) :
    coordinateBlend left right left.length = right := by
  unfold coordinateBlend
  have htake : right.take left.length = right := by
    rw [hlength]
    exact List.take_length
  rw [htake, List.drop_length, List.append_nil]

/-- The Boolean state obtained by evaluating `event` after each successive
coordinate replacement. -/
def coordinateEventState {A : Type} (event : List A → Bool)
    (left right : List A) (index : Nat) : Bool :=
  event (coordinateBlend left right index)

/-- Constructively select the first coordinate step at which an arbitrary
finite Boolean event changes from true to false. -/
def coordinateEventPivot {A : Type} (event : List A → Bool)
    (left right : List A) (hlength : left.length = right.length)
    (hleft : event left = true) (hright : event right = false) :
    TrueToFalseTransition
      (coordinateEventState event left right) left.length := by
  apply trueToFalseTransition
  · simpa only [coordinateEventState, coordinateBlend_zero] using hleft
  · simpa only [coordinateEventState,
      coordinateBlend_all left right hlength] using hright

theorem coordinateEventPivot_index_lt {A : Type}
    (event : List A → Bool) (left right : List A)
    (hlength : left.length = right.length)
    (hleft : event left = true) (hright : event right = false) :
    (coordinateEventPivot event left right hlength hleft hright).index <
      left.length :=
  (coordinateEventPivot event left right hlength hleft hright).index_lt

theorem coordinateEventPivot_spec {A : Type}
    (event : List A → Bool) (left right : List A)
    (hlength : left.length = right.length)
    (hleft : event left = true) (hright : event right = false) :
    let pivot := coordinateEventPivot event left right hlength hleft hright
    event (coordinateBlend left right pivot.index) = true ∧
      event (coordinateBlend left right (pivot.index + 1)) = false := by
  intro pivot
  exact ⟨pivot.before_true, pivot.after_false⟩

end YMGap.Continuum.FiniteBooleanEventPivot

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteBooleanEventPivot.trueToFalseTransition
#print axioms YMGap.Continuum.FiniteBooleanEventPivot.coordinateEventPivot
#print axioms YMGap.Continuum.FiniteBooleanEventPivot.coordinateEventPivot_spec
