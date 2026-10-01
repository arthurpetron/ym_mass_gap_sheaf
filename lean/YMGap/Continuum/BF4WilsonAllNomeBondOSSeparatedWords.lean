/-
# Same-theory finite separated Wilson correlations on the bond completion

Finite products of the actual buffered operators have literal source
representatives: each new loop is inserted after one original time step.
Every mixed dense matrix element is exactly the ORIGINAL odd reflected
joint limit; every vacuum word is its original normalized Wilson joint
limit. Reversal is the adjoint on EVERY completed bond input.

These are one-step-separated products at fixed nome and spatial width.
No bare time-zero multiplier, equal-time product homomorphism, continuum
OS root, physical-time scaling, or full QFT reconstruction is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSInsertion
import YMGap.Continuum.BF4WilsonAllNomeWindowExpectation

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner unitState embed)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum (positiveAction_vacuum_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd crossOdd_within)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image image_unit bondForm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion ofSource bondCompletedInner constant_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (vacuum bondValue_inner bondValue_ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSInsertion
  (act act_ofSource act_symmetric bufferedSource halfTime halfTime_action)
open YMGap.Continuum.BF4WilsonAllNomeWindowPins (embedWindow)
open YMGap.Continuum.BF4WilsonAllNomeWindowExpectation (vacuum_embedWindow)

variable {width : Nat}

/-- The finite supplied list retains actual loops and representation labels. -/
abbrev Word (width : Nat) := List (SourceLoop width × Nat)

/-- Keep the original expression, inserting each next loop at its actual
advanced radius. There is exactly one original time step per list entry. -/
def sourceWord : Word width → IntrinsicExpression width → IntrinsicExpression width
  | [], x => x
  | a :: rest, x => bufferedSource a.1 a.2 (sourceWord rest x)

theorem sourceWord_radius (word : Word width) (x : IntrinsicExpression width) :
    (sourceWord word x).radius = x.radius + word.length := by
  induction word with
  | nil => simp only [sourceWord, List.length_nil, Nat.add_zero]
  | cons a rest ih =>
      change (sourceWord rest x).radius + 1 = x.radius + (rest.length+1)
      rw [ih, Nat.add_assoc]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1

def wordAct : Word width → H → H
  | [], x => x
  | a :: rest, x => act hw0 hw1 a.1 a.2 (wordAct rest x)

theorem wordAct_append (left right : Word width) (x : H) :
    wordAct hw0 hw1 (left ++ right) x =
      wordAct hw0 hw1 left (wordAct hw0 hw1 right x) := by
  induction left with
  | nil => rfl
  | cons a rest ih =>
      change act hw0 hw1 a.1 a.2 (wordAct hw0 hw1 (rest ++ right) x) = _
      rw [ih]
      rfl

/-- The adjoint is word reversal; no commutativity of buffered operators
is assumed, even when the underlying time-zero multipliers commute. -/
theorem wordAct_adjoint (word : Word width) (x y : H) :
    B (wordAct hw0 hw1 word x) y = B x (wordAct hw0 hw1 word.reverse y) := by
  induction word generalizing y with
  | nil => rfl
  | cons a rest ih =>
      change B (act hw0 hw1 a.1 a.2 (wordAct hw0 hw1 rest x)) y = _
      rw [act_symmetric, ih, List.reverse_cons, wordAct_append]
      rfl

/-- Finite products act on the SAME geometric sources, not independently
supplied moment data. The original source may itself have signed coefficients. -/
theorem wordAct_ofSource (word : Word width) (x : IntrinsicExpression width) :
    wordAct hw0 hw1 word (ofSource hw0 hw1 x) =
      ofSource hw0 hw1 (sourceWord word x) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      change act hw0 hw1 a.1 a.2 (wordAct hw0 hw1 rest (ofSource hw0 hw1 x)) = _
      rw [ih, act_ofSource]
      rfl

/-- EVERY mixed dense matrix element is pinned to the original normalized
reflected Wilson joint limit, including all signed terms of both sources. -/
theorem wordAct_source_pairing (word : Word width) (x y : IntrinsicExpression width) :
    B (ofSource hw0 hw1 x) (wordAct hw0 hw1 word (ofSource hw0 hw1 y)) =
      Quotient.mk crealSetoid
        (originalJointLimit hw0 hw1 (2*(max x.radius (sourceWord word y).radius)+1)
          (crossOdd x (sourceWord word y)) (crossOdd_within x (sourceWord word y))) := by
  rw [wordAct_ofSource, constant_pairing]
  rfl

/-- The physical bond vacuum sees the unmodified original joint functional;
the exterior half-step disappears by original vacuum invariance. -/
theorem vacuum_ofSource (x : IntrinsicExpression width) :
    B (vacuum hw0 hw1) (ofSource hw0 hw1 x) =
      Quotient.mk crealSetoid
        (originalJointLimit hw0 hw1 x.radius x.expression x.within) := by
  rw [bondValue_inner, vacuum, bondValue_ofSource, bondValue_ofSource, image_unit]
  change completedInner hw0 hw1 (unitState hw0 hw1 width)
    (BF4WilsonAllNomeNestedRootBasics.root hw0 hw1 1 (embed hw0 hw1 x)) = _
  rw [← halfTime_action, positiveAction_vacuum_pairing]
  exact vacuum_embedWindow hw0 hw1 x.radius x.expression x.within

/-- Arbitrarily long original one-step-separated Wilson words are genuine
vacuum moments on this SAME bond completion, not a different stochastic gap. -/
theorem vacuum_word (word : Word width) :
    B (vacuum hw0 hw1) (wordAct hw0 hw1 word (vacuum hw0 hw1)) =
      Quotient.mk crealSetoid
        (originalJointLimit hw0 hw1 (sourceWord word (unit width)).radius
          (sourceWord word (unit width)).expression (sourceWord word (unit width)).within) := by
  change B (vacuum hw0 hw1) (wordAct hw0 hw1 word (ofSource hw0 hw1 (unit width))) = _
  rw [wordAct_ofSource, vacuum_ofSource]

#print axioms sourceWord_radius
#print axioms wordAct_append
#print axioms wordAct_adjoint
#print axioms wordAct_ofSource
#print axioms wordAct_source_pairing
#print axioms vacuum_ofSource
#print axioms vacuum_word

end YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
