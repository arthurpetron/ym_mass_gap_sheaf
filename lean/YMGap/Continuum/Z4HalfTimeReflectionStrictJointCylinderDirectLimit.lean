/-
# The strict-cylinder base direct limit and its time action

Strict cylinder presentations are indexed by the finite source-box base.
Canonical base transport is already linear, functorial, and isometric.  This
module forms the corresponding constructive direct-limit carrier: two staged
vectors agree when their canonical transports agree in one explicit common
outer box.  The indexed geometric time translation respects that relation and
therefore acts on the quotient.

This is an algebraic carrier construction only.  Completion and the
self-adjointness of the descended action remain separate obligations.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction

/-- One vector together with the finite base box in which it is presented. -/
structure StrictJointCylinderStage where
  base : Nat
  vector : StrictJointCylinderVector base

namespace StrictJointCylinderStage

/-- Canonical transport of a staged vector to a larger base. -/
def transport (stage : StrictJointCylinderStage)
    (outer : Nat) (hbase : stage.base <= outer) :
    StrictJointCylinderStage :=
  ⟨outer, boxTransportStrictJointCylinderVector hbase stage.vector⟩

/-- Indexed geometric time translation as an operation on staged vectors. -/
def timeTranslate (shift : Nat) (stage : StrictJointCylinderStage) :
    StrictJointCylinderStage :=
  ⟨stage.base + shift,
    timeTranslateStrictJointCylinderVector shift stage.vector⟩

end StrictJointCylinderStage

/-- Two staged vectors represent the same direct-limit vector when their
canonical transports are literally equal in one explicit common outer box. -/
def StrictJointCylinderStageEquivalent
    (left right : StrictJointCylinderStage) : Prop :=
  ∃ outer, ∃ hleft : left.base <= outer, ∃ hright : right.base <= outer,
      boxTransportStrictJointCylinderVector hleft left.vector =
        boxTransportStrictJointCylinderVector hright right.vector

theorem strictJointCylinderStageEquivalent_refl
    (stage : StrictJointCylinderStage) :
    StrictJointCylinderStageEquivalent stage stage := by
  exact ⟨stage.base, Nat.le_refl _, Nat.le_refl _, rfl⟩

theorem strictJointCylinderStageEquivalent_symm
    {left right : StrictJointCylinderStage}
    (h : StrictJointCylinderStageEquivalent left right) :
    StrictJointCylinderStageEquivalent right left := by
  rcases h with ⟨outer, hleft, hright, heq⟩
  exact ⟨outer, hright, hleft, heq.symm⟩

theorem strictJointCylinderStageEquivalent_trans
    {first middle last : StrictJointCylinderStage}
    (hfirst : StrictJointCylinderStageEquivalent first middle)
    (hlast : StrictJointCylinderStageEquivalent middle last) :
    StrictJointCylinderStageEquivalent first last := by
  rcases hfirst with ⟨firstOuter, hfirst, hmiddleFirst, heqFirst⟩
  rcases hlast with ⟨lastOuter, hmiddleLast, hlast, heqLast⟩
  let outer := max firstOuter lastOuter
  have hfirstOuter : firstOuter <= outer := Nat.le_max_left _ _
  have hlastOuter : lastOuter <= outer := Nat.le_max_right _ _
  have hfirstFinal : first.base <= outer :=
    Nat.le_trans hfirst hfirstOuter
  have hlastFinal : last.base <= outer :=
    Nat.le_trans hlast hlastOuter
  refine ⟨outer, hfirstFinal, hlastFinal, ?_⟩
  calc
    boxTransportStrictJointCylinderVector hfirstFinal first.vector =
        boxTransportStrictJointCylinderVector hfirstOuter
          (boxTransportStrictJointCylinderVector hfirst first.vector) :=
      (boxTransportStrictJointCylinderVector_trans
        hfirst hfirstOuter first.vector).symm
    _ = boxTransportStrictJointCylinderVector hfirstOuter
          (boxTransportStrictJointCylinderVector hmiddleFirst middle.vector) :=
      congrArg (boxTransportStrictJointCylinderVector hfirstOuter) heqFirst
    _ = boxTransportStrictJointCylinderVector
          (Nat.le_trans hmiddleFirst hfirstOuter) middle.vector :=
      boxTransportStrictJointCylinderVector_trans
        hmiddleFirst hfirstOuter middle.vector
    _ = boxTransportStrictJointCylinderVector
          (Nat.le_trans hmiddleLast hlastOuter) middle.vector := by
      rfl
    _ = boxTransportStrictJointCylinderVector hlastOuter
          (boxTransportStrictJointCylinderVector hmiddleLast middle.vector) :=
      (boxTransportStrictJointCylinderVector_trans
        hmiddleLast hlastOuter middle.vector).symm
    _ = boxTransportStrictJointCylinderVector hlastOuter
          (boxTransportStrictJointCylinderVector hlast last.vector) :=
      congrArg (boxTransportStrictJointCylinderVector hlastOuter) heqLast
    _ = boxTransportStrictJointCylinderVector hlastFinal last.vector :=
      boxTransportStrictJointCylinderVector_trans
        hlast hlastOuter last.vector

theorem strictJointCylinderStageEquivalent_equivalence :
    Equivalence StrictJointCylinderStageEquivalent :=
  ⟨strictJointCylinderStageEquivalent_refl,
    @strictJointCylinderStageEquivalent_symm,
    @strictJointCylinderStageEquivalent_trans⟩

/-- Base transport does not change a staged direct-limit vector. -/
theorem strictJointCylinderStage_equivalent_transport
    (stage : StrictJointCylinderStage)
    (outer : Nat) (hbase : stage.base <= outer) :
    StrictJointCylinderStageEquivalent
      (stage.transport outer hbase) stage := by
  refine ⟨outer, Nat.le_refl _, hbase, ?_⟩
  exact boxTransportStrictJointCylinderVector_refl
    (boxTransportStrictJointCylinderVector hbase stage.vector)

/-- Geometric time translation respects the common-transport relation. -/
theorem strictJointCylinderStageEquivalent_timeTranslate
    {left right : StrictJointCylinderStage}
    (h : StrictJointCylinderStageEquivalent left right)
    (shift : Nat) :
    StrictJointCylinderStageEquivalent
      (left.timeTranslate shift) (right.timeTranslate shift) := by
  rcases h with ⟨outer, hleft, hright, heq⟩
  refine ⟨outer + shift,
    Nat.add_le_add_right hleft shift,
    Nat.add_le_add_right hright shift, ?_⟩
  calc
    boxTransportStrictJointCylinderVector
        (Nat.add_le_add_right hleft shift)
        (timeTranslateStrictJointCylinderVector shift left.vector) =
      timeTranslateStrictJointCylinderVector shift
        (boxTransportStrictJointCylinderVector hleft left.vector) :=
      (timeTranslate_boxTransportStrictJointCylinderVector
        hleft shift left.vector).symm
    _ = timeTranslateStrictJointCylinderVector shift
        (boxTransportStrictJointCylinderVector hright right.vector) :=
      congrArg (timeTranslateStrictJointCylinderVector shift) heq
    _ = boxTransportStrictJointCylinderVector
        (Nat.add_le_add_right hright shift)
        (timeTranslateStrictJointCylinderVector shift right.vector) :=
      timeTranslate_boxTransportStrictJointCylinderVector
        hright shift right.vector

def strictJointCylinderStageSetoid : Setoid StrictJointCylinderStage where
  r := StrictJointCylinderStageEquivalent
  iseqv := strictJointCylinderStageEquivalent_equivalence

/-- The base-independent algebraic strict-cylinder carrier. -/
def StrictJointCylinderDirectLimit : Type :=
  Quotient strictJointCylinderStageSetoid

/-- Insert one finite-base presentation into the direct limit. -/
def StrictJointCylinderDirectLimit.embed
    (stage : StrictJointCylinderStage) : StrictJointCylinderDirectLimit :=
  Quotient.mk strictJointCylinderStageSetoid stage

/-- The descended geometric time action on the direct-limit carrier. -/
def StrictJointCylinderDirectLimit.timeTranslate
    (shift : Nat) :
    StrictJointCylinderDirectLimit -> StrictJointCylinderDirectLimit :=
  Quotient.lift
    (fun stage => StrictJointCylinderDirectLimit.embed
      (stage.timeTranslate shift))
    (fun _ _ h => Quotient.sound
      (strictJointCylinderStageEquivalent_timeTranslate h shift))

@[simp] theorem strictJointCylinderDirectLimit_timeTranslate_embed
    (shift : Nat) (stage : StrictJointCylinderStage) :
    StrictJointCylinderDirectLimit.timeTranslate shift
        (StrictJointCylinderDirectLimit.embed stage) =
      StrictJointCylinderDirectLimit.embed (stage.timeTranslate shift) := rfl

private theorem boxTransportStrictJointCylinderVector_of_eq
    {base outer : Nat} (hbase : base = outer)
    (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector (Nat.le_of_eq hbase) vector =
      rebaseStrictJointCylinderVector hbase vector := by
  subst outer
  calc
    boxTransportStrictJointCylinderVector (Nat.le_refl base) vector = vector :=
      boxTransportStrictJointCylinderVector_refl vector
    _ = rebaseStrictJointCylinderVector rfl vector := by rfl

/-- Zero time translation is the identity already at the direct-limit level. -/
theorem strictJointCylinderStage_timeTranslate_zero
    (stage : StrictJointCylinderStage) :
    StrictJointCylinderStageEquivalent (stage.timeTranslate 0) stage := by
  refine ⟨stage.base, Nat.le_refl _, Nat.le_refl _, ?_⟩
  change
    boxTransportStrictJointCylinderVector (Nat.le_refl stage.base)
        (timeTranslateStrictJointCylinderVector 0 stage.vector) =
      boxTransportStrictJointCylinderVector (Nat.le_refl stage.base)
        stage.vector
  rw [boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVector_refl]
  exact timeTranslateStrictJointCylinderVector_zero stage.vector

/-- The reassociated indexed action satisfies the additive law in the direct
limit. -/
theorem strictJointCylinderStage_timeTranslate_add
    (first second : Nat) (stage : StrictJointCylinderStage) :
    StrictJointCylinderStageEquivalent
      (stage.timeTranslate (first + second))
      ((stage.timeTranslate first).timeTranslate second) := by
  have hbase : (stage.base + first) + second =
      stage.base + (first + second) := Nat.add_assoc _ _ _
  refine ⟨stage.base + (first + second), Nat.le_refl _,
    Nat.le_of_eq hbase, ?_⟩
  change
    boxTransportStrictJointCylinderVector
        (Nat.le_refl (stage.base + (first + second)))
        (timeTranslateStrictJointCylinderVector
          (first + second) stage.vector) =
      boxTransportStrictJointCylinderVector (Nat.le_of_eq hbase)
        (timeTranslateStrictJointCylinderVector second
          (timeTranslateStrictJointCylinderVector first stage.vector))
  rw [boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVector_of_eq]
  exact (rebase_timeTranslateStrictJointCylinderVector_add
    first second stage.vector).symm

theorem StrictJointCylinderDirectLimit.timeTranslate_zero
    (vector : StrictJointCylinderDirectLimit) :
    StrictJointCylinderDirectLimit.timeTranslate 0 vector = vector := by
  refine Quotient.inductionOn vector (fun stage => ?_)
  exact Quotient.sound (strictJointCylinderStage_timeTranslate_zero stage)

theorem StrictJointCylinderDirectLimit.timeTranslate_add
    (first second : Nat) (vector : StrictJointCylinderDirectLimit) :
    StrictJointCylinderDirectLimit.timeTranslate (first + second) vector =
      StrictJointCylinderDirectLimit.timeTranslate second
        (StrictJointCylinderDirectLimit.timeTranslate first vector) := by
  refine Quotient.inductionOn vector (fun stage => ?_)
  exact Quotient.sound
    (strictJointCylinderStage_timeTranslate_add first second stage)

#print axioms strictJointCylinderStageEquivalent_trans
#print axioms strictJointCylinderStage_equivalent_transport
#print axioms strictJointCylinderStageEquivalent_timeTranslate
#print axioms StrictJointCylinderDirectLimit
#print axioms StrictJointCylinderDirectLimit.timeTranslate
#print axioms StrictJointCylinderDirectLimit.timeTranslate_zero
#print axioms StrictJointCylinderDirectLimit.timeTranslate_add

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
