/-
# A represented linear sector of the original Wilson time range

States retain an explicit `RangeLimit` witness for the original completed
time operator.  Equality compares only underlying completed vectors; the
witness is never quotiented away.  Cauchy limits are computed on the existing
original completion and their range witnesses are propagated by its proved
closedness.  This is not an OS or physical-sector identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear

namespace YMGap.Continuum.BF4WilsonAllNomeTimeSector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completedRealSmul)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
  (representedLimit representative representative_pin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- An original completed state together with supplied data witnessing that
it is a limit of original `T(1)` images. -/
structure State where
  val : V
  range : RangeLimit hw0 hw1 val

/-- Witnesses remain stored in `State`; this setoid compares its image only. -/
def stateSetoid : Setoid (State hw0 hw1 (width := width)) where
  r x y := x.val = y.val
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Construct an element from an original represented input. -/
def fromTime (X : (D).Cauchy) : State hw0 hw1 (width := width) where
  val := T 1 (Class X)
  range := BF4WilsonAllNomeTimeRangeClosure.fromTime hw0 hw1 X

/-- Zero, addition, negation, and constructive-real scaling use the already
checked operations on explicit original range witnesses. -/
def zero : State hw0 hw1 (width := width) where
  val := completedZero hw0 hw1 width
  range := BF4WilsonAllNomeTimeRangeLinear.zero hw0 hw1

def add (x y : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) where
  val := completedAdd hw0 hw1 x.val y.val
  range := BF4WilsonAllNomeTimeRangeLinear.add hw0 hw1 x.range y.range

def negate (x : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) where
  val := completedNeg hw0 hw1 x.val
  range := BF4WilsonAllNomeTimeRangeLinear.negate hw0 hw1 x.range

def realSmul (s : CReal) (cs : QCauchy s.approx)
    (x : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) where
  val := completedRealSmul hw0 hw1 s cs x.val
  range := BF4WilsonAllNomeTimeRangeLinear.realSmul hw0 hw1 s cs x.range

/-- A state-valued Cauchy sequence, with its original completed-distance
modulus supplied explicitly. -/
structure CauchySequence where
  seq : Nat → State hw0 hw1 (width := width)
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ m n,
    modulus e ≤ m → modulus e ≤ n →
      RCle (dist (seq m).val (seq n).val) (rat e)

/-- Represent each state using its own supplied range witness. -/
def representedRows (C : CauchySequence hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => representative hw0 hw1 (C.seq n).range
  modulus := C.modulus
  isCauchy := by
    intro e he m n hm hn
    change RCle (dist (Class (representative hw0 hw1 (C.seq m).range))
      (Class (representative hw0 hw1 (C.seq n).range))) (rat e)
    rw [representative_pin, representative_pin]
    exact C.bound e he m n hm hn

theorem representedRows_point (C : CauchySequence hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (representedRows hw0 hw1 C) n = (C.seq n).val :=
  representative_pin hw0 hw1 (C.seq n).range

/-- The computed original-carrier limit, with its propagated range witness. -/
def limit (C : CauchySequence hw0 hw1 (width := width)) :
    State hw0 hw1 (width := width) where
  val := BF4WilsonAllNomeCauchyRows.limit hw0 hw1 (representedRows hw0 hw1 C)
  range := representedLimit hw0 hw1 (representedRows hw0 hw1 C)
    (fun n => (representedRows_point hw0 hw1 C n).symm ▸ (C.seq n).range)

/-- The existing completion diagonal consumes the outer modulus at e/16,
not at e. Preserve this loss explicitly in the returned convergence data. -/
def limitRate (C : CauchySequence hw0 hw1 (width := width)) : Q' → Nat :=
  BF4WilsonAllNomeCauchyRows.limitRate hw0 hw1 (representedRows hw0 hw1 C)

/-- The supplied outer modulus controls convergence to the state-sector limit. -/
theorem limit_bound (C : CauchySequence hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (n : Nat) (hn : limitRate hw0 hw1 C e ≤ n) :
    RCle (dist (C.seq n).val (limit hw0 hw1 C).val) (rat e) := by
  have h := BF4WilsonAllNomeCauchyRows.limit_bound hw0 hw1
    (representedRows hw0 hw1 C) e he n hn
  rw [representedRows_point] at h
  exact h

/-- Uniqueness is stated only for the underlying original completed vector. -/
theorem limit_unique (C : CauchySequence hw0 hw1 (width := width))
    (z : V) (rate : Q' → Nat)
    (h : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (dist (C.seq n).val z) (rat e)) :
    (limit hw0 hw1 C).val = z := by
  apply BF4WilsonAllNomeCauchyRows.limit_unique hw0 hw1
    (representedRows hw0 hw1 C) z rate
  intro e he n hn
  rw [representedRows_point]
  exact h e he n hn

/-- State and its explicit all-tail convergence modulus, preserving the
original range witness in the returned state. -/
def limitCertificate (C : CauchySequence hw0 hw1 (width := width)) :
    Σ' x : State hw0 hw1 (width := width), Σ' rate : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
        RCle (dist (C.seq n).val x.val) (rat e) :=
  ⟨limit hw0 hw1 C, limitRate hw0 hw1 C, limit_bound hw0 hw1 C⟩

#print axioms stateSetoid
#print axioms fromTime
#print axioms zero
#print axioms add
#print axioms negate
#print axioms realSmul
#print axioms representedRows
#print axioms representedRows_point
#print axioms limit
#print axioms limitRate
#print axioms limit_bound
#print axioms limit_unique
#print axioms limitCertificate

end YMGap.Continuum.BF4WilsonAllNomeTimeSector
