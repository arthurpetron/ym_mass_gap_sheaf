/-
# Original ambient Wilson observables with inverse time and reflection

The quotient is by equality against all signed-time multipliers of the
original mean, not by the OS null relation. Product congruence and inverse
time/reflection congruence are proved before the operations are descended.
The product is commutative, associative and unital. The original normalized
positive expectation descends to RC without choosing CReal representatives.

The existing supported stage pairings and completed dense transfer
correlators are exactly this quotient's reflected mean. This constructs a
fixed-base ambient observable object, not a global-base quotient, a full
rational module law suite, a canonical rational OS root, or continuum QFT.
Real conjugation is identity; time reflection is the distinct constructed map.
-/

import YMGap.Continuum.BF4WilsonSignedTimeContext
import YMGap.Continuum.ObservableMeasure

namespace YMGap.Continuum.BF4WilsonSignedTimeObservable

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4WilsonSignedTimeContext
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression intrinsicForm)
open YMGap.Continuum.BF4WilsonSpatialUnion (Stage atBase)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (embedStage completedTime)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.ObservableMeasure (ObsAlg ObsHom)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0 < base)

def contextSetoid : Setoid (Expression base) where
  r := ContextEq hw0 hw1 hsmall hd hs hb
  iseqv := ⟨context_refl hw0 hw1 hsmall hd hs hb,
    context_symm hw0 hw1 hsmall hd hs hb, context_trans hw0 hw1 hsmall hd hs hb⟩

def Observable : Type := Quotient (contextSetoid hw0 hw1 hsmall hd hs hb)

local notation "O" => Observable hw0 hw1 hsmall hd hs hb

def ofExpression (e : Expression base) : O := Quotient.mk (contextSetoid hw0 hw1 hsmall hd hs hb) e

def one : O := ofExpression hw0 hw1 hsmall hd hs hb .one

def mul : O → O → O :=
  Quotient.lift₂ (fun a b => ofExpression hw0 hw1 hsmall hd hs hb (.mul a b))
    (fun _ _ _ _ ha hb' => Quotient.sound (context_mul hw0 hw1 hsmall hd hs hb ha hb'))

def add : O → O → O :=
  Quotient.lift₂ (fun a b => ofExpression hw0 hw1 hsmall hd hs hb (.add a b))
    (fun _ _ _ _ ha hb' => Quotient.sound (context_add hw0 hw1 hsmall hd hs hb ha hb'))

def smul (s : Q') : O → O :=
  Quotient.lift (fun a => ofExpression hw0 hw1 hsmall hd hs hb (.smul s a))
    (fun _ _ h => Quotient.sound (context_smul hw0 hw1 hsmall hd hs hb s h))

def forwardTime (n : Nat) : O → O :=
  Quotient.lift (fun a => ofExpression hw0 hw1 hsmall hd hs hb (forward n a))
    (fun _ _ h => Quotient.sound (context_forward hw0 hw1 hsmall hd hs hb n h))

def backwardTime (n : Nat) : O → O :=
  Quotient.lift (fun a => ofExpression hw0 hw1 hsmall hd hs hb (backward n a))
    (fun _ _ h => Quotient.sound (context_backward hw0 hw1 hsmall hd hs hb n h))

def reflection : O → O :=
  Quotient.lift (fun a => ofExpression hw0 hw1 hsmall hd hs hb (reflect a))
    (fun _ _ h => Quotient.sound (context_reflect hw0 hw1 hsmall hd hs hb h))

theorem mul_comm (a b : O) : mul hw0 hw1 hsmall hd hs hb a b = mul hw0 hw1 hsmall hd hs hb b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (context_mul_comm hw0 hw1 hsmall hd hs hb x y)

theorem mul_assoc (a b c : O) :
    mul hw0 hw1 hsmall hd hs hb (mul hw0 hw1 hsmall hd hs hb a b) c =
      mul hw0 hw1 hsmall hd hs hb a (mul hw0 hw1 hsmall hd hs hb b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (context_mul_assoc hw0 hw1 hsmall hd hs hb x y z)

theorem mul_one (a : O) : mul hw0 hw1 hsmall hd hs hb a (one hw0 hw1 hsmall hd hs hb) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (context_mul_one hw0 hw1 hsmall hd hs hb x)

theorem one_mul (a : O) : mul hw0 hw1 hsmall hd hs hb (one hw0 hw1 hsmall hd hs hb) a = a := by
  rw [mul_comm, mul_one]

theorem add_comm (a b : O) : add hw0 hw1 hsmall hd hs hb a b = add hw0 hw1 hsmall hd hs hb b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (context_add_comm hw0 hw1 hsmall hd hs hb x y)

theorem add_assoc (a b c : O) :
    add hw0 hw1 hsmall hd hs hb (add hw0 hw1 hsmall hd hs hb a b) c =
      add hw0 hw1 hsmall hd hs hb a (add hw0 hw1 hsmall hd hs hb b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (context_add_assoc hw0 hw1 hsmall hd hs hb x y z)

theorem mul_add (a b c : O) :
    mul hw0 hw1 hsmall hd hs hb a (add hw0 hw1 hsmall hd hs hb b c) =
      add hw0 hw1 hsmall hd hs hb (mul hw0 hw1 hsmall hd hs hb a b) (mul hw0 hw1 hsmall hd hs hb a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (context_mul_add hw0 hw1 hsmall hd hs hb x y z)

theorem smul_mul (s : Q') (a b : O) :
    mul hw0 hw1 hsmall hd hs hb (smul hw0 hw1 hsmall hd hs hb s a) b =
      smul hw0 hw1 hsmall hd hs hb s (mul hw0 hw1 hsmall hd hs hb a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (context_smul_mul hw0 hw1 hsmall hd hs hb s x y)

theorem backward_forwardTime (n : Nat) (a : O) :
    backwardTime hw0 hw1 hsmall hd hs hb n (forwardTime hw0 hw1 hsmall hd hs hb n a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofExpression hw0 hw1 hsmall hd hs hb (backward n (forward n x)) = ofExpression hw0 hw1 hsmall hd hs hb x
  rw [backward_forward]

theorem forward_backwardTime (n : Nat) (a : O) :
    forwardTime hw0 hw1 hsmall hd hs hb n (backwardTime hw0 hw1 hsmall hd hs hb n a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofExpression hw0 hw1 hsmall hd hs hb (forward n (backward n x)) = ofExpression hw0 hw1 hsmall hd hs hb x
  rw [forward_backward]

theorem reflection_involutive (a : O) :
    reflection hw0 hw1 hsmall hd hs hb (reflection hw0 hw1 hsmall hd hs hb a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofExpression hw0 hw1 hsmall hd hs hb (reflect (reflect x)) = ofExpression hw0 hw1 hsmall hd hs hb x
  rw [reflect_reflect]

theorem reflection_time_inverse (n : Nat) (a : O) :
    reflection hw0 hw1 hsmall hd hs hb
      (forwardTime hw0 hw1 hsmall hd hs hb n (reflection hw0 hw1 hsmall hd hs hb a)) =
      backwardTime hw0 hw1 hsmall hd hs hb n a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofExpression hw0 hw1 hsmall hd hs hb (reflect (forward n (reflect x))) =
    ofExpression hw0 hw1 hsmall hd hs hb (backward n x)
  rw [reflect_forward, reflect_reflect]

/-- Minimal real observable-star data, with the product laws proved above.
The identity star is real conjugation, not the distinct `reflection` map. -/
def observableAlg : ObsAlg where
  carrier := O
  one := one hw0 hw1 hsmall hd hs hb
  mul := mul hw0 hw1 hsmall hd hs hb
  star := id

def forwardHom (n : Nat) : ObsHom (observableAlg hw0 hw1 hsmall hd hs hb)
    (observableAlg hw0 hw1 hsmall hd hs hb) where
  map := forwardTime hw0 hw1 hsmall hd hs hb n
  map_one := rfl
  map_mul := fun a b => Quotient.inductionOn₂ a b (fun _ _ => rfl)
  map_star := fun _ => rfl

def backwardHom (n : Nat) : ObsHom (observableAlg hw0 hw1 hsmall hd hs hb)
    (observableAlg hw0 hw1 hsmall hd hs hb) where
  map := backwardTime hw0 hw1 hsmall hd hs hb n
  map_one := rfl
  map_mul := fun a b => Quotient.inductionOn₂ a b (fun _ _ => rfl)
  map_star := fun _ => rfl

def reflectionHom : ObsHom (observableAlg hw0 hw1 hsmall hd hs hb)
    (observableAlg hw0 hw1 hsmall hd hs hb) where
  map := reflection hw0 hw1 hsmall hd hs hb
  map_one := rfl
  map_mul := fun a b => Quotient.inductionOn₂ a b (fun _ _ => rfl)
  map_star := fun _ => rfl

/-- The original mean's RC class; no representative is selected from this quotient. -/
def meanRC : O → RC :=
  Quotient.lift (fun a => Quotient.mk crealSetoid (mean hw0 hw1 hsmall hd hs hb a))
    (fun _ _ h => Quotient.sound (context_mean hw0 hw1 hsmall hd hs hb h))

theorem meanRC_one : meanRC hw0 hw1 hsmall hd hs hb (one hw0 hw1 hsmall hd hs hb) =
    Quotient.mk crealSetoid (ofQ' 1) := Quotient.sound (mean_one hw0 hw1 hsmall hd hs hb)

theorem meanRC_add (a b : O) :
    meanRC hw0 hw1 hsmall hd hs hb (add hw0 hw1 hsmall hd hs hb a b) =
      RCadd (meanRC hw0 hw1 hsmall hd hs hb a) (meanRC hw0 hw1 hsmall hd hs hb b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (mean_add hw0 hw1 hsmall hd hs hb x y)

theorem meanRC_smul (s : Q') (a : O) :
    meanRC hw0 hw1 hsmall hd hs hb (smul hw0 hw1 hsmall hd hs hb s a) =
      RCmul (Quotient.mk crealSetoid (ofQ' s)) (meanRC hw0 hw1 hsmall hd hs hb a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_smul hw0 hw1 hsmall hd hs hb s x)

theorem meanRC_forward (n : Nat) (a : O) :
    meanRC hw0 hw1 hsmall hd hs hb (forwardTime hw0 hw1 hsmall hd hs hb n a) =
      meanRC hw0 hw1 hsmall hd hs hb a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_forward hw0 hw1 hsmall hd hs hb n x)

theorem meanRC_backward (n : Nat) (a : O) :
    meanRC hw0 hw1 hsmall hd hs hb (backwardTime hw0 hw1 hsmall hd hs hb n a) =
      meanRC hw0 hw1 hsmall hd hs hb a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_backward hw0 hw1 hsmall hd hs hb n x)

theorem meanRC_reflection (a : O) :
    meanRC hw0 hw1 hsmall hd hs hb (reflection hw0 hw1 hsmall hd hs hb a) =
      meanRC hw0 hw1 hsmall hd hs hb a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_reflect hw0 hw1 hsmall hd hs hb x)

theorem meanRC_square_nonnegative (a : O) :
    RCnonneg (meanRC hw0 hw1 hsmall hd hs hb (mul hw0 hw1 hsmall hd hs hb a a)) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact mean_square_nonnegative hw0 hw1 hsmall hd hs hb x

/-- The actual quotient reflected mean on two original supported observables. -/
theorem reflectedMean_intrinsic (x y : IntrinsicExpression base) :
    meanRC hw0 hw1 hsmall hd hs hb (mul hw0 hw1 hsmall hd hs hb
      (reflection hw0 hw1 hsmall hd hs hb (ofExpression hw0 hw1 hsmall hd hs hb (fromIntrinsic x)))
      (ofExpression hw0 hw1 hsmall hd hs hb (fromIntrinsic y))) =
      Quotient.mk crealSetoid (intrinsicForm hw0 hw1 hsmall hd hs hb x y) :=
  Quotient.sound (mean_reflected_intrinsic hw0 hw1 hsmall hd hs hb x y)

/-- The current completed dense correlator uses these SAME quotient operations.
The common finite base is computed from the two original stages. -/
theorem completedTime_as_observable_mean (n : Nat) (x y : Stage) :
    completedInner hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (completedTime hw0 hw1 hsmall hd hs n (embedStage hw0 hw1 hsmall hd hs y)) =
      let hN := Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base)
      meanRC hw0 hw1 hsmall hd hs hN (mul hw0 hw1 hsmall hd hs hN
        (reflection hw0 hw1 hsmall hd hs hN
          (ofExpression hw0 hw1 hsmall hd hs hN (fromIntrinsic (atBase x (Nat.le_max_left _ _)))))
        (forwardTime hw0 hw1 hsmall hd hs hN n
          (ofExpression hw0 hw1 hsmall hd hs hN (fromIntrinsic (atBase y (Nat.le_max_right _ _)))))) :=
  completedTime_correlator_as_mean hw0 hw1 hsmall hd hs n x y

end YMGap.Continuum.BF4WilsonSignedTimeObservable

#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.contextSetoid
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.Observable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.ofExpression
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.backwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.reflection
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.mul_comm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.mul_assoc
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.mul_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.one_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.add_comm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.add_assoc
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.mul_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.smul_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.backward_forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.forward_backwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.reflection_involutive
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.reflection_time_inverse
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.observableAlg
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.forwardHom
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.backwardHom
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.reflectionHom
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_reflection
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.meanRC_square_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.reflectedMean_intrinsic
#print axioms YMGap.Continuum.BF4WilsonSignedTimeObservable.completedTime_as_observable_mean
