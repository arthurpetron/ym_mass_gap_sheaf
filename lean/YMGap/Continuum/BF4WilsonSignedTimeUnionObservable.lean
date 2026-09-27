/-
# One ambient observable quotient over every finite spatial base

The quotient is by original all-test contextual equality at a common base.
Products, rational linear operations, inverse discrete time, reflection and
the original RC mean descend without selecting representatives from quotients.
The real conjugation is identity, distinct from time reflection. The supported
physical observable embedding is constructed separately on this same object.

No rational canonical functional, canonical OS root, continuum theory or
physical mass calibration is asserted.
-/

import YMGap.Continuum.BF4WilsonSignedTimeUnion

namespace YMGap.Continuum.BF4WilsonSignedTimeUnionObservable

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4WilsonSignedTimeContext
open YMGap.Continuum.BF4WilsonSignedTimeUnion
open YMGap.Continuum.ObservableMeasure (ObsAlg ObsHom)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

def contextSetoid : Setoid Stage where
  r := Related hw0 hw1 hsmall hd hs
  iseqv := ⟨related_refl hw0 hw1 hsmall hd hs,
    related_symm hw0 hw1 hsmall hd hs, related_trans hw0 hw1 hsmall hd hs⟩
def Observable : Type := Quotient (contextSetoid hw0 hw1 hsmall hd hs)
local notation "O" => Observable hw0 hw1 hsmall hd hs
def ofStage (x : Stage) : O := Quotient.mk (contextSetoid hw0 hw1 hsmall hd hs) x
def one : O := ofStage hw0 hw1 hsmall hd hs unitStage
def mul : O → O → O := Quotient.lift₂ (fun x y => ofStage hw0 hw1 hsmall hd hs (mulStage x y))
  (fun _ _ _ _ h k => Quotient.sound (related_mul hw0 hw1 hsmall hd hs h k))
def add : O → O → O := Quotient.lift₂ (fun x y => ofStage hw0 hw1 hsmall hd hs (addStage x y))
  (fun _ _ _ _ h k => Quotient.sound (related_add hw0 hw1 hsmall hd hs h k))
def smul (s : Q') : O → O := Quotient.lift (fun x => ofStage hw0 hw1 hsmall hd hs (smulStage s x))
  (fun _ _ h => Quotient.sound (related_smul hw0 hw1 hsmall hd hs s h))
def forwardTime (n : Nat) : O → O := Quotient.lift (fun x => ofStage hw0 hw1 hsmall hd hs (forwardStage n x))
  (fun _ _ h => Quotient.sound (related_forward hw0 hw1 hsmall hd hs n h))
def backwardTime (n : Nat) : O → O := Quotient.lift (fun x => ofStage hw0 hw1 hsmall hd hs (backwardStage n x))
  (fun _ _ h => Quotient.sound (related_backward hw0 hw1 hsmall hd hs n h))
def reflection : O → O := Quotient.lift (fun x => ofStage hw0 hw1 hsmall hd hs (reflectStage x))
  (fun _ _ h => Quotient.sound (related_reflect hw0 hw1 hsmall hd hs h))

theorem ofStage_eq_of_context {x y : Stage} {N : Nat} (hx : x.base ≤ N) (hy : y.base ≤ N)
    (h : ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy)) :
    ofStage hw0 hw1 hsmall hd hs x = ofStage hw0 hw1 hsmall hd hs y :=
  Quotient.sound ((related_iff_at hw0 hw1 hsmall hd hs x y hx hy).mpr h)

/-- Literal quotient equality under any witnessed enlargement, not a choice of base. -/
theorem ofStage_at (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    ofStage hw0 hw1 hsmall hd hs x =
      ofStage hw0 hw1 hsmall hd hs ⟨N,Nat.lt_of_lt_of_le x.positive hx,atBase x hx⟩ := by
  apply ofStage_eq_of_context hw0 hw1 hsmall hd hs hx (Nat.le_refl N)
  rw [atBase_self]
  exact context_refl hw0 hw1 hsmall hd hs _ _

theorem mul_comm (a b : O) : mul hw0 hw1 hsmall hd hs a b = mul hw0 hw1 hsmall hd hs b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  apply ofStage_eq_of_context hw0 hw1 hsmall hd hs
    (x := mulStage x y) (y := mulStage y x) (Nat.max_le.mpr ⟨hx,hy⟩) (Nat.max_le.mpr ⟨hy,hx⟩)
  rw [atBase_mul x y hx hy, atBase_mul y x hy hx]
  exact context_mul_comm hw0 hw1 hsmall hd hs _ _ _

theorem mul_assoc (a b c : O) :
    mul hw0 hw1 hsmall hd hs (mul hw0 hw1 hsmall hd hs a b) c =
      mul hw0 hw1 hsmall hd hs a (mul hw0 hw1 hsmall hd hs b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  let N := max x.base (max y.base z.base)
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  have hxy : (mulStage x y).base ≤ N := Nat.max_le.mpr ⟨hx,hy⟩
  have hyz : (mulStage y z).base ≤ N := Nat.max_le.mpr ⟨hy,hz⟩
  apply ofStage_eq_of_context hw0 hw1 hsmall hd hs
    (x := mulStage (mulStage x y) z) (y := mulStage x (mulStage y z))
    (Nat.max_le.mpr ⟨hxy,hz⟩) (Nat.max_le.mpr ⟨hx,hyz⟩)
  rw [atBase_mul (mulStage x y) z hxy hz, atBase_mul x (mulStage y z) hx hyz,
    atBase_mul x y hx hy, atBase_mul y z hy hz]
  exact context_mul_assoc hw0 hw1 hsmall hd hs _ _ _ _

theorem mul_one (a : O) : mul hw0 hw1 hsmall hd hs a (one hw0 hw1 hsmall hd hs) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  have hu : unitStage.base ≤ x.base := Nat.succ_le_of_lt x.positive
  apply ofStage_eq_of_context hw0 hw1 hsmall hd hs (x := mulStage x unitStage) (y := x)
    (Nat.max_le.mpr ⟨Nat.le_refl _,hu⟩) (Nat.le_refl _)
  rw [atBase_mul x unitStage (Nat.le_refl _) hu, atBase_unit]
  exact context_mul_one hw0 hw1 hsmall hd hs _ _

theorem one_mul (a : O) : mul hw0 hw1 hsmall hd hs (one hw0 hw1 hsmall hd hs) a = a :=
  (mul_comm hw0 hw1 hsmall hd hs _ _).trans (mul_one hw0 hw1 hsmall hd hs a)

theorem backward_forwardTime (n : Nat) (a : O) :
    backwardTime hw0 hw1 hsmall hd hs n (forwardTime hw0 hw1 hsmall hd hs n a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofStage hw0 hw1 hsmall hd hs ⟨x.base,x.positive,backward n (forward n x.expression)⟩ = _
  rw [backward_forward]
  rfl

theorem forward_backwardTime (n : Nat) (a : O) :
    forwardTime hw0 hw1 hsmall hd hs n (backwardTime hw0 hw1 hsmall hd hs n a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofStage hw0 hw1 hsmall hd hs ⟨x.base,x.positive,forward n (backward n x.expression)⟩ = _
  rw [forward_backward]
  rfl

theorem reflection_involutive (a : O) :
    reflection hw0 hw1 hsmall hd hs (reflection hw0 hw1 hsmall hd hs a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofStage hw0 hw1 hsmall hd hs ⟨x.base,x.positive,reflect (reflect x.expression)⟩ = _
  rw [reflect_reflect]
  rfl

theorem reflection_time_inverse (n : Nat) (a : O) :
    reflection hw0 hw1 hsmall hd hs (forwardTime hw0 hw1 hsmall hd hs n a) =
      backwardTime hw0 hw1 hsmall hd hs n (reflection hw0 hw1 hsmall hd hs a) := by
  refine Quotient.inductionOn a ?_
  intro x
  change ofStage hw0 hw1 hsmall hd hs ⟨x.base,x.positive,reflect (forward n x.expression)⟩ = _
  rw [reflect_forward]
  rfl

/-- Real conjugation is identity; time reflection remains a separate operation. -/
def observableAlg : ObsAlg where
  carrier := O
  one := one hw0 hw1 hsmall hd hs
  mul := mul hw0 hw1 hsmall hd hs
  star := id

theorem forward_mul (n : Nat) (a b : O) :
    forwardTime hw0 hw1 hsmall hd hs n (mul hw0 hw1 hsmall hd hs a b) =
      mul hw0 hw1 hsmall hd hs (forwardTime hw0 hw1 hsmall hd hs n a)
        (forwardTime hw0 hw1 hsmall hd hs n b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  have hx := Nat.le_max_left x.base y.base
  have hy := Nat.le_max_right x.base y.base
  change ofStage hw0 hw1 hsmall hd hs
      ⟨max x.base y.base,Nat.lt_of_lt_of_le x.positive hx,
        .mul (forward n (atBase x hx)) (forward n (atBase y hy))⟩ =
    ofStage hw0 hw1 hsmall hd hs
      ⟨max x.base y.base,Nat.lt_of_lt_of_le x.positive hx,
        .mul (atBase (forwardStage n x) hx) (atBase (forwardStage n y) hy)⟩
  rw [atBase_forward n x hx, atBase_forward n y hy]

theorem backward_mul (n : Nat) (a b : O) :
    backwardTime hw0 hw1 hsmall hd hs n (mul hw0 hw1 hsmall hd hs a b) =
      mul hw0 hw1 hsmall hd hs (backwardTime hw0 hw1 hsmall hd hs n a)
        (backwardTime hw0 hw1 hsmall hd hs n b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  have hx := Nat.le_max_left x.base y.base
  have hy := Nat.le_max_right x.base y.base
  change ofStage hw0 hw1 hsmall hd hs
      ⟨max x.base y.base,Nat.lt_of_lt_of_le x.positive hx,
        .mul (backward n (atBase x hx)) (backward n (atBase y hy))⟩ =
    ofStage hw0 hw1 hsmall hd hs
      ⟨max x.base y.base,Nat.lt_of_lt_of_le x.positive hx,
        .mul (atBase (backwardStage n x) hx) (atBase (backwardStage n y) hy)⟩
  rw [atBase_backward n x hx, atBase_backward n y hy]

theorem reflection_mul (a b : O) :
    reflection hw0 hw1 hsmall hd hs (mul hw0 hw1 hsmall hd hs a b) =
      mul hw0 hw1 hsmall hd hs (reflection hw0 hw1 hsmall hd hs a)
        (reflection hw0 hw1 hsmall hd hs b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  have hx := Nat.le_max_left x.base y.base
  have hy := Nat.le_max_right x.base y.base
  change ofStage hw0 hw1 hsmall hd hs
      ⟨max x.base y.base,Nat.lt_of_lt_of_le x.positive hx,
        .mul (reflect (atBase x hx)) (reflect (atBase y hy))⟩ =
    ofStage hw0 hw1 hsmall hd hs
      ⟨max x.base y.base,Nat.lt_of_lt_of_le x.positive hx,
        .mul (atBase (reflectStage x) hx) (atBase (reflectStage y) hy)⟩
  rw [atBase_reflect x hx, atBase_reflect y hy]

def forwardHom (n : Nat) : ObsHom (observableAlg hw0 hw1 hsmall hd hs) (observableAlg hw0 hw1 hsmall hd hs) where
  map := forwardTime hw0 hw1 hsmall hd hs n
  map_one := rfl
  map_mul := forward_mul hw0 hw1 hsmall hd hs n
  map_star := fun _ => rfl
def backwardHom (n : Nat) : ObsHom (observableAlg hw0 hw1 hsmall hd hs) (observableAlg hw0 hw1 hsmall hd hs) where
  map := backwardTime hw0 hw1 hsmall hd hs n
  map_one := rfl
  map_mul := backward_mul hw0 hw1 hsmall hd hs n
  map_star := fun _ => rfl
def reflectionHom : ObsHom (observableAlg hw0 hw1 hsmall hd hs) (observableAlg hw0 hw1 hsmall hd hs) where
  map := reflection hw0 hw1 hsmall hd hs
  map_one := rfl
  map_mul := reflection_mul hw0 hw1 hsmall hd hs
  map_star := fun _ => rfl

def meanRC : O → RC := Quotient.lift
  (fun x => Quotient.mk crealSetoid (stageMean hw0 hw1 hsmall hd hs x))
  (fun _ _ h => Quotient.sound (stageMean_congr hw0 hw1 hsmall hd hs h))

theorem meanRC_at (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    meanRC hw0 hw1 hsmall hd hs (ofStage hw0 hw1 hsmall hd hs x) =
      Quotient.mk crealSetoid (mean hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx)) :=
  Quotient.sound (stageMean_at hw0 hw1 hsmall hd hs x hx)

theorem meanRC_one : meanRC hw0 hw1 hsmall hd hs (one hw0 hw1 hsmall hd hs) =
    Quotient.mk crealSetoid (ofQ' 1) := Quotient.sound (mean_one hw0 hw1 hsmall hd hs (by decide : 0 < 1))

theorem meanRC_add (a b : O) :
    meanRC hw0 hw1 hsmall hd hs (add hw0 hw1 hsmall hd hs a b) =
      RCadd (meanRC hw0 hw1 hsmall hd hs a) (meanRC hw0 hw1 hsmall hd hs b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  apply Quotient.sound
  exact (mean_add hw0 hw1 hsmall hd hs _ _ _).trans
    (Equiv_add (stageMean_at hw0 hw1 hsmall hd hs x (Nat.le_max_left x.base y.base)).symm
      (stageMean_at hw0 hw1 hsmall hd hs y (Nat.le_max_right x.base y.base)).symm)

theorem meanRC_smul (s : Q') (a : O) :
    meanRC hw0 hw1 hsmall hd hs (smul hw0 hw1 hsmall hd hs s a) =
      RCmul (Quotient.mk crealSetoid (ofQ' s)) (meanRC hw0 hw1 hsmall hd hs a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_smul hw0 hw1 hsmall hd hs x.positive s x.expression)

theorem meanRC_forward (n : Nat) (a : O) :
    meanRC hw0 hw1 hsmall hd hs (forwardTime hw0 hw1 hsmall hd hs n a) = meanRC hw0 hw1 hsmall hd hs a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_forward hw0 hw1 hsmall hd hs x.positive n x.expression)
theorem meanRC_backward (n : Nat) (a : O) :
    meanRC hw0 hw1 hsmall hd hs (backwardTime hw0 hw1 hsmall hd hs n a) = meanRC hw0 hw1 hsmall hd hs a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_backward hw0 hw1 hsmall hd hs x.positive n x.expression)
theorem meanRC_reflection (a : O) :
    meanRC hw0 hw1 hsmall hd hs (reflection hw0 hw1 hsmall hd hs a) = meanRC hw0 hw1 hsmall hd hs a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (mean_reflect hw0 hw1 hsmall hd hs x.positive x.expression)

theorem meanRC_square_nonnegative (a : O) :
    RCnonneg (meanRC hw0 hw1 hsmall hd hs (mul hw0 hw1 hsmall hd hs a a)) := by
  refine Quotient.inductionOn a ?_
  intro x
  change leEv (ofQ' 0) (mean hw0 hw1 hsmall hd hs _
    (.mul (atBase x (Nat.le_max_left x.base x.base)) (atBase x (Nat.le_max_right x.base x.base))))
  exact mean_square_nonnegative hw0 hw1 hsmall hd hs _ _

end YMGap.Continuum.BF4WilsonSignedTimeUnionObservable

#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.contextSetoid
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.Observable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.ofStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.backwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.reflection
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.ofStage_eq_of_context
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.ofStage_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.mul_comm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.mul_assoc
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.mul_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.one_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.backward_forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.forward_backwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.reflection_involutive
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.reflection_time_inverse
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.observableAlg
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.forward_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.backward_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.reflection_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.forwardHom
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.backwardHom
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.reflectionHom
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_reflection
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionObservable.meanRC_square_nonnegative
