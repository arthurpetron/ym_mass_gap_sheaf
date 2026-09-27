/-
# Time-tested supported observables on the original Wilson carrier

The quotient uses the proved time-context relation, not the OS null relation.
It has a commutative associative unital product, descended rational linear
operations, and forward-time product endomorphisms. Its state map lands in
the SAME existing spatial-union completion and exactly intertwines its time.

The vacuum mean is normalized, stationary, rational-linear and nonnegative
on supported squares. It takes values in RC: no CReal representative is selected
from that quotient. This is a fixed-spacing real supported-observable object,
not a canonical reflected OS root or a continuum QFT observable algebra.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionContextLaws
import YMGap.Continuum.BF4WilsonSpatialUnionBilinear
import YMGap.Continuum.BF4WilsonSpatialUnionProductPositivity
import YMGap.Continuum.ObservableMeasure

namespace YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionProduct
open YMGap.Continuum.BF4WilsonSpatialUnionContextLaws
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
  (completedInner_add_left completedInner_smul_left)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm (completedInner_time_balance)
open YMGap.Continuum.ObservableMeasure (ObsAlg ObsHom)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

def contextSetoid : Setoid Stage where
  r := TimeContextEq hw0 hw1 hsmall hd hs
  iseqv := ⟨timeContext_refl hw0 hw1 hsmall hd hs,
    timeContext_symm hw0 hw1 hsmall hd hs,
    timeContext_trans hw0 hw1 hsmall hd hs⟩

def Observable : Type := Quotient (contextSetoid hw0 hw1 hsmall hd hs)

local notation "O" => Observable hw0 hw1 hsmall hd hs

def ofStage (x : Stage) : O := Quotient.mk (contextSetoid hw0 hw1 hsmall hd hs) x

def one : O := ofStage hw0 hw1 hsmall hd hs unitStage

def mul : O → O → O :=
  Quotient.lift₂ (fun a b => ofStage hw0 hw1 hsmall hd hs (productStage a b))
    (fun _ _ _ _ ha hb => Quotient.sound (timeContext_product hw0 hw1 hsmall hd hs ha hb))

def add : O → O → O :=
  Quotient.lift₂ (fun a b => ofStage hw0 hw1 hsmall hd hs (sumStage a b))
    (fun _ _ _ _ ha hb => Quotient.sound (timeContext_sum hw0 hw1 hsmall hd hs ha hb))

def smul (c : Q') : O → O :=
  Quotient.lift (fun a => ofStage hw0 hw1 hsmall hd hs (smulStage c a))
    (fun _ _ h => Quotient.sound (timeContext_smul hw0 hw1 hsmall hd hs c h))

def forward (n : Nat) : O → O :=
  Quotient.lift (fun a => ofStage hw0 hw1 hsmall hd hs (time n a))
    (fun _ _ h => Quotient.sound (timeContext_time hw0 hw1 hsmall hd hs n h))

theorem mul_comm (a b : O) : mul hw0 hw1 hsmall hd hs a b = mul hw0 hw1 hsmall hd hs b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (context_product_comm hw0 hw1 hsmall hd hs x y)

theorem mul_assoc (a b c : O) :
    mul hw0 hw1 hsmall hd hs (mul hw0 hw1 hsmall hd hs a b) c =
      mul hw0 hw1 hsmall hd hs a (mul hw0 hw1 hsmall hd hs b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (context_product_assoc hw0 hw1 hsmall hd hs x y z)

theorem mul_one (a : O) : mul hw0 hw1 hsmall hd hs a (one hw0 hw1 hsmall hd hs) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (context_product_unit_right hw0 hw1 hsmall hd hs x)

theorem one_mul (a : O) : mul hw0 hw1 hsmall hd hs (one hw0 hw1 hsmall hd hs) a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (context_product_unit_left hw0 hw1 hsmall hd hs x)

theorem mul_add (a b c : O) :
    mul hw0 hw1 hsmall hd hs a (add hw0 hw1 hsmall hd hs b c) =
      add hw0 hw1 hsmall hd hs (mul hw0 hw1 hsmall hd hs a b)
        (mul hw0 hw1 hsmall hd hs a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (context_product_sum_right hw0 hw1 hsmall hd hs x y z)

theorem mul_smul_left (c : Q') (a b : O) :
    mul hw0 hw1 hsmall hd hs (smul hw0 hw1 hsmall hd hs c a) b =
      smul hw0 hw1 hsmall hd hs c (mul hw0 hw1 hsmall hd hs a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (context_product_smul_left hw0 hw1 hsmall hd hs c x y)

theorem forward_one (n : Nat) :
    forward hw0 hw1 hsmall hd hs n (one hw0 hw1 hsmall hd hs) = one hw0 hw1 hsmall hd hs :=
  Quotient.sound (context_time_unit hw0 hw1 hsmall hd hs n)

theorem forward_mul (n : Nat) (a b : O) :
    forward hw0 hw1 hsmall hd hs n (mul hw0 hw1 hsmall hd hs a b) =
      mul hw0 hw1 hsmall hd hs (forward hw0 hw1 hsmall hd hs n a)
        (forward hw0 hw1 hsmall hd hs n b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact congrArg (ofStage hw0 hw1 hsmall hd hs) (time_product n x y)

theorem forward_zero (a : O) : forward hw0 hw1 hsmall hd hs 0 a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact congrArg (ofStage hw0 hw1 hsmall hd hs) (time_zero x)

theorem forward_sum (n : Nat) (a b : O) :
    forward hw0 hw1 hsmall hd hs n (add hw0 hw1 hsmall hd hs a b) =
      add hw0 hw1 hsmall hd hs (forward hw0 hw1 hsmall hd hs n a)
        (forward hw0 hw1 hsmall hd hs n b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact congrArg (ofStage hw0 hw1 hsmall hd hs) (time_sum n x y)

theorem forward_smul (n : Nat) (c : Q') (a : O) :
    forward hw0 hw1 hsmall hd hs n (smul hw0 hw1 hsmall hd hs c a) =
      smul hw0 hw1 hsmall hd hs c (forward hw0 hw1 hsmall hd hs n a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact congrArg (ofStage hw0 hw1 hsmall hd hs) (time_smul n c x)

theorem forward_add (m n : Nat) (a : O) :
    forward hw0 hw1 hsmall hd hs (m+n) a =
      forward hw0 hw1 hsmall hd hs m (forward hw0 hw1 hsmall hd hs n a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact congrArg (ofStage hw0 hw1 hsmall hd hs) (time_add m n x)

/-- Minimal observable interface on the real Wilson syntax. Its star is
identity, NOT time reflection; product laws are proved above separately. -/
def observableAlg : ObsAlg where
  carrier := O
  one := one hw0 hw1 hsmall hd hs
  mul := mul hw0 hw1 hsmall hd hs
  star := id

/-- The existing unital product-hom interface is concretely inhabited. -/
def forwardHom (n : Nat) :
    ObsHom (observableAlg hw0 hw1 hsmall hd hs) (observableAlg hw0 hw1 hsmall hd hs) where
  map := forward hw0 hw1 hsmall hd hs n
  map_one := forward_one hw0 hw1 hsmall hd hs n
  map_mul := forward_mul hw0 hw1 hsmall hd hs n
  map_star := fun _ => rfl

/-- A well-defined map to the original physical completion; not assumed
injective and not used to define multiplication on completed states. -/
def state : O → UnionCompletion hw0 hw1 hsmall hd hs :=
  Quotient.lift (embedStage hw0 hw1 hsmall hd hs)
    (fun _ _ h => timeContext_embed hw0 hw1 hsmall hd hs h)

theorem state_ofStage (x : Stage) :
    state hw0 hw1 hsmall hd hs (ofStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs x := rfl

theorem state_one :
    state hw0 hw1 hsmall hd hs (one hw0 hw1 hsmall hd hs) =
      completedUnit hw0 hw1 hsmall hd hs := rfl

theorem state_forward (n : Nat) (a : O) :
    state hw0 hw1 hsmall hd hs (forward hw0 hw1 hsmall hd hs n a) =
      completedTime hw0 hw1 hsmall hd hs n (state hw0 hw1 hsmall hd hs a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact (completedTime_embedStage hw0 hw1 hsmall hd hs n x).symm

theorem state_add (a b : O) :
    state hw0 hw1 hsmall hd hs (add hw0 hw1 hsmall hd hs a b) =
      completedAdd hw0 hw1 hsmall hd hs (state hw0 hw1 hsmall hd hs a)
        (state hw0 hw1 hsmall hd hs b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact (completedAdd_embedStage hw0 hw1 hsmall hd hs x y).symm

theorem state_smul (c : Q') (a : O) :
    state hw0 hw1 hsmall hd hs (smul hw0 hw1 hsmall hd hs c a) =
      completedSmul hw0 hw1 hsmall hd hs c (state hw0 hw1 hsmall hd hs a) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact (completedSmul_embedStage hw0 hw1 hsmall hd hs c x).symm

/-- Quotient-valued expectation. This selects no CReal representative. -/
def vacuumMean (a : O) : RC :=
  completedInner hw0 hw1 hsmall hd hs (state hw0 hw1 hsmall hd hs a)
    (completedUnit hw0 hw1 hsmall hd hs)

theorem vacuumMean_ofStage (x : Stage) :
    vacuumMean hw0 hw1 hsmall hd hs (ofStage hw0 hw1 hsmall hd hs x) =
      Quotient.mk crealSetoid (pairing hw0 hw1 hsmall hd hs x unitStage) :=
  completedInner_embedStage hw0 hw1 hsmall hd hs x unitStage

theorem vacuumMean_one :
    vacuumMean hw0 hw1 hsmall hd hs (one hw0 hw1 hsmall hd hs) =
      Quotient.mk crealSetoid cone := completedUnit_norm_one hw0 hw1 hsmall hd hs

theorem vacuumMean_add (a b : O) :
    vacuumMean hw0 hw1 hsmall hd hs (add hw0 hw1 hsmall hd hs a b) =
      RCadd (vacuumMean hw0 hw1 hsmall hd hs a) (vacuumMean hw0 hw1 hsmall hd hs b) := by
  unfold vacuumMean
  rw [state_add, completedInner_add_left]

theorem vacuumMean_smul (c : Q') (a : O) :
    vacuumMean hw0 hw1 hsmall hd hs (smul hw0 hw1 hsmall hd hs c a) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (vacuumMean hw0 hw1 hsmall hd hs a) := by
  unfold vacuumMean
  rw [state_smul, completedInner_smul_left]

/-- Stationarity uses the actual self-adjoint time and fixed vacuum. -/
theorem vacuumMean_forward (n : Nat) (a : O) :
    vacuumMean hw0 hw1 hsmall hd hs (forward hw0 hw1 hsmall hd hs n a) =
      vacuumMean hw0 hw1 hsmall hd hs a := by
  unfold vacuumMean
  rw [state_forward, completedInner_time_balance, completedUnit_fixed]

/-- Ordinary square positivity, inherited from the original finite-window
action and its spatial limit, not from a reflected-form diagonal shortcut. -/
theorem vacuumMean_square_nonnegative (a : O) :
    RCnonneg (vacuumMean hw0 hw1 hsmall hd hs (mul hw0 hw1 hsmall hd hs a a)) := by
  refine Quotient.inductionOn a ?_
  intro x
  exact BF4WilsonSpatialUnionProductPositivity.product_square_vacuum_nonnegative
    hw0 hw1 hsmall hd hs x

end YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.contextSetoid
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.Observable
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.ofStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.mul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.smul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.mul_comm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.mul_assoc
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.mul_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.one_mul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.mul_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.mul_smul_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward_mul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward_sum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward_smul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forward_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.observableAlg
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.forwardHom
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.state
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.state_ofStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.state_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.state_forward
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.state_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.state_smul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean_ofStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean_smul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean_forward
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionObservableQuotient.vacuumMean_square_nonnegative
