/-
# Commuting Wilson observables on the SAME all-nome complex carrier

Each existing real time-zero Wilson multiplier acts componentwise on the
already constructed complexification. It is complex-linear with supplied
scalar moduli, symmetric in the actual sesquilinear inner product, and has
the same spin-only squared-norm cap. Equal-time multipliers commute on every
state. The vacuum-created fundamental state and its discrete-time correlation
remain pinned to the original loop and original lag moment.

These are fixed-width, fixed-spacing Wilson observable laws for every
rational nome 0<w<1. They do not construct continuous physical time, continuum
spacelike locality, full QFT, or a useful signed scaling estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeZeroCommutation
import YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum
import YMGap.Continuum.BF4WilsonAllNomeComplexGap

namespace YMGap.Continuum.BF4WilsonAllNomeComplexObservables

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroCommutation
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum
open YMGap.Continuum.BF4WilsonAllNomeComplexification
open YMGap.Continuum.BF4WilsonAllNomeComplexGap (complexUnit)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "M" => completedMultiply hw0 hw1
local notation "I" => inner hw0 hw1 width
local notation "E" => embedReal hw0 hw1 width
local notation "CT" => complexTime hw0 hw1 width

/-- This acts on the existing complexification, not a new observable carrier. -/
def complexMultiply (L : SourceLoop width) (spin : Nat) (x : VC) : VC :=
  (M L spin x.1, M L spin x.2)

local notation "CM" => complexMultiply hw0 hw1

theorem complexMultiply_embedReal (L : SourceLoop width) (spin : Nat) (x : V) :
    CM L spin (E x) = E (M L spin x) := by
  simp only [complexMultiply, embedReal, completedMultiply_zero]

theorem complexMultiply_zero (L : SourceLoop width) (spin : Nat) :
    CM L spin (complexZero hw0 hw1 width) = complexZero hw0 hw1 width := by
  simp only [complexMultiply, complexZero, completedMultiply_zero]

theorem complexMultiply_add (L : SourceLoop width) (spin : Nat) (x y : VC) :
    CM L spin (complexAdd hw0 hw1 width x y) =
      complexAdd hw0 hw1 width (CM L spin x) (CM L spin y) := by
  simp only [complexMultiply, complexAdd, completedMultiply_add]

private theorem multiplier_sub (L : SourceLoop width) (spin : Nat) (x y : V) :
    M L spin (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (M L spin x) (M L spin y) := by
  simp only [completedSub, completedNeg, completedMultiply_add, completedMultiply_smul]

/-- Complex linearity keeps both supplied constructive-real moduli. -/
theorem complexMultiply_smul (L : SourceLoop width) (spin : Nat)
    (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : VC) :
    CM L spin (complexSmul hw0 hw1 width s t cs ct x) =
      complexSmul hw0 hw1 width s t cs ct (CM L spin x) := by
  simp only [complexMultiply, complexSmul, multiplier_sub, completedMultiply_add,
    completedMultiply_realSmul]

theorem inner_multiplier_balance (L : SourceLoop width) (spin : Nat) (x y : VC) :
    I (CM L spin x) y = I x (CM L spin y) := by
  simp only [inner, complexMultiply, completedInner_multiplier_balance]

/-- The actual complex reflected squared norm has the SAME spin-only cap. -/
theorem inner_multiplier_bound (L : SourceLoop width) (spin : Nat) (x : VC) :
    RCle (I (CM L spin x) (CM L spin x)).1
      (RCscale (characterBound spin) (I x x).1) := by
  have h1 := completedInner_multiplier_bound hw0 hw1 L spin x.1
  have h2 := completedInner_multiplier_bound hw0 hw1 L spin x.2
  change RCle _ (RCscale (characterBound spin) (completedInner hw0 hw1 x.1 x.1)) at h1
  change RCle _ (RCscale (characterBound spin) (completedInner hw0 hw1 x.2 x.2)) at h2
  have h := RCadd_le_add h1 h2
  rw [← RCscale_RCadd] at h
  exact h

/-- Equal-time commutation holds on every state of the existing complex carrier. -/
theorem complexMultiply_comm (L R : SourceLoop width) (i j : Nat) (x : VC) :
    CM L i (CM R j x) = CM R j (CM L i x) := by
  simp only [complexMultiply, completedMultiply_comm hw0 hw1 L R i j]

theorem inner_multiplier_product_balance (L R : SourceLoop width) (i j : Nat)
    (x y : VC) : I (CM L i (CM R j x)) y = I x (CM L i (CM R j y)) := by
  rw [inner_multiplier_balance, inner_multiplier_balance,
    complexMultiply_comm hw0 hw1 R L j i y]

/-- The fundamental generator creates the SAME original loop state. -/
theorem complexMultiply_unit (L : SourceLoop width) :
    CM L 1 (complexUnit hw0 hw1 width) = E (embed hw0 hw1 (loopState L)) := by
  unfold complexUnit
  rw [complexMultiply_embedReal, completedMultiply_unitState]

/-- The complex theory retains the original real lag moment with zero imaginary part. -/
theorem complexMultiply_unit_lag (L : SourceLoop width) (n : Nat) :
    I (CM L 1 (complexUnit hw0 hw1 width))
      (CT n (CM L 1 (complexUnit hw0 hw1 width))) =
      (Quotient.mk crealSetoid (lagMoment hw0 hw1 L n), RCzero) := by
  unfold complexUnit
  simp only [complexMultiply_embedReal, complexTime_embedReal, inner_embedReal,
    completedMultiply_unitState_lag]
  rfl

#print axioms complexMultiply
#print axioms complexMultiply_embedReal
#print axioms complexMultiply_zero
#print axioms complexMultiply_add
#print axioms complexMultiply_smul
#print axioms inner_multiplier_balance
#print axioms inner_multiplier_bound
#print axioms complexMultiply_comm
#print axioms inner_multiplier_product_balance
#print axioms complexMultiply_unit
#print axioms complexMultiply_unit_lag

end YMGap.Continuum.BF4WilsonAllNomeComplexObservables
