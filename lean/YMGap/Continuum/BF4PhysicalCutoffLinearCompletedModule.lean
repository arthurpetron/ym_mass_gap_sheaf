/-
# Rational module laws on the completed physical BF4 cutoff carrier

The preceding layer constructs addition, zero, negation, and rational scaling
on the explicit-modulus completion.  This module proves that those operations
satisfy the additive-group and rational-module laws on every completed point.

Each presentation law is first proved by exact rational evaluation.  Semantic
equivalence gives zero limiting squared distance through the literal
finite-stage GNS bridge.  Quotient induction then applies that null law
pointwise to arbitrary constructive Cauchy representatives.  No representative
is selected from a quotient.

This is still a fixed-nome, fixed-finite-half-extent rational linear carrier.
It has no cutoff-independent transfer or completed inner product yet.

## Axiom gate

The construction uses finite rational algebra, explicit Cauchy moduli, and
`Quotient.sound` only.  There is no classical choice, noncomputable
declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Semantic rational-module laws -/

theorem equivalent_add_zero
    (observable : CentralPhysicalLinearObservable) :
    Equivalent (add observable zero) observable :=
  equivalent_trans (add_comm observable zero) (zero_add observable)

theorem equivalent_smul_one
    (observable : CentralPhysicalLinearObservable) :
    Equivalent (smul 1 observable) observable :=
  fun state => Q'.one_mul_eqv (observable.value state)

theorem equivalent_smul_zero
    (observable : CentralPhysicalLinearObservable) :
    Equivalent (smul 0 observable) zero :=
  fun state => Q'.zero_mul_eqv (observable.value state)

theorem equivalent_smul_mul
    (first second : Q')
    (observable : CentralPhysicalLinearObservable) :
    Equivalent (smul first (smul second observable))
      (smul (first * second) observable) :=
  fun state => Q'.eqv_symm
    (Q'.mul_assoc_eqv first second (observable.value state))

theorem equivalent_add_scalar_smul
    (first second : Q')
    (observable : CentralPhysicalLinearObservable) :
    Equivalent (smul (first + second) observable)
      (add (smul first observable) (smul second observable)) :=
  fun state => Q'.add_mul_eqv
    first second (observable.value state)

theorem equivalent_smul_add
    (scalar : Q') (left right : CentralPhysicalLinearObservable) :
    Equivalent (smul scalar (add left right))
      (add (smul scalar left) (smul scalar right)) :=
  fun state => Q'.mul_add_eqv
    scalar (left.value state) (right.value state)

/-! ## 2. Semantic equality is limiting metric nullity -/

theorem physicalLinearDistSq_equiv_czero_of_equivalent
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {left right : CentralPhysicalLinearObservable}
    (h : Equivalent left right) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half left right)
      CReal.czero :=
  Equiv_of_approx_eqv (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    exact Q'.eqv_trans _ _ _
      (physicalLinearDistSq_approx_eqv_stage
        hw0 hw1 half cutoff left right)
      (rad_of_veq D h))

theorem physicalLinear_add_zero_right_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half (add observable zero) observable)
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (equivalent_add_zero observable)

theorem physicalLinear_add_zero_left_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half (add zero observable) observable)
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (zero_add observable)

theorem physicalLinear_neg_add_self_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (add (neg observable) observable) zero)
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (neg_add observable)

theorem physicalLinear_add_comm_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (add left right) (add right left))
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (add_comm left right)

theorem physicalLinear_add_assoc_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (first second third : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (add (add first second) third)
        (add first (add second third)))
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (add_assoc first second third)

theorem physicalLinear_smul_one_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half (smul 1 observable) observable)
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (equivalent_smul_one observable)

theorem physicalLinear_smul_zero_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half (smul 0 observable) zero)
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (equivalent_smul_zero observable)

theorem physicalLinear_smul_mul_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (first second : Q')
    (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (smul first (smul second observable))
        (smul (first * second) observable))
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (equivalent_smul_mul first second observable)

theorem physicalLinear_add_scalar_smul_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (first second : Q')
    (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (smul (first + second) observable)
        (add (smul first observable) (smul second observable)))
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (equivalent_add_scalar_smul first second observable)

theorem physicalLinear_smul_add_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (smul scalar (add left right))
        (add (smul scalar left) (smul scalar right)))
      CReal.czero :=
  physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 half (equivalent_smul_add scalar left right)

/-! ## 3. Additive and scalar laws on every completion point -/

theorem completedPhysicalLinearAdd_zero_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable :
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearAdd hw0 hw1 half observable
        (completedPhysicalLinearZero hw0 hw1 half) = observable := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_add_zero_right_null
      hw0 hw1 half (X.seq n))⟩

theorem completedPhysicalLinearAdd_zero_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable :
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearAdd hw0 hw1 half
        (completedPhysicalLinearZero hw0 hw1 half) observable = observable := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_add_zero_left_null
      hw0 hw1 half (X.seq n))⟩

theorem completedPhysicalLinearNeg_add_self
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable :
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearAdd hw0 hw1 half
        (completedPhysicalLinearNeg hw0 hw1 half observable) observable =
      completedPhysicalLinearZero hw0 hw1 half := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_neg_add_self_null
      hw0 hw1 half (X.seq n))⟩

theorem completedPhysicalLinearAdd_comm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearAdd hw0 hw1 half left right =
      completedPhysicalLinearAdd hw0 hw1 half right left := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_add_comm_null
      hw0 hw1 half (X.seq n) (Y.seq n))⟩

theorem completedPhysicalLinearAdd_assoc
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (first second third :
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearAdd hw0 hw1 half
        (completedPhysicalLinearAdd hw0 hw1 half first second) third =
      completedPhysicalLinearAdd hw0 hw1 half first
        (completedPhysicalLinearAdd hw0 hw1 half second third) := by
  refine Quotient.inductionOn first (fun X => ?_)
  refine Quotient.inductionOn second (fun Y => ?_)
  refine Quotient.inductionOn third (fun Z => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_add_assoc_null
      hw0 hw1 half (X.seq n) (Y.seq n) (Z.seq n))⟩

theorem completedPhysicalLinearSmul_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable :
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearSmul hw0 hw1 half 1 observable = observable := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_smul_one_null
      hw0 hw1 half (X.seq n))⟩

theorem completedPhysicalLinearSmul_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable :
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearSmul hw0 hw1 half 0 observable =
      completedPhysicalLinearZero hw0 hw1 half := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_smul_zero_null
      hw0 hw1 half (X.seq n))⟩

theorem completedPhysicalLinearSmul_mul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (first second : Q')
    (observable : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearSmul hw0 hw1 half first
        (completedPhysicalLinearSmul hw0 hw1 half second observable) =
      completedPhysicalLinearSmul hw0 hw1 half
        (first * second) observable := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_smul_mul_null
      hw0 hw1 half first second (X.seq n))⟩

theorem completedPhysicalLinear_add_scalar_smul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (first second : Q')
    (observable : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearSmul hw0 hw1 half
        (first + second) observable =
      completedPhysicalLinearAdd hw0 hw1 half
        (completedPhysicalLinearSmul hw0 hw1 half first observable)
        (completedPhysicalLinearSmul hw0 hw1 half second observable) := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_add_scalar_smul_null
      hw0 hw1 half first second (X.seq n))⟩

theorem completedPhysicalLinearSmul_add
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedPhysicalLinearSmul hw0 hw1 half scalar
        (completedPhysicalLinearAdd hw0 hw1 half left right) =
      completedPhysicalLinearAdd hw0 hw1 half
        (completedPhysicalLinearSmul hw0 hw1 half scalar left)
        (completedPhysicalLinearSmul hw0 hw1 half scalar right) := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => physicalLinear_smul_add_null
      hw0 hw1 half scalar (X.seq n) (Y.seq n))⟩

/-! ## 4. Bundled completed rational module -/

/-- A choice-free rational module carrier with literal equality laws. -/
structure CompletedQModuleData where
  Carrier : Type
  zero : Carrier
  add : Carrier -> Carrier -> Carrier
  neg : Carrier -> Carrier
  smul : Q' -> Carrier -> Carrier
  add_zero_right : forall value, add value zero = value
  add_zero_left : forall value, add zero value = value
  neg_add : forall value, add (neg value) value = zero
  add_comm : forall left right, add left right = add right left
  add_assoc : forall first second third,
    add (add first second) third = add first (add second third)
  smul_one : forall value, smul 1 value = value
  smul_zero : forall value, smul 0 value = zero
  smul_mul : forall first second value,
    smul first (smul second value) = smul (first * second) value
  add_scalar_smul : forall first second value,
    smul (first + second) value = add (smul first value) (smul second value)
  smul_add : forall scalar left right,
    smul scalar (add left right) = add (smul scalar left) (smul scalar right)

/-- The concrete fixed-nome completed physical rational module. -/
def centralPhysicalCutoffCompletedQModule
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CompletedQModuleData where
  Carrier := CentralPhysicalCutoffLinearCompletion hw0 hw1 half
  zero := completedPhysicalLinearZero hw0 hw1 half
  add := completedPhysicalLinearAdd hw0 hw1 half
  neg := completedPhysicalLinearNeg hw0 hw1 half
  smul := completedPhysicalLinearSmul hw0 hw1 half
  add_zero_right := completedPhysicalLinearAdd_zero_right hw0 hw1 half
  add_zero_left := completedPhysicalLinearAdd_zero_left hw0 hw1 half
  neg_add := completedPhysicalLinearNeg_add_self hw0 hw1 half
  add_comm := completedPhysicalLinearAdd_comm hw0 hw1 half
  add_assoc := completedPhysicalLinearAdd_assoc hw0 hw1 half
  smul_one := completedPhysicalLinearSmul_one hw0 hw1 half
  smul_zero := completedPhysicalLinearSmul_zero hw0 hw1 half
  smul_mul := completedPhysicalLinearSmul_mul hw0 hw1 half
  add_scalar_smul := completedPhysicalLinear_add_scalar_smul hw0 hw1 half
  smul_add := completedPhysicalLinearSmul_add hw0 hw1 half

/-! ## Axiom audit -/

#print axioms physicalLinearDistSq_equiv_czero_of_equivalent
#print axioms completedPhysicalLinearAdd_assoc
#print axioms completedPhysicalLinearSmul_mul
#print axioms completedPhysicalLinearSmul_add
#print axioms CompletedQModuleData
#print axioms centralPhysicalCutoffCompletedQModule

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
