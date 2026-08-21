/-
# The cutoff-removed physical BF4 finite-linear GNS form

The fixed-nome cutoff functional is initially defined only on globally
`[0,1]`-valued observables.  That multiplicative carrier is sufficient for
individual moments, but it is not an additive carrier on which a GNS
completion or a vacuum complement can live.

This module takes the constructive finite rational span of those unit
observables.  Its syntax is deliberately finite and choice-free.  Evaluation
maps the syntax to the literal rational observable used by every finite BF4
physical GNS.  The limiting bilinear form is assembled from the already
constructed cutoff limits of products of unit observables.

The load-bearing bridge proves that approximation `K` of the limiting form is
equivalent to the literal stationary-marginal inner product of the evaluated
linear observables at representation cutoff `K`.  Consequently the limiting
form is symmetric, rational-bilinear, semantic-congruence invariant, and
positive.

This is a fixed-nome, fixed-finite-volume positive pre-inner form.  It does not
yet quotient its radical, instantiate the `CReal` squared-seminorm completion,
construct a limiting transfer operator, take a thermodynamic/spacing limit, or
prove the Clay mass-gap theorem.

## Axiom gate

Only finite inductive syntax, exact rational algebra, the proved finite
physical GNS, and constructive `CReal` operations are used.  There is no
`Classical`, choice, `sorry`, `native_decide`, noncomputable declaration, or
custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
import YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite rational syntax and literal evaluation -/

/-- The constructive finite rational span of physical `[0,1]` observables. -/
inductive CentralPhysicalLinearObservable : Type where
  | zero : CentralPhysicalLinearObservable
  | atom : CentralPhysicalUnitObservable -> CentralPhysicalLinearObservable
  | add : CentralPhysicalLinearObservable ->
      CentralPhysicalLinearObservable -> CentralPhysicalLinearObservable
  | smul : Q' -> CentralPhysicalLinearObservable ->
      CentralPhysicalLinearObservable

namespace CentralPhysicalLinearObservable

/-- Literal rational observable represented by a finite-linear expression. -/
def value : CentralPhysicalLinearObservable -> EdgeLabelling -> Q'
  | zero, _ => 0
  | atom observable, state => observable.value state
  | add left right, state => left.value state + right.value state
  | smul scalar observable, state => scalar * observable.value state

/-- Additive inverse, expressed using rational scalar multiplication. -/
def neg (observable : CentralPhysicalLinearObservable) :
    CentralPhysicalLinearObservable :=
  smul (-1) observable

/-- Subtraction in the finite-linear syntax. -/
def sub (left right : CentralPhysicalLinearObservable) :
    CentralPhysicalLinearObservable :=
  add left right.neg

/-- Semantic equivalence of finite-linear presentations. -/
def Equivalent (left right : CentralPhysicalLinearObservable) : Prop :=
  forall state, left.value state ≈ right.value state

theorem equivalent_refl (observable : CentralPhysicalLinearObservable) :
    Equivalent observable observable :=
  fun _ => Q'.eqv_refl _

theorem equivalent_symm {left right : CentralPhysicalLinearObservable}
    (h : Equivalent left right) : Equivalent right left :=
  fun state => Q'.eqv_symm (h state)

theorem equivalent_trans {first middle last : CentralPhysicalLinearObservable}
    (hfirst : Equivalent first middle) (hlast : Equivalent middle last) :
    Equivalent first last :=
  fun state => Q'.eqv_trans _ _ _ (hfirst state) (hlast state)

theorem add_congr {left left' right right' : CentralPhysicalLinearObservable}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (add left right) (add left' right') :=
  fun state => Q'.add_eqv_congr' (hleft state) (hright state)

theorem smul_congr (scalar : Q')
    {left right : CentralPhysicalLinearObservable}
    (h : Equivalent left right) :
    Equivalent (smul scalar left) (smul scalar right) :=
  fun state => Q'.mul_eqv_congr_left scalar _ _ (h state)

theorem add_assoc (first middle last : CentralPhysicalLinearObservable) :
    Equivalent (add (add first middle) last) (add first (add middle last)) :=
  fun state => Q'.add_assoc_eqv
    (first.value state) (middle.value state) (last.value state)

theorem add_comm (left right : CentralPhysicalLinearObservable) :
    Equivalent (add left right) (add right left) :=
  fun state => Q'.add_comm_eqv (left.value state) (right.value state)

theorem zero_add (observable : CentralPhysicalLinearObservable) :
    Equivalent (add zero observable) observable :=
  fun state => Q'.eqv_of_eq (Q'.zero_add' (observable.value state))

private theorem neg_one_mul_eqv (value : Q') :
    ((-1 : Q') * value) ≈ (-value) :=
  Q'.eqv_trans _ _ _
    (Q'.neg_mul_eqv 1 value)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv value))

theorem neg_add (observable : CentralPhysicalLinearObservable) :
    Equivalent (add observable.neg observable) zero := by
  intro state
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (neg_one_mul_eqv (observable.value state)) (Q'.eqv_refl _))
    (Q'.neg_add_self_eqv (observable.value state))

/-! ## 2. The limiting bilinear form -/

/-- Limiting product moment for two unit-observable atoms. -/
def atomInnerLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalUnitObservable) : CReal :=
  centralPhysicalStationaryCutoffLimit hw0 hw1 half
    (centralPhysicalUnitObservableMul left right)

/-- Right-linear extension of one atomic limiting moment. -/
def atomLinearInnerLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left : CentralPhysicalUnitObservable) :
    CentralPhysicalLinearObservable -> CReal
  | zero => CReal.czero
  | atom right => atomInnerLimit hw0 hw1 half left right
  | add first second =>
      CReal.add
        (atomLinearInnerLimit hw0 hw1 half left first)
        (atomLinearInnerLimit hw0 hw1 half left second)
  | smul scalar right =>
      CReal.mul (CReal.ofQ' scalar)
        (atomLinearInnerLimit hw0 hw1 half left right)

/-- The cutoff-removed physical bilinear form on finite rational expressions. -/
def innerLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalLinearObservable ->
      CentralPhysicalLinearObservable -> CReal
  | zero, _ => CReal.czero
  | atom left, right => atomLinearInnerLimit hw0 hw1 half left right
  | add first second, right =>
      CReal.add
        (innerLimit hw0 hw1 half first right)
        (innerLimit hw0 hw1 half second right)
  | smul scalar left, right =>
      CReal.mul (CReal.ofQ' scalar)
        (innerLimit hw0 hw1 half left right)

/-! ## 3. Exact bridge to every finite physical GNS stage -/

theorem atomInnerLimit_approx_eq_weightedInner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (left right : CentralPhysicalUnitObservable) :
    (atomInnerLimit hw0 hw1 half left right).approx cutoff =
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half left.value right.value :=
  rfl

theorem atomLinearInnerLimit_approx_eqv_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (left : CentralPhysicalUnitObservable) :
    forall right : CentralPhysicalLinearObservable,
      (atomLinearInnerLimit hw0 hw1 half left right).approx cutoff ≈
        (centralPhysicalSmulGNS
          w (Q'.le_of_lt hw0) cutoff half).toGNSData.B
          left.value right.value
  | zero => by
      let D := (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData
      change (0 : Q') ≈
        D.B left.value D.zero
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (D.B_symm left.value D.zero)
          (D.B_zero_left left.value))
  | atom right => by
      exact Q'.eqv_of_eq
        (atomInnerLimit_approx_eq_weightedInner
          hw0 hw1 half cutoff left right)
  | add first second => by
      let D := (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (atomLinearInnerLimit_approx_eqv_stage
            hw0 hw1 half cutoff left first)
          (atomLinearInnerLimit_approx_eqv_stage
            hw0 hw1 half cutoff left second))
        (Q'.eqv_symm (D.B_add_right left.value first.value second.value))
  | smul scalar right => by
      let D := (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left scalar _ _
          (atomLinearInnerLimit_approx_eqv_stage
            hw0 hw1 half cutoff left right))
        (Q'.eqv_symm (D.B_smul_right scalar left.value right.value))

/-- Approximation `K` of the limiting form is the literal physical GNS form
at representation cutoff `K`, modulo exact rational representation. -/
theorem innerLimit_approx_eqv_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) :
    forall left right : CentralPhysicalLinearObservable,
      (innerLimit hw0 hw1 half left right).approx cutoff ≈
        (centralPhysicalSmulGNS
          w (Q'.le_of_lt hw0) cutoff half).toGNSData.B
          left.value right.value
  | zero, right => by
      exact Q'.eqv_symm
        ((centralPhysicalSmulGNS
          w (Q'.le_of_lt hw0) cutoff half).toGNSData.B_zero_left
          right.value)
  | atom left, right =>
      atomLinearInnerLimit_approx_eqv_stage
        hw0 hw1 half cutoff left right
  | add first second, right => by
      let D := (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (innerLimit_approx_eqv_stage
            hw0 hw1 half cutoff first right)
          (innerLimit_approx_eqv_stage
            hw0 hw1 half cutoff second right))
        (Q'.eqv_symm (D.B_add_left first.value second.value right.value))
  | smul scalar left, right => by
      let D := (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left scalar _ _
          (innerLimit_approx_eqv_stage
            hw0 hw1 half cutoff left right))
        (Q'.eqv_symm (D.B_smul_left scalar left.value right.value))

/-! ## 4. Positive pre-inner-form laws after cutoff removal -/

theorem innerLimit_congr_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {left left' : CentralPhysicalLinearObservable}
    (right : CentralPhysicalLinearObservable)
    (h : Equivalent left left') :
    CReal.Equiv
      (innerLimit hw0 hw1 half left right)
      (innerLimit hw0 hw1 half left' right) :=
  Equiv_of_approx_eqv (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    exact Q'.eqv_trans _ _ _
      (innerLimit_approx_eqv_stage hw0 hw1 half cutoff left right)
      (Q'.eqv_trans _ _ _
        (D.B_congr_left right.value h)
        (Q'.eqv_symm
          (innerLimit_approx_eqv_stage hw0 hw1 half cutoff left' right))))

theorem innerLimit_add_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right test : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half (add left right) test)
      (CReal.add
        (innerLimit hw0 hw1 half left test)
        (innerLimit hw0 hw1 half right test)) :=
  CReal.Equiv.refl _

theorem innerLimit_smul_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half (smul scalar left) right)
      (CReal.mul (CReal.ofQ' scalar)
        (innerLimit hw0 hw1 half left right)) :=
  CReal.Equiv.refl _

theorem innerLimit_symm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half left right)
      (innerLimit hw0 hw1 half right left) :=
  Equiv_of_approx_eqv (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    exact Q'.eqv_trans _ _ _
      (innerLimit_approx_eqv_stage hw0 hw1 half cutoff left right)
      (Q'.eqv_trans _ _ _ (D.B_symm left.value right.value)
        (Q'.eqv_symm
          (innerLimit_approx_eqv_stage hw0 hw1 half cutoff right left))))

theorem innerLimit_self_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.leEv CReal.czero
      (innerLimit hw0 hw1 half observable observable) := by
  apply CReal.leEv_ofQ'_of_approx_ge
  intro cutoff
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) cutoff half).toGNSData
  exact Q'.le_trans' _ _ _
    (D.self_nonneg observable.value)
    (Q'.ge_of_eqv
      (innerLimit_approx_eqv_stage
        hw0 hw1 half cutoff observable observable))

/-! ## 5. A bundled honest CReal-valued GNS form datum -/

/-- Additive rational module data with a positive `CReal`-valued bilinear
form.  This is the correct pre-quotient interface for a limiting OS/GNS form;
radical descent is intentionally not hidden in the structure. -/
structure CRealGNSFormData where
  V : Type
  veq : V -> V -> Prop
  veq_refl : forall value, veq value value
  veq_symm : forall {left right}, veq left right -> veq right left
  veq_trans : forall {first middle last},
    veq first middle -> veq middle last -> veq first last
  zero : V
  add : V -> V -> V
  neg : V -> V
  smul : Q' -> V -> V
  add_congr : forall {left left' right right'},
    veq left left' -> veq right right' ->
      veq (add left right) (add left' right')
  smul_congr : forall scalar {left right},
    veq left right -> veq (smul scalar left) (smul scalar right)
  add_assoc : forall first middle last,
    veq (add (add first middle) last) (add first (add middle last))
  add_comm : forall left right, veq (add left right) (add right left)
  zero_add : forall value, veq (add zero value) value
  neg_add : forall value, veq (add (neg value) value) zero
  B : V -> V -> CReal
  B_congr_left : forall {left left'} right,
    veq left left' -> CReal.Equiv (B left right) (B left' right)
  B_add_left : forall left right test,
    CReal.Equiv (B (add left right) test)
      (CReal.add (B left test) (B right test))
  B_smul_left : forall scalar left right,
    CReal.Equiv (B (smul scalar left) right)
      (CReal.mul (CReal.ofQ' scalar) (B left right))
  B_symm : forall left right, CReal.Equiv (B left right) (B right left)
  self_nonneg : forall value, CReal.leEv CReal.czero (B value value)

/-- The concrete fixed-nome, fixed-volume physical finite-linear limiting
form.  Unlike the prior multiplicative unit carrier, this datum is additive. -/
def centralPhysicalCutoffLinearGNSForm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CRealGNSFormData where
  V := CentralPhysicalLinearObservable
  veq := Equivalent
  veq_refl := equivalent_refl
  veq_symm := @equivalent_symm
  veq_trans := @equivalent_trans
  zero := zero
  add := add
  neg := neg
  smul := smul
  add_congr := @add_congr
  smul_congr := smul_congr
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  neg_add := neg_add
  B := innerLimit hw0 hw1 half
  B_congr_left := innerLimit_congr_left hw0 hw1 half
  B_add_left := innerLimit_add_left hw0 hw1 half
  B_smul_left := innerLimit_smul_left hw0 hw1 half
  B_symm := innerLimit_symm hw0 hw1 half
  self_nonneg := innerLimit_self_nonnegative hw0 hw1 half

end CentralPhysicalLinearObservable

/-! ## Axiom audit -/

#print axioms CentralPhysicalLinearObservable
#print axioms CentralPhysicalLinearObservable.innerLimit_approx_eqv_stage
#print axioms CentralPhysicalLinearObservable.innerLimit_congr_left
#print axioms CentralPhysicalLinearObservable.innerLimit_symm
#print axioms CentralPhysicalLinearObservable.innerLimit_self_nonnegative
#print axioms CentralPhysicalLinearObservable.CRealGNSFormData
#print axioms CentralPhysicalLinearObservable.centralPhysicalCutoffLinearGNSForm

end YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
