/-
# Squared-seminorm completion of the cutoff-removed physical BF4 form

The cutoff-removed physical form is already positive and its radical kills
every cross term.  This module turns that analytic datum into the exact input
expected by `CRealSeminormCompletion`: squared distance is the limiting norm
of the finite-linear presentation difference.

The reflexive, symmetric, nonnegative, and sqrt-free triangle laws are checked
against the literal finite physical GNS at every representation cutoff.  The
endpoint-replacement law is genuinely a limiting statement and uses the
previously proved `CReal` radical descent.  The resulting null quotient and
explicit-modulus Cauchy completion are therefore concrete Types, not
postulated interfaces.

This remains fixed nome and fixed finite half-extent.  It does not yet descend
the additive operations or a cutoff-independent transfer to the completion,
and it supplies no thermodynamic or continuum limit.

## Axiom gate

Only finite rational algebra, the proved finite-stage physical GNS laws,
constructive Bishop-real estimates, and `Quotient` are used.  There is no
choice, classical logic, noncomputable declaration, custom axiom, or unproved
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact algebra of finite-linear presentation differences -/

theorem sub_value_equiv
    (left right : CentralPhysicalLinearObservable)
    (state : SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    (sub left right).value state ≈
      left.value state + (-(right.value state)) := by
  change left.value state + ((-1 : Q') * right.value state) ≈
    left.value state + (-(right.value state))
  q_ring

private theorem q_sub_add_cancel_eqv (left right : Q') :
    ((left + (-right)) + right) ≈ left := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv left (-right) right) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left left ((-right) + right) 0
      (Q'.neg_add_self_eqv right)) ?_
  exact QPoly.q_add_zero_eqv left

private theorem q_sub_chain_eqv (first middle last : Q') :
    (first + (-last)) ≈
      ((first + (-middle)) + (middle + (-last))) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (first + (-middle)) middle (-last))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      ((first + (-middle)) + middle) first (-last)
      (q_sub_add_cancel_eqv first middle)) ?_
  exact Q'.eqv_refl _

theorem sub_self_equivalent_zero
    (observable : CentralPhysicalLinearObservable) :
    Equivalent (sub observable observable) zero := by
  intro state
  change (sub observable observable).value state ≈ 0
  refine Q'.eqv_trans _ _ _ (sub_value_equiv observable observable state) ?_
  exact Q'.add_neg_self_eqv (observable.value state)

theorem sub_symm_equivalent_neg
    (left right : CentralPhysicalLinearObservable) :
    Equivalent (sub right left) (neg (sub left right)) := by
  intro state
  change (sub right left).value state ≈
    (-1 : Q') * (sub left right).value state
  refine Q'.eqv_trans _ _ _ (sub_value_equiv right left state) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.mul_eqv_congr_left (-1) _ _
      (Q'.eqv_symm (sub_value_equiv left right state)))
  q_ring

theorem sub_chain_equivalent
    (first middle last : CentralPhysicalLinearObservable) :
    Equivalent (sub first last)
      (add (sub first middle) (sub middle last)) := by
  intro state
  change (sub first last).value state ≈
    (sub first middle).value state + (sub middle last).value state
  refine Q'.eqv_trans _ _ _ (sub_value_equiv first last state) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (sub_value_equiv first middle state))
      (Q'.eqv_symm (sub_value_equiv middle last state)))
  exact q_sub_chain_eqv
    (first.value state) (middle.value state) (last.value state)

theorem sub_sub_equivalent
    (left left' right right' : CentralPhysicalLinearObservable) :
    Equivalent
      (sub (sub left right) (sub left' right'))
      (sub (sub left left') (sub right right')) := by
  intro state
  change (sub (sub left right) (sub left' right')).value state ≈
    (sub (sub left left') (sub right right')).value state
  refine Q'.eqv_trans _ _ _
    (sub_value_equiv (sub left right) (sub left' right') state) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (sub_value_equiv left right state)
      (Q'.neg_eqv_congr _ _ (sub_value_equiv left' right' state))) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (sub_value_equiv (sub left left') (sub right right') state)
      (Q'.add_eqv_congr'
        (sub_value_equiv left left' state)
        (Q'.neg_eqv_congr _ _ (sub_value_equiv right right' state)))))
  q_ring

theorem sub_add_right_equivalent
    (left right : CentralPhysicalLinearObservable) :
    Equivalent left (add (sub left right) right) := by
  intro state
  change left.value state ≈
    (sub left right).value state + right.value state
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (sub_value_equiv left right state)))
  exact Q'.eqv_symm
    (q_sub_add_cancel_eqv (left.value state) (right.value state))

/-! ## 2. The limiting squared distance and its finite-stage meaning -/

/-- Squared distance induced by the cutoff-removed physical limiting form. -/
def physicalLinearDistSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) : CReal :=
  innerLimit hw0 hw1 half (sub left right) (sub left right)

/-- Every approximation of the limiting squared distance is the actual finite
physical GNS squared distance of the evaluated observables. -/
theorem physicalLinearDistSq_approx_eqv_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (left right : CentralPhysicalLinearObservable) :
    (physicalLinearDistSq hw0 hw1 half left right).approx cutoff ≈
      (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData.distSqQ
        left.value right.value := by
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) cutoff half).toGNSData
  have hsub : D.veq (sub left right).value
      (D.sub left.value right.value) := by
    intro state
    exact sub_value_equiv left right state
  exact Q'.eqv_trans _ _ _
    (innerLimit_approx_eqv_stage
      hw0 hw1 half cutoff (sub left right) (sub left right))
    (D.B_diag_congr hsub)

private theorem leEv_of_approx_le {left right : CReal}
    (h : forall cutoff, left.approx cutoff <= right.approx cutoff) :
    CReal.leEv left right := by
  intro epsilon hepsilon
  exact ⟨0, fun cutoff _ =>
    Q'.le_trans' _ _ _ (h cutoff)
      (Q'.add_le_self_of_nonneg
        (right.approx cutoff) epsilon (Q'.le_of_lt hepsilon))⟩

theorem physicalLinearDistSq_refl
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half observable observable)
      CReal.czero :=
  Equiv_of_approx_eqv (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    exact Q'.eqv_trans _ _ _
      (physicalLinearDistSq_approx_eqv_stage
        hw0 hw1 half cutoff observable observable)
      (D.rad_refl observable.value))

theorem physicalLinearDistSq_symm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half left right)
      (physicalLinearDistSq hw0 hw1 half right left) :=
  Equiv_of_approx_eqv (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    exact Q'.eqv_trans _ _ _
      (physicalLinearDistSq_approx_eqv_stage
        hw0 hw1 half cutoff left right)
      (Q'.eqv_trans _ _ _
        (D.distSqQ_comm left.value right.value)
        (Q'.eqv_symm
          (physicalLinearDistSq_approx_eqv_stage
            hw0 hw1 half cutoff right left))))

theorem physicalLinearDistSq_nonneg
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.leEv CReal.czero
      (physicalLinearDistSq hw0 hw1 half left right) :=
  innerLimit_self_nonnegative hw0 hw1 half (sub left right)

theorem physicalLinearDistSq_triangle
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (first middle last : CentralPhysicalLinearObservable) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half first last)
      (CReal.add
        (CReal.add
          (physicalLinearDistSq hw0 hw1 half first middle)
          (physicalLinearDistSq hw0 hw1 half first middle))
        (CReal.add
          (physicalLinearDistSq hw0 hw1 half middle last)
          (physicalLinearDistSq hw0 hw1 half middle last))) :=
  leEv_of_approx_le (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    have hleft := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff first last
    have hfirst := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff first middle
    have hlast := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff middle last
    have hright :
        ((D.distSqQ first.value middle.value +
            D.distSqQ first.value middle.value) +
          (D.distSqQ middle.value last.value +
            D.distSqQ middle.value last.value)) ≈
        (((physicalLinearDistSq hw0 hw1 half first middle).approx cutoff +
            (physicalLinearDistSq hw0 hw1 half first middle).approx cutoff) +
          ((physicalLinearDistSq hw0 hw1 half middle last).approx cutoff +
            (physicalLinearDistSq hw0 hw1 half middle last).approx cutoff)) :=
      Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_symm hfirst) (Q'.eqv_symm hfirst))
        (Q'.add_eqv_congr' (Q'.eqv_symm hlast) (Q'.eqv_symm hlast))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _
        (D.distSqQ_triangle first.value middle.value last.value)
        (Q'.le_of_eqv hright)))

/-! ## 3. Limiting radical closure and endpoint replacement -/

theorem innerLimit_congr_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left : CentralPhysicalLinearObservable)
    {right right' : CentralPhysicalLinearObservable}
    (h : Equivalent right right') :
    CReal.Equiv
      (innerLimit hw0 hw1 half left right)
      (innerLimit hw0 hw1 half left right') :=
  CReal.Equiv.trans
    (innerLimit_symm hw0 hw1 half left right)
    (CReal.Equiv.trans
      (innerLimit_congr_left hw0 hw1 half left h)
      (innerLimit_symm hw0 hw1 half right' left))

theorem innerLimit_congr
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {left left' right right' : CentralPhysicalLinearObservable}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    CReal.Equiv
      (innerLimit hw0 hw1 half left right)
      (innerLimit hw0 hw1 half left' right') :=
  CReal.Equiv.trans
    (innerLimit_congr_left hw0 hw1 half right hleft)
    (innerLimit_congr_right hw0 hw1 half left' hright)

theorem innerLimit_add_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (test left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half test (add left right))
      (CReal.add
        (innerLimit hw0 hw1 half test left)
        (innerLimit hw0 hw1 half test right)) :=
  CReal.Equiv.trans
    (innerLimit_symm hw0 hw1 half test (add left right))
    (CReal.Equiv.trans
      (innerLimit_add_left hw0 hw1 half left right test)
      (CReal.Equiv_add
        (innerLimit_symm hw0 hw1 half left test)
        (innerLimit_symm hw0 hw1 half right test)))

private theorem cadd_zero_equiv (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  Equiv_of_approx_eqv (fun cutoff =>
    QPoly.q_add_zero_eqv (value.approx cutoff))

private theorem czero_add_equiv (value : CReal) :
    CReal.Equiv (CReal.add CReal.czero value) value :=
  Equiv_of_approx_eqv (fun cutoff =>
    QPoly.q_zero_add_eqv (value.approx cutoff))

private theorem creal_mul_congr_right
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

private theorem cmul_czero_equiv (scalar : CReal) :
    CReal.Equiv (CReal.mul scalar CReal.czero) CReal.czero :=
  Equiv_of_approx_eqv (fun cutoff =>
    Q'.mul_zero_eqv (scalar.approx cutoff))

private theorem cadd_left_equiv_of_zero {zeroLike right : CReal}
    (hzero : CReal.Equiv zeroLike CReal.czero) :
    CReal.Equiv (CReal.add zeroLike right) right :=
  CReal.Equiv.trans (CReal.add_congr_left hzero)
    (czero_add_equiv right)

/-- The difference of two limiting-null finite-linear observables is null. -/
theorem innerLimit_sub_self_equiv_czero_of_null
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable)
    (hleft : CReal.Equiv
      (innerLimit hw0 hw1 half left left) CReal.czero)
    (hright : CReal.Equiv
      (innerLimit hw0 hw1 half right right) CReal.czero) :
    CReal.Equiv
      (innerLimit hw0 hw1 half (sub left right) (sub left right))
      CReal.czero := by
  let difference := sub left right
  have hradLeft := innerLimit_equiv_czero_of_self_equiv_czero
    hw0 hw1 half left difference hleft
  have hradRight := innerLimit_equiv_czero_of_self_equiv_czero
    hw0 hw1 half right difference hright
  have hscaled := innerLimit_smul_left
    hw0 hw1 half (-1) right difference
  have hscaledZero : CReal.Equiv
      (innerLimit hw0 hw1 half (neg right) difference)
      CReal.czero :=
    CReal.Equiv.trans hscaled
      (CReal.Equiv.trans (creal_mul_congr_right hradRight)
        (cmul_czero_equiv (CReal.ofQ' (-1))))
  have hadd := innerLimit_add_left
    hw0 hw1 half left (neg right) difference
  have hsumZero : CReal.Equiv
      (CReal.add
        (innerLimit hw0 hw1 half left difference)
        (innerLimit hw0 hw1 half (neg right) difference))
      CReal.czero :=
    CReal.Equiv.trans (CReal.Equiv_add hradLeft hscaledZero)
      (czero_add_equiv CReal.czero)
  exact CReal.Equiv.trans hadd hsumZero

/-- Replacing both endpoints by null-equivalent presentations preserves the
limiting squared distance. -/
theorem physicalLinearDistSq_null_congr
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {left left' right right' : CentralPhysicalLinearObservable}
    (hleft : CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half left left') CReal.czero)
    (hright : CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half right right') CReal.czero) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half left right)
      (physicalLinearDistSq hw0 hw1 half left' right') := by
  let firstDifference := sub left right
  let secondDifference := sub left' right'
  let leftChange := sub left left'
  let rightChange := sub right right'
  let changeDifference := sub leftChange rightChange
  let totalChange := sub firstDifference secondDifference
  have hchangeNull : CReal.Equiv
      (innerLimit hw0 hw1 half changeDifference changeDifference)
      CReal.czero :=
    innerLimit_sub_self_equiv_czero_of_null
      hw0 hw1 half leftChange rightChange hleft hright
  have hregroup : Equivalent totalChange changeDifference :=
    sub_sub_equivalent left left' right right'
  have htotalNull : CReal.Equiv
      (innerLimit hw0 hw1 half totalChange totalChange)
      CReal.czero :=
    CReal.Equiv.trans
      (innerLimit_congr hw0 hw1 half hregroup hregroup)
      hchangeNull
  have hdecompose : Equivalent firstDifference
      (add totalChange secondDifference) :=
    sub_add_right_equivalent firstDifference secondDifference
  have hradFirst := innerLimit_equiv_czero_of_self_equiv_czero
    hw0 hw1 half totalChange firstDifference htotalNull
  have hradSecond := innerLimit_equiv_czero_of_self_equiv_czero
    hw0 hw1 half totalChange secondDifference htotalNull
  have hfirstRadRight : CReal.Equiv
      (innerLimit hw0 hw1 half firstDifference totalChange)
      CReal.czero :=
    CReal.Equiv.trans
      (innerLimit_symm hw0 hw1 half firstDifference totalChange)
      hradFirst
  have hdiagToCross : CReal.Equiv
      (innerLimit hw0 hw1 half firstDifference firstDifference)
      (innerLimit hw0 hw1 half firstDifference secondDifference) := by
    exact CReal.Equiv.trans
      (innerLimit_congr_right hw0 hw1 half firstDifference hdecompose)
      (CReal.Equiv.trans
        (innerLimit_add_right
          hw0 hw1 half firstDifference totalChange secondDifference)
        (cadd_left_equiv_of_zero hfirstRadRight))
  have hcrossToDiag : CReal.Equiv
      (innerLimit hw0 hw1 half firstDifference secondDifference)
      (innerLimit hw0 hw1 half secondDifference secondDifference) := by
    exact CReal.Equiv.trans
      (innerLimit_congr_left hw0 hw1 half secondDifference hdecompose)
      (CReal.Equiv.trans
        (innerLimit_add_left
          hw0 hw1 half totalChange secondDifference secondDifference)
        (cadd_left_equiv_of_zero hradSecond))
  exact CReal.Equiv.trans hdiagToCross hcrossToDiag

/-! ## 4. Concrete null quotient and explicit-modulus completion -/

/-- The fully discharged squared seminorm of the cutoff-removed physical
finite-linear form. -/
def centralPhysicalCutoffLinearSquaredSeminorm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CRealSeminormCompletion.SquaredSeminorm where
  Carrier := CentralPhysicalLinearObservable
  distSq := physicalLinearDistSq hw0 hw1 half
  distSq_refl := physicalLinearDistSq_refl hw0 hw1 half
  distSq_symm := physicalLinearDistSq_symm hw0 hw1 half
  distSq_nonneg := physicalLinearDistSq_nonneg hw0 hw1 half
  distSq_triangle := physicalLinearDistSq_triangle hw0 hw1 half
  null_congr := physicalLinearDistSq_null_congr hw0 hw1 half

/-- The positive-definite physical finite-linear carrier after quotienting the
limiting radical. -/
abbrev CentralPhysicalCutoffLinearQuotient
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type :=
  (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).QuotSpace

/-- The actual choice-free, explicit-modulus Cauchy completion of the
cutoff-removed physical finite-linear carrier. -/
abbrev CentralPhysicalCutoffLinearCompletion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type :=
  (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).Completion

/-- Constant-sequence embedding of finite-linear physical observables into
the completed carrier. -/
def embedCentralPhysicalLinearObservable
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CentralPhysicalLinearObservable ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).embedRep

/-- The constant embedding descended through the limiting radical quotient. -/
def embedCentralPhysicalCutoffLinearQuotient
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CentralPhysicalCutoffLinearQuotient hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).embedQuot

/-! ## Axiom audit -/

#print axioms physicalLinearDistSq_approx_eqv_stage
#print axioms physicalLinearDistSq_triangle
#print axioms innerLimit_sub_self_equiv_czero_of_null
#print axioms physicalLinearDistSq_null_congr
#print axioms centralPhysicalCutoffLinearSquaredSeminorm
#print axioms CentralPhysicalCutoffLinearCompletion
#print axioms embedCentralPhysicalLinearObservable

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
