/-
# Cutoff products converge to completed BF4 heat products

This module closes the finite-product limit step left open by the completed
pointwise heat layer.  For a finite list of factors it proves:

* the literal rational cutoff product, embedded in `CReal`, is equivalent to
  the recursively multiplied cutoff product;
* uniform one-factor approximation bounds tensorize to a bound on every
  completed tail product;
* factorwise convergence therefore implies convergence of the simultaneous
  cutoff product to `completedFactorProduct`.

The result is then instantiated with the genuine completed SU(2) pointwise
heat series at `0 <= w <= 1/2`.  Consequently, the finite all-label cutoff
product on any retained factor list -- in particular a list of length 23 --
converges to the completed retained kinetic weight used by the BF4 Harnack
consumer.

Honest scope: the theorem is a simultaneous character-cutoff limit for a
supplied finite retained product.  It does not identify that product with the
interacting physical BF4 block kernel, and the strong-coupling window
`w <= 1/2` is not the asymptotically-free continuum trajectory `w -> 1`.

## Axiom gate

Only finite-list induction, exact `Q'` bounds, and constructive `CReal`
multiplication continuity are used.  There is no `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge
import YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.CRealExp
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4CompletedProductLimitBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge

/-! ## 1. Literal rational and recursively lifted cutoff products -/

/-- The literal finite rational product of the factor values at one common
cutoff.  Thus all factors are truncated at the same all-label cutoff. -/
def rationalCutoffFactorProduct {Factor : Type}
    (term : Factor → Nat → Q') : List Factor → Nat → Q'
  | [], _ => 1
  | factor :: tail, cutoff =>
      term factor cutoff *
        rationalCutoffFactorProduct term tail cutoff

/-- The same common-cutoff product formed recursively inside `CReal`.
Pointwise this has exactly the rational product above as every approximation;
the recursive form is convenient for applying multiplication continuity. -/
def liftedCutoffFactorProduct {Factor : Type}
    (term : Factor → Nat → Q') : List Factor → Nat → CReal
  | [], _ => CReal.ofQ' (1 : Q')
  | factor :: tail, cutoff =>
      CReal.mul
        (CReal.ofQ' (term factor cutoff))
        (liftedCutoffFactorProduct term tail cutoff)

@[simp] theorem liftedCutoffFactorProduct_approx
    {Factor : Type} (term : Factor → Nat → Q')
    (factors : List Factor) (cutoff approximation : Nat) :
    (liftedCutoffFactorProduct term factors cutoff).approx approximation =
      rationalCutoffFactorProduct term factors cutoff := by
  induction factors with
  | nil =>
      rfl
  | cons factor tail ih =>
      change
        term factor cutoff *
            (liftedCutoffFactorProduct term tail cutoff).approx approximation =
          term factor cutoff *
            rationalCutoffFactorProduct term tail cutoff
      rw [ih]

/-- The embedded literal rational product and the recursively lifted product
are the same constructive real. -/
theorem ofQ'_rationalCutoffFactorProduct_equiv_lifted
    {Factor : Type} (term : Factor → Nat → Q')
    (factors : List Factor) (cutoff : Nat) :
    CReal.Equiv
      (CReal.ofQ'
        (rationalCutoffFactorProduct term factors cutoff))
      (liftedCutoffFactorProduct term factors cutoff) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun approximation => by
      rw [liftedCutoffFactorProduct_approx]
      exact Q'.eqv_refl _)

/-! ## 2. Bounds on completed finite tails -/

/-- The multiplicative bound attached to a finite factor list. -/
def finiteFactorBound {Factor : Type}
    (bound : Q') : List Factor → Q'
  | [] => 1
  | _ :: tail => bound * finiteFactorBound bound tail

theorem finiteFactorBound_nonnegative
    {Factor : Type} {bound : Q'} (bound_nonnegative : (0 : Q') ≤ bound) :
    ∀ factors : List Factor,
      (0 : Q') ≤ finiteFactorBound bound factors
  | [] => Q'.zero_le_one
  | _ :: tail =>
      Q'.mul_nonneg _ _
        bound_nonnegative
        (finiteFactorBound_nonnegative bound_nonnegative tail)

/-- Uniform one-factor bounds imply the corresponding bound on every
approximation of the completed finite product. -/
theorem completedFactorProduct_abs_approx_le
    {Factor : Type} (value : Factor → CReal)
    (bound : Q') (bound_nonnegative : (0 : Q') ≤ bound) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        ∀ approximation,
          Q'.abs ((value factor).approx approximation) ≤ bound) →
      ∀ approximation,
        Q'.abs
            ((completedFactorProduct value factors).approx approximation) ≤
          finiteFactorBound bound factors
  | [], _, approximation => by
      change Q'.abs (1 : Q') ≤ 1
      rw [ExpNeg.abs_of_nonneg Q'.zero_le_one]
      exact Q'.le_refl' 1
  | factor :: tail, factor_bound, approximation => by
      change
        Q'.abs
            ((value factor).approx approximation *
              (completedFactorProduct value tail).approx approximation) ≤
          bound * finiteFactorBound bound tail
      refine Q'.le_trans' _ _ _
        (ExpNeg.abs_mul_le
          ((value factor).approx approximation)
          ((completedFactorProduct value tail).approx approximation)) ?_
      exact Q'.mul_le_mul_of_nonneg
        (factor_bound factor List.mem_cons_self approximation)
        (completedFactorProduct_abs_approx_le
          value bound bound_nonnegative tail
          (fun item hitem =>
            factor_bound item
              (List.mem_cons_of_mem factor hitem))
          approximation)
        bound_nonnegative
        (Q'.abs_nonneg
          ((completedFactorProduct value tail).approx approximation))

/-! ## 3. Generic finite-product convergence -/

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ => value) value := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun approximation _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)

/-- Factorwise convergence plus uniform approximation bounds implies
convergence of the simultaneous-cutoff finite product.  The proof is a finite
induction.  At a cons step, `max bound tailBound` supplies precisely the common
bound required by constructive multiplication continuity. -/
theorem liftedCutoffFactorProduct_converges
    {Factor : Type}
    (term : Factor → Nat → Q')
    (value : Factor → CReal)
    (bound : Q') (bound_nonnegative : (0 : Q') ≤ bound) :
    ∀ factors : List Factor,
      (∀ factor, factor ∈ factors →
        CReal.ConvergesTo
          (fun cutoff => CReal.ofQ' (term factor cutoff))
          (value factor)) →
      (∀ factor, factor ∈ factors →
        ∀ cutoff,
          Q'.abs (term factor cutoff) ≤ bound) →
      (∀ factor, factor ∈ factors →
        ∀ approximation,
          Q'.abs ((value factor).approx approximation) ≤ bound) →
      CReal.ConvergesTo
        (liftedCutoffFactorProduct term factors)
        (completedFactorProduct value factors)
  | [], _, _, _ =>
      convergesTo_const (CReal.ofQ' (1 : Q'))
  | factor :: tail, factor_converges, partial_bound, value_bound => by
      let commonBound : Q' :=
        Q'.max' bound (finiteFactorBound bound tail)
      have commonBound_nonnegative :
          (0 : Q') ≤ commonBound :=
        Q'.le_trans' _ _ _
          bound_nonnegative
          (Q'.le_max'_left
            bound (finiteFactorBound bound tail))
      have head_bound :
          ∀ cutoff approximation,
            Q'.abs
                ((CReal.ofQ'
                  (term factor cutoff)).approx approximation) ≤
              commonBound := by
        intro cutoff approximation
        exact Q'.le_trans' _ _ _
          (partial_bound factor List.mem_cons_self cutoff)
          (Q'.le_max'_left
            bound (finiteFactorBound bound tail))
      have tail_value_bound :
          ∀ approximation,
            Q'.abs
                ((completedFactorProduct value tail).approx approximation) ≤
              commonBound := by
        intro approximation
        exact Q'.le_trans' _ _ _
          (completedFactorProduct_abs_approx_le
            value bound bound_nonnegative tail
            (fun item hitem =>
              value_bound item
                (List.mem_cons_of_mem factor hitem))
            approximation)
          (Q'.le_max'_right
            bound (finiteFactorBound bound tail))
      exact CReal.convergesTo_mul
        commonBound_nonnegative
        head_bound
        tail_value_bound
        (factor_converges factor List.mem_cons_self)
        (liftedCutoffFactorProduct_converges
          term value bound bound_nonnegative tail
          (fun item hitem =>
            factor_converges item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            partial_bound item
              (List.mem_cons_of_mem factor hitem))
          (fun item hitem =>
            value_bound item
              (List.mem_cons_of_mem factor hitem)))

/-- Explicit convergence of the embedded literal rational cutoff products,
obtained from the recursive product theorem by termwise `CReal.Equiv`
transport. -/
theorem rationalCutoffFactorProduct_converges
    {Factor : Type}
    (term : Factor → Nat → Q')
    (value : Factor → CReal)
    (bound : Q') (bound_nonnegative : (0 : Q') ≤ bound)
    (factors : List Factor)
    (factor_converges :
      ∀ factor, factor ∈ factors →
        CReal.ConvergesTo
          (fun cutoff => CReal.ofQ' (term factor cutoff))
          (value factor))
    (partial_bound :
      ∀ factor, factor ∈ factors →
        ∀ cutoff,
          Q'.abs (term factor cutoff) ≤ bound)
    (value_bound :
      ∀ factor, factor ∈ factors →
        ∀ approximation,
          Q'.abs ((value factor).approx approximation) ≤ bound) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (rationalCutoffFactorProduct term factors cutoff))
      (completedFactorProduct value factors) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (t :=
      fun cutoff =>
        CReal.ofQ'
          (rationalCutoffFactorProduct term factors cutoff))
  · intro cutoff
    exact CReal.Equiv.symm
      (ofQ'_rationalCutoffFactorProduct_equiv_lifted
        term factors cutoff)
  · exact liftedCutoffFactorProduct_converges
      term value bound bound_nonnegative factors
      factor_converges partial_bound value_bound

/-! ## 4. Genuine SU(2) all-label cutoff-product specialization -/

/-- The common-cutoff rational retained kinetic product made from the genuine
finite SU(2) pointwise heat partials. -/
def pointwiseHeatCutoffRetainedKinetic
    {Source Target State Factor : Type}
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (source : Source) (target : Target)
    (path : List State) (cutoff : Nat) : Q' :=
  rationalCutoffFactorProduct
    (fun factor cutoff' =>
      pointwiseHeatPartial
        (w source target path factor)
        (x source target path factor)
        cutoff')
    factors cutoff

private theorem pointwiseHeatPartial_abs_le_ceiling
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (cutoff : Nat) :
    Q'.abs (pointwiseHeatPartial w x cutoff) ≤
      allLabelHaarCeiling := by
  have partial_nonnegative :
      (0 : Q') ≤ pointwiseHeatPartial w x cutoff :=
    Q'.le_trans' _ _ _
      (Q'.le_of_lt allLabelHaarFloor_pos)
      (allLabelHaarFloor_le_pointwiseHeatPartial
        hw0 hw hxLower hxUpper cutoff)
  rw [ExpNeg.abs_of_nonneg partial_nonnegative]
  exact pointwiseHeatPartial_le_allLabelHaarCeiling
    hw0 hw hxLower hxUpper cutoff

/-- For any finite retained factor list, the literal common-cutoff SU(2)
all-label product converges to the completed retained kinetic product. -/
theorem pointwiseHeatCutoffRetainedKinetic_converges
    {Source Target State Factor : Type}
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (source : Source) (target : Target) (path : List State) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pointwiseHeatCutoffRetainedKinetic
            factors w x source target path cutoff))
      (completedPointwiseRetainedKinetic
        factors w x
        w_nonnegative w_le_half x_lower x_upper
        source target path) := by
  unfold pointwiseHeatCutoffRetainedKinetic
  unfold completedPointwiseRetainedKinetic
  apply rationalCutoffFactorProduct_converges
    (bound := allLabelHaarCeiling)
    (bound_nonnegative :=
      Q'.le_of_lt allLabelHaarCeiling_pos)
  · intro factor _
    exact pointwiseHeatPartials_converge
      (w_nonnegative source target path factor)
      (w_le_half source target path factor)
      (x_lower source target path factor)
      (x_upper source target path factor)
  · intro factor _ cutoff
    exact pointwiseHeatPartial_abs_le_ceiling
      (w_nonnegative source target path factor)
      (w_le_half source target path factor)
      (x_lower source target path factor)
      (x_upper source target path factor)
      cutoff
  · intro factor _ approximation
    change
      Q'.abs
          (pointwiseHeatPartial
            (w source target path factor)
            (x source target path factor)
            approximation) ≤
        allLabelHaarCeiling
    exact pointwiseHeatPartial_abs_le_ceiling
      (w_nonnegative source target path factor)
      (w_le_half source target path factor)
      (x_lower source target path factor)
      (x_upper source target path factor)
      approximation

/-- The requested BF4 form: for a literal 23-factor retained carrier, the
same cutoff products converge to the completed BF4 retained kinetic weight.
The length hypothesis records the physical retained count; convergence itself
uses only finiteness. -/
theorem pointwiseHeatCutoffBF4RetainedKinetic_converges
    {Source Target State Factor : Type}
    (factors : List Factor)
    (_factor_count : factors.length = bf4SpatialCycleCount)
    (w x : Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (source : Source) (target : Target) (path : List State) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pointwiseHeatCutoffRetainedKinetic
            factors w x source target path cutoff))
      (completedPointwiseRetainedKinetic
        factors w x
        w_nonnegative w_le_half x_lower x_upper
        source target path) :=
  pointwiseHeatCutoffRetainedKinetic_converges
    factors w x
    w_nonnegative w_le_half x_lower x_upper
    source target path

end YMGap.Continuum.BF4CompletedProductLimitBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedProductLimitBridge.rationalCutoffFactorProduct_converges
#print axioms YMGap.Continuum.BF4CompletedProductLimitBridge.pointwiseHeatCutoffRetainedKinetic_converges
#print axioms YMGap.Continuum.BF4CompletedProductLimitBridge.pointwiseHeatCutoffBF4RetainedKinetic_converges
