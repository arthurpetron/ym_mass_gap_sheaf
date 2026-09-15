/-
# Constructed bounded symmetric ORIGINAL uniform-sequence action

Linearity and symmetry pass through the actual represented row limits.
Every uniformly Cauchy polynomial sequence produces a bounded operator:
no additional uniform norm-bound hypothesis is required. At N=modulus(1),
the tail differs from p_N by at most one on [0,1]. The original polynomial
norm estimate and the norm-of-sum inequality give the computed squared-
norm factor 2+2*normFactor(p_N). Its reciprocal budget gives a usable
input-continuity modulus. Supplied sharper eventual interval bounds also
pass to the limit without retaining a finite-prefix loss.

These are laws of the SAME original fixed-nome/spacing transfer calculus,
not a spectral model, a square-root construction, time injectivity or a
physical-scale/continuum gap. No additional physical premise is introduced.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (normFactor normFactor_nonnegative vector_norm_bound linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction (operatorRows operatorRows_pin operator_rowLimit)
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear (addRows addRows_pin rowLimit_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (norm_add_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- A finite prefix cannot affect the norm bound of the constructed original limit. -/
theorem rowLimit_norm_upper_eventual (R : CauchyRows) (N : Nat) (b : RC)
    (h : ∀ n,N≤n → RCle (completedInner (rowPoint R n) (rowPoint R n)) b) :
    RCle (completedInner (rowLimit R) (rowLimit R)) b := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := max N (pairingModulus R R epsilon)
  exact RCle_trans (row_pairing_bound R R epsilon he n (Nat.le_max_right _ _)).2
    (RCadd_le_add (h n (Nat.le_max_left _ _)) (RCle_refl _))

theorem sequenceAction_add (P : UniformSequence) (x y : Completion) :
    sequenceAction P (completedAdd x y)=completedAdd (sequenceAction P x) (sequenceAction P y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h : representedAction P (addition.mapCauchy X Y)=
      rowLimit (addRows (actionRows P X) (actionRows P Y)) := by
    apply rowLimit_independent
    intro n
    rw [actionRows_pin,addRows_pin,actionRows_pin,actionRows_pin]
    exact vector_base_add (point X) (point Y) (P.polynomial n) 0
  exact h.trans (rowLimit_add _ _)

theorem sequenceAction_smul (P : UniformSequence) (c : Q') (x : Completion) :
    sequenceAction P (completedSmul c x)=completedSmul c (sequenceAction P x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : representedAction P ((scalarContinuous c).mapCauchy X)=
      rowLimit (operatorRows [c] (actionRows P X)) := by
    apply rowLimit_independent
    intro n
    rw [actionRows_pin,operatorRows_pin,actionRows_pin,operator_constant]
    exact vector_base_smul c (point X) (P.polynomial n) 0
  exact h.trans ((operator_rowLimit _ _).trans (operator_constant _ _))

theorem sequenceAction_sub (P : UniformSequence) (x y : Completion) :
    sequenceAction P (completedSub x y)=completedSub (sequenceAction P x) (sequenceAction P y) := by
  unfold completedSub completedNeg
  rw [sequenceAction_add,sequenceAction_smul]

theorem sequenceAction_symmetric (P : UniformSequence) (x y : Completion) :
    completedInner (sequenceAction P x) y=completedInner x (sequenceAction P y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (actionRows P X) (constantRows Y)
    (constantRows X) (actionRows P Y) (by
      intro n
      rw [actionRows_pin,actionRows_pin,constantRows_pin,constantRows_pin]
      exact operator_symmetric _ _ _)
  rw [rowLimit_constant,rowLimit_constant] at h
  exact h

/-- A supplied eventual interval bound is retained sharply on every original vector. -/
theorem sequenceAction_tail_norm_bound (P : UniformSequence) (N : Nat) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ n,N≤n → ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval (P.polynomial n) t)≤M)
    (x : Completion) :
    RCle (completedInner (sequenceAction P x) (sequenceAction P x)) (RCscale (M*M) (completedInner x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_norm_upper_eventual (actionRows P X) N
  intro n hn
  rw [actionRows_pin]
  exact polynomial_norm_bound (point X) _ M hM (h n hn)

/-- The coarse bound is COMPUTED from one explicitly indexed polynomial, not postulated. -/
def sequenceNormFactor (P : UniformSequence) : Q' :=
  (1*1+1*1)+(normFactor (P.polynomial (P.modulus 1))+normFactor (P.polynomial (P.modulus 1)))

theorem sequenceNormFactor_nonnegative (P : UniformSequence) : (0 : Q')≤sequenceNormFactor P :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (normFactor_nonnegative _) (normFactor_nonnegative _))

/-- Uniform Cauchy data alone imply an explicitly bounded operator on the full original carrier. -/
theorem sequenceAction_norm_bound (P : UniformSequence) (x : Completion) :
    RCle (completedInner (sequenceAction P x) (sequenceAction P x))
      (RCscale (sequenceNormFactor P) (completedInner x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let N := P.modulus 1
  apply rowLimit_norm_upper_eventual (actionRows P X) N
  intro n hn
  rw [actionRows_pin]
  have hd := polynomial_difference_bound (point X) (P.polynomial n) (P.polynomial N) 1 Q'.zero_le_one
    (fun t ht h1 => abs_sub_le_of_bounds
      (P.cauchy 1 (by decide) n N hn (Nat.le_refl N) t ht h1).1
      (P.cauchy 1 (by decide) n N hn (Nat.le_refl N) t ht h1).2)
  have hp := vector_norm_bound (P.polynomial N) (point X) 0
  have h := RCle_trans (norm_add_bound
      (completedSub (polynomialOperator (P.polynomial n) (point X)) (polynomialOperator (P.polynomial N) (point X)))
      (polynomialOperator (P.polynomial N) (point X)))
    (RCadd_le_add (RCadd_le_add hd hd) (RCadd_le_add hp hp))
  rw [completedSub_add_cancel,← scale_add,← scale_add,← scale_add] at h
  exact h

theorem sequenceAction_distance_bound (P : UniformSequence) (x y : Completion) :
    RCle (completedDist (sequenceAction P x) (sequenceAction P y))
      (RCscale (sequenceNormFactor P) (completedDist x y)) := by
  have h := sequenceAction_norm_bound P (completedSub x y)
  rw [sequenceAction_sub] at h
  exact h

def inputTolerance (P : UniformSequence) (epsilon : Q') : Q' :=
  linearTolerance (sequenceNormFactor P) (sequenceNormFactor_nonnegative P) epsilon

theorem inputTolerance_pos (P : UniformSequence) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<inputTolerance P epsilon := linearTolerance_pos _ _ he

theorem sequenceAction_close (P : UniformSequence) (x y : Completion)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : RCle (completedDist x y) (rat (inputTolerance P epsilon))) :
    RCle (completedDist (sequenceAction P x) (sequenceAction P y)) (rat epsilon) :=
  RCle_trans (sequenceAction_distance_bound P x y) (RCle_trans
    (RCscale_mono (sequenceNormFactor_nonnegative P) h)
    (leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget _ (sequenceNormFactor_nonnegative P) he)))

/-- Every input sequence constructs its own positive all-vector continuity tolerance. -/
def continuityCertificate (P : UniformSequence) :
    {delta : Q' → Q' // (∀ epsilon : Q',(0 : Q')<epsilon → (0 : Q')<delta epsilon) ∧
      ∀ epsilon : Q',(0 : Q')<epsilon → ∀ x y : Completion,
        RCle (completedDist x y) (rat (delta epsilon)) →
        RCle (completedDist (sequenceAction P x) (sequenceAction P y)) (rat epsilon)} :=
  ⟨inputTolerance P,⟨fun _ he => inputTolerance_pos P he,
    fun epsilon he x y => sequenceAction_close P x y epsilon he⟩⟩

theorem sequenceAction_form_nonnegative (P : UniformSequence)
    (h : ∀ n,∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤QPoly.eval (P.polynomial n) t)
    (x : Completion) : RCnonneg (completedInner (sequenceAction P x) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have hp := rowLimit_pairing_nonnegative (actionRows P X) (constantRows X) (by
    intro n
    rw [actionRows_pin,constantRows_pin,completedInner_symm]
    exact polynomialForm_nonnegative (point X) _ (h n))
  rw [rowLimit_constant] at hp
  exact hp

end YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.rowLimit_norm_upper_eventual
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_tail_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceNormFactor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceNormFactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.inputTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.inputTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.continuityCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear.sequenceAction_form_nonnegative
