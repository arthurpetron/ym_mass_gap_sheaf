/-
The original dyadic resolvent limit is bounded, symmetric and rational-linear,
and satisfies A u=T(x-lambda*u). The finite derivative quotients INCLUDING T
are uniformly contractive, so moving resolvent inputs can pass to the limit.
Unshifted state quotients have no such uniform bound; they are not used.
This equation on the full original carrier is not by itself a sector-domain
or physical Hamiltonian identification. The original time kernel remains.
-/

import YMGap.Continuum.BF4WilsonAllNomeResolventLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicResolventLaws
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

namespace YMGap.Continuum.BF4WilsonAllNomeResolventEquation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (completedInner_sub_left)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
  (differenceQuotient derivativeAction derivativeAction_pin quotientRows quotientRows_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
  (quotient_symmetric quotient_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent (dyadic)
open YMGap.Continuum.BF4WilsonAllNomeDyadicResolventLaws
open YMGap.Continuum.BF4WilsonAllNomeResolventLimit
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (completedDist_sub_le)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear (completedDist_smul)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "Q" => differenceQuotient hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "R" => resolvent hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem resolvent_norm_bound (lambda : Q') (hl : (0 : Q') < lambda) (x : V) :
    RCle (B (R lambda hl x) (R lambda hl x))
      (RCscale (Q'.recipPos lambda hl * Q'.recipPos lambda hl) (B x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_norm_bound hw0 hw1 (resolventRows hw0 hw1 lambda hl X)
  intro n
  rw [resolventRows_pin]
  exact dyadic_norm_bound hw0 hw1 n lambda hl (Class X)

theorem resolvent_symmetric (lambda : Q') (hl : (0 : Q') < lambda) (x y : V) :
    B (R lambda hl x) y = B x (R lambda hl y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1
    (resolventRows hw0 hw1 lambda hl X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (resolventRows hw0 hw1 lambda hl Y) (fun n => by
      rw [resolventRows_pin, constantRows_point, constantRows_point, resolventRows_pin]
      exact dyadic_symmetric hw0 hw1 n lambda hl (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  exact h

theorem resolvent_add (lambda : Q') (hl : (0 : Q') < lambda) (x y : V) :
    R lambda hl (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (R lambda hl x) (R lambda hl y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [resolvent_symmetric, completedInner_add_left, completedInner_add_left,
    resolvent_symmetric, resolvent_symmetric]

theorem resolvent_smul (lambda : Q') (hl : (0 : Q') < lambda) (c : Q') (x : V) :
    R lambda hl (S c x) = S c (R lambda hl x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [resolvent_symmetric, completedInner_smul_left, completedInner_smul_left,
    resolvent_symmetric]

theorem resolvent_sub (lambda : Q') (hl : (0 : Q') < lambda) (x y : V) :
    R lambda hl (Sub x y) = Sub (R lambda hl x) (R lambda hl y) := by
  unfold completedSub completedNeg
  rw [resolvent_add, resolvent_smul]

private theorem quotient_sub (depth : Nat) (x y : V) :
    Q depth (Sub x y) = Sub (Q depth x) (Q depth y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [quotient_symmetric, completedInner_sub_left, completedInner_sub_left,
    quotient_symmetric, quotient_symmetric]

/-- Uniform in depth precisely because these quotients include the original T. -/
theorem quotient_distance_bound (depth : Nat) (x y : V) :
    RCle (d (Q depth x) (Q depth y)) (d x y) := by
  unfold completedDist
  rw [← quotient_sub]
  exact quotient_norm_bound hw0 hw1 depth (Sub x y)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem residual_distance_bound (lambda : Q') (x y z : V) :
    RCle (d (T 1 (Sub x (S lambda y))) (T 1 (Sub x (S lambda z))))
      (RCadd (RCscale (lambda*lambda) (d y z)) (RCscale (lambda*lambda) (d y z))) := by
  have h := completedDist_sub_le hw0 hw1 x x (S lambda y) (S lambda z)
  rw [(completedDist_zero_iff hw0 hw1 x x).mpr rfl, rc_zero_add, rc_zero_add,
    completedDist_smul] at h
  exact RCle_trans (completedDist_time hw0 hw1 1 _ _) h

def equationFactor (lambda : Q') : Q' := 2+4*(lambda*lambda)

theorem equationFactor_nonnegative (lambda : Q') : (0 : Q') ≤ equationFactor lambda :=
  Q'.zero_le_add _ _ (by decide) (Q'.mul_nonneg _ _ (by decide)
    (SumOfSquares.q_mul_self_nonneg lambda))

private theorem rc_error_budget (lambda : Q') (a : RC) :
    RCadd (RCadd a a)
      (RCadd (RCadd (RCscale (lambda*lambda) a) (RCscale (lambda*lambda) a))
        (RCadd (RCscale (lambda*lambda) a) (RCscale (lambda*lambda) a))) =
      RCscale (equationFactor lambda) a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 1))
        (.add
          (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
            (.mul (.mul (.var 0) (.var 0)) (.var 1)))
          (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
            (.mul (.mul (.var 0) (.var 0)) (.var 1)))))
      (.mul (.add (.const 2) (.mul (.const 4) (.mul (.var 0) (.var 0)))) (.var 1))
      (by decide) (fun | 0 => lambda | _ => X.approx n)))

/-- Moving the finite input costs a depth-INDEPENDENT squared-distance factor. -/
theorem equation_error_bound (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x u : V) :
    RCle (d (Q depth u) (T 1 (Sub x (S lambda u))))
      (RCscale (equationFactor lambda) (d (dyadic hw0 hw1 depth lambda hl x) u)) := by
  let uk := dyadic hw0 hw1 depth lambda hl x
  have hfirst := quotient_distance_bound hw0 hw1 depth u uk
  rw [completedDist_symm hw0 hw1 u uk] at hfirst
  have hsecond := residual_distance_bound hw0 hw1 lambda x uk u
  rw [← dyadic_quotient_equation hw0 hw1 depth lambda hl x] at hsecond
  have h := RCle_trans (completedDist_triangle hw0 hw1 (Q depth u)
    (Q depth uk) (T 1 (Sub x (S lambda u))))
    (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
  rw [rc_error_budget] at h
  exact h

def equationModulus (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') : Nat :=
  convergenceModulus hw0 hw1 lambda hl X
    (linearTolerance (equationFactor lambda) (equationFactor_nonnegative lambda) epsilon)

theorem equation_approximation (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : equationModulus hw0 hw1 lambda hl X epsilon ≤ n) :
    RCle (d (Q n (R lambda hl (Class X)))
      (T 1 (Sub (Class X) (S lambda (R lambda hl (Class X)))))) (rat epsilon) := by
  have ha := approximation hw0 hw1 lambda hl X _
    (linearTolerance_pos _ _ he) n hn
  have h := RCle_trans (equation_error_bound hw0 hw1 n lambda hl (Class X)
    (R lambda hl (Class X)))
    (RCscale_mono (equationFactor_nonnegative lambda) ha)
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    linearTolerance_budget (equationFactor lambda) (equationFactor_nonnegative lambda) he))

/-- The actual limit solves the original derivative equation, with T retained. -/
theorem resolvent_equation (lambda : Q') (hl : (0 : Q') < lambda) (x : V) :
    A (R lambda hl x) = T 1 (Sub x (S lambda (R lambda hl x))) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [← outputRepresentative_pin hw0 hw1 lambda hl X, derivativeAction_pin]
  apply limit_unique hw0 hw1
    (quotientRows hw0 hw1 (outputRepresentative hw0 hw1 lambda hl X))
    _ (equationModulus hw0 hw1 lambda hl X)
  intro epsilon he n hn
  rw [quotientRows_pin, outputRepresentative_pin]
  exact equation_approximation hw0 hw1 lambda hl X epsilon he n hn

#print axioms resolvent_norm_bound
#print axioms resolvent_symmetric
#print axioms resolvent_add
#print axioms resolvent_smul
#print axioms resolvent_sub
#print axioms quotient_distance_bound
#print axioms equationFactor
#print axioms equationFactor_nonnegative
#print axioms equation_error_bound
#print axioms equationModulus
#print axioms equation_approximation
#print axioms resolvent_equation

end YMGap.Continuum.BF4WilsonAllNomeResolventEquation
