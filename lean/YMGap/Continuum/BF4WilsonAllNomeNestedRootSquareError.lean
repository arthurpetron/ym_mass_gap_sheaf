/-
# Exact finite square error for nested roots on the original Wilson carrier

This is a finite polynomial identity.  Its error is the positive-coefficient
composed scalar square defect, whose mass is bounded by the original scalar
root residual.  Passing the identity to fixed-depth limits is a separate step.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
import YMGap.Continuum.ComplementRootNestedMass
import YMGap.Continuum.SU2ClassPolynomialExtensionalReflection

namespace YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion (CoeffNonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower)
open YMGap.Continuum.ComplementRootComposition
open YMGap.Continuum.ComplementRootError
open YMGap.Continuum.ComplementRootNestedMass
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra (compose eval_compose)
open YMGap.Continuum.SU2ClassPolynomialAlgebra (PolyEqv)
open YMGap.Continuum.SU2ClassPolynomialExtensionalReflection (allZero_psub_of_polyEqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "DP" => defectPower hw0 hw1

/-- The exact positive finite square error, with the inner defect polynomial
first in the repository's Horner-composition convention. -/
def nestedError (k n : Nat) : Poly :=
  compose (nested k n) (errorPolynomial n)

def rootPolynomial (k n : Nat) : Poly :=
  psub [1] (nested k n)

theorem nestedError_coeffNonnegative (k n : Nat) :
    CoeffNonnegative (nestedError k n) :=
  compose_coeffNonnegative _ _ (nested_coeffNonnegative k n)
    (error_coeffNonnegative n)

private theorem eval_one (t : Q') : (eval ([1] : Poly) t).eqv 1 := by
  change ((1 : Q') + t*0).eqv 1
  exact Q'.eqv_trans _ _ _
    (q_add_congr (Q'.eqv_refl 1) (q_mul_zero t))
    (q_add_zero_eqv 1)

private theorem eval_rootPolynomial (k n : Nat) (t : Q') :
    (eval (rootPolynomial k n) t).eqv (1 - eval (nested k n) t) := by
  exact Q'.eqv_trans _ _ _ (eval_psub _ _ _)
    (q_add_congr (eval_one t) (Q'.eqv_refl _))

private theorem square_congr {a b : Q'} (h : a.eqv b) :
    (a*a).eqv (b*b) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h)

/-- A pointwise identity is reflected to all coefficients, not postulated as
an operator functional calculus. -/
theorem finite_square_polynomial_eqv (k n : Nat) :
    PolyEqv
      (pmul (rootPolynomial (k+1) n) (rootPolynomial (k+1) n))
      (padd (rootPolynomial k n) (nestedError k n)) := by
  intro t
  let q := nested k n
  let a := eval q t
  let b := eval (ComplementRootPolynomial.polynomial n) a
  have hnext : (eval (nested (k+1) n) t).eqv b :=
    eval_compose q t (ComplementRootPolynomial.polynomial n)
  have herror : (eval (nestedError k n) t).eqv
      (eval (errorPolynomial n) a) :=
    eval_compose q t (errorPolynomial n)
  have hroot : (eval (rootPolynomial (k+1) n) t).eqv (1-b) :=
    Q'.eqv_trans _ _ _ (eval_rootPolynomial (k+1) n t)
      (q_add_congr (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ hnext))
  have hzero : (eval (rootPolynomial k n) t).eqv (1-a) :=
    eval_rootPolynomial k n t
  have hbridge : ((1-b)*(1-b)).eqv
      ((1-a) + eval (errorPolynomial n) a) := by
    have hring : ((1-b)*(1-b)).eqv
        ((1-a) + ((1-b)*(1-b) - (1-a))) :=
      poly_identity_of_normal_eq
        (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.const 1) (.neg (.var 0))))
        (.add (.add (.const 1) (.neg (.var 1)))
          (.add
            (.mul (.add (.const 1) (.neg (.var 0)))
              (.add (.const 1) (.neg (.var 0))))
            (.neg (.add (.const 1) (.neg (.var 1))))))
        (by decide) (fun | 0 => b | _ => a)
    exact Q'.eqv_trans _ _ _ hring
      (q_add_congr (Q'.eqv_refl _)
        (Q'.eqv_symm (eval_error n a)))
  exact Q'.eqv_trans _ _ _ (eval_pmul _ _ t)
    (Q'.eqv_trans _ _ _ (square_congr hroot)
      (Q'.eqv_trans _ _ _ hbridge
        (Q'.eqv_trans _ _ _
          (q_add_congr (Q'.eqv_symm hzero) (Q'.eqv_symm herror))
          (Q'.eqv_symm (eval_padd _ _ t)))))

private theorem actionFrom_allZero (p : Poly) (i : Nat) (x : V)
    (hp : allZero p) : actionFrom hw0 hw1 p i x = Z := by
  induction p generalizing i with
  | nil => rfl
  | cons c p ih =>
      have hparts : decide (c.eqv 0) = true ∧ allZeroB p = true := by
        have h := hp
        rw [allZero, allZeroB, Bool.and_eq_true] at h
        exact h
      have hc : c.eqv 0 := of_decide_eq_true hparts.1
      change A (S c (DP i x)) (actionFrom hw0 hw1 p (i+1) x) = Z
      rw [completedSmul_congr hw0 hw1 hc, completedSmul_zero,
        ih (i+1) hparts.2, completedZero_add]

/-- Rational-polynomial extensionality descends to the actual finite defect
action, using its zero-coefficient reflection certificate. -/
theorem action_eq_of_polyEqv (p q : Poly) (hpq : PolyEqv p q) (x : V) :
    action hw0 hw1 p x = action hw0 hw1 q x := by
  have hz : action hw0 hw1 (psub p q) x = Z :=
    actionFrom_allZero hw0 hw1 (psub p q) 0 x
      (allZero_psub_of_polyEqv hpq)
  apply (completedDist_zero_iff hw0 hw1 _ _).mp
  unfold completedDist
  rw [← action_sub hw0 hw1 p q x, hz, completedInner_zero_left]

/-- The finite square law has an explicit positive error on the SAME
original completed Wilson carrier. -/
theorem finite_square_action_identity (k n : Nat) (x : V) :
    action hw0 hw1
        (pmul (rootPolynomial (k+1) n) (rootPolynomial (k+1) n)) x =
      A (action hw0 hw1 (rootPolynomial k n) x)
        (action hw0 hw1 (nestedError k n) x) := by
  rw [action_eq_of_polyEqv hw0 hw1 _ _
    (finite_square_polynomial_eqv k n) x,
    action_add]

/-- Pairing form used to pass this exact finite square relation through the
already constructed fixed-depth represented limits. -/
theorem finite_square_pairing_identity (k n : Nat) (x y : V) :
    B (action hw0 hw1 (rootPolynomial (k+1) n) x)
      (action hw0 hw1 (rootPolynomial (k+1) n) y) =
      RCadd
        (B x (action hw0 hw1 (rootPolynomial k n) y))
        (B x (action hw0 hw1 (nestedError k n) y)) := by
  rw [action_symmetric hw0 hw1 (rootPolynomial (k+1) n) x,
    ← action_pmul hw0 hw1 (rootPolynomial (k+1) n)
      (rootPolynomial (k+1) n) y,
    finite_square_action_identity hw0 hw1 k n y,
    completedInner_add_right]

/-- Composing the positive error with a mass-at-most-one polynomial does not
increase its coefficient mass. -/
theorem nestedError_mass_le (k n : Nat) :
    eval (nestedError k n) 1 ≤
      ComplementRootMass.residual n * ComplementRootMass.residual n := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (eval_compose (nested k n) 1 (errorPolynomial n)))
    (Q'.le_trans' _ _ _
      (eval_monotone _ (error_coeffNonnegative n)
        (mass_nonnegative k n) (mass_le_one k n))
      (Q'.le_of_eqv (error_mass n)))

theorem nestedError_action_norm_bound (k n : Nat) (x : V) :
    RCle (B (action hw0 hw1 (nestedError k n) x)
        (action hw0 hw1 (nestedError k n) x))
      (RCscale
        ((ComplementRootMass.residual n * ComplementRootMass.residual n) *
          (ComplementRootMass.residual n * ComplementRootMass.residual n))
        (B x x)) := by
  have hmass := nestedError_mass_le k n
  have hnonneg := BF4WilsonAllNomeDefectPolynomial.mass_nonnegative (nestedError k n)
    (nestedError_coeffNonnegative k n)
  have hcap0 : (0 : Q') ≤ ComplementRootMass.residual n * ComplementRootMass.residual n :=
    Q'.mul_nonneg _ _ (ComplementRootMass.residual_nonnegative n)
      (ComplementRootMass.residual_nonnegative n)
  exact RCle_trans
    (action_norm_bound hw0 hw1 (nestedError k n)
      (nestedError_coeffNonnegative k n) x)
    (RCscale_scalar_mono
      (Q'.mul_le_mul_of_nonneg hmass hmass hcap0 hnonneg)
      (completedInner_nonnegative hw0 hw1 x))

#print axioms finite_square_polynomial_eqv
#print axioms action_eq_of_polyEqv
#print axioms finite_square_action_identity
#print axioms finite_square_pairing_identity
#print axioms nestedError_coeffNonnegative
#print axioms nestedError_mass_le
#print axioms nestedError_action_norm_bound

end YMGap.Continuum.BF4WilsonAllNomeNestedRootSquareError
