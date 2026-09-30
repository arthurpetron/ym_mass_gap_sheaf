/-
# A convergent complementary-root iteration on the ORIGINAL Wilson carrier

The positive polynomials p_0=0, p_(n+1)=(d+p_n^2)/2 act at d=I-T on
the original completion. Their ordered differences have nonnegative
coefficients and vanishing coefficient mass. The resulting same-carrier
norm Cauchy bound constructs a represented limit, without selecting quotient
representatives or invoking a scalar spectral theorem.

This file constructs the limit of the complementary-root approximants.
The square equation, dyadic compatibility, strong continuity and the
regularized-log generator identification are separate obligations.
No spacing calibration, scaling survival or continuum mass gap is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
import YMGap.Continuum.BF4WilsonAllNomeLogSeries
import YMGap.Continuum.ComplementRootPolynomial

namespace YMGap.Continuum.BF4WilsonAllNomeRootIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial
open YMGap.Continuum.BF4WilsonAllNomeLogSeries (defectPowerCauchy defectPowerCauchy_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower time_defectPower)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.ComplementRootPolynomial

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Class" => Quotient.mk (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
  (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- All finite actions have explicitly constructed original representatives. -/
def polynomialCauchy : Poly → Nat → (D).Cauchy → (D).Cauchy
  | [], _, _ => (D).constant (zero width)
  | a::p, i, X => (addition hw0 hw1).mapCauchy
      ((scalarContinuous hw0 hw1 a).mapCauchy (defectPowerCauchy hw0 hw1 i X))
      (polynomialCauchy p (i+1) X)

theorem polynomialCauchy_pin (p : Poly) (i : Nat) (X : (D).Cauchy) :
    Class (polynomialCauchy hw0 hw1 p i X) = actionFrom hw0 hw1 p i (Class X) := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
      change completedAdd hw0 hw1
        (completedSmul hw0 hw1 a (Class (defectPowerCauchy hw0 hw1 i X)))
        (Class (polynomialCauchy hw0 hw1 p (i+1) X)) = _
      rw [defectPowerCauchy_pin, ih]
      rfl

def approximant (n : Nat) (x : V) : V := action hw0 hw1 (polynomial n) x

/-- Retains the difference's signed algebra before using its proved
coefficient positivity; no absolute bound on two separate approximants. -/
theorem ordered_distance_bound (m n : Nat) (hmn : m ≤ n) (x : V) :
    RCle (completedDist hw0 hw1 (approximant hw0 hw1 n x) (approximant hw0 hw1 m x))
      (RCscale (ComplementRootMass.residual m * ComplementRootMass.residual m) (B x x)) := by
  have h := action_distance_bound hw0 hw1 (polynomial n) (polynomial m)
    (ordered_difference_nonnegative hmn) x
  have hd := mass_nonnegative (psub (polynomial n) (polynomial m))
    (ordered_difference_nonnegative hmn)
  have hm : eval (psub (polynomial n) (polynomial m)) 1 ≤ ComplementRootMass.residual m := by
    have he := eval_difference_one m n
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_add_right _ _ (-(ComplementRootMass.mass m))
        (ComplementRootMass.mass_le_one n))
  exact RCle_trans h (RCscale_scalar_mono
    (Q'.mul_le_mul_of_nonneg hm hm (ComplementRootMass.residual_nonnegative m) hd)
    (completedInner_nonnegative hw0 hw1 x))

private theorem cap_tail_small (cap epsilon : Q') (hc : (0 : Q') ≤ cap)
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : max cap.num.toNat epsilon.den ≤ n) :
    (Q'.invSucc n * Q'.invSucc n) * cap ≤ epsilon := by
  have hcap : cap * Q'.invSucc n ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_left _ _) hn)) hc)
      (ExpNeg.mul_invSucc_toNat_le_one cap hc)
  have heq : Q'.eqv ((Q'.invSucc n * Q'.invSucc n)*cap)
      ((cap * Q'.invSucc n)*Q'.invSucc n) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.mul (.var 1) (.var 0)) (.var 0)) (by decide)
      (fun | 0 => Q'.invSucc n | _ => cap)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcap (Q'.invSucc_nonneg n))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le epsilon he))))

/-- Depends on the supplied representative's norm ceiling, not a selected
representative of an arbitrary quotient-valued sequence. -/
def iterationModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  max (4 * normCeiling PD X).num.toNat epsilon.den

private theorem distance_small (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hmn : m ≤ n) (hm : iterationModulus hw0 hw1 X epsilon ≤ m) :
    RCle (completedDist hw0 hw1 (approximant hw0 hw1 n (Class X))
      (approximant hw0 hw1 m (Class X))) (Rq epsilon) := by
  let c := normCeiling PD X
  have hc : (0 : Q') ≤ c := normCeiling_nonnegative PD X
  have hr := Q'.le_trans' _ _ _ (ComplementRootMass.residual_tail_le m)
    (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (ExpNeg.invSucc_le_of_le (Nat.le_succ m)) (by decide))
  have hr0 := ComplementRootMass.residual_nonnegative m
  have h2 : (0 : Q') ≤ 2 * Q'.invSucc m :=
    Q'.mul_nonneg _ _ (by decide) (Q'.invSucc_nonneg m)
  have h := RCle_trans (ordered_distance_bound hw0 hw1 m n hmn (Class X))
    (RCscale_mono (Q'.mul_nonneg _ _ hr0 hr0) (completedInner_diagonal_le_normCeiling PD X))
  have hscale (a b : Q') : RCscale a (Rq b) = Rq (a*b) :=
    Quotient.sound (CRealAlg.ofQ'_mul a b).symm
  rw [hscale] at h
  apply RCle_trans h
  apply leEv_le_ofQ'_of_approx_le
  intro k
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ c
    (Q'.mul_le_mul_of_nonneg hr hr h2 hr0) hc
  have heq : Q'.eqv (((2*Q'.invSucc m)*(2*Q'.invSucc m))*c)
      ((Q'.invSucc m*Q'.invSucc m)*(4*c)) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0))) (.var 1))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.const 4) (.var 1)))
      (by decide) (fun | 0 => Q'.invSucc m | _ => c)
  exact Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (cap_tail_small (4*c) epsilon (Q'.mul_nonneg _ _ (by decide) hc) he m hm))

def iterationRows (X : (D).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => polynomialCauchy hw0 hw1 (polynomial n) 0 X
  modulus := iterationModulus hw0 hw1 X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist hw0 hw1
      (Class (polynomialCauchy hw0 hw1 (polynomial m) 0 X))
      (Class (polynomialCauchy hw0 hw1 (polynomial n) 0 X))) _
    rw [polynomialCauchy_pin, polynomialCauchy_pin]
    change RCle (completedDist hw0 hw1 (approximant hw0 hw1 m (Class X))
      (approximant hw0 hw1 n (Class X))) _
    rcases Nat.le_total m n with hmn | hnm
    · rw [completedDist_symm]
      exact distance_small hw0 hw1 X epsilon he m n hmn hm
    · exact distance_small hw0 hw1 X epsilon he n m hnm hn

theorem iterationRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (iterationRows hw0 hw1 X) n = approximant hw0 hw1 n (Class X) :=
  polynomialCauchy_pin hw0 hw1 (polynomial n) 0 X

/-- The actual same-carrier limit. This name asserts no unchecked square law. -/
def complementLimit : V → V :=
  Quotient.lift (fun X => limit hw0 hw1 (iterationRows hw0 hw1 X)) (fun X Y h => by
    apply limit_independent hw0 hw1
    intro n
    rw [iterationRows_point, iterationRows_point, Quotient.sound h])

def convergenceModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  limitRate hw0 hw1 (iterationRows hw0 hw1 X) epsilon

theorem complementLimit_approximation (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : convergenceModulus hw0 hw1 X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 (approximant hw0 hw1 n (Class X))
      (complementLimit hw0 hw1 (Class X))) (Rq epsilon) := by
  change RCle (completedDist hw0 hw1 (approximant hw0 hw1 n (Class X))
    (limit hw0 hw1 (iterationRows hw0 hw1 X))) _
  rw [← iterationRows_point]
  exact limit_bound hw0 hw1 (iterationRows hw0 hw1 X) epsilon he n hn

def complementLimitCertificate (X : (D).Cauchy) :
    Σ' y : V, Σ' modulus : Q' → Nat,
      (y = complementLimit hw0 hw1 (Class X)) ×'
      (∀ epsilon, (0 : Q') < epsilon → ∀ n, modulus epsilon ≤ n →
        RCle (completedDist hw0 hw1 (approximant hw0 hw1 n (Class X)) y) (Rq epsilon)) :=
  ⟨complementLimit hw0 hw1 (Class X), convergenceModulus hw0 hw1 X, rfl,
    complementLimit_approximation hw0 hw1 X⟩

#print axioms polynomialCauchy_pin
#print axioms ordered_distance_bound
#print axioms iterationRows
#print axioms complementLimit
#print axioms complementLimit_approximation
#print axioms complementLimitCertificate

end YMGap.Continuum.BF4WilsonAllNomeRootIteration
