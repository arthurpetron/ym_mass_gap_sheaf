/-
# Original polynomial-moment convergence for every supplied Cauchy vector

Finite Bernstein row moments and their original polynomial limits retain
CReal representatives and QCauchy moduli. Signed coefficients propagate
the all-vector moment error with the explicit rational ceiling
  (sum |c_r| C(r))/(n+1) * normCap(X).
The input tolerance epsilon/(normCap(X)+1) supplies a convergence rate.

The limit is pinned to <x,p(T2)x> for the SAME original completed x.
The cap is computed from supplied Cauchy data, not selected from a quotient;
no normalization, cyclic density or spectral realization is assumed.
This is fixed SU(2) nome/spacing, not continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments (momentRepresentative momentCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows (node)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence (wordRealSum wordRealSumCauchy wordRealSum_pin rat_mono)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (combine combineCauchy combine_pin combineRC evalAt polynomialVector errorAt errorAt_factor)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar (rationalCauchy)
open YMGap.Continuum.RationalScalarTwoSidedError (scale_error add_error)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

def powerRepresentative (X : seminorm.Cauchy) (n r : Nat) : CReal :=
  wordRealSum (n+1) (fun p => CReal.mul (ofQ' (node n p^r))
    (momentRepresentative X (timeCount p) (defectCount p)))

def powerCauchy (X : seminorm.Cauchy) (n r : Nat) : QCauchy (powerRepresentative X n r).approx :=
  wordRealSumCauchy _ _ (fun p => scalarMulCauchy _ _ (rationalCauchy _)
    (momentCauchy X (timeCount p) (defectCount p)))

theorem powerRepresentative_pin (X : seminorm.Cauchy) (n r : Nat) :
    Quotient.mk crealSetoid (powerRepresentative X n r)=powerMoment (point X) n r := by
  rw [powerRepresentative,wordRealSum_pin]
  change wordSum (n+1) (fun p => RCscale (node n p^r)
    (Quotient.mk crealSetoid (momentRepresentative X (timeCount p) (defectCount p))))=_
  unfold powerMoment average
  apply congrArg (wordSum (n+1))
  funext p
  apply congrArg (RCscale (node n p^r))
  simp only [wordMoment,Nat.zero_add]
  exact (BF4ExactSlabThermodynamicTimeDefectMoments.moment_pin X (timeCount p) (defectCount p)).symm

def limitRepresentative (X : seminorm.Cauchy) (r : Nat) : CReal := momentRepresentative X r 0

def limitCauchy (X : seminorm.Cauchy) (r : Nat) : QCauchy (limitRepresentative X r).approx := momentCauchy X r 0

theorem limitRepresentative_pin (X : seminorm.Cauchy) (r : Nat) :
    Quotient.mk crealSetoid (limitRepresentative X r)=moment (point X) r :=
  (BF4ExactSlabThermodynamicTimeDefectMoments.moment_pin X r 0).symm

theorem average_evalAt (x : Completion) (n : Nat) (p : QPoly.Poly) (r : Nat) :
    average x n (fun w => evalAt p r (node n w))=combineRC (powerMoment x n) p r := by
  induction p generalizing r with
  | nil => exact (average_const x n 0).trans (scale_zero _)
  | cons c p ih =>
      change average x n (fun w => c*node n w^r+evalAt p (r+1) (node n w))=_
      rw [average_add,average_scale,ih]
      rfl

def rowAt (X : seminorm.Cauchy) (n : Nat) (p : QPoly.Poly) (r : Nat) : CReal :=
  combine (powerRepresentative X n) p r

def limitAt (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat) : CReal := combine (limitRepresentative X) p r

def rowCauchy (X : seminorm.Cauchy) (n : Nat) (p : QPoly.Poly) (r : Nat) : QCauchy (rowAt X n p r).approx :=
  combineCauchy _ (powerCauchy X n) p r

def polynomialCauchy (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat) : QCauchy (limitAt X p r).approx :=
  combineCauchy _ (limitCauchy X) p r

theorem rowAt_pin (X : seminorm.Cauchy) (n : Nat) (p : QPoly.Poly) (r : Nat) :
    Quotient.mk crealSetoid (rowAt X n p r)=average (point X) n (fun w => evalAt p r (node n w)) := by
  rw [rowAt,combine_pin]
  simp only [powerRepresentative_pin]
  exact (average_evalAt (point X) n p r).symm

theorem limitAt_pin (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat) :
    Quotient.mk crealSetoid (limitAt X p r)=completedInner (point X) (polynomialVector (point X) p r) := by
  induction p generalizing r with
  | nil => exact (completedInner_zero_right _).symm
  | cons c p ih =>
      change RCadd (RCscale c (Quotient.mk crealSetoid (limitRepresentative X r)))
        (Quotient.mk crealSetoid (limitAt X p (r+1)))=_
      rw [ih,limitRepresentative_pin,moment_pin,polynomialVector,completedInner_add_right,completedInner_smul_right]
      rfl

def cappedError (B : Q') (n : Nat) : QPoly.Poly → Nat → Q'
  | [],_ => 0
  | c::p,r => Q'.abs c*(BernsteinFallingProductError.error n r*B)+cappedError B n p (r+1)

theorem cappedError_factor (B : Q') (n : Nat) (p : QPoly.Poly) (r : Nat) :
    Q'.eqv (cappedError B n p r) (errorAt n p r*B) := by
  induction p generalizing r with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_mul B)
  | cons c p ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (ih (r+1)))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 2)))
          (.mul (.add (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
          (fun | 0 => Q'.abs c | 1 => BernsteinFallingProductError.error n r | 2 => B | _ => errorAt n p (r+1)))

theorem polynomial_error (X : seminorm.Cauchy) (n : Nat) (p : QPoly.Poly) (r : Nat) :
    RCle (Quotient.mk crealSetoid (rowAt X n p r))
      (RCadd (Quotient.mk crealSetoid (limitAt X p r)) (rat (cappedError (normCap X) n p r))) ∧
    RCle (Quotient.mk crealSetoid (limitAt X p r))
      (RCadd (Quotient.mk crealSetoid (rowAt X n p r)) (rat (cappedError (normCap X) n p r))) := by
  induction p generalizing r with
  | nil =>
      constructor <;> intro epsilon he <;> refine ⟨0,fun _ _ => ?_⟩ <;>
        change (0 : Q')≤0+0+epsilon
      all_goals simpa only [Q'.zero_add'] using Q'.le_of_lt he
  | cons c p ih =>
      have h := powerMoment_error_cap X n r
      have he := Q'.mul_nonneg _ _ (BernsteinFallingProductError.error_nonnegative n r) (normCap_nonnegative X)
      have h1 := scale_error c _ he _ _ h.1 h.2
      have h2 := scale_error c _ he _ _ h.2 h.1
      rw [← powerRepresentative_pin,← limitRepresentative_pin] at h1 h2
      exact ⟨add_error _ _ _ _ _ _ h1 (ih (r+1)).1,add_error _ _ _ _ _ _ h2 (ih (r+1)).2⟩

def polynomialModulus (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat)
    (epsilon : Q') (he : (0 : Q')<epsilon) : Nat :=
  BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomialModulus p r
    (linearTolerance (normCap X) (normCap_nonnegative X) epsilon)
    (linearTolerance_pos _ _ he)

theorem cappedError_small (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : polynomialModulus X p r epsilon he≤n) :
    cappedError (normCap X) n p r≤epsilon := by
  have h := BF4ExactSlabThermodynamicBernsteinPolynomialMoments.errorAt_small p r
    (linearTolerance (normCap X) (normCap_nonnegative X) epsilon) (linearTolerance_pos _ _ he) n hn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (cappedError_factor (normCap X) n p r))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h (normCap_nonnegative X))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (linearTolerance_budget (normCap X) (normCap_nonnegative X) he)))

theorem polynomial_error_le (X : seminorm.Cauchy) (p : QPoly.Poly) (r : Nat)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : polynomialModulus X p r epsilon he≤n) :
    leEv (rowAt X n p r) (CReal.add (limitAt X p r) (ofQ' epsilon)) ∧
    leEv (limitAt X p r) (CReal.add (rowAt X n p r) (ofQ' epsilon)) := by
  have hh := rat_mono (cappedError_small X p r epsilon he n hn)
  have h := polynomial_error X n p r
  exact ⟨RCle_trans h.1 (RCadd_le_add (RCle_refl _) hh),RCle_trans h.2 (RCadd_le_add (RCle_refl _) hh)⟩

def polynomialConvergenceCertificate (X : seminorm.Cauchy) (p : QPoly.Poly) :
    Σ' a : CReal, QCauchy a.approx ×'
      (Quotient.mk crealSetoid a=completedInner (point X) (polynomialVector (point X) p 0)) ×'
      {M : (epsilon : Q') → (0 : Q')<epsilon → Nat // ∀ epsilon he n,M epsilon he≤n →
        leEv (rowAt X n p 0) (CReal.add a (ofQ' epsilon)) ∧
        leEv a (CReal.add (rowAt X n p 0) (ofQ' epsilon))} :=
  ⟨limitAt X p 0,polynomialCauchy X p 0,limitAt_pin X p 0,⟨polynomialModulus X p 0,polynomial_error_le X p 0⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.powerRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.powerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.powerRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.limitRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.limitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.limitRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.average_evalAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.rowAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.limitAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.rowCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.polynomialCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.rowAt_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.limitAt_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.cappedError
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.cappedError_factor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.polynomial_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.polynomialModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.cappedError_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.polynomial_error_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialConvergence.polynomialConvergenceCertificate
