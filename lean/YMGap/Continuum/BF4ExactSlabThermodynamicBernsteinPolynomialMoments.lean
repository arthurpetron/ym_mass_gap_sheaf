/-
# Signed-polynomial convergence on the ORIGINAL transfer

Every rational coefficient list is evaluated against the already proved
original moments, retaining actual CReal representatives and QCauchy data.
The error is bounded by (sum |c_r| C(r))/N. A computed modulus is returned,
and the limit is pinned to the polynomial in the SAME completed transfer.
No spectral resolution, additional analytic premise or continuum limit.
-/

import YMGap.Continuum.RationalScalarTwoSidedError

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinProbeRows
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarAddCauchy scalarMulCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar (rationalCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.RationalScalarTwoSidedError
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def combine (f : Nat → CReal) : QPoly.Poly → Nat → CReal
  | [],_ => czero
  | c::p,r => CReal.add (CReal.mul (ofQ' c) (f r)) (combine f p (r+1))

def combineCauchy (f : Nat → CReal) (hf : ∀ r,QCauchy (f r).approx) :
    (p : QPoly.Poly) → (r : Nat) → QCauchy (combine f p r).approx
  | [],_ => rationalCauchy 0
  | c::p,r => scalarAddCauchy _ _ (scalarMulCauchy _ _ (rationalCauchy c) (hf r))
      (combineCauchy f hf p (r+1))

def combineRC (f : Nat → RC) : QPoly.Poly → Nat → RC
  | [],_ => RCzero
  | c::p,r => RCadd (RCscale c (f r)) (combineRC f p (r+1))

theorem combine_pin (f : Nat → CReal) (p : QPoly.Poly) (r : Nat) :
    Quotient.mk crealSetoid (combine f p r)=combineRC (fun j => Quotient.mk crealSetoid (f j)) p r := by
  induction p generalizing r with
  | nil => rfl
  | cons c p ih =>
      change RCadd (RCscale c (Quotient.mk crealSetoid (f r)))
        (Quotient.mk crealSetoid (combine f p (r+1)))=_
      rw [ih]
      rfl

def evalAt : QPoly.Poly → Nat → Q' → Q'
  | [],_,_ => 0
  | c::p,r,t => c*t^r+evalAt p (r+1) t

theorem evalAt_horner (p : QPoly.Poly) (r : Nat) (t : Q') :
    Q'.eqv (evalAt p r t) (t^r*QPoly.eval p t) := by
  induction p generalizing r with
  | nil => exact Q'.eqv_symm (QPoly.q_mul_zero _)
  | cons c p ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (ih (r+1)))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 1)) (.var 3)))
          (.mul (.var 1) (.add (.var 0) (.mul (.var 2) (.var 3)))) (by decide)
          (fun | 0 => c | 1 => t^r | 2 => t | _ => QPoly.eval p t))

theorem evalAt_zero (p : QPoly.Poly) (t : Q') : Q'.eqv (evalAt p 0 t) (QPoly.eval p t) :=
  Q'.eqv_trans _ _ _ (evalAt_horner p 0 t) (Q'.one_mul_eqv _)

theorem rowAverage_scale (n : Nat) (c : Q') (f : Word (n+1) → Q') :
    rowAverage n (fun w => c*f w)=RCscale c (rowAverage n f) := by
  unfold rowAverage
  simp only [← RCscale_RCscale,wordSum_scale]

theorem rowAverage_evalAt (n : Nat) (p : QPoly.Poly) (r : Nat) :
    rowAverage n (fun w => evalAt p r (node n w))=combineRC (powerMoment n) p r := by
  induction p generalizing r with
  | nil => exact rowAverage_const n 0
  | cons c p ih =>
      change rowAverage n (fun w => c*node n w^r+evalAt p (r+1) (node n w))=_
      rw [rowAverage_add,rowAverage_scale,ih]
      rfl

def rowAt (n : Nat) (p : QPoly.Poly) (r : Nat) : CReal := combine (powerRepresentative n) p r

def limitAt (p : QPoly.Poly) (r : Nat) : CReal := combine limitRepresentative p r

def rowCauchy (n : Nat) (p : QPoly.Poly) (r : Nat) : QCauchy (rowAt n p r).approx :=
  combineCauchy _ (powerCauchy n) p r

def polynomialCauchy (p : QPoly.Poly) (r : Nat) : QCauchy (limitAt p r).approx :=
  combineCauchy _ limitCauchy p r

theorem rowAt_pin (n : Nat) (p : QPoly.Poly) (r : Nat) :
    Quotient.mk crealSetoid (rowAt n p r)=rowAverage n (fun w => evalAt p r (node n w)) := by
  rw [rowAt,combine_pin]
  simp only [powerRepresentative_pin]
  exact (rowAverage_evalAt n p r).symm

/-- A polynomial of the actual two-step transfer, not a diagonal model. -/
def polynomialVector (x : Completion) : QPoly.Poly → Nat → Completion
  | [],_ => completedZero
  | c::p,r => completedAdd (completedSmul c (completedTime (r+r) x)) (polynomialVector x p (r+1))

theorem limitAt_pin (p : QPoly.Poly) (r : Nat) :
    Quotient.mk crealSetoid (limitAt p r)=completedInner unitProbe.val (polynomialVector unitProbe.val p r) := by
  induction p generalizing r with
  | nil => exact (completedInner_zero_right _).symm
  | cons c p ih =>
      change RCadd (RCscale c (limitMoment r)) (Quotient.mk crealSetoid (limitAt p (r+1)))=_
      rw [ih,limitMoment_pin,polynomialVector,completedInner_add_right,completedInner_smul_right]
      rfl

def errorAt (n : Nat) : QPoly.Poly → Nat → Q'
  | [],_ => 0
  | c::p,r => Q'.abs c*BernsteinFallingProductError.error n r+errorAt n p (r+1)

def coefficientAt : QPoly.Poly → Nat → Q'
  | [],_ => 0
  | c::p,r => Q'.abs c*Q'.ofNat (BernsteinFallingProductError.coefficient r)+coefficientAt p (r+1)

theorem coefficientAt_nonnegative (p : QPoly.Poly) (r : Nat) : (0 : Q')≤coefficientAt p r := by
  induction p generalizing r with
  | nil => exact Q'.le_refl' 0
  | cons c p ih => exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (Q'.abs_nonneg c) (Q'.ofNat_nonneg _)) (ih (r+1))

theorem errorAt_factor (n : Nat) (p : QPoly.Poly) (r : Nat) :
    Q'.eqv (errorAt n p r) (Q'.invSucc n*coefficientAt p r) := by
  induction p generalizing r with
  | nil => exact Q'.eqv_symm (QPoly.q_mul_zero _)
  | cons c p ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (ih (r+1)))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
          (fun | 0 => Q'.abs c | 1 => Q'.invSucc n
               | 2 => Q'.ofNat (BernsteinFallingProductError.coefficient r) | _ => coefficientAt p (r+1)))

theorem polynomial_error (n : Nat) (p : QPoly.Poly) (r : Nat) :
    RCle (Quotient.mk crealSetoid (rowAt n p r)) (RCadd (Quotient.mk crealSetoid (limitAt p r)) (rat (errorAt n p r))) ∧
    RCle (Quotient.mk crealSetoid (limitAt p r)) (RCadd (Quotient.mk crealSetoid (rowAt n p r)) (rat (errorAt n p r))) := by
  induction p generalizing r with
  | nil =>
      constructor <;> intro epsilon he <;> refine ⟨0,fun _ _ => ?_⟩ <;>
        change (0 : Q')≤0+0+epsilon
      all_goals
        simpa only [Q'.zero_add'] using Q'.le_of_lt he
  | cons c p ih =>
      have h := powerMoment_error n r
      have h1 := scale_error c _ (BernsteinFallingProductError.error_nonnegative n r) _ _ h.1 h.2
      have h2 := scale_error c _ (BernsteinFallingProductError.error_nonnegative n r) _ _ h.2 h.1
      rw [← powerRepresentative_pin] at h1 h2
      exact ⟨add_error _ _ _ _ _ _ h1 (ih (r+1)).1,add_error _ _ _ _ _ _ h2 (ih (r+1)).2⟩

/-- The tolerance is positive input; the threshold is returned as data. -/
def polynomialModulus (p : QPoly.Poly) (r : Nat) (epsilon : Q') (he : (0 : Q')<epsilon) : Nat :=
  (mulModulus (coefficientAt p r) epsilon (coefficientAt_nonnegative p r) he).1.den

theorem errorAt_small (p : QPoly.Poly) (r : Nat) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : polynomialModulus p r epsilon he≤n) : errorAt n p r≤epsilon := by
  let d := mulModulus (coefficientAt p r) epsilon (coefficientAt_nonnegative p r) he
  have hs : Q'.invSucc n≤d.1 := Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le d.1 d.2.1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (errorAt_factor n p r))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hs (coefficientAt_nonnegative p r))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) d.2.2))

theorem polynomial_error_le (p : QPoly.Poly) (r : Nat) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : polynomialModulus p r epsilon he≤n) :
    leEv (rowAt n p r) (CReal.add (limitAt p r) (ofQ' epsilon)) ∧
    leEv (limitAt p r) (CReal.add (rowAt n p r) (ofQ' epsilon)) := by
  have hh := rat_mono (errorAt_small p r epsilon he n hn)
  have h := polynomial_error n p r
  exact ⟨RCle_trans h.1 (RCadd_le_add (RCle_refl _) hh),RCle_trans h.2 (RCadd_le_add (RCle_refl _) hh)⟩

def polynomialConvergenceCertificate (p : QPoly.Poly) :
    Σ' a : CReal, QCauchy a.approx ×'
      (Quotient.mk crealSetoid a=completedInner unitProbe.val (polynomialVector unitProbe.val p 0)) ×'
      {M : (epsilon : Q') → (0 : Q')<epsilon → Nat // ∀ epsilon he n,M epsilon he≤n →
        leEv (rowAt n p 0) (CReal.add a (ofQ' epsilon)) ∧
        leEv a (CReal.add (rowAt n p 0) (ofQ' epsilon))} :=
  ⟨limitAt p 0,polynomialCauchy p 0,limitAt_pin p 0,⟨polynomialModulus p 0,polynomial_error_le p 0⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.combine
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.combineCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.combineRC
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.combine_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.evalAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.evalAt_horner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.evalAt_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.rowAverage_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.rowAverage_evalAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.rowAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.limitAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.rowCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomialCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.rowAt_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomialVector
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.limitAt_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.errorAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.coefficientAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.coefficientAt_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.errorAt_factor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomial_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomialModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.errorAt_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomial_error_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments.polynomialConvergenceCertificate
