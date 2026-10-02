/-
# Original Haar certificate for a nonnegative Bernstein row

Given certificates for the actual substituted variable y and 1-y, and
nonnegative rational row entries, compile the literal QPoly Bernstein row
into the existing original QuaternionHaar `Certificate`. This is a generic
producer: no positivity or reconstruction premise about a target heat
polynomial is included.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
import YMGap.Continuum.BernsteinRationalPositiveRow
import YMGap.Constructive.CRealArtanhEulerPolynomialAnchor

namespace YMGap.Continuum.QuaternionHaarBernsteinRowCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinRationalPositiveRow
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2ClassPolynomialAlgebra

local infix:50 " ≈ " => Q'.eqv

private abbrev anchorPpow :=
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow
private abbrev anchorPvar :=
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar

/-- The second Bernstein factor is represented by the actual polynomial `1-z`. -/
def oneMinusVar : Poly := [1, -1]

/-- The actual polynomial basis row entry before rational scaling. -/
def bernsteinBasisPoly (degree index : Nat) : Poly :=
  pmul (anchorPpow anchorPvar index) (anchorPpow oneMinusVar (degree-index))

/-- The literal rational Bernstein row, as a low-to-high coefficient list. -/
def polyFinSum (f : Nat → Poly) : Nat → Poly
  | 0 => []
  | n+1 => padd (polyFinSum f n) (f n)

def bernsteinRowPoly (degree : Nat) (coefficient : Nat → Q') : Poly :=
  polyFinSum (fun j => pscale (coefficient j) (bernsteinBasisPoly degree j)) (degree+1)

private theorem subst_pvar_eqv (y : RatPoly) :
    RatPolyCoeffEqv (subst y anchorPvar) y := by
  unfold anchorPvar YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar
  exact (subst_zero_cons y [1]).trans
    (((subst_singleton y 1).mul_left y).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 1 y polyOne).trans
        ((RatPolyCoeffEqv.one_smul (polyMul y polyOne)).trans
          (RatPolyCoeffEqv.mul_one y))))

private def ppowCertificate {blocks : Nat} (y : RatPoly) (base : Poly)
    (baseCertificate : Certificate blocks (subst y base)) :
    (power : Nat) → Certificate blocks (subst y (anchorPpow base power))
  | 0 => by
      change Certificate blocks (subst y [1])
      exact .ofCoeff
        ((subst_singleton y 1).trans (RatPolyCoeffEqv.one_smul polyOne))
        (.one blocks)
  | power+1 => by
      change Certificate blocks (subst y (pmul base (anchorPpow base power)))
      exact .ofCoeff (subst_pmul y base (anchorPpow base power))
        (.mul baseCertificate (ppowCertificate y base baseCertificate power))

private def basisCertificate {blocks : Nat} (y : RatPoly)
    (variableCertificate : Certificate blocks y)
    (oneMinusCertificate : Certificate blocks (subst y oneMinusVar))
    (degree index : Nat) : Certificate blocks
      (subst y (bernsteinBasisPoly degree index)) := by
  let variablePower := ppowCertificate y anchorPvar
    (.ofCoeff (subst_pvar_eqv y) variableCertificate) index
  let oneMinusPower := ppowCertificate y oneMinusVar oneMinusCertificate
    (degree-index)
  exact .ofCoeff (subst_pmul y (anchorPpow anchorPvar index)
    (anchorPpow oneMinusVar (degree-index)))
    (.mul variablePower oneMinusPower)

private def termCertificate {blocks : Nat} (y : RatPoly)
    (variableCertificate : Certificate blocks y)
    (oneMinusCertificate : Certificate blocks (subst y oneMinusVar))
    (degree index : Nat) (coefficient : Q') (nonnegative : (0 : Q') ≤ coefficient) :
    Certificate blocks
      (subst y (pscale coefficient (bernsteinBasisPoly degree index))) := by
  exact .ofCoeff (subst_pscale y coefficient (bernsteinBasisPoly degree index))
    (.smul coefficient nonnegative
      (basisCertificate y variableCertificate oneMinusCertificate degree index))

private def rowSumCertificate {blocks : Nat} (y : RatPoly)
    (variableCertificate : Certificate blocks y)
    (oneMinusCertificate : Certificate blocks (subst y oneMinusVar))
    (degree : Nat) (coefficient : Nat → Q') :
    (count : Nat) → (∀ j, j < count → (0 : Q') ≤ coefficient j) →
      Certificate blocks
        (subst y (polyFinSum (fun j =>
          pscale (coefficient j) (bernsteinBasisPoly degree j)) count))
  | 0, _ => by
      change Certificate blocks (subst y [])
      exact .ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
        (.constant blocks 0 (Q'.le_refl' 0))
  | count+1, hcoeff => by
      change Certificate blocks
        (subst y (padd
          (polyFinSum (fun j => pscale (coefficient j)
            (bernsteinBasisPoly degree j)) count)
          (pscale (coefficient count) (bernsteinBasisPoly degree count))))
      exact .ofCoeff
        (subst_padd y
          (polyFinSum (fun j => pscale (coefficient j)
            (bernsteinBasisPoly degree j)) count)
          (pscale (coefficient count) (bernsteinBasisPoly degree count)))
        (.add
          (rowSumCertificate y variableCertificate oneMinusCertificate
            degree coefficient count (fun j hj => hcoeff j (Nat.lt_succ_of_lt hj)))
          (termCertificate y variableCertificate oneMinusCertificate degree count
            (coefficient count) (hcoeff count (Nat.lt_succ_self count))))

/-- Compile a literal row with nonnegative rational coefficients into the
existing original Haar certificate. The only inputs are the two base
certificates and the checked coefficient signs. -/
def certificate {blocks : Nat} (y : RatPoly) (degree : Nat)
    (variableCertificate : Certificate blocks y)
    (oneMinusCertificate : Certificate blocks (subst y oneMinusVar))
    (coefficient : Nat → Q')
    (nonnegative : ∀ j, j ≤ degree → (0 : Q') ≤ coefficient j) :
    Certificate blocks (subst y (bernsteinRowPoly degree coefficient)) := by
  unfold bernsteinRowPoly
  exact rowSumCertificate y variableCertificate oneMinusCertificate degree coefficient
    (degree+1) (fun j hj => nonnegative j (by omega))

private theorem eval_oneMinusVar (x : Q') :
    (eval oneMinusVar x).eqv ((1 : Q') + -x) := by
  change (1 + x * (-1 + x * 0)).eqv (1 + -x)
  have hinner : (-1 + x * 0).eqv (-1) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) (x*0) 0 (Q'.mul_zero_eqv x))
      (QPoly.q_add_zero_eqv (-1))
  have hneg : (x * -1).eqv (-x) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv x (-1))
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 x)
        (Q'.neg_eqv_congr (1*x) x (Q'.one_mul_eqv x)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_eqv_congr_left x _ _ hinner))
    (Q'.add_eqv_congr_left 1 _ _ hneg)

private theorem eval_polyFinSum (f : Nat → Poly) : ∀ n x,
    (eval (polyFinSum f n) x).eqv
      (RationalTail.finSum (fun j => eval (f j) x) n)
  | 0, _ => Q'.eqv_refl _
  | n+1, x => by
      change (eval (padd (polyFinSum f n) (f n)) x).eqv _
      exact Q'.eqv_trans _ _ _ (eval_padd (polyFinSum f n) (f n) x)
        (Q'.add_eqv_congr' (eval_polyFinSum f n x) (Q'.eqv_refl _))

private theorem eval_bernsteinBasisPoly (degree index : Nat) (x : Q') :
    (eval (bernsteinBasisPoly degree index) x).eqv
      (bernsteinBasis degree x index) := by
  unfold bernsteinBasisPoly bernsteinBasis
  have hv := YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.eval_ppow_pvar x index
  have hm : (eval (anchorPpow oneMinusVar (degree-index)) x).eqv
      ((1-x)^(degree-index)) :=
    Q'.eqv_trans _ _ _
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.eval_ppow
        oneMinusVar x (degree-index))
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pow_eqv_congr
        (eval_oneMinusVar x) (degree-index))
  exact Q'.eqv_trans _ _ _ (eval_pmul (anchorPpow anchorPvar index)
      (anchorPpow oneMinusVar (degree-index)) x)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hv)
      (Q'.mul_eqv_congr_left _ _ _ hm))

/-- Evaluating the literal QPoly row gives the same rational Bernstein row
used by the finite coefficient reconstruction. This holds at every rational
argument, without restricting the argument to the positivity interval. -/
theorem bernsteinRowPoly_eval (degree : Nat) (coefficient : Nat → Q') (x : Q') :
    (eval (bernsteinRowPoly degree coefficient) x).eqv
      (RationalTail.finSum
        (fun j => coefficient j * bernsteinBasis degree x j) (degree+1)) := by
  unfold bernsteinRowPoly
  exact Q'.eqv_trans _ _ _
    (eval_polyFinSum (fun j =>
      pscale (coefficient j) (bernsteinBasisPoly degree j)) (degree+1) x)
    (RationalTail.finSum_eqv_congr
      (fun j => eval (pscale (coefficient j) (bernsteinBasisPoly degree j)) x)
      (fun j => coefficient j * bernsteinBasis degree x j)
      (fun j => Q'.eqv_trans _ _ _
        (eval_pscale (coefficient j) (bernsteinBasisPoly degree j) x)
        (Q'.mul_eqv_congr_left (coefficient j) _ _
          (eval_bernsteinBasisPoly degree j x))) (degree+1))

/-- A strict margin for an actual rational polynomial computes a Bernstein
degree and nonnegative row, then transports its witness back to the ACTUAL
substituted polynomial. No positivity/reconstruction witness is assumed. -/
def strictPolynomialCertificate {blocks : Nat} (y : RatPoly) (p : Poly)
    (eta : Q') (etaPositive : (0 : Q') < eta)
    (margin : ∀ t : Q', (0 : Q') ≤ t → t ≤ (1 : Q') → eta ≤ eval p t)
    (variableCertificate : Certificate blocks y)
    (oneMinusCertificate : Certificate blocks (subst y oneMinusVar)) :
    Certificate blocks (subst y p) := by
  let cutoff := rowCutoff p eta
  let coefficient : Nat → Q' := unnormalizedRow p cutoff
  have cutoffSelf : rowCutoff p eta ≤ cutoff := Nat.le_refl _
  have degreeFits : p.length ≤ cutoff+1 :=
    Nat.le_trans (rowCutoff_degree p eta) (Nat.le_succ _)
  have hrowEval : ∀ x : Q',
      (eval (bernsteinRowPoly (cutoff+1) coefficient) x).eqv (eval p x) := by
    intro x
    exact Q'.eqv_trans _ _ _
      (bernsteinRowPoly_eval (cutoff+1) coefficient x)
      (unnormalizedRow_reconstruction p cutoff degreeFits x)
  have rowPolyEqv : PolyEqv (bernsteinRowPoly (cutoff+1) coefficient) p :=
    polyEqv_of_ge_neg_one (fun x _ => hrowEval x)
  have hrow : Certificate blocks
      (subst y (bernsteinRowPoly (cutoff+1) coefficient)) :=
    certificate y (cutoff+1) variableCertificate oneMinusCertificate coefficient
      (fun j hj => unnormalizedRow_nonnegative p eta etaPositive margin cutoff j
        cutoffSelf hj)
  exact Certificate.ofCoeff (subst_polyEqv y rowPolyEqv).symm hrow

end YMGap.Continuum.QuaternionHaarBernsteinRowCertificate

#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.certificate
#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.bernsteinRowPoly_eval
#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.strictPolynomialCertificate
#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.oneMinusVar
#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.bernsteinBasisPoly
#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.polyFinSum
#print axioms YMGap.Continuum.QuaternionHaarBernsteinRowCertificate.bernsteinRowPoly
