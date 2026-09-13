/-
# The undifferentiated Jacobi triple product on the original real interval

The existing theta product CReal equals 1 + 2 times the existing Chebyshev-T
series CReal, for every rational 0<q<1 and -1<=x<=1. The proof uses the actual
finite Jacobi identity and its whole-polynomial comparison modulus. No
per-cutoff equality to bare theta partials or same-limit premise is assumed.

The central one and factor two are essential. This does NOT identify the
full product with the nonconstant half-series alone. Differentiated JTP,
off-interval continuation, heat positivity and action positivity are not
asserted here.
-/

import YMGap.Continuum.FiniteJacobiSeriesComparison
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.ThetaPtwiseTotalizerClose

namespace YMGap.Continuum.JacobiTripleProductOnBox

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.FiniteJacobiSeriesComparison
open YMGap.Continuum.ThetaPtwiseTotalizerClose

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Exact normalization of the bare finite polynomial in the existing series. -/
theorem bareTheta_eq_one_add_two_chebTTrunc (q x : Q') (N : Nat) :
    bareTheta q x N ≈ 1 + (2 : Q') * ThetaSeriesFDDeriv.chebTTrunc q N x := by
  induction N with
  | zero =>
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
        (by rw [Q'.add_zero']; exact Q'.eqv_refl _))
  | succ N ih =>
      calc bareTheta q x (N + 1)
          ≈ (1 + (2 : Q') * ThetaSeriesFDDeriv.chebTTrunc q N x)
            + (2 : Q') * q ^ ((N + 1) * (N + 1)) * Cheb.T (N + 1) x :=
              Q'.add_eqv_congr_right _ _ _ ih
        _ ≈ 1 + (2 : Q') * ThetaSeriesFDDeriv.chebTTrunc q (N + 1) x := by
          change (1 + (2 : Q') * ThetaSeriesFDDeriv.chebTTrunc q N x)
              + (2 : Q') * q ^ ((N + 1) * (N + 1)) * Cheb.T (N + 1) x
            ≈ 1 + (2 : Q') * (ThetaSeriesFDDeriv.chebTTrunc q N x
              + q ^ ((N + 1) * (N + 1)) * Cheb.T (N + 1) x)
          mul_add_ring

/-- The correctly normalized full theta series, using the proved on-box
majorant, with no off-box totalizer or analytic input supplied. -/
def fullThetaSeries {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) : CReal :=
  CReal.add (CReal.ofQ' 1) (CReal.mul (CReal.ofQ' 2)
    (chebTConvPt hq0 hq1 (onBoxPtMajorant hq0 hq1 hx1 hxm1)))

theorem fullThetaSeries_approx {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    (fullThetaSeries hq0 hq1 hx1 hxm1).approx N ≈ bareTheta q x N :=
  Q'.eqv_symm (bareTheta_eq_one_add_two_chebTTrunc q x N)

/-- Actual product and series approximations approach each other with the
computed, x-independent on-box cutoff. The CReal representatives are pinned. -/
theorem product_series_approx_close {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : comparisonCutoff q ε ≤ N) :
    Q'.abs ((ThetaConvGen.thetaConvCRealGen hq0 hq1 hxm1 hx1).approx N
      + -(fullThetaSeries hq0 hq1 hx1 hxm1).approx N) ≤ ε := by
  have he : (ThetaConvGen.thetaConvCRealGen hq0 hq1 hxm1 hx1).approx N
      + -(fullThetaSeries hq0 hq1 hx1 hxm1).approx N
      ≈ ThetaConv.Ppart q x N + -bareTheta q x N :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (fullThetaSeries_approx hq0 hq1 hx1 hxm1 N))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
    (Ppart_sub_bareTheta_close hq0 hq1 hx1 hxm1 hε N hN)

/-- Undifferentiated Jacobi triple product: equality of the ORIGINAL product
and correctly normalized series limits on [-1,1], proved without an identity
premise. The equality's cutoff is explicitly comparisonCutoff q epsilon. -/
theorem thetaProduct_eq_fullThetaSeries {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    CReal.Equiv (ThetaConvGen.thetaConvCRealGen hq0 hq1 hxm1 hx1)
      (fullThetaSeries hq0 hq1 hx1 hxm1) := by
  intro ε hε
  refine ⟨comparisonCutoff q ε, fun N hN => ?_⟩
  have h := product_series_approx_close hq0 hq1 hx1 hxm1 hε N hN
  exact ⟨ExpNeg.le_add_of_abs_sub_le h, ExpNeg.le_add_of_abs_sub_le
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ExpNeg.abs_sub_comm _ _)) h)⟩

end YMGap.Continuum.JacobiTripleProductOnBox

#print axioms YMGap.Continuum.JacobiTripleProductOnBox.bareTheta_eq_one_add_two_chebTTrunc
#print axioms YMGap.Continuum.JacobiTripleProductOnBox.fullThetaSeries
#print axioms YMGap.Continuum.JacobiTripleProductOnBox.fullThetaSeries_approx
#print axioms YMGap.Continuum.JacobiTripleProductOnBox.product_series_approx_close
#print axioms YMGap.Continuum.JacobiTripleProductOnBox.thetaProduct_eq_fullThetaSeries
