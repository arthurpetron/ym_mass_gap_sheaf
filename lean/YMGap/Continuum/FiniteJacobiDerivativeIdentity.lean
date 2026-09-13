/-
# The actual finite differentiated Jacobi identity

The original Gaussian coefficients obey the differentiated three-neighbor
rule. Hence the EXISTING finite factor-product derivative is its Gaussian
Chebyshev derivative sum. Restoring the actual Euler normalizer identifies
the full finite Leibniz derivative with twice the weighted heat-series
partial sum. No derivative/limit interchange or same-function premise is
assumed. The weights remain the actual finite q-binomial/Euler weights.
-/

import YMGap.Continuum.FiniteJacobiIdentity
import YMGap.Continuum.FiniteSymmetricChebyshevDerivative
import YMGap.Continuum.JTPFullProductDerivativeNormalization

namespace YMGap.Continuum.FiniteJacobiDerivativeIdentity

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteJacobiCoefficients
open YMGap.Continuum.FiniteJacobiIdentity
open YMGap.Continuum.FiniteSymmetricChebyshevDerivative
open YMGap.Continuum.JTPFullProductDerivativeNormalization

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Derivative sum with the original Gaussian q-binomial coefficients. -/
def gaussianDerivative (q x : Q') (N : Nat) : Q' := dsum (coeff q N) x N

theorem gaussianDerivative_step {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (x : Q') (N : Nat) :
    gaussianDerivative q x (N + 1)
      ≈ gaussianDerivative q x N * HKPos.factor (HKPos.geoAmp q N) x
        + gaussianPartial q x N * HKPos.two (HKPos.geoAmp q N) := by
  calc gaussianDerivative q x (N + 1)
      ≈ dsum (FiniteSymmetricChebyshev.step (middle q N) (amp q N) (coeff q N)) x (N + 1) :=
        dsum_congr _ _ x (N + 1) (coeff_step hq0 hq1 N)
    _ ≈ (middle q N + (2 : Q') * amp q N * x) * gaussianDerivative q x N
        + (2 : Q') * amp q N * gaussianPartial q x N :=
      dsum_step _ _ _ x N (coeff_out_of_range q N (N + 1) (by omega))
        (coeff_out_of_range q N (N + 2) (by omega))
    _ ≈ HKPos.factor (HKPos.geoAmp q N) x * gaussianDerivative q x N
        + HKPos.two (HKPos.geoAmp q N) * gaussianPartial q x N :=
      Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_right _ _ _ (factor_pin q x N))
        (Q'.mul_eqv_congr_right _ _ _ (Cheb.two_mul_eqv (amp q N)))
    _ ≈ gaussianDerivative q x N * HKPos.factor (HKPos.geoAmp q N) x
        + gaussianPartial q x N * HKPos.two (HKPos.geoAmp q N) := by mul_add_ring

/-- The EXISTING finite factor-product derivative equals the Gaussian sum,
for all rational x. The proof is the actual finite Leibniz recurrence. -/
theorem factorProdDx_eq_gaussianDerivative {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (x : Q') (N : Nat) :
    CoeffChebSineClose.factorProdDx q x N ≈ gaussianDerivative q x N := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      calc CoeffChebSineClose.factorProdDx q x (N + 1)
          ≈ gaussianDerivative q x N * HKPos.factor (HKPos.geoAmp q N) x
            + gaussianPartial q x N * HKPos.two (HKPos.geoAmp q N) :=
          Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_right _ _ _ ih)
            (Q'.mul_eqv_congr_right _ _ _ (factorProd_eq_gaussianPartial hq0 hq1 x N))
        _ ≈ gaussianDerivative q x (N + 1) := Q'.eqv_symm (gaussianDerivative_step hq0 hq1 x N)

/-- Full finite derivative polynomial with its actual Euler-normalized weights. -/
def finiteJacobiDerivative (q x : Q') (N : Nat) : Q' :=
  dsum (fun j => q ^ (j * j) * centeredWeight (q * q) N j) x N

theorem finiteJacobiDerivative_eq_euler_mul (q x : Q') (N : Nat) :
    finiteJacobiDerivative q x N ≈ euler (q * q) N * gaussianDerivative q x N := by
  calc finiteJacobiDerivative q x N
      ≈ dsum (fun j => euler (q * q) N * coeff q N j) x N := by
        apply dsum_congr
        intro j _
        unfold centeredWeight coeff
        mul_add_ring
    _ ≈ euler (q * q) N * gaussianDerivative q x N := dsum_scale _ _ x N

/-- The original full finite Leibniz derivative is the normalized weighted
Chebyshev derivative sum; no limit identity is used. -/
theorem fullProdDx_eq_finiteJacobiDerivative {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    fullProdDx q x N ≈ finiteJacobiDerivative q x N := by
  calc fullProdDx q x N
      ≈ RealTheta.eulerProd q N * CoeffChebSineClose.factorProdDx q x N :=
        fullProdDx_eqv_eulerProd_mul_factorProdDx hq0 hq1 hxm1 N
    _ ≈ euler (q * q) N * gaussianDerivative q x N :=
      Cheb.mul_eqv_congr _ _ _ _ (Q'.eqv_symm (euler_square_eq_theta q N))
        (factorProdDx_eq_gaussianDerivative hq0 hq1 x N)
    _ ≈ finiteJacobiDerivative q x N := Q'.eqv_symm (finiteJacobiDerivative_eq_euler_mul q x N)

/-- Arbitrary fixed coefficient weights multiply the ORIGINAL dTerm series.
The factor two comes from the symmetric theta polynomial, not a convention. -/
theorem dsum_eq_two_weighted_dPartial (q x : Q') (w : Nat → Q') (M : Nat) :
    dsum (fun j => q ^ (j * j) * w j) x M
      ≈ (2 : Q') * finSum (fun r => w (r + 1) * JTPIdentity.dTerm q x r) M := by
  induction M with
  | zero => exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  | succ M ih =>
      calc dsum (fun j => q ^ (j * j) * w j) x (M + 1)
          ≈ (2 : Q') * finSum (fun r => w (r + 1) * JTPIdentity.dTerm q x r) M
            + (2 : Q') * (q ^ ((M + 1) * (M + 1)) * w (M + 1))
              * ChebTFwdRatioClose.Lcoef x (M + 1) := Q'.add_eqv_congr_right _ _ _ ih
        _ ≈ (2 : Q') * finSum (fun r => w (r + 1) * JTPIdentity.dTerm q x r) (M + 1) := by
          change (2 : Q') * finSum (fun r => w (r + 1) * JTPIdentity.dTerm q x r) M
              + (2 : Q') * (q ^ ((M + 1) * (M + 1)) * w (M + 1))
                * (Q'.ofNat (M + 1) * Cheb.U M x)
            ≈ (2 : Q') * (finSum (fun r => w (r + 1) * JTPIdentity.dTerm q x r) M
              + w (M + 1) * ((Q'.ofNat (M + 1) * q ^ ((M + 1) * (M + 1))) * Cheb.U M x))
          mul_add_ring

/-- Finite differentiated JTP with the ACTUAL weights and correct factor two.
Passing these weights to one still requires quantitative derivative control. -/
theorem fullProdDx_eq_two_weighted_dPartial {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    fullProdDx q x N ≈ (2 : Q') * finSum
      (fun r => centeredWeight (q * q) N (r + 1) * JTPIdentity.dTerm q x r) N :=
  Q'.eqv_trans _ _ _ (fullProdDx_eq_finiteJacobiDerivative hq0 hq1 hxm1 N)
    (dsum_eq_two_weighted_dPartial q x (centeredWeight (q * q) N) N)

end YMGap.Continuum.FiniteJacobiDerivativeIdentity

#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.gaussianDerivative
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.gaussianDerivative_step
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.factorProdDx_eq_gaussianDerivative
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.finiteJacobiDerivative
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.finiteJacobiDerivative_eq_euler_mul
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.fullProdDx_eq_finiteJacobiDerivative
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.dsum_eq_two_weighted_dPartial
#print axioms YMGap.Continuum.FiniteJacobiDerivativeIdentity.fullProdDx_eq_two_weighted_dPartial
