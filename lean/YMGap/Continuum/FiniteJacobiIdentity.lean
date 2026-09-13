/-
# The finite symmetric Jacobi identity over the real rational substrate

For every `0<q<1`, rational x, and finite N, the ORIGINAL theta factor product
is exactly

  [2N choose N]_(q*q)
    + 2 sum_{j=1..N} q^(j*j) [2N choose N+j]_(q*q) T_j(x).

The proof uses the original recursive q-binomial, its proved two-sided
Pascal rule, and the original Chebyshev T recurrence. No complex parameters,
formal differentiation assumption, or per-N equality premise is supplied.

Multiplying by the actual Euler factor pins `ThetaConv.Ppart` to the finite
series with Euler-normalized Gaussian coefficients. These coefficients are
NOT replaced by one. Their quantitative convergence and the differentiated
limit identity remain open; finite JTP is not heat or action positivity.
-/

import YMGap.Continuum.FiniteJacobiCoefficients

namespace YMGap.Continuum.FiniteJacobiIdentity

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.FiniteJacobiCoefficients
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_add_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.add_num, Q'.add_den_cast, Cheb.mul_num,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Finite symmetric Gaussian series WITH its q-binomial coefficients. -/
def gaussianPartial (q x : Q') (N : Nat) : Q' :=
  FiniteSymmetricChebyshev.sum (coeff q N) x N

/-- The recurrence factor is the ORIGINAL Jacobi quadratic. -/
theorem factor_pin (q x : Q') (N : Nat) :
    middle q N + (2 : Q') * amp q N * x ≈ HKPos.factor (HKPos.geoAmp q N) x := by
  calc middle q N + (2 : Q') * amp q N * x
      ≈ middle q N + (amp q N + amp q N) * x :=
        Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Cheb.two_mul_eqv _))
    _ ≈ HKPos.factor (HKPos.geoAmp q N) x := by
      unfold middle amp HKPos.factor HKPos.geoAmp HKPos.two
      mul_add_ring

/-- Exact multiplication of the finite Gaussian series by its next factor. -/
theorem gaussianPartial_step {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (x : Q') (N : Nat) :
    gaussianPartial q x (N + 1)
      ≈ gaussianPartial q x N * HKPos.factor (HKPos.geoAmp q N) x := by
  calc gaussianPartial q x (N + 1)
      ≈ FiniteSymmetricChebyshev.sum
          (FiniteSymmetricChebyshev.step (middle q N) (amp q N) (coeff q N)) x (N + 1) :=
        FiniteSymmetricChebyshev.sum_congr _ _ x (N + 1) (coeff_step hq0 hq1 N)
    _ ≈ (middle q N + (2 : Q') * amp q N * x) * gaussianPartial q x N :=
      FiniteSymmetricChebyshev.sum_step _ _ _ x N
        (coeff_out_of_range q N (N + 1) (by omega))
        (coeff_out_of_range q N (N + 2) (by omega))
    _ ≈ HKPos.factor (HKPos.geoAmp q N) x * gaussianPartial q x N :=
      Q'.mul_eqv_congr_right _ _ _ (factor_pin q x N)
    _ ≈ gaussianPartial q x N * HKPos.factor (HKPos.geoAmp q N) x := Q'.mul_comm_eqv _ _

/-- The finite symmetric Jacobi identity, pinned to the EXISTING theta factor
product, for all finite N and every rational x. -/
theorem factorProd_eq_gaussianPartial {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (x : Q') (N : Nat) :
    RealTheta.factorProd q x N ≈ gaussianPartial q x N := by
  induction N with
  | zero => exact Q'.eqv_symm (coeff_top q 0)
  | succ N ih =>
      calc RealTheta.factorProd q x (N + 1)
          ≈ gaussianPartial q x N * HKPos.factor (HKPos.geoAmp q N) x :=
            Q'.mul_eqv_congr_right _ _ _ ih
        _ ≈ gaussianPartial q x (N + 1) := Q'.eqv_symm (gaussianPartial_step hq0 hq1 x N)

/-- Exact scaling of a finite symmetric Chebyshev series. -/
theorem sum_scale (c : Q') (a : Nat → Q') (x : Q') (N : Nat) :
    FiniteSymmetricChebyshev.sum (fun j => c * a j) x N
      ≈ c * FiniteSymmetricChebyshev.sum a x N := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      change (FiniteSymmetricChebyshev.sum (fun j => c * a j) x N
        + (2 : Q') * (c * a (N + 1)) * Cheb.T (N + 1) x) ≈ _
      calc FiniteSymmetricChebyshev.sum (fun j => c * a j) x N
              + (2 : Q') * (c * a (N + 1)) * Cheb.T (N + 1) x
          ≈ c * FiniteSymmetricChebyshev.sum a x N
              + (2 : Q') * (c * a (N + 1)) * Cheb.T (N + 1) x := Q'.add_eqv_congr_right _ _ _ ih
        _ ≈ c * FiniteSymmetricChebyshev.sum a x (N + 1) := by
          rw [FiniteSymmetricChebyshev.sum]; mul_add_ring

/-- Finite series with the ACTUAL Euler-normalized coefficients, not the
bare theta truncation. Its coefficients must still be controlled in limits. -/
def finiteJacobi (q x : Q') (N : Nat) : Q' :=
  FiniteSymmetricChebyshev.sum
    (fun j => q ^ (j * j) * centeredWeight (q * q) N j) x N

theorem finiteJacobi_eq_euler_mul (q x : Q') (N : Nat) :
    finiteJacobi q x N ≈ euler (q * q) N * gaussianPartial q x N := by
  calc finiteJacobi q x N
      ≈ FiniteSymmetricChebyshev.sum (fun j => euler (q * q) N * coeff q N j) x N := by
        apply FiniteSymmetricChebyshev.sum_congr
        intro j _
        unfold centeredWeight coeff
        mul_add_ring
    _ ≈ euler (q * q) N * gaussianPartial q x N := sum_scale _ _ x N

/-- The ORIGINAL full theta product equals the Euler-normalized finite
Gaussian series. This is a proved per-N identity with the correct finite
coefficients, not an assumed equality to the bare infinite-theta partials. -/
theorem Ppart_eq_finiteJacobi {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (x : Q') (N : Nat) :
    ThetaConv.Ppart q x N ≈ finiteJacobi q x N := by
  calc ThetaConv.Ppart q x N
      ≈ RealTheta.eulerProd q N * RealTheta.factorProd q x N := RealTheta.Ppart_eqv_prodRegroup q x N
    _ ≈ euler (q * q) N * gaussianPartial q x N :=
      Cheb.mul_eqv_congr _ _ _ _ (Q'.eqv_symm (euler_square_eq_theta q N))
        (factorProd_eq_gaussianPartial hq0 hq1 x N)
    _ ≈ finiteJacobi q x N := Q'.eqv_symm (finiteJacobi_eq_euler_mul q x N)

end YMGap.Continuum.FiniteJacobiIdentity

#print axioms YMGap.Continuum.FiniteJacobiIdentity.gaussianPartial
#print axioms YMGap.Continuum.FiniteJacobiIdentity.factor_pin
#print axioms YMGap.Continuum.FiniteJacobiIdentity.gaussianPartial_step
#print axioms YMGap.Continuum.FiniteJacobiIdentity.factorProd_eq_gaussianPartial
#print axioms YMGap.Continuum.FiniteJacobiIdentity.sum_scale
#print axioms YMGap.Continuum.FiniteJacobiIdentity.finiteJacobi
#print axioms YMGap.Continuum.FiniteJacobiIdentity.finiteJacobi_eq_euler_mul
#print axioms YMGap.Continuum.FiniteJacobiIdentity.Ppart_eq_finiteJacobi
