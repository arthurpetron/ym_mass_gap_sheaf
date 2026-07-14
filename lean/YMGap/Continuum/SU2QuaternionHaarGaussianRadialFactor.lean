/-
# Exact sphere-to-Gaussian radial factors

For a four-coordinate monomial, the normalized sphere moment times its
positive radial denominator is exactly the corresponding product-Gaussian
moment numerator.  On a bihomogeneous parity block these denominators are
constant, so positivity reduces to product-Gaussian square positivity.
-/

import YMGap.Continuum.SU2QuaternionHaarParityPolynomial

namespace YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

def halfDegree4 (e0 e1 e2 e3 : Nat) : Nat :=
  e0 / 2 + e1 / 2 + e2 / 2 + e3 / 2

/-- The unnormalized product-Gaussian monomial moment with covariance one. -/
def gaussianMoment4 (e0 e1 e2 e3 : Nat) : Q' :=
  if _hEven : e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0 then
    Q'.ofNat
      (oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
        oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2))
  else 0

/-- Exact radial factorization, stated without division. -/
theorem sphereMoment4_mul_radialDenominator (e0 e1 e2 e3 : Nat) :
    sphereMoment4 e0 e1 e2 e3 *
        Q'.ofNat (sphereFourDenominator (halfDegree4 e0 e1 e2 e3)) ≈
      gaussianMoment4 e0 e1 e2 e3 := by
  by_cases hEven :
      e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0
  · let N := oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
        oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2)
    let D := sphereFourDenominator (halfDegree4 e0 e1 e2 e3)
    have hD : 0 < D := sphereFourDenominator_pos _
    have hs : sphereMoment4 e0 e1 e2 e3 =
        Q'.mkPos (Int.ofNat N) D hD := by
      simp [sphereMoment4, hEven, N, D, halfDegree4]
    have hg : gaussianMoment4 e0 e1 e2 e3 = Q'.ofNat N := by
      simp [gaussianMoment4, hEven, N]
    rw [hs, hg]
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num,
      Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast]
    push_cast
    ac_rfl
  · have hs : sphereMoment4 e0 e1 e2 e3 = 0 := by
      simp [sphereMoment4, hEven]
    have hg : gaussianMoment4 e0 e1 e2 e3 = 0 := by
      simp [gaussianMoment4, hEven]
    rw [hs, hg]
    exact Q'.zero_mul_eqv _

def gHalfDegree (m : List Nat) : Nat :=
  halfDegree4 (exponentAt m 0) (exponentAt m 1)
    (exponentAt m 2) (exponentAt m 3)

def hHalfDegree (m : List Nat) : Nat :=
  halfDegree4 (exponentAt m 4) (exponentAt m 5)
    (exponentAt m 6) (exponentAt m 7)

def productGaussianMono (m : List Nat) : Q' :=
  gaussianMoment4 (exponentAt m 0) (exponentAt m 1)
      (exponentAt m 2) (exponentAt m 3) *
    gaussianMoment4 (exponentAt m 4) (exponentAt m 5)
      (exponentAt m 6) (exponentAt m 7)

/-- Exact two-boundary radial factorization for every monomial supported in
the eight quaternion coordinates. -/
theorem productHaarMono_mul_radialDenominators (m : List Nat)
    (htail : allZero (m.drop 8) = true) :
    productHaarMono m *
        (Q'.ofNat (sphereFourDenominator (gHalfDegree m)) *
          Q'.ofNat (sphereFourDenominator (hHalfDegree m))) ≈
      productGaussianMono m := by
  unfold productHaarMono
  rw [if_pos htail]
  refine Q'.eqv_trans _
    ((sphereMoment4 (exponentAt m 0) (exponentAt m 1)
          (exponentAt m 2) (exponentAt m 3) *
        Q'.ofNat (sphereFourDenominator (gHalfDegree m))) *
      (sphereMoment4 (exponentAt m 4) (exponentAt m 5)
          (exponentAt m 6) (exponentAt m 7) *
        Q'.ofNat (sphereFourDenominator (hHalfDegree m)))) _
    (q_mul4_swap _ _ _ _) ?_
  unfold productGaussianMono gHalfDegree hHalfDegree
  refine Q'.eqv_trans _
    (gaussianMoment4 (exponentAt m 0) (exponentAt m 1)
        (exponentAt m 2) (exponentAt m 3) *
      (sphereMoment4 (exponentAt m 4) (exponentAt m 5)
          (exponentAt m 6) (exponentAt m 7) *
        Q'.ofNat
          (sphereFourDenominator
            (halfDegree4 (exponentAt m 4) (exponentAt m 5)
              (exponentAt m 6) (exponentAt m 7))))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (sphereMoment4_mul_radialDenominator
        (exponentAt m 0) (exponentAt m 1)
        (exponentAt m 2) (exponentAt m 3))
  · exact Q'.mul_eqv_congr_left _ _ _
      (sphereMoment4_mul_radialDenominator
        (exponentAt m 4) (exponentAt m 5)
        (exponentAt m 6) (exponentAt m 7))

end YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor

#print axioms YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor.sphereMoment4_mul_radialDenominator
#print axioms YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor.productHaarMono_mul_radialDenominators
