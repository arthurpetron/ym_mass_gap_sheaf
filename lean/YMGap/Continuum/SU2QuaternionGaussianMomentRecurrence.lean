/-
# Constructive product-Gaussian moment recurrences

The Hermite positivity route starts from the exact algebraic integration-by-
parts recurrence `mu_(n+2) = (n+1) mu_n`.  No representing measure is used:
the recurrence follows directly from the odd-double-factorial formula.
-/

import YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor

namespace YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

private theorem oddDoubleFactorial_succ (k : Nat) :
    oddDoubleFactorial (k + 1) =
      (2 * k + 1) * oddDoubleFactorial k := by
  rfl

/-- Gaussian integration-by-parts recurrence in the first coordinate. -/
theorem gaussianMoment4_shift0 (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 (e0 + 2) e1 e2 e3 ≈
      Q'.ofNat (e0 + 1) * gaussianMoment4 e0 e1 e2 e3 := by
  by_cases h0 : e0 % 2 = 0
  · by_cases h1 : e1 % 2 = 0
    · by_cases h2 : e2 % 2 = 0
      · by_cases h3 : e3 % 2 = 0
        · have h0plus : (e0 + 2) % 2 = 0 := by omega
          have hdiv : (e0 + 2) / 2 = e0 / 2 + 1 := by omega
          have hcoeff : e0 + 1 = 2 * (e0 / 2) + 1 := by omega
          have hg0 : gaussianMoment4 e0 e1 e2 e3 =
              Q'.ofNat
                (oddDoubleFactorial (e0 / 2) * oddDoubleFactorial (e1 / 2) *
                  oddDoubleFactorial (e2 / 2) * oddDoubleFactorial (e3 / 2)) := by
            simp [gaussianMoment4, h0, h1, h2, h3]
          have hg2 : gaussianMoment4 (e0 + 2) e1 e2 e3 =
              Q'.ofNat
                (oddDoubleFactorial (e0 / 2 + 1) *
                  oddDoubleFactorial (e1 / 2) * oddDoubleFactorial (e2 / 2) *
                  oddDoubleFactorial (e3 / 2)) := by
            simp [gaussianMoment4, h0plus, h1, h2, h3, hdiv]
          rw [hg0, hg2, hcoeff, oddDoubleFactorial_succ]
          show _ * (_ : Int) = _ * (_ : Int)
          simp only [Q'.mul_num_cast, Q'.mul_den_cast,
            Q'.ofNat_num_cast, Q'.ofNat_den_cast]
          push_cast
          ac_rfl
        · have h3plus : ¬ e3 % 2 = 0 := h3
          simp [gaussianMoment4, h3plus]
          exact Q'.eqv_refl 0
      · have h2plus : ¬ e2 % 2 = 0 := h2
        simp [gaussianMoment4, h2plus]
        exact Q'.eqv_refl 0
    · have h1plus : ¬ e1 % 2 = 0 := h1
      simp [gaussianMoment4, h1plus]
      exact Q'.eqv_refl 0
  · simp [gaussianMoment4, h0]
    exact Q'.eqv_refl 0

end YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence

#print axioms YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence.gaussianMoment4_shift0
