/-
# Eight-coordinate product-Gaussian tensor form

The quaternion product-Gaussian monomial functional is exposed as the tensor
product of eight copies of the exact univariate Gaussian moment.  This is the
bridge from the univariate Hermite SOS theorem to the raw `RatPoly` carrier.
-/

import YMGap.Continuum.SU2QuaternionGaussianPolynomialPositivity

namespace YMGap.Continuum.SU2QuaternionProductGaussianTensor

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 500000
set_option maxRecDepth 10000

private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, Int.add_mul, Int.mul_add,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero];
             try ac_rfl))

private theorem gaussianMoment4_tensor (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 e3 ≈
      gaussianMoment1 e0 * (gaussianMoment1 e1 *
        (gaussianMoment1 e2 * gaussianMoment1 e3)) := by
  unfold gaussianMoment1
  by_cases h0 : e0 % 2 = 0
  · by_cases h1 : e1 % 2 = 0
    · by_cases h2 : e2 % 2 = 0
      · by_cases h3 : e3 % 2 = 0
        · simp only [gaussianMoment4, h0, h1, h2, h3, Nat.zero_mod,
            and_self, and_true, true_and, ↓reduceDIte, oddDoubleFactorial]
          let a := oddDoubleFactorial (e0 / 2)
          let b := oddDoubleFactorial (e1 / 2)
          let c := oddDoubleFactorial (e2 / 2)
          let d := oddDoubleFactorial (e3 / 2)
          refine Q'.eqv_trans _
            (Q'.ofNat ((a * b) * c) * Q'.ofNat d) _
            (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv ((a * b) * c) d) ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat (a * b) * Q'.ofNat c) * Q'.ofNat d) _
            (Q'.mul_eqv_congr_right _ _ _
              (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv (a * b) c)) ?_
          refine Q'.eqv_trans _
            (((Q'.ofNat a * Q'.ofNat b) * Q'.ofNat c) * Q'.ofNat d) _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv a b))) ?_
          ring_qeqv
        · simp only [gaussianMoment4, h0, h1, h2, h3, Nat.zero_mod,
            and_self, and_true, true_and, false_and, ↓reduceDIte]
          ring_qeqv
      · simp only [gaussianMoment4, h0, h1, h2, Nat.zero_mod,
          and_self, and_true, true_and, false_and, ↓reduceDIte]
        ring_qeqv
    · simp only [gaussianMoment4, h0, h1, Nat.zero_mod,
        and_self, and_true, true_and, false_and, ↓reduceDIte]
      ring_qeqv
  · simp only [gaussianMoment4, h0, Nat.zero_mod,
      and_self, and_true, true_and, false_and, ↓reduceDIte]
    ring_qeqv

/-- Fixed eight-fold tensor moment. -/
def gaussianMoment8 (m : List Nat) : Q' :=
  gaussianMoment1 (exponentAt m 0) *
    (gaussianMoment1 (exponentAt m 1) *
      (gaussianMoment1 (exponentAt m 2) *
        (gaussianMoment1 (exponentAt m 3) *
          (gaussianMoment1 (exponentAt m 4) *
            (gaussianMoment1 (exponentAt m 5) *
              (gaussianMoment1 (exponentAt m 6) *
                gaussianMoment1 (exponentAt m 7)))))))

theorem productGaussianMono_eq_tensor (m : List Nat) :
    productGaussianMono m ≈ gaussianMoment8 m := by
  unfold productGaussianMono gaussianMoment8
  refine Q'.eqv_trans _
    ((gaussianMoment1 (exponentAt m 0) *
        (gaussianMoment1 (exponentAt m 1) *
          (gaussianMoment1 (exponentAt m 2) *
            gaussianMoment1 (exponentAt m 3)))) *
      gaussianMoment4 (exponentAt m 4) (exponentAt m 5)
        (exponentAt m 6) (exponentAt m 7)) _
    (Q'.mul_eqv_congr_right _ _ _
      (gaussianMoment4_tensor _ _ _ _)) ?_
  refine Q'.eqv_trans _
    ((gaussianMoment1 (exponentAt m 0) *
        (gaussianMoment1 (exponentAt m 1) *
          (gaussianMoment1 (exponentAt m 2) *
            gaussianMoment1 (exponentAt m 3)))) *
      (gaussianMoment1 (exponentAt m 4) *
        (gaussianMoment1 (exponentAt m 5) *
          (gaussianMoment1 (exponentAt m 6) *
            gaussianMoment1 (exponentAt m 7))))) _
    (Q'.mul_eqv_congr_left _ _ _ (gaussianMoment4_tensor _ _ _ _)) ?_
  ring_qeqv

private theorem exponentAt_monoMul (a b : List Nat) (i : Nat) :
    exponentAt (monoMul a b) i = exponentAt a i + exponentAt b i := by
  induction a generalizing b i with
  | nil => simp [monoMul, exponentAt]
  | cons x xs ih =>
      cases b with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases i with
          | zero => simp [monoMul, exponentAt]
          | succ i =>
              change exponentAt (monoMul xs ys) i =
                exponentAt xs i + exponentAt ys i
              exact ih ys i

theorem productGaussianMono_mul_tensor (a b : List Nat) :
    productGaussianMono (monoMul a b) ≈
      gaussianMoment1 (exponentAt a 0 + exponentAt b 0) *
        (gaussianMoment1 (exponentAt a 1 + exponentAt b 1) *
          (gaussianMoment1 (exponentAt a 2 + exponentAt b 2) *
            (gaussianMoment1 (exponentAt a 3 + exponentAt b 3) *
              (gaussianMoment1 (exponentAt a 4 + exponentAt b 4) *
                (gaussianMoment1 (exponentAt a 5 + exponentAt b 5) *
                  (gaussianMoment1 (exponentAt a 6 + exponentAt b 6) *
                    gaussianMoment1
                      (exponentAt a 7 + exponentAt b 7))))))) := by
  refine Q'.eqv_trans _ (gaussianMoment8 (monoMul a b)) _
    (productGaussianMono_eq_tensor _) ?_
  simp only [gaussianMoment8, exponentAt_monoMul]
  exact Q'.eqv_refl _

/-- Linear eight-coordinate product-Gaussian functional on `RatPoly`. -/
def productGaussian : RatPoly → Q'
  | [] => 0
  | (m, c) :: p => c * productGaussianMono m + productGaussian p

end YMGap.Continuum.SU2QuaternionProductGaussianTensor

#print axioms YMGap.Continuum.SU2QuaternionProductGaussianTensor.productGaussianMono_eq_tensor
#print axioms YMGap.Continuum.SU2QuaternionProductGaussianTensor.productGaussianMono_mul_tensor
