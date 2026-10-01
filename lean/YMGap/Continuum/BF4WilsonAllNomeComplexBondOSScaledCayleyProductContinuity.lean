/-
# Uniform finite-product continuity on the actual derivative graph

The physical dyadic Cayley product uses `2^n` applications at rational step
`t*(1/2)^n`.  Its squared displacement from an ORIGINAL graph input is at
most `4*t^2` times the ORIGINAL graph-output norm, independently of `n`.
This is a finite-product estimate; a limit passage or physical-time
calibration is not claimed here.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
  (dyadic_iterate_comparison)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "N" => normSq hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1

/-- The exact rational coefficient produced before dyadic cancellation. -/
def displacementCoefficient (t : Q') (n : Nat) : Q' :=
  (4 : Q')^n * (4 * (step t n * step t n))

theorem displacementCoefficient_pin (t : Q') (n : Nat) :
    Q'.eqv (displacementCoefficient t n) (4 * (t*t)) := by
  induction n with
  | zero =>
      unfold displacementCoefficient step
      simp only [Q'.pow_zero]
      exact poly_identity_of_normal_eq
        (.mul (.const 1)
          (.mul (.const 4)
            (.mul (.mul (.var 0) (.const 1))
              (.mul (.var 0) (.const 1)))))
        (.mul (.const 4) (.mul (.var 0) (.var 0)))
        (by decide) (fun _ => t)
  | succ n ih =>
      have hrec : Q'.eqv (displacementCoefficient t (n+1))
          ((4*HalfPow.half*HalfPow.half)*displacementCoefficient t n) := by
        unfold displacementCoefficient step
        rw [Q'.pow_succ (4 : Q') n,Q'.pow_succ HalfPow.half n]
        exact poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 0))
            (.mul (.const 4)
              (.mul (.mul (.var 1) (.mul (.var 2) (.var 3)))
                (.mul (.var 1) (.mul (.var 2) (.var 3))))))
          (.mul (.mul (.mul (.const 4) (.var 2)) (.var 2))
            (.mul (.var 0)
              (.mul (.const 4)
                (.mul (.mul (.var 1) (.var 3))
                  (.mul (.var 1) (.var 3))))))
          (by decide)
          (fun | 0 => (4 : Q')^n | 1 => t
               | 2 => HalfPow.half | _ => HalfPow.half^n)
      have hunit : Q'.eqv (4*HalfPow.half*HalfPow.half) 1 := by decide
      have hscale := Q'.mul_eqv_congr_right
        (4*HalfPow.half*HalfPow.half) 1 (displacementCoefficient t n) hunit
      exact Q'.eqv_trans _ _ _ hrec
        (Q'.eqv_trans _ _ _ hscale
          (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ih))

/-- Every ACTUAL finite dyadic product stays quadratically close to an
original witnessed graph input. No third graph derivative is used. -/
theorem product_domain_distance_le_four (t : Q') (ht : (0 : Q') < t)
    (d : D) (n : Nat) :
    RCle
      (distance hw0 hw1
        (iterate hw0 hw1 (step t n) (step_pos t ht n)
          (input hw0 hw1 d) (2^n))
        (input hw0 hw1 d))
      (RCscale (4*(t*t)) (N (output hw0 hw1 d))) := by
  let s := step t n
  let hs := step_pos t ht n
  let x := input hw0 hw1 d
  have hpow := dyadic_iterate_comparison hw0 hw1 s s hs hs x 1 0 n
  simp only [Nat.one_mul,Nat.zero_mul] at hpow
  change RCle
      (N (diff hw0 hw1 (iterate hw0 hw1 s hs x (2^n)) x))
      (RCscale ((4 : Q')^n) (N (diff hw0 hw1 (C s hs x) x))) at hpow
  have hsingle :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.cayley_domain_difference_norm_le_four
      hw0 hw1 s hs d
  change RCle (N (diff hw0 hw1 x (C s hs x)))
    (RCscale (4*(s*s)) (N (output hw0 hw1 d))) at hsingle
  have hreverse : N (diff hw0 hw1 (C s hs x) x) =
      N (diff hw0 hw1 x (C s hs x)) := by
    calc
      N (diff hw0 hw1 (C s hs x) x) =
          distance hw0 hw1 (C s hs x) x :=
        (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit.distance_eq_norm_difference
          hw0 hw1 (C s hs x) x).symm
      _ = distance hw0 hw1 x (C s hs x) :=
        BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.distance_symm hw0 hw1 _ _
      _ = N (diff hw0 hw1 x (C s hs x)) :=
        BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit.distance_eq_norm_difference
          hw0 hw1 x (C s hs x)
  rw [hreverse] at hpow
  have hscaled := RCscale_mono
    (Q'.pow_nonneg 4 (by decide) n) hsingle
  have h := RCle_trans hpow hscaled
  rw [RCscale_RCscale] at h
  change RCle
      (N (diff hw0 hw1 (iterate hw0 hw1 (step t n) (step_pos t ht n)
        (input hw0 hw1 d) (2^n)) (input hw0 hw1 d)))
      (RCscale (displacementCoefficient t n) (N (output hw0 hw1 d))) at h
  rw [YMGap.Continuum.RCSignedPairBudget.scale_congr
    (displacementCoefficient_pin t n)] at h
  rwa [BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit.distance_eq_norm_difference]

#print axioms displacementCoefficient
#print axioms displacementCoefficient_pin
#print axioms product_domain_distance_le_four

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity
