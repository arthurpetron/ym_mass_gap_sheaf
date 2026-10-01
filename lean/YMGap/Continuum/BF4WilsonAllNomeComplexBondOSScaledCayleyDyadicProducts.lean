/-
# Original physical dyadic Cayley products

Every product below is an iterate of the actual complex Wilson-bond Cayley
operator, and `productRows` retains its original represented state.  The
consecutive estimate is a finite same-graph estimate on the represented
second core; this file asserts no physical-time or continuum identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows ofState value value_injective value_ofState)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (input)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
  (iterate iterateRows iterateRows_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq preimageNorm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
  (dyadic_iterate_comparison)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "N" => normSq hw0 hw1
local notation "D" => BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)

/-- Actual rational dyadic Cayley step; the outer parameter is strictly
positive, whereas the index is any natural number. -/
def step (t : Q') (n : Nat) : Q' := t*HalfPow.half^n

private theorem half_pos : (0 : Q') < HalfPow.half := by decide

private theorem rational_pow_pos (a : Q') (ha : (0 : Q') < a) :
    ∀ n : Nat, (0 : Q') < a^n
  | 0 => by simpa only [Q'.pow_zero] using (show (0 : Q') < 1 by decide)
  | n+1 => Q'.mul_pos ha (rational_pow_pos a ha n)

theorem step_pos (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    (0 : Q') < step t n :=
  Q'.mul_pos ht (rational_pow_pos HalfPow.half half_pos n)

theorem double_step_pos (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    (0 : Q') < 2*step t (n+1) :=
  Q'.mul_pos (by decide : (0 : Q') < 2) (step_pos t ht (n+1))

private theorem one_mul_eqv (a : Q') : Q'.eqv ((1 : Q')*a) a :=
  poly_identity_of_normal_eq (.mul (.const 1) (.var 0)) (.var 0)
    (by decide) (fun _ => a)

/-- Rational equivalence, not literal equality of unreduced numerator and
denominator records, identifies successive Cayley parameters. -/
theorem double_step_eqv (t : Q') (n : Nat) :
    Q'.eqv (2*step t (n+1)) (step t n) := by
  unfold step
  rw [Q'.pow_succ]
  have h₁ : Q'.eqv (2*(t*(HalfPow.half*HalfPow.half^n)))
      ((2*HalfPow.half)*(t*HalfPow.half^n)) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide)
      (fun | 0 => t | 1 => HalfPow.half | _ => HalfPow.half^n)
  have h₂ : Q'.eqv ((2*HalfPow.half)*(t*HalfPow.half^n))
      (1*(t*HalfPow.half^n)) :=
    Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (2*HalfPow.half) 1)
  exact Q'.eqv_trans _ _ _ h₁
    (Q'.eqv_trans _ _ _ h₂ (one_mul_eqv _))

private def sourceState (Y : (D).Cauchy × (D).Cauchy) :=
  BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1
    (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)

private theorem sourceState_pin (Y : (D).Cauchy × (D).Cauchy) :
    ofState hw0 hw1 (sourceState hw0 hw1 Y) =
      input hw0 hw1 (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y) := by
  apply value_injective hw0 hw1
  rw [value_ofState]
  change BF4WilsonAllNomeComplexSectorDerivative.stateValue hw0 hw1
      (BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1
        (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)) =
    value hw0 hw1 (input hw0 hw1
      (BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1
        (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)))
  exact (BF4WilsonAllNomeComplexBondOSDerivative.value_input_ofPoint hw0 hw1
    (BF4WilsonAllNomeComplexBondOSSecondCore.firstPoint hw0 hw1 Y)).symm

/-- The dyadic iterate remains on the ORIGINAL completed complex bond
carrier, with the genuine input of the first physical second-core point. -/
def product (Y : (D).Cauchy × (D).Cauchy) (t : Q') (ht : (0 : Q') < t)
    (n : Nat) : H :=
  iterate hw0 hw1 (step t n) (step_pos t ht n)
    (input hw0 hw1 (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))
    (2^n)

/-- The same product with its original pair of Cauchy rows retained. -/
def productRows (Y : (D).Cauchy × (D).Cauchy) (t : Q') (ht : (0 : Q') < t)
    (n : Nat) : Rows hw0 hw1 (width := width) :=
  iterateRows hw0 hw1 (step t n) (step_pos t ht n)
    (sourceState hw0 hw1 Y) (2^n)

theorem productRows_pin (Y : (D).Cauchy × (D).Cauchy)
    (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    ofRows hw0 hw1 (productRows hw0 hw1 Y t ht n) =
      product hw0 hw1 Y t ht n := by
  unfold productRows product
  rw [iterateRows_pin,sourceState_pin]

/-- The uncollapsed finite bound before simplifying its dyadic coefficient.
It already compares ACTUAL consecutive physical products. -/
theorem product_consecutive_parameter_bound
    (Y : (D).Cauchy × (D).Cauchy)
    (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    RCle
      (N (diff hw0 hw1 (product hw0 hw1 Y t ht (n+1))
        (product hw0 hw1 Y t ht n)))
      (RCscale ((4 : Q')^n)
        (RCscale ((352 : Q')*
          ((step t (n+1)*step t (n+1))*
            (step t (n+1)*step t (n+1))))
          (preimageNorm hw0 hw1 Y))) := by
  let h := step t (n+1)
  let hh := step_pos t ht (n+1)
  let h2 := double_step_pos t ht n
  let x := input hw0 hw1
    (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)
  have hp := BF4WilsonAllNomeComplexBondOSScaledCayleyParameter.iterate_parameter_congr
    hw0 hw1 (step_pos t ht n) h2 (Q'.eqv_symm (double_step_eqv t n)) x (2^n)
  have hcount : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
  have hpow := dyadic_iterate_comparison hw0 hw1 h (2*h) hh h2 x 2 1 n
  have hlocal :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound.secondCore_doubled_error_norm_le
      hw0 hw1 h hh h2 Y
  have hnonneg : (0 : Q') ≤ (4 : Q')^n :=
    Q'.pow_nonneg 4 (by decide) n
  have hscaled := RCscale_mono hnonneg hlocal
  have hfinal := RCle_trans hpow hscaled
  change RCle
    (N (diff hw0 hw1 (product hw0 hw1 Y t ht (n+1))
      (product hw0 hw1 Y t ht n)))
    (RCscale ((4 : Q')^n)
      (RCscale ((352 : Q')*((h*h)*(h*h))) (preimageNorm hw0 hw1 Y)))
  unfold product
  rw [hcount,hp]
  simpa only [Nat.one_mul] using hfinal

private def fourth (a : Q') : Q' := (a*a)*(a*a)

private def coefficient (t : Q') (n : Nat) : Q' :=
  ((4 : Q')^n)*(352*fourth (step t (n+1)))

private def fourthExpr (p : PolyExpr) : PolyExpr :=
  .mul (.mul p p) (.mul p p)

private theorem coefficient_eqv (t : Q') (n : Nat) :
    Q'.eqv (coefficient t n)
      ((22*fourth t)*
        BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.quarter^n) := by
  let q := BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.quarter
  have hhalf : Q'.eqv ((4 : Q')*fourth HalfPow.half) q := by decide
  have hbase : Q'.eqv (352*fourth HalfPow.half) 22 := by decide
  induction n with
  | zero =>
      have h₁ : Q'.eqv (coefficient t 0)
          ((352*fourth HalfPow.half)*fourth t) := by
        unfold coefficient fourth step
        simp only [Q'.pow_zero,Q'.pow_succ]
        exact poly_identity_of_normal_eq
          (.mul (.const 1)
            (.mul (.const 352)
              (fourthExpr (.mul (.var 0)
                (.mul (.var 1) (.const 1))))))
          (.mul (.mul (.const 352) (fourthExpr (.var 1)))
            (fourthExpr (.var 0)))
          (by decide) (fun | 0 => t | _ => HalfPow.half)
      have h₂ := Q'.mul_eqv_congr_right
        (352*fourth HalfPow.half) 22 (fourth t) hbase
      have h₃ : Q'.eqv (22*fourth t)
          ((22*fourth t)*q^0) := by
        simp only [Q'.pow_zero]
        exact Q'.eqv_symm (Q'.mul_one_eqv _)
      exact Q'.eqv_trans _ _ _ h₁ (Q'.eqv_trans _ _ _ h₂ h₃)
  | succ n ih =>
      have h₁ : Q'.eqv (coefficient t (n+1))
          ((4*fourth HalfPow.half)*coefficient t n) := by
        unfold coefficient fourth step
        rw [Q'.pow_succ (4 : Q') n,
          Q'.pow_succ HalfPow.half (n+1)]
        exact poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 1))
            (.mul (.const 352)
              (fourthExpr (.mul (.var 0)
                (.mul (.var 2) (.var 3))))))
          (.mul (.mul (.const 4) (fourthExpr (.var 2)))
            (.mul (.var 1)
              (.mul (.const 352)
                (fourthExpr (.mul (.var 0) (.var 3))))))
          (by decide)
          (fun | 0 => t | 1 => (4 : Q')^n
               | 2 => HalfPow.half | _ => HalfPow.half^(n+1))
      have h₂ := Q'.mul_eqv_congr_right
        (4*fourth HalfPow.half) q (coefficient t n) hhalf
      have h₃ := Q'.mul_eqv_congr_left q (coefficient t n)
        ((22*fourth t)*q^n) ih
      have h₄ : Q'.eqv (q*((22*fourth t)*q^n))
          ((22*fourth t)*q^(n+1)) := by
        rw [Q'.pow_succ]
        exact poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide)
          (fun | 0 => q | 1 => 22*fourth t | _ => q^n)
      exact Q'.eqv_trans _ _ _ h₁
        (Q'.eqv_trans _ _ _ h₂
          (Q'.eqv_trans _ _ _ h₃ h₄))

/-- The actual represented second-core products have quarter-geometric
consecutive squared error.  Its coefficient retains the original Cauchy
preimage norm rather than a changed physical input norm. -/
theorem product_consecutive_norm_le
    (Y : (D).Cauchy × (D).Cauchy)
    (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    RCle
      (N (diff hw0 hw1 (product hw0 hw1 Y t ht (n+1))
        (product hw0 hw1 Y t ht n)))
      (RCscale ((22*((t*t)*(t*t)))*
        BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.quarter^n)
        (preimageNorm hw0 hw1 Y)) := by
  have h := product_consecutive_parameter_bound hw0 hw1 Y t ht n
  rw [RCscale_RCscale] at h
  change RCle _ (RCscale (coefficient t n) (preimageNorm hw0 hw1 Y)) at h
  rw [scale_congr (coefficient_eqv t n) (preimageNorm hw0 hw1 Y)] at h
  exact h

#print axioms step_pos
#print axioms double_step_eqv
#print axioms product
#print axioms productRows_pin
#print axioms product_consecutive_parameter_bound
#print axioms product_consecutive_norm_le

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
