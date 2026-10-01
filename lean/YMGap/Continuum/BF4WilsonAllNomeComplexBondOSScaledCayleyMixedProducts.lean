/-
# Mixed finite products on the original represented second core

The mixed Cayley defect is fourth order in its two rational parameters.
The actual commuting finite-power comparison amplifies its squared distance
by `4^n`, while both parameters are halved `n` times.  The result is an
exact quarter-geometric budget against the ORIGINAL represented preimage.
This is a finite same-carrier comparison, not a rational composition law,
physical-time calibration, continuum construction, or spectral assertion.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedBound
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedProducts

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedBound
  (mixedCoefficient mixed_error_norm_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison
  (compositeIterate dyadic_composite_comparison)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter
  (cayley_parameter_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq preimageNorm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit (quarter)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "Dom" => Domain hw0 hw1 (width := width)
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1

/-- The two halved parameters add to the halved sum modulo rational value. -/
theorem step_add_eqv (a b : Q') (n : Nat) :
    Q'.eqv (step a n + step b n) (step (a+b) n) := by
  unfold step
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
    (.mul (.add (.var 0) (.var 1)) (.var 2))
    (by decide) (fun | 0 => a | 1 => b | _ => HalfPow.half^n)

private def fourth (x : Q') : Q' := (x*x)*(x*x)

private def fourthExpr (x : PolyExpr) : PolyExpr :=
  .mul (.mul x x) (.mul x x)

private def mixedExpr (a b : PolyExpr) : PolyExpr :=
  let a4 := fourthExpr a
  let b4 := fourthExpr b
  let c4 := fourthExpr (.add a b)
  let cross := .mul (.mul (.mul b b) (.const 4))
    (.mul (.const 4) (.mul a a))
  .add
    (.mul (.const 2)
      (.add
        (.mul (.const 2)
          (.add
            (.mul (.const 2) (.mul (.const 4) b4))
            (.mul (.const 2) (.mul (.const 4) a4))))
        (.mul (.const 2) (.mul (.const 4) c4))))
    (.mul (.const 2) cross)

/-- Exact degree-four homogeneity of the genuine mixed-error coefficient. -/
theorem mixedCoefficient_scale_eqv (a b h : Q') :
    Q'.eqv (mixedCoefficient (h*a) (h*b))
      (fourth h * mixedCoefficient a b) := by
  unfold mixedCoefficient fourth
  exact poly_identity_of_normal_eq
    (mixedExpr (.mul (.var 2) (.var 0)) (.mul (.var 2) (.var 1)))
    (.mul (fourthExpr (.var 2)) (mixedExpr (.var 0) (.var 1)))
    (by decide) (fun | 0 => a | 1 => b | _ => h)

/-- The `4^n` finite-power loss cancels two of the four dyadic halvings
in the squared local error, leaving the exact quarter-geometric rate. -/
theorem dyadic_fourth_factor_eqv (n : Nat) :
    Q'.eqv (((4 : Q')^n)*fourth (HalfPow.half^n)) (quarter^n) := by
  have hhalf : Q'.eqv ((4 : Q')*fourth HalfPow.half) quarter := by decide
  induction n with
  | zero =>
      unfold fourth
      simp only [Q'.pow_zero]
      decide
  | succ n ih =>
      have h₁ : Q'.eqv
          (((4 : Q')^(n+1))*fourth (HalfPow.half^(n+1)))
          ((4*fourth HalfPow.half)*
            (((4 : Q')^n)*fourth (HalfPow.half^n))) := by
        unfold fourth
        rw [Q'.pow_succ (4 : Q') n, Q'.pow_succ HalfPow.half n]
        exact poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 0))
            (fourthExpr (.mul (.var 1) (.var 2))))
          (.mul (.mul (.const 4) (fourthExpr (.var 1)))
            (.mul (.var 0) (fourthExpr (.var 2))))
          (by decide)
          (fun | 0 => (4 : Q')^n | 1 => HalfPow.half | _ => HalfPow.half^n)
      have h₂ := Q'.mul_eqv_congr_right
        (4*fourth HalfPow.half) quarter
        (((4 : Q')^n)*fourth (HalfPow.half^n)) hhalf
      have h₃ := Q'.mul_eqv_congr_left quarter
        (((4 : Q')^n)*fourth (HalfPow.half^n)) (quarter^n) ih
      have h₄ : Q'.eqv (quarter*quarter^n) (quarter^(n+1)) := by
        rw [Q'.pow_succ]
        exact Q'.eqv_refl _
      exact Q'.eqv_trans _ _ _ h₁
        (Q'.eqv_trans _ _ _ h₂ (Q'.eqv_trans _ _ _ h₃ h₄))

/-- Exact mixed coefficient of the dyadic finite-product comparison. -/
theorem dyadic_mixed_coefficient_eqv (a b : Q') (n : Nat) :
    Q'.eqv (((4 : Q')^n)*mixedCoefficient (step a n) (step b n))
      (quarter^n*mixedCoefficient a b) := by
  have hscale : Q'.eqv
      (mixedCoefficient (step a n) (step b n))
      (fourth (HalfPow.half^n)*mixedCoefficient a b) := by
    unfold step
    have h := mixedCoefficient_scale_eqv a b (HalfPow.half^n)
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (mixedExpr (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (mixedExpr (.mul (.var 2) (.var 0)) (.mul (.var 2) (.var 1)))
        (by decide) (fun | 0 => a | 1 => b | _ => HalfPow.half^n)) h
  have h₁ := Q'.mul_eqv_congr_left ((4 : Q')^n)
    (mixedCoefficient (step a n) (step b n))
    (fourth (HalfPow.half^n)*mixedCoefficient a b) hscale
  have h₂ : Q'.eqv
      (((4 : Q')^n)*(fourth (HalfPow.half^n)*mixedCoefficient a b))
      ((((4 : Q')^n)*fourth (HalfPow.half^n))*mixedCoefficient a b) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have h₃ := Q'.mul_eqv_congr_right
    (((4 : Q')^n)*fourth (HalfPow.half^n)) (quarter^n)
    (mixedCoefficient a b) (dyadic_fourth_factor_eqv n)
  exact Q'.eqv_trans _ _ _ h₁
    (Q'.eqv_trans _ _ _ h₂ h₃)

private theorem mixedCoefficient_nonnegative (a b : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ mixedCoefficient a b := by
  have hsqA : (0 : Q') ≤ a*a := Q'.mul_nonneg _ _ ha ha
  have hsqB : (0 : Q') ≤ b*b := Q'.mul_nonneg _ _ hb hb
  have hsqC : (0 : Q') ≤ (a+b)*(a+b) :=
    Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ ha hb)
      (Q'.zero_le_add _ _ ha hb)
  have ha4 := Q'.mul_nonneg _ _ hsqA hsqA
  have hb4 := Q'.mul_nonneg _ _ hsqB hsqB
  have hc4 := Q'.mul_nonneg _ _ hsqC hsqC
  have hcross : (0 : Q') ≤ ((b*b)*4)*(4*(a*a)) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hsqB (by decide))
      (Q'.mul_nonneg _ _ (by decide) hsqA)
  unfold mixedCoefficient
  dsimp only
  apply Q'.zero_le_add
  · apply Q'.mul_nonneg _ _ (by decide)
    apply Q'.zero_le_add
    · apply Q'.mul_nonneg _ _ (by decide)
      apply Q'.zero_le_add
      · exact Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ (by decide) hb4)
      · exact Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ (by decide) ha4)
    · exact Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (by decide) hc4)
  · exact Q'.mul_nonneg _ _ (by decide) hcross

/-- The actual commuting mixed products have a quarter-geometric squared
distance budget on each represented original second-core input. -/
theorem mixed_products_bound
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy)
    (a b : Q') (ha : (0 : Q') < a) (hb : (0 : Q') < b) (n : Nat) :
    RCle
      (distance hw0 hw1
        (compositeIterate hw0 hw1 (step a n) (step b n)
          (step_pos a ha n) (step_pos b hb n)
          (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)) (2^n))
        (iterate hw0 hw1 (step (a+b) n)
          (step_pos (a+b) (Q'.add_pos ha hb) n)
          (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)) (2^n)))
      (RCscale (quarter^n*mixedCoefficient a b) (preimageNorm hw0 hw1 Y)) := by
  let d : Dom := BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y
  let e : Dom := BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y
  let sa := step a n
  let sb := step b n
  let sc := step (a+b) n
  have hlink : Out d = In e :=
    BF4WilsonAllNomeComplexBondOSSecondCore.first_output_eq_second_input
      hw0 hw1 Y
  have hsum : (0 : Q') < sa+sb := Q'.add_pos (step_pos a ha n) (step_pos b hb n)
  have hsource : RCle (normSq hw0 hw1 (Out e)) (preimageNorm hw0 hw1 Y) :=
    BF4WilsonAllNomeComplexBondOSSecondCore.second_output_norm_le hw0 hw1 Y
  have hnonneg : (0 : Q') ≤ mixedCoefficient sa sb :=
    mixedCoefficient_nonnegative sa sb
      (Q'.le_of_lt (step_pos a ha n)) (Q'.le_of_lt (step_pos b hb n))
  have hlocal := mixed_error_norm_le hw0 hw1 sa sb
    (step_pos a ha n) (step_pos b hb n) hsum d e hlink
  have hparameter : C (sa+sb) hsum (In d) =
      C sc (step_pos (a+b) (Q'.add_pos ha hb) n) (In d) :=
    cayley_parameter_congr hw0 hw1 hsum
      (step_pos (a+b) (Q'.add_pos ha hb) n)
      (step_add_eqv a b n) (In d)
  rw [hparameter] at hlocal
  have hweighted := RCscale_mono hnonneg hsource
  have hstep := RCle_trans hlocal hweighted
  have hpow := dyadic_composite_comparison hw0 hw1 sa sb sc
    (step_pos a ha n) (step_pos b hb n)
    (step_pos (a+b) (Q'.add_pos ha hb) n) (In d) n
  rw [distance_eq_norm_difference hw0 hw1
    (C sb (step_pos b hb n) (C sa (step_pos a ha n) (In d)))
    (C sc (step_pos (a+b) (Q'.add_pos ha hb) n) (In d))] at hpow
  have hpow_nonneg : (0 : Q') ≤ (4 : Q')^n :=
    Q'.pow_nonneg 4 (by decide) n
  have hscaled := RCscale_mono hpow_nonneg hstep
  rw [RCscale_RCscale] at hscaled
  have h := RCle_trans hpow hscaled
  rw [scale_congr (dyadic_mixed_coefficient_eqv a b n)
    (preimageNorm hw0 hw1 Y)] at h
  exact h

#print axioms step_add_eqv
#print axioms mixedCoefficient_scale_eqv
#print axioms dyadic_fourth_factor_eqv
#print axioms dyadic_mixed_coefficient_eqv
#print axioms mixed_products_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedProducts
