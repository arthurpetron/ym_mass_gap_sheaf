/-
# Explicit nome-defect budget for the signed quartic bulk polynomial

The checked six-term majorant now yields the explicit bound
P <= 148*n*h^2 + 16*n^5*h^4, h=1-w, n=k+3, A=w^(2k+3), V=w^2.
All parameters and constants are rational data. This scalar estimate is
not by itself a finite-prefix insertion bound, a variance comparison, or
a physical scaling family.
-/

import YMGap.Continuum.SU2HeatQuarticCoefficientMajorant
import YMGap.Continuum.R1CornerAtoms
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SU2HeatQuarticNomeBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2HeatQuarticCoefficientMajorant
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
local notation "rp" => RingNormaliser.qpow

/-- Literal polynomial budget, with no hidden coupling constant. -/
def budget (n h : Q') : Q' :=
  16*n*((n*n)*(n*n))*((h*h)*(h*h)) + 148*n*(h*h)

private theorem rp_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ k, (0 : Q') ≤ rp a k
  | 0 => by change (0 : Q') ≤ 1; decide
  | k+1 => Q'.mul_nonneg _ _ (rp_nonnegative ha k) ha

private theorem rp_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ k, rp a k ≤ rp b k
  | 0 => Q'.le_refl' _
  | k+1 =>
      Q'.mul_le_mul_of_nonneg (rp_mono ha hab k) hab
        (rp_nonnegative (Q'.le_trans' _ _ _ ha hab) k)
        ha

private theorem dimension_cap {n : Q'} (hn : (3 : Q') ≤ n) :
    60*(n+2) ≤ 100*n := by
  have hgap := Q'.mul_nonneg (40 : Q') (n + -3) (by decide)
    (Q'.sub_nonneg_of_le hn)
  have he : 60*(n+2) + 40*(n + -3) ≈ 100*n :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 60) (.add (.var 0) (.const 2)))
        (.mul (.const 40) (.add (.var 0) (.neg (.const 3)))))
      (.mul (.const 100) (.var 0)) (by decide) (fun _ => n)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hgap) (Q'.le_of_eqv he)

private theorem fourth_pin (n h : Q') :
    n * rp (2*n*h) 4 ≈ 16*n*((n*n)*(n*n))*((h*h)*(h*h)) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.pow (.mul (.mul (.const 2) (.var 0)) (.var 1)) 4))
    (.mul (.mul (.mul (.const 16) (.var 0))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => n | _ => h)

private theorem mixed_pin (n h : Q') :
    12*((2*h)*(2*n*h)) ≈ 48*n*(h*h) :=
  poly_identity_of_normal_eq
    (.mul (.const 12) (.mul (.mul (.const 2) (.var 1))
      (.mul (.mul (.const 2) (.var 0)) (.var 1))))
    (.mul (.mul (.const 48) (.var 0)) (.mul (.var 1) (.var 1)))
    (by decide) (fun | 0 => n | _ => h)

private theorem second_pin (n h : Q') :
    15*((n+2)*rp (2*h) 2) ≈ 60*(n+2)*(h*h) :=
  poly_identity_of_normal_eq
    (.mul (.const 15) (.mul (.add (.var 0) (.const 2))
      (.pow (.mul (.const 2) (.var 1)) 2)))
    (.mul (.mul (.const 60) (.add (.var 0) (.const 2)))
      (.mul (.var 1) (.var 1)))
    (by decide) (fun | 0 => n | _ => h)

private theorem combine_pin (n h : Q') :
    (16*n*((n*n)*(n*n))*((h*h)*(h*h)) + 48*n*(h*h)) +
      100*n*(h*h) ≈ budget n h := by
  let z := 16*n*((n*n)*(n*n))*((h*h)*(h*h))
  change (z + 48*n*(h*h)) + 100*n*(h*h) ≈ z + 148*n*(h*h)
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.mul (.mul (.const 48) (.var 1)) (.var 2)))
      (.mul (.mul (.const 100) (.var 1)) (.var 2)))
    (.add (.var 0) (.mul (.mul (.const 148) (.var 1)) (.var 2)))
    (by decide) (fun | 0 => z | 1 => n | _ => h*h)

/-- Quantitative consequence of the scalar majorant. The two defect bounds
will be supplied by Bernoulli for the actual heat exponents below. -/
theorem majorant_le_budget {n A V h : Q'} (hn3 : (3 : Q') ≤ n)
    (hh : (0 : Q') ≤ h) (hA1 : A ≤ (1 : Q')) (hV1 : V ≤ (1 : Q'))
    (hd : 1 + -A ≤ 2*n*h) (he : 1 + -V ≤ 2*h) :
    quarticMajorant n A V ≤ budget n h := by
  have hn : (0 : Q') ≤ n := Q'.le_trans' _ _ _ (by decide) hn3
  have hd0 := Q'.sub_nonneg_of_le hA1
  have he0 := Q'.sub_nonneg_of_le hV1
  have hn2 := Q'.zero_le_add n 2 hn (by decide)
  have h20 := Q'.mul_nonneg (2 : Q') h (by decide) hh
  have hh2 := Q'.mul_nonneg h h hh hh
  have hfour := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ n (rp_mono hd0 hd 4) hn)
    (Q'.le_of_eqv (fourth_pin n h))
  have hmix := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (12 : Q')
      (Q'.mul_le_mul_of_nonneg he hd h20 hd0) (by decide))
    (Q'.le_of_eqv (mixed_pin n h))
  have hsecond := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (15 : Q')
      (Q'.mul_le_mul_of_nonneg_left _ _ (n+2) (rp_mono he0 he 2) hn2)
      (by decide))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (second_pin n h))
      (Q'.mul_le_mul_of_nonneg_right _ _ (h*h) (dimension_cap hn3) hh2))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (quarticMajorant_formula n A V))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.add_le_add hfour hmix) hsecond)
      (Q'.le_of_eqv (combine_pin n h)))

private theorem native_defect {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Nat) :
    1 + -(w^a) ≤ Q'.ofNat a * (1 + -w) :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr_left (1 : Q') _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (qpow_eqv_pow w a)))))
    (R1CornerAtoms.oneSub_qpow_le hw0 hw1 a)

/-- The ACTUAL bulk exponent substitution. No asymptotic or spacing
assumption is used, and the output constant is the displayed rational budget. -/
theorem nome_majorant_le_budget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat) :
    quarticMajorant (Q'.ofNat (k+3)) (w^(2*k+3)) (w^2) ≤
      budget (Q'.ofNat (k+3)) (1 + -w) := by
  have hh := Q'.sub_nonneg_of_le hw1
  have hn3 : (3 : Q') ≤ Q'.ofNat (k+3) := by
    change Q'.ofNat 3 ≤ Q'.ofNat (k+3)
    exact CReal.ofNat_le_ofNat (show 3 ≤ k+3 by omega)
  have hc : Q'.ofNat (2*k+3) ≤ 2 * Q'.ofNat (k+3) := by
    have hn := CReal.ofNat_le_ofNat (show 2*k+3 ≤ 2*(k+3) by omega)
    have he : Q'.ofNat (2*(k+3)) ≈ 2 * Q'.ofNat (k+3) :=
      HeatKernelRGStep.ofNat_mul_eqv 2 (k+3)
    exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he)
  have hd := Q'.le_trans' _ _ _ (native_defect hw0 hw1 (2*k+3))
    (Q'.mul_le_mul_of_nonneg_right _ _ (1 + -w) hc hh)
  exact majorant_le_budget hn3 hh (HKPos.pow_le_one hw0 hw1 _)
    (HKPos.pow_le_one hw0 hw1 _) hd (native_defect hw0 hw1 2)

theorem nome_polynomial_le_budget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat) :
    quarticP (Q'.ofNat (k+3)) (w^(2*k+3)) (w^2) ≤
      budget (Q'.ofNat (k+3)) (1 + -w) :=
  Q'.le_trans' _ _ _
    (quarticP_le_majorant (Q'.ofNat_nonneg _) (Q'.pow_nonneg w hw0 _)
      (HKPos.pow_le_one hw0 hw1 _) (Q'.pow_nonneg w hw0 _) (HKPos.pow_le_one hw0 hw1 _))
    (nome_majorant_le_budget hw0 hw1 k)

#print axioms majorant_le_budget
#print axioms nome_majorant_le_budget
#print axioms nome_polynomial_le_budget

end YMGap.Continuum.SU2HeatQuarticNomeBudget
