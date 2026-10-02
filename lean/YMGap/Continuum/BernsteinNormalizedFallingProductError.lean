/-
# Explicit error for the actual normalized falling-factorial coefficient

At N=n+1 the coefficient is the literal quotient

  product n j r / product n N r = (j)_r/(N)_r.

The existing falling-product error constructs a cutoff with denominator
at least 1/2. At that cutoff the quotient differs from (j/N)^r by at most
2*C(r)/N; the reverse error is at most C(r)/N. Every order, including
0 and 1, and every truncated numerator j<r is covered. A tolerance cutoff
is computed from the existing rational moduli.

This is numerical coefficient algebra. It does NOT construct a rational
Bernstein row reconstruction, an original Haar square certificate, a heat
profile or any continuum/survival result.
-/

import YMGap.Continuum.BernsteinFallingProductError

namespace YMGap.Continuum.BernsteinNormalizedFallingProductError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BernsteinFallingProductError
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Computed cutoff guaranteeing a denominator floor, including low orders. -/
def denominatorCutoff (r : Nat) : Nat := modulus r HalfPow.half

theorem topProduct_half_floor (n r : Nat) (hn : denominatorCutoff r ≤ n) :
    HalfPow.half ≤ product n (n+1) r := by
  have hs : error n r ≤ HalfPow.half := error_small r HalfPow.half (by decide) n hn
  have ht : (1 : Q') ≤ product n (n+1) r+HalfPow.half := Q'.le_trans' _ _ _
    (top_product_budget n r) (Q'.add_le_add_left _ _ _ hs)
  have h := Q'.add_le_add_right _ _ (-HalfPow.half) ht
  have he : (product n (n+1) r+HalfPow.half)+ -HalfPow.half ≈ product n (n+1) r :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => product n (n+1) r | _ => HalfPow.half)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : (1 : Q')+ -HalfPow.half ≈ HalfPow.half))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))

/-- Actual positive-denominator proof; no external positivity datum is used. -/
theorem topProduct_positive (n r : Nat) (hn : denominatorCutoff r ≤ n) :
    (0 : Q') < product n (n+1) r := by
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half)
    (topProduct_half_floor n r hn)

/-- The actual normalized falling product at the computed denominator cutoff. -/
def normalizedProduct (n j r : Nat) (hn : denominatorCutoff r ≤ n) : Q' :=
  Q'.divPos (product n j r) (product n (n+1) r) (topProduct_positive n r hn)

theorem normalizedProduct_mul_top (n j r : Nat) (hn : denominatorCutoff r ≤ n) :
    normalizedProduct n j r hn*product n (n+1) r ≈ product n j r :=
  Q'.divPos_mul_eqv _ _ _

theorem normalizedProduct_nonnegative (n j r : Nat) (hn : denominatorCutoff r ≤ n) :
    (0 : Q') ≤ normalizedProduct n j r hn :=
  Q'.mul_nonneg _ _ (product_nonnegative n j r)
    (Q'.le_of_lt (Q'.recipPos_pos _ (topProduct_positive n r hn)))

/-- Dividing by the top product, which is at most one, cannot decrease the
nonnegative numerator. This keeps the sharper reverse error C(r)/N. -/
theorem power_le_normalizedProduct_error (n j r : Nat) (hj : j ≤ n+1)
    (hn : denominatorCutoff r ≤ n) :
    grid n j^r ≤ normalizedProduct n j r hn+error n r := by
  have hA : product n j r ≤ normalizedProduct n j r hn :=
    Q'.le_divPos_of_mul_le _ _ (topProduct_positive n r hn)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (product n j r)
          (product_le_one n (n+1) r (Nat.le_refl _)) (product_nonnegative n j r))
        (Q'.le_of_eqv (Q'.mul_one_eqv _)))
  exact Q'.le_trans' _ _ _ (power_le_product_error n j hj r)
    (Q'.add_le_add_right _ _ _ hA)

/-- The other direction pays at most twice the existing falling-product
error, since the computed top-product denominator is at least one half. -/
theorem normalizedProduct_le_power_error (n j r : Nat) (hj : j ≤ n+1)
    (hn : denominatorCutoff r ≤ n) :
    normalizedProduct n j r hn ≤ grid n j^r+2*error n r := by
  let A := product n j r
  let B := product n (n+1) r
  let P := grid n j^r
  let e := error n r
  have hP0 : (0 : Q') ≤ P := Q'.pow_nonneg _ (grid_nonnegative n j) r
  have hP1 : P ≤ (1 : Q') := HKPos.pow_le_one (grid_nonnegative n j) (grid_le_one n j hj) r
  have he0 : (0 : Q') ≤ e := error_nonnegative n r
  have he2 : (0 : Q') ≤ 2*e := Q'.mul_nonneg _ _ (by decide) he0
  have hPB : P ≤ P*B+e := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ P (top_product_budget n r) hP0
    have hPe : P*e ≤ e := Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ e hP1 he0) (Q'.le_of_eqv (Q'.one_mul_eqv e))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv P))
      (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv P B e))
        (Q'.add_le_add_left _ _ _ hPe)))
  have heB : e ≤ (2*e)*B := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (.mul (.mul (.const 2) (.var 1)) (.var 0))
        (by decide) (fun | 0 => e | _ => HalfPow.half))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ e (by decide : (2 : Q')*HalfPow.half ≈ 1))
        (Q'.one_mul_eqv e))))
    (Q'.mul_le_mul_of_nonneg_left _ _ (2*e) (topProduct_half_floor n r hn) he2)
  have hA : A ≤ (P+2*e)*B := Q'.le_trans' _ _ _ (product_le_power n j r)
    (Q'.le_trans' _ _ _ hPB (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ heB)
      (Q'.ge_of_eqv (Q'.add_mul_eqv P (2*e) B))))
  exact Q'.divPos_le_of_le_mul _ _ (topProduct_positive n r hn) hA

/-- Computed tolerance index, combining denominator safety and 2e<=epsilon. -/
def toleranceCutoff (r : Nat) (epsilon : Q') : Nat :=
  max (denominatorCutoff r) (modulus r (HalfPow.half*epsilon))

/-- Both orders of the actual coefficient comparison, with explicit modulus.
No Bernstein positivity or original Haar certificate is assumed or returned. -/
theorem normalizedProduct_close (r : Nat) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : toleranceCutoff r epsilon ≤ n) (j : Nat) (hj : j ≤ n+1) :
    let hden : denominatorCutoff r ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    normalizedProduct n j r hden ≤ grid n j^r+epsilon ∧
      grid n j^r ≤ normalizedProduct n j r hden+epsilon := by
  let hden : denominatorCutoff r ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hs : error n r ≤ HalfPow.half*epsilon := error_small r (HalfPow.half*epsilon)
    (Q'.mul_pos (by decide) he) n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have htwo : 2*error n r ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hs (by decide))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half epsilon))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ epsilon (by decide : (2 : Q')*HalfPow.half ≈ 1))
        (Q'.one_mul_eqv epsilon))))
  have herror : error n r ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (error n r)))
      (Q'.mul_le_mul_of_nonneg_right _ _ (error n r) (by decide : (1 : Q') ≤ 2)
        (error_nonnegative n r))) htwo
  exact ⟨Q'.le_trans' _ _ _ (normalizedProduct_le_power_error n j r hj hden)
      (Q'.add_le_add_left _ _ _ htwo),
    Q'.le_trans' _ _ _ (power_le_normalizedProduct_error n j r hj hden)
      (Q'.add_le_add_left _ _ _ herror)⟩

#print axioms denominatorCutoff
#print axioms topProduct_half_floor
#print axioms topProduct_positive
#print axioms normalizedProduct
#print axioms normalizedProduct_mul_top
#print axioms normalizedProduct_nonnegative
#print axioms power_le_normalizedProduct_error
#print axioms normalizedProduct_le_power_error
#print axioms toleranceCutoff
#print axioms normalizedProduct_close

end YMGap.Continuum.BernsteinNormalizedFallingProductError
