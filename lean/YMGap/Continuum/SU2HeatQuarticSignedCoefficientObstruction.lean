/-
# A finite coefficient obstruction to signed quartic kernel transport

The original finite quartic compiler retains output spin K+2. Its coefficient
is the strictly positive ORIGINAL heat coefficient at K, whereas an affine
multiple of the SAME-cutoff squared-nome heat prefix has zero there. A constant
kernel error changes only spin zero. Thus the actual affine residual has a
negative top coefficient for every q>0 and every cutoff, including K=0.

This is only a coefficient-level obstruction. It does not assemble an original
Haar negative-quadratic witness, refute a bound for the particular centered
Wilson source, or bound the actual response. In particular it does not conflict
with the proved positive-source Haar Certificate: a pointwise-positive kernel
polynomial need not have nonnegative character coefficients.
-/

import YMGap.Continuum.SU2HeatQuarticFiniteRegroup

namespace YMGap.Continuum.SU2HeatQuarticSignedCoefficientObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RGTransport (dimQ c4 qpow)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup

local infix:50 " ≈ " => Q'.eqv

private theorem qpow_positive {q : Q'} (hq : (0 : Q') < q) :
    ∀ n, (0 : Q') < qpow q n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (qpow_positive hq n) hq

private theorem heat_coefficient_positive {q : Q'} (hq : (0 : Q') < q)
    (K : Nat) : (0 : Q') < coeffW q K := by
  unfold coeffW dimQ
  exact Q'.mul_pos (Q'.ofNat_succ_pos K) (qpow_positive hq (c4 K))

private theorem negative_of_positive {a : Q'} (ha : (0 : Q') < a) :
    -a < (0 : Q') := by
  have hn : (0 : Int) < a.num := Q'.num_pos_of_pos ha
  change -a.num * 1 < 0 * ((-a).den : Int)
  simp only [Int.mul_one, Int.zero_mul]
  omega

/-- Exact top row of the existing finite quartic coefficient compiler. No
untruncated coefficient or omitted-mode approximation is substituted. -/
theorem quarticCoeff_top_eqv (q : Q') (K : Nat) :
    quarticCoeff (cutCoeff q K) (K+2) ≈ coeffW q K := by
  have h1 : K < K+1 := by omega
  have h2 : K < K+2 := by omega
  have h3 : K < K+3 := by omega
  have h4 : K < K+4 := by omega
  change ((6 * cutCoeff q K (K+2) +
    -(4 * (cutCoeff q K (K+1) + cutCoeff q K (K+3)))) +
    cutCoeff q K K) + cutCoeff q K (K+4) ≈ coeffW q K
  rw [cutCoeff_zero_of_gt q K (K+1) h1,
    cutCoeff_zero_of_gt q K (K+2) h2,
    cutCoeff_zero_of_gt q K (K+3) h3,
    cutCoeff_zero_of_gt q K (K+4) h4]
  have hself : cutCoeff q K K = coeffW q K := if_pos (Nat.le_refl K)
  rw [hself]
  have hleft : (6*0 + -(4*(0+0)) : Q') + coeffW q K ≈ coeffW q K :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (by decide : (6*0 + -(4*(0+0)) : Q') ≈ 0))
      (Q'.eqv_of_eq (Q'.zero_add' _))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ 0 hleft)
    (Q'.eqv_of_eq (Q'.add_zero' _))

theorem quarticCoeff_top_positive {q : Q'} (hq : (0 : Q') < q) (K : Nat) :
    (0 : Q') < quarticCoeff (cutCoeff q K) (K+2) :=
  Q'.pos_of_lt_of_le (heat_coefficient_positive hq K)
    (Q'.ge_of_eqv (quarticCoeff_top_eqv q K))

/-- Actual affine residual coefficient, with the constant error confined to
its original vacuum character. The nome is q*q, not an independent parameter. -/
def affineResidualCoeff (q : Q') (K : Nat) (c e : Q') (j : Nat) : Q' :=
  c * cutCoeff (q*q) K j + (if j = 0 then e else 0) -
    quarticCoeff (cutCoeff q K) j

theorem affineMajorant_top_zero (q : Q') (K : Nat) (c e : Q') :
    c * cutCoeff (q*q) K (K+2) + (if K+2 = 0 then e else 0) ≈ 0 := by
  rw [cutCoeff_zero_of_gt (q*q) K (K+2) (by omega),
    if_neg (show K+2 ≠ 0 by omega)]
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (Q'.mul_zero_eqv c)

theorem affineResidual_top_eqv (q : Q') (K : Nat) (c e : Q') :
    affineResidualCoeff q K c e (K+2) ≈ -(coeffW q K) := by
  unfold affineResidualCoeff
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (affineMajorant_top_zero q K c e)
      (Q'.neg_eqv_congr _ _ (quarticCoeff_top_eqv q K)))
    (Q'.eqv_of_eq (Q'.zero_add' _))

/-- No sign or upper bound on c/e, no q<1 assumption, and no positive-cutoff
guard can remove this SAME-prefix top-spin coefficient. -/
theorem affineResidual_top_negative {q : Q'} (hq : (0 : Q') < q)
    (K : Nat) (c e : Q') : affineResidualCoeff q K c e (K+2) < (0 : Q') :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv (affineResidual_top_eqv q K c e))
    (negative_of_positive (heat_coefficient_positive hq K))

/-- Prunes only nonnegative-character-coefficient domination by this affine
SAME-cutoff majorant; it is not an assembled operator counterexample. -/
theorem not_affineResidual_coefficients_nonnegative {q : Q'}
    (hq : (0 : Q') < q) (K : Nat) (c e : Q') :
    ¬ (∀ j, (0 : Q') ≤ affineResidualCoeff q K c e j) := by
  intro h
  have hf : (0 : Q') < 0 := Q'.lt_of_le_of_lt (h (K+2))
    (affineResidual_top_negative hq K c e)
  exact (by decide : ¬ ((0 : Q') < 0)) hf

#print axioms quarticCoeff_top_eqv
#print axioms quarticCoeff_top_positive
#print axioms affineResidualCoeff
#print axioms affineMajorant_top_zero
#print axioms affineResidual_top_eqv
#print axioms affineResidual_top_negative
#print axioms not_affineResidual_coefficients_nonnegative

end YMGap.Continuum.SU2HeatQuarticSignedCoefficientObstruction
