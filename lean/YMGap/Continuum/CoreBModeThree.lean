/-
# Core-B mode-three cross-ratio prefix

This file proves the `s = 3` member of `CrossRatioMonotone.cross` uniformly
for every exact rational coupling `0 ≤ w ≤ wH`.  All range-four
autoconvolution and endpoint constants are derived from the library
definitions.  With `x = w²`, the endpoint-scaled polynomial difference is
certified reflectively as

  458500 M(x) - 1009899 A(x) = 4 (1 - 4x) P(x),

where

  P(x) = 3029697x⁸ + 41018x⁷ + 4554800x⁶ + 1138700x⁵
       + 749170x⁴ - 2391770x³ + 19095088x²
       - 2562228x + 9284625.

The two negative monomials are bounded coarsely using `x ≤ 1/4` and
`x³ ≤ 1/64`; all remaining monomials are nonnegative.  Thus no numerical
scouting identity is assumed.
-/

import YMGap.Continuum.CoreBModeTwo
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBModeThree

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.FiniteSMarginWorstcase
open YMGap.Continuum.AcNReserveAnalytic

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl
private theorem zero_num : (0 : Q').num = 0 := rfl
private theorem zero_den : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num, zero_num, zero_den, one_num, one_den,
               Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

private theorem mul_eqv_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem mul_two_by_three (a b c d e : Q') :
    (a + b) * (c + d + e) ≈
      a * c + a * d + a * e + b * c + b * d + b * e := by
  refine Q'.eqv_trans _ (a * (c + d + e) + b * (c + d + e)) _
    (Q'.add_mul_eqv a b (c + d + e)) ?_
  have ha : a * (c + d + e) ≈ a * c + a * d + a * e := by
    refine Q'.eqv_trans _ (a * (c + d) + a * e) _
      (Q'.mul_add_eqv a (c + d) e) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv a c d)
  have hb : b * (c + d + e) ≈ b * c + b * d + b * e := by
    refine Q'.eqv_trans _ (b * (c + d) + b * e) _
      (Q'.mul_add_eqv b (c + d) e) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv b c d)
  refine Q'.eqv_trans _
    ((a * c + a * d + a * e) + (b * c + b * d + b * e)) _
    (Q'.add_eqv_congr' ha hb) ?_
  ring_qeqv

private theorem mul_three_by_three (a b c d e f : Q') :
    (a + b + c) * (d + e + f) ≈
      a * d + a * e + a * f + b * d + b * e + b * f +
        c * d + c * e + c * f := by
  refine Q'.eqv_trans _ ((a + b) * (d + e + f) + c * (d + e + f)) _
    (Q'.add_mul_eqv (a + b) c (d + e + f)) ?_
  have hc : c * (d + e + f) ≈ c * d + c * e + c * f := by
    refine Q'.eqv_trans _ (c * (d + e) + c * f) _
      (Q'.mul_add_eqv c (d + e) f) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv c d e)
  refine Q'.eqv_trans _
    ((a * d + a * e + a * f + b * d + b * e + b * f) +
      (c * d + c * e + c * f)) _
    (Q'.add_eqv_congr' (mul_two_by_three a b d e f) hc) ?_
  ring_qeqv

private theorem move_common (c q m : Q') : c * (q * m) ≈ q * (c * m) := by
  refine Q'.eqv_trans _ ((c * q) * m) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv c q m)) ?_
  refine Q'.eqv_trans _ ((q * c) * m) _
    (Q'.mul_eqv_congr_right _ _ m (Q'.mul_comm_eqv c q)) ?_
  exact Q'.mul_assoc_eqv q c m

private theorem factor_two (q a b : Q') :
    q * a + q * b ≈ q * (a + b) := Q'.eqv_symm (Q'.mul_add_eqv q a b)

private theorem factor_three (q a b c : Q') :
    q * a + q * b + q * c ≈ q * (a + b + c) := by
  exact Q'.eqv_trans _ (q * (a + b) + q * c) _
    (Q'.add_eqv_congr_right _ _ _ (factor_two q a b))
    (factor_two q (a + b) c)

private theorem factor_four (q a b c d : Q') :
    q * a + q * b + q * c + q * d ≈ q * (a + b + c + d) := by
  exact Q'.eqv_trans _ (q * (a + b + c) + q * d) _
    (Q'.add_eqv_congr_right _ _ _ (factor_three q a b c))
    (factor_two q (a + b + c) d)

private theorem factor_five (q a b c d e : Q') :
    q * a + q * b + q * c + q * d + q * e ≈
      q * (a + b + c + d + e) := by
  exact Q'.eqv_trans _ (q * (a + b + c + d) + q * e) _
    (Q'.add_eqv_congr_right _ _ _ (factor_four q a b c d))
    (factor_two q (a + b + c + d) e)

private theorem factor_six (q a b c d e f : Q') :
    q * a + q * b + q * c + q * d + q * e + q * f ≈
      q * (a + b + c + d + e + f) := by
  exact Q'.eqv_trans _ (q * (a + b + c + d + e) + q * f) _
    (Q'.add_eqv_congr_right _ _ _ (factor_five q a b c d e))
    (factor_two q (a + b + c + d + e) f)

private def addSixL : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
    (.var 5)

private def addSixR : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.var 0) (.add (.var 1) (.var 3))) (.var 4)) (.var 2))
    (.var 5)

private theorem addSix_normal : RingNormaliser.normalize addSixL =
    RingNormaliser.normalize addSixR := by
  decide

private theorem add_six_reorder (a b c d e f : Q') :
    a + b + c + d + e + f ≈ a + (b + d) + e + c + f := by
  have h := RingNormaliser.poly_identity_of_normal_eq addSixL addSixR addSix_normal
    (fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f)
  simpa [RingNormaliser.eval, addSixL, addSixR] using h

private def addNineL : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2))
    (.var 3)) (.var 4)) (.var 5)) (.var 6)) (.var 7)) (.var 8)

private def addNineR : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.add
        (.add
          (.add (.var 0) (.add (.var 1) (.var 3)))
          (.var 4))
        (.add (.var 2) (.var 6)))
      (.add (.var 5) (.var 7)))
    (.var 8)

private theorem addNine_normal : RingNormaliser.normalize addNineL =
    RingNormaliser.normalize addNineR := by
  decide

private theorem add_nine_reorder (a b c d e f g h i : Q') :
    a + b + c + d + e + f + g + h + i ≈
      a + (b + d) + e + (c + g) + (f + h) + i := by
  have hn := RingNormaliser.poly_identity_of_normal_eq addNineL addNineR addNine_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
      | 5 => f | 6 => g | 7 => h | _ => i)
  simpa [RingNormaliser.eval, addNineL, addNineR] using hn

private def addNinePartitionR : RingNormaliser.PolyExpr :=
  .add
    (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.var 4)) (.var 6))
    (.add (.add (.var 5) (.var 7)) (.var 8))

private theorem addNine_partition_normal : RingNormaliser.normalize addNineL =
    RingNormaliser.normalize addNinePartitionR := by
  decide

private theorem add_nine_partition (a b c d e f g h i : Q') :
    a + b + c + d + e + f + g + h + i ≈
      (a + b + c + d + e + g) + (f + h + i) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq addNineL addNinePartitionR
    addNine_partition_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
      | 5 => f | 6 => g | 7 => h | _ => i)
  simpa [RingNormaliser.eval, addNineL, addNinePartitionR] using hn

private def zeroAddFourL : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.const 0) (.var 0)) (.var 1)) (.var 2)) (.var 3)

private def zeroAddFourPairR : RingNormaliser.PolyExpr :=
  .add (.add (.var 1) (.var 2)) (.add (.var 0) (.var 3))

private def zeroAddFourMiddleR : RingNormaliser.PolyExpr :=
  .add (.add (.var 2) (.add (.var 1) (.var 3))) (.var 0)

private def zeroAddFourLastR : RingNormaliser.PolyExpr :=
  .add (.add (.add (.var 2) (.var 3)) (.var 1)) (.var 0)

private theorem zeroAddFour_pair_normal : RingNormaliser.normalize zeroAddFourL =
    RingNormaliser.normalize zeroAddFourPairR := by
  decide

private theorem zeroAddFour_middle_normal : RingNormaliser.normalize zeroAddFourL =
    RingNormaliser.normalize zeroAddFourMiddleR := by
  decide

private theorem zeroAddFour_last_normal : RingNormaliser.normalize zeroAddFourL =
    RingNormaliser.normalize zeroAddFourLastR := by
  decide

private theorem zero_add_four_pair (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ (b + c) + (a + d) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFourL zeroAddFourPairR
    zeroAddFour_pair_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, zeroAddFourL, zeroAddFourPairR] using hn

private theorem zero_add_four_middle (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ c + (b + d) + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFourL zeroAddFourMiddleR
    zeroAddFour_middle_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, zeroAddFourL, zeroAddFourMiddleR] using hn

private theorem zero_add_four_last (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ c + d + b + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFourL zeroAddFourLastR
    zeroAddFour_last_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, zeroAddFourL, zeroAddFourLastR] using hn

/-! ## 1. Exact range-four autoconvolutions -/

private theorem acN_four_three (w : Q') :
    acN w 4 3 ≈ (12 : Q') * qpow w 11 + (8 : Q') * qpow w 15 := by
  have h03 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 3
  have h12 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 2
  have h21 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 1
  have h30 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 0
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero, Nat.sub_self]
  refine Q'.eqv_trans _
    ((0 : Q') + ((4 : Q') * qpow w 15) + ((6 : Q') * qpow w 11) +
      ((6 : Q') * qpow w 11) + ((4 : Q') * qpow w 15)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h03))
          (by simpa only [c4] using h12))
        (by simpa only [c4] using h21))
      (by simpa only [c4] using h30)
  · have h11 :
        (6 : Q') * qpow w 11 + (6 : Q') * qpow w 11 ≈
          (12 : Q') * qpow w 11 := by
      refine Q'.eqv_trans _ (((6 : Q') + 6) * qpow w 11) _
        (Q'.eqv_symm (Q'.add_mul_eqv 6 6 (qpow w 11))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h15 :
        (4 : Q') * qpow w 15 + (4 : Q') * qpow w 15 ≈
          (8 : Q') * qpow w 15 := by
      refine Q'.eqv_trans _ (((4 : Q') + 4) * qpow w 15) _
        (Q'.eqv_symm (Q'.add_mul_eqv 4 4 (qpow w 15))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      (((6 : Q') * qpow w 11 + (6 : Q') * qpow w 11) +
        ((4 : Q') * qpow w 15 + (4 : Q') * qpow w 15)) _
      (zero_add_four_pair _ _ _ _) ?_
    exact Q'.add_eqv_congr' h11 h15

private theorem acN_four_four (w : Q') :
    acN w 4 4 ≈
      (9 : Q') * qpow w 16 + (16 : Q') * qpow w 18 +
        (5 : Q') * qpow w 24 := by
  have h04 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 4
  have h13 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 3
  have h22 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 2
  have h31 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 1
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((5 : Q') * qpow w 24) + ((8 : Q') * qpow w 18) +
      ((9 : Q') * qpow w 16) + ((8 : Q') * qpow w 18)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h04))
          (by simpa only [c4] using h13))
        (by simpa only [c4] using h22))
      (by simpa only [c4] using h31)
  · have h18 :
        (8 : Q') * qpow w 18 + (8 : Q') * qpow w 18 ≈
          (16 : Q') * qpow w 18 := by
      refine Q'.eqv_trans _ (((8 : Q') + 8) * qpow w 18) _
        (Q'.eqv_symm (Q'.add_mul_eqv 8 8 (qpow w 18))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((9 : Q') * qpow w 16 +
        ((8 : Q') * qpow w 18 + (8 : Q') * qpow w 18) +
        (5 : Q') * qpow w 24) _ (zero_add_four_middle _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left ((9 : Q') * qpow w 16) _ _ h18)
      (Q'.eqv_refl _)

private theorem acN_four_five (w : Q') :
    acN w 4 5 ≈
      (24 : Q') * qpow w 23 + (10 : Q') * qpow w 27 +
        (6 : Q') * qpow w 35 := by
  have h05 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 5
  have h14 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 4
  have h23 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 3
  have h32 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 2
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((6 : Q') * qpow w 35) + ((10 : Q') * qpow w 27) +
      ((12 : Q') * qpow w 23) + ((12 : Q') * qpow w 23)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h05))
          (by simpa only [c4] using h14))
        (by simpa only [c4] using h23))
      (by simpa only [c4] using h32)
  · have h23 :
        (12 : Q') * qpow w 23 + (12 : Q') * qpow w 23 ≈
          (24 : Q') * qpow w 23 := by
      refine Q'.eqv_trans _ (((12 : Q') + 12) * qpow w 23) _
        (Q'.eqv_symm (Q'.add_mul_eqv 12 12 (qpow w 23))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      (((12 : Q') * qpow w 23 + (12 : Q') * qpow w 23) +
        (10 : Q') * qpow w 27 + (6 : Q') * qpow w 35) _
      (zero_add_four_last _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_right _ _ ((10 : Q') * qpow w 27) h23)
      (Q'.eqv_refl _)

/-! ## 2. Derived off-diagonal and diagonal products -/

/-- Exact mode-three off-diagonal product. -/
theorem modeThreeA_formula (w : Q') :
    acN w 4 3 * acN w 4 5 ≈
      (288 : Q') * qpow w 34 + (312 : Q') * qpow w 38 +
        (80 : Q') * qpow w 42 + (72 : Q') * qpow w 46 +
          (48 : Q') * qpow w 50 := by
  refine Q'.eqv_trans _
    (((12 : Q') * qpow w 11 + (8 : Q') * qpow w 15) *
      ((24 : Q') * qpow w 23 + (10 : Q') * qpow w 27 +
        (6 : Q') * qpow w 35)) _
    (mul_eqv_congr₂ (acN_four_three w) (acN_four_five w)) ?_
  have h34 := Q'.eqv_symm (qpow_add w 11 23)
  have h38a := Q'.eqv_symm (qpow_add w 11 27)
  have h46 := Q'.eqv_symm (qpow_add w 11 35)
  have h38b := Q'.eqv_symm (qpow_add w 15 23)
  have h42 := Q'.eqv_symm (qpow_add w 15 27)
  have h50 := Q'.eqv_symm (qpow_add w 15 35)
  refine Q'.eqv_trans _
    (((12 : Q') * 24) * (qpow w 11 * qpow w 23) +
      ((12 : Q') * 10) * (qpow w 11 * qpow w 27) +
      ((12 : Q') * 6) * (qpow w 11 * qpow w 35) +
      ((8 : Q') * 24) * (qpow w 15 * qpow w 23) +
      ((8 : Q') * 10) * (qpow w 15 * qpow w 27) +
      ((8 : Q') * 6) * (qpow w 15 * qpow w 35)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (((12 : Q') * qpow w 11) * ((24 : Q') * qpow w 23) +
        ((12 : Q') * qpow w 11) * ((10 : Q') * qpow w 27) +
        ((12 : Q') * qpow w 11) * ((6 : Q') * qpow w 35) +
        ((8 : Q') * qpow w 15) * ((24 : Q') * qpow w 23) +
        ((8 : Q') * qpow w 15) * ((10 : Q') * qpow w 27) +
        ((8 : Q') * qpow w 15) * ((6 : Q') * qpow w 35)) _
      (mul_two_by_three _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (mul_swap4 12 (qpow w 11) 24 (qpow w 23))
              (mul_swap4 12 (qpow w 11) 10 (qpow w 27)))
            (mul_swap4 12 (qpow w 11) 6 (qpow w 35)))
          (mul_swap4 8 (qpow w 15) 24 (qpow w 23)))
        (mul_swap4 8 (qpow w 15) 10 (qpow w 27)))
      (mul_swap4 8 (qpow w 15) 6 (qpow w 35))
  refine Q'.eqv_trans _
    ((288 : Q') * qpow w 34 + (120 : Q') * qpow w 38 +
      (72 : Q') * qpow w 46 + (192 : Q') * qpow w 38 +
      (80 : Q') * qpow w 42 + (48 : Q') * qpow w 50) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (mul_eqv_congr₂ (by decide) h34)
              (mul_eqv_congr₂ (by decide) h38a))
            (mul_eqv_congr₂ (by decide) h46))
          (mul_eqv_congr₂ (by decide) h38b))
        (mul_eqv_congr₂ (by decide) h42))
      (mul_eqv_congr₂ (by decide) h50)
  · have h38 :
        (120 : Q') * qpow w 38 + (192 : Q') * qpow w 38 ≈
          (312 : Q') * qpow w 38 := by
      refine Q'.eqv_trans _ (((120 : Q') + 192) * qpow w 38) _
        (Q'.eqv_symm (Q'.add_mul_eqv 120 192 (qpow w 38))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((288 : Q') * qpow w 34 +
        ((120 : Q') * qpow w 38 + (192 : Q') * qpow w 38) +
        (80 : Q') * qpow w 42 + (72 : Q') * qpow w 46 +
        (48 : Q') * qpow w 50) _
      (add_six_reorder _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left ((288 : Q') * qpow w 34) _ _ h38)
          (Q'.eqv_refl _))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)

/-- Exact mode-three diagonal square. -/
theorem modeThreeM_formula (w : Q') :
    acN w 4 4 * acN w 4 4 ≈
      (81 : Q') * qpow w 32 + (288 : Q') * qpow w 34 +
        (256 : Q') * qpow w 36 + (90 : Q') * qpow w 40 +
          (160 : Q') * qpow w 42 + (25 : Q') * qpow w 48 := by
  refine Q'.eqv_trans _
    (((9 : Q') * qpow w 16 + (16 : Q') * qpow w 18 +
        (5 : Q') * qpow w 24) *
      ((9 : Q') * qpow w 16 + (16 : Q') * qpow w 18 +
        (5 : Q') * qpow w 24)) _
    (mul_eqv_congr₂ (acN_four_four w) (acN_four_four w)) ?_
  have h32 := Q'.eqv_symm (qpow_add w 16 16)
  have h34a := Q'.eqv_symm (qpow_add w 16 18)
  have h40a := Q'.eqv_symm (qpow_add w 16 24)
  have h34b := Q'.eqv_symm (qpow_add w 18 16)
  have h36 := Q'.eqv_symm (qpow_add w 18 18)
  have h42a := Q'.eqv_symm (qpow_add w 18 24)
  have h40b := Q'.eqv_symm (qpow_add w 24 16)
  have h42b := Q'.eqv_symm (qpow_add w 24 18)
  have h48 := Q'.eqv_symm (qpow_add w 24 24)
  refine Q'.eqv_trans _
    (((9 : Q') * 9) * (qpow w 16 * qpow w 16) +
      ((9 : Q') * 16) * (qpow w 16 * qpow w 18) +
      ((9 : Q') * 5) * (qpow w 16 * qpow w 24) +
      ((16 : Q') * 9) * (qpow w 18 * qpow w 16) +
      ((16 : Q') * 16) * (qpow w 18 * qpow w 18) +
      ((16 : Q') * 5) * (qpow w 18 * qpow w 24) +
      ((5 : Q') * 9) * (qpow w 24 * qpow w 16) +
      ((5 : Q') * 16) * (qpow w 24 * qpow w 18) +
      ((5 : Q') * 5) * (qpow w 24 * qpow w 24)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (((9 : Q') * qpow w 16) * ((9 : Q') * qpow w 16) +
        ((9 : Q') * qpow w 16) * ((16 : Q') * qpow w 18) +
        ((9 : Q') * qpow w 16) * ((5 : Q') * qpow w 24) +
        ((16 : Q') * qpow w 18) * ((9 : Q') * qpow w 16) +
        ((16 : Q') * qpow w 18) * ((16 : Q') * qpow w 18) +
        ((16 : Q') * qpow w 18) * ((5 : Q') * qpow w 24) +
        ((5 : Q') * qpow w 24) * ((9 : Q') * qpow w 16) +
        ((5 : Q') * qpow w 24) * ((16 : Q') * qpow w 18) +
        ((5 : Q') * qpow w 24) * ((5 : Q') * qpow w 24)) _
      (mul_three_by_three _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (mul_swap4 9 (qpow w 16) 9 (qpow w 16))
                    (mul_swap4 9 (qpow w 16) 16 (qpow w 18)))
                  (mul_swap4 9 (qpow w 16) 5 (qpow w 24)))
                (mul_swap4 16 (qpow w 18) 9 (qpow w 16)))
              (mul_swap4 16 (qpow w 18) 16 (qpow w 18)))
            (mul_swap4 16 (qpow w 18) 5 (qpow w 24)))
          (mul_swap4 5 (qpow w 24) 9 (qpow w 16)))
        (mul_swap4 5 (qpow w 24) 16 (qpow w 18)))
      (mul_swap4 5 (qpow w 24) 5 (qpow w 24))
  refine Q'.eqv_trans _
    ((81 : Q') * qpow w 32 + (144 : Q') * qpow w 34 +
      (45 : Q') * qpow w 40 + (144 : Q') * qpow w 34 +
      (256 : Q') * qpow w 36 + (80 : Q') * qpow w 42 +
      (45 : Q') * qpow w 40 + (80 : Q') * qpow w 42 +
      (25 : Q') * qpow w 48) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (mul_eqv_congr₂ (by decide) h32)
                    (mul_eqv_congr₂ (by decide) h34a))
                  (mul_eqv_congr₂ (by decide) h40a))
                (mul_eqv_congr₂ (by decide) h34b))
              (mul_eqv_congr₂ (by decide) h36))
            (mul_eqv_congr₂ (by decide) h42a))
          (mul_eqv_congr₂ (by decide) h40b))
        (mul_eqv_congr₂ (by decide) h42b))
      (mul_eqv_congr₂ (by decide) h48)
  · have h34 :
        (144 : Q') * qpow w 34 + (144 : Q') * qpow w 34 ≈
          (288 : Q') * qpow w 34 := by
      refine Q'.eqv_trans _ (((144 : Q') + 144) * qpow w 34) _
        (Q'.eqv_symm (Q'.add_mul_eqv 144 144 (qpow w 34))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h40 :
        (45 : Q') * qpow w 40 + (45 : Q') * qpow w 40 ≈
          (90 : Q') * qpow w 40 := by
      refine Q'.eqv_trans _ (((45 : Q') + 45) * qpow w 40) _
        (Q'.eqv_symm (Q'.add_mul_eqv 45 45 (qpow w 40))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h42 :
        (80 : Q') * qpow w 42 + (80 : Q') * qpow w 42 ≈
          (160 : Q') * qpow w 42 := by
      refine Q'.eqv_trans _ (((80 : Q') + 80) * qpow w 42) _
        (Q'.eqv_symm (Q'.add_mul_eqv 80 80 (qpow w 42))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((81 : Q') * qpow w 32 +
        ((144 : Q') * qpow w 34 + (144 : Q') * qpow w 34) +
        (256 : Q') * qpow w 36 +
        ((45 : Q') * qpow w 40 + (45 : Q') * qpow w 40) +
        ((80 : Q') * qpow w 42 + (80 : Q') * qpow w 42) +
        (25 : Q') * qpow w 48) _
      (add_nine_reorder _ _ _ _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left ((81 : Q') * qpow w 32) _ _ h34)
            (Q'.eqv_refl _))
          h40)
        h42)
      (Q'.eqv_refl _)

/-! ## 3. Reflective endpoint factorization -/

private def xE : RingNormaliser.PolyExpr := .var 0
private def xPowE (n : Nat) : RingNormaliser.PolyExpr := .pow xE n

private def factorLHS : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 458500)
      (.add
        (.add
          (.add
            (.add
              (.add (.const 81) (.mul (.const 288) xE))
              (.mul (.const 256) (xPowE 2)))
            (.mul (.const 90) (xPowE 4)))
          (.mul (.const 160) (xPowE 5)))
        (.mul (.const 25) (xPowE 8))))
    (.neg (.mul (.const 1009899)
      (.add
        (.add
          (.add
            (.add (.mul (.const 288) xE)
              (.mul (.const 312) (xPowE 3)))
            (.mul (.const 80) (xPowE 5)))
          (.mul (.const 72) (xPowE 7)))
        (.mul (.const 48) (xPowE 9)))))

private def factorRHS : RingNormaliser.PolyExpr :=
  .mul (.const 4)
    (.mul (.add (.const 1) (.neg (.mul (.const 4) xE)))
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add
                    (.add
                      (.mul (.const 3029697) (xPowE 8))
                      (.mul (.const 41018) (xPowE 7)))
                    (.mul (.const 4554800) (xPowE 6)))
                  (.mul (.const 1138700) (xPowE 5)))
                (.mul (.const 749170) (xPowE 4)))
              (.neg (.mul (.const 2391770) (xPowE 3))))
            (.mul (.const 19095088) (xPowE 2)))
          (.neg (.mul (.const 2562228) xE)))
        (.const 9284625)))

private theorem factor_normal : RingNormaliser.normalize factorLHS =
    RingNormaliser.normalize factorRHS := by
  decide

private theorem modeThree_factorization (x : Q') :
    (458500 : Q') *
        ((81 : Q') + 288 * x + 256 * RingNormaliser.qpow x 2 +
          90 * RingNormaliser.qpow x 4 + 160 * RingNormaliser.qpow x 5 +
          25 * RingNormaliser.qpow x 8) +
      -((1009899 : Q') *
        ((288 : Q') * x + 312 * RingNormaliser.qpow x 3 +
          80 * RingNormaliser.qpow x 5 + 72 * RingNormaliser.qpow x 7 +
          48 * RingNormaliser.qpow x 9)) ≈
      (4 : Q') * (((1 : Q') + -(4 * x)) *
        ((3029697 : Q') * RingNormaliser.qpow x 8 +
          41018 * RingNormaliser.qpow x 7 +
          4554800 * RingNormaliser.qpow x 6 +
          1138700 * RingNormaliser.qpow x 5 +
          749170 * RingNormaliser.qpow x 4 +
          -(2391770 * RingNormaliser.qpow x 3) +
          19095088 * RingNormaliser.qpow x 2 + -(2562228 * x) + 9284625)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq factorLHS factorRHS factor_normal
    (fun _ => x)
  simpa [RingNormaliser.eval, factorLHS, factorRHS, xE, xPowE] using h

/-! ## 4. Powers of `x = w²` and common-factor extraction -/

private theorem rpow_nonneg (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ n, (0 : Q') ≤ RingNormaliser.qpow x n
  | 0 => by
      change (0 : Q') ≤ 1
      decide
  | n + 1 => Q'.mul_nonneg _ _ (rpow_nonneg x hx n) hx

private theorem rpow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n, RingNormaliser.qpow x n ≤ RingNormaliser.qpow y n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hy : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
      exact Q'.mul_le_mul_of_nonneg (rpow_mono hx hxy n) hxy
        (rpow_nonneg y hy n) hx

private theorem rpow_one (x : Q') : RingNormaliser.qpow x 1 ≈ x := by
  change (1 : Q') * x ≈ x
  exact Q'.one_mul_eqv x

private theorem qpow_even_as_xpow (w : Q') :
    ∀ n, qpow w (2 * n) ≈ RingNormaliser.qpow (qpow w 2) n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      change qpow w (2 * n + 2) ≈
        RingNormaliser.qpow (qpow w 2) n * qpow w 2
      exact Q'.eqv_trans _ _ _ (qpow_add w (2 * n) 2)
        (mul_eqv_congr₂ (qpow_even_as_xpow w n) (Q'.eqv_refl _))

private theorem qpow_from_thirtyTwo_as_xpow (w : Q') (n : Nat) :
    qpow w (32 + 2 * n) ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) n := by
  exact Q'.eqv_trans _ _ _ (qpow_add w 32 (2 * n))
    (Q'.mul_eqv_congr_left (qpow w 32) _ _ (qpow_even_as_xpow w n))

private theorem modeThreeA_factored (w : Q') :
    acN w 4 3 * acN w 4 5 ≈
      qpow w 32 *
        ((288 : Q') * qpow w 2 +
          312 * RingNormaliser.qpow (qpow w 2) 3 +
          80 * RingNormaliser.qpow (qpow w 2) 5 +
          72 * RingNormaliser.qpow (qpow w 2) 7 +
          48 * RingNormaliser.qpow (qpow w 2) 9) := by
  refine Q'.eqv_trans _ _ _ (modeThreeA_formula w) ?_
  have h34a := qpow_from_thirtyTwo_as_xpow w 1
  have h34 : qpow w 34 ≈ qpow w 32 * qpow w 2 := by
    exact Q'.eqv_trans _ _ _ (by simpa only using h34a)
      (Q'.mul_eqv_congr_left (qpow w 32) _ _ (rpow_one (qpow w 2)))
  have h38 : qpow w 38 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 3 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 3
  have h42 : qpow w 42 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 5 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 5
  have h46 : qpow w 46 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 7 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 7
  have h50 : qpow w 50 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 9 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 9
  refine Q'.eqv_trans _
    ((288 : Q') * (qpow w 32 * qpow w 2) +
      (312 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 3) +
      (80 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 5) +
      (72 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 7) +
      (48 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 9)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left 288 _ _ h34)
            (Q'.mul_eqv_congr_left 312 _ _ h38))
          (Q'.mul_eqv_congr_left 80 _ _ h42))
        (Q'.mul_eqv_congr_left 72 _ _ h46))
      (Q'.mul_eqv_congr_left 48 _ _ h50)
  · refine Q'.eqv_trans _
      (qpow w 32 * ((288 : Q') * qpow w 2) +
        qpow w 32 * (312 * RingNormaliser.qpow (qpow w 2) 3) +
        qpow w 32 * (80 * RingNormaliser.qpow (qpow w 2) 5) +
        qpow w 32 * (72 * RingNormaliser.qpow (qpow w 2) 7) +
        qpow w 32 * (48 * RingNormaliser.qpow (qpow w 2) 9)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (move_common 288 (qpow w 32) (qpow w 2))
              (move_common 312 (qpow w 32)
                (RingNormaliser.qpow (qpow w 2) 3)))
            (move_common 80 (qpow w 32)
              (RingNormaliser.qpow (qpow w 2) 5)))
          (move_common 72 (qpow w 32)
            (RingNormaliser.qpow (qpow w 2) 7)))
        (move_common 48 (qpow w 32)
          (RingNormaliser.qpow (qpow w 2) 9))
    · exact factor_five (qpow w 32)
        ((288 : Q') * qpow w 2)
        (312 * RingNormaliser.qpow (qpow w 2) 3)
        (80 * RingNormaliser.qpow (qpow w 2) 5)
        (72 * RingNormaliser.qpow (qpow w 2) 7)
        (48 * RingNormaliser.qpow (qpow w 2) 9)

private theorem modeThreeM_factored (w : Q') :
    acN w 4 4 * acN w 4 4 ≈
      qpow w 32 *
        ((81 : Q') + 288 * qpow w 2 +
          256 * RingNormaliser.qpow (qpow w 2) 2 +
          90 * RingNormaliser.qpow (qpow w 2) 4 +
          160 * RingNormaliser.qpow (qpow w 2) 5 +
          25 * RingNormaliser.qpow (qpow w 2) 8) := by
  refine Q'.eqv_trans _ _ _ (modeThreeM_formula w) ?_
  have h34a := qpow_from_thirtyTwo_as_xpow w 1
  have h34 : qpow w 34 ≈ qpow w 32 * qpow w 2 := by
    exact Q'.eqv_trans _ _ _ (by simpa only using h34a)
      (Q'.mul_eqv_congr_left (qpow w 32) _ _ (rpow_one (qpow w 2)))
  have h36 : qpow w 36 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 2 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 2
  have h40 : qpow w 40 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 4 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 4
  have h42 : qpow w 42 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 5 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 5
  have h48 : qpow w 48 ≈
      qpow w 32 * RingNormaliser.qpow (qpow w 2) 8 := by
    simpa only using qpow_from_thirtyTwo_as_xpow w 8
  refine Q'.eqv_trans _
    ((81 : Q') * qpow w 32 + (288 : Q') * (qpow w 32 * qpow w 2) +
      (256 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 2) +
      (90 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 4) +
      (160 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 5) +
      (25 : Q') * (qpow w 32 * RingNormaliser.qpow (qpow w 2) 8)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left ((81 : Q') * qpow w 32) _ _
              (Q'.mul_eqv_congr_left 288 _ _ h34))
            (Q'.mul_eqv_congr_left 256 _ _ h36))
          (Q'.mul_eqv_congr_left 90 _ _ h40))
        (Q'.mul_eqv_congr_left 160 _ _ h42))
      (Q'.mul_eqv_congr_left 25 _ _ h48)
  · refine Q'.eqv_trans _
      (qpow w 32 * (81 : Q') + qpow w 32 * (288 * qpow w 2) +
        qpow w 32 * (256 * RingNormaliser.qpow (qpow w 2) 2) +
        qpow w 32 * (90 * RingNormaliser.qpow (qpow w 2) 4) +
        qpow w 32 * (160 * RingNormaliser.qpow (qpow w 2) 5) +
        qpow w 32 * (25 * RingNormaliser.qpow (qpow w 2) 8)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.mul_comm_eqv 81 (qpow w 32))
                (move_common 288 (qpow w 32) (qpow w 2)))
              (move_common 256 (qpow w 32)
                (RingNormaliser.qpow (qpow w 2) 2)))
            (move_common 90 (qpow w 32)
              (RingNormaliser.qpow (qpow w 2) 4)))
          (move_common 160 (qpow w 32)
            (RingNormaliser.qpow (qpow w 2) 5)))
        (move_common 25 (qpow w 32)
          (RingNormaliser.qpow (qpow w 2) 8))
    · exact factor_six (qpow w 32) 81
        (288 * qpow w 2)
        (256 * RingNormaliser.qpow (qpow w 2) 2)
        (90 * RingNormaliser.qpow (qpow w 2) 4)
        (160 * RingNormaliser.qpow (qpow w 2) 5)
        (25 * RingNormaliser.qpow (qpow w 2) 8)

/-! ## 5. Positivity of the signed degree-eight factor -/

private theorem modeThree_poly_nonneg {x : Q'}
    (hx0 : (0 : Q') ≤ x) (hxq : x ≤ Q'.mkPos 1 4 (by decide)) :
    (0 : Q') ≤
      (3029697 : Q') * RingNormaliser.qpow x 8 +
        41018 * RingNormaliser.qpow x 7 +
        4554800 * RingNormaliser.qpow x 6 +
        1138700 * RingNormaliser.qpow x 5 +
        749170 * RingNormaliser.qpow x 4 +
        -(2391770 * RingNormaliser.qpow x 3) +
        19095088 * RingNormaliser.qpow x 2 + -(2562228 * x) + 9284625 := by
  let q4 : Q' := Q'.mkPos 1 4 (by decide)
  let q64 : Q' := Q'.mkPos 1 64 (by decide)
  have hq40 : (0 : Q') ≤ q4 := by decide
  have hx3q : RingNormaliser.qpow x 3 ≤ q64 := by
    refine Q'.le_trans' _ (RingNormaliser.qpow q4 3) _
      (rpow_mono hx0 hxq 3) ?_
    exact Q'.le_of_eqv (by decide)
  have hc3 : (2391770 : Q') * RingNormaliser.qpow x 3 ≤
      (2391770 : Q') * q64 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hx3q (by decide)
  have hc1 : (2562228 : Q') * x ≤ (2562228 : Q') * q4 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hxq (by decide)
  have hcostStep :
      (2391770 : Q') * RingNormaliser.qpow x 3 + (2562228 : Q') * x ≤
        (2391770 : Q') * q64 + (2562228 : Q') * q4 :=
    Q'.le_trans' _
      ((2391770 : Q') * q64 + (2562228 : Q') * x) _
      (Q'.add_le_add_right _ _ _ hc3)
      (Q'.add_le_add_left _ _ _ hc1)
  have hcost :
      (2391770 : Q') * RingNormaliser.qpow x 3 + (2562228 : Q') * x ≤
        (9284625 : Q') :=
    Q'.le_trans' _ _ _ hcostStep (by decide)
  have hbase : (0 : Q') ≤
      (9284625 : Q') +
        -((2391770 : Q') * RingNormaliser.qpow x 3 + (2562228 : Q') * x) :=
    Q'.sub_nonneg_of_le hcost
  have hnegEq :
      -(2391770 * RingNormaliser.qpow x 3) + -(2562228 * x) + 9284625 ≈
        (9284625 : Q') +
          -((2391770 : Q') * RingNormaliser.qpow x 3 + (2562228 : Q') * x) := by
    ring_qeqv
  have hneg : (0 : Q') ≤
      -(2391770 * RingNormaliser.qpow x 3) + -(2562228 * x) + 9284625 :=
    Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv (Q'.eqv_symm hnegEq))
  have hpos : (0 : Q') ≤
      (3029697 : Q') * RingNormaliser.qpow x 8 +
        41018 * RingNormaliser.qpow x 7 +
        4554800 * RingNormaliser.qpow x 6 +
        1138700 * RingNormaliser.qpow x 5 +
        749170 * RingNormaliser.qpow x 4 +
        19095088 * RingNormaliser.qpow x 2 := by
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.zero_le_add _ _
              (Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 8))
              (Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 7)))
            (Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 6)))
          (Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 5)))
        (Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 4)))
      (Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 2))
  have hsum := Q'.zero_le_add _ _ hpos hneg
  have hpolyEq :
      (3029697 : Q') * RingNormaliser.qpow x 8 +
          41018 * RingNormaliser.qpow x 7 +
          4554800 * RingNormaliser.qpow x 6 +
          1138700 * RingNormaliser.qpow x 5 +
          749170 * RingNormaliser.qpow x 4 +
          -(2391770 * RingNormaliser.qpow x 3) +
          19095088 * RingNormaliser.qpow x 2 + -(2562228 * x) + 9284625 ≈
        ((3029697 : Q') * RingNormaliser.qpow x 8 +
          41018 * RingNormaliser.qpow x 7 +
          4554800 * RingNormaliser.qpow x 6 +
          1138700 * RingNormaliser.qpow x 5 +
          749170 * RingNormaliser.qpow x 4 +
          19095088 * RingNormaliser.qpow x 2) +
        (-(2391770 * RingNormaliser.qpow x 3) + -(2562228 * x) + 9284625) := by
    exact add_nine_partition _ _ _ _ _ _ _ _ _
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hpolyEq))

/-! ## 6. Uniform scaled ratio and the cross-ratio member -/

private theorem modeThree_scaled_ratio {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (1009899 : Q') * (acN w 4 3 * acN w 4 5) ≤
      (458500 : Q') * (acN w 4 4 * acN w 4 4) := by
  let x := qpow w 2
  have hx0 : (0 : Q') ≤ x := qpow_nonneg w hw0 2
  have hxq : x ≤ Q'.mkPos 1 4 (by decide) := by
    refine Q'.le_trans' _ (qpow wH 2) _ (qpow_mono hw0 hwH 2) ?_
    exact Q'.le_of_eqv (by decide)
  have h4x : (4 : Q') * x ≤ 1 :=
    Q'.le_trans' _ ((4 : Q') * Q'.mkPos 1 4 (by decide)) _
      (Q'.mul_le_mul_of_nonneg_left _ _ 4 hxq (by decide))
      (Q'.le_of_eqv (by decide))
  have hlinear : (0 : Q') ≤ (1 : Q') + -(4 * x) :=
    Q'.sub_nonneg_of_le h4x
  have hpoly := modeThree_poly_nonneg hx0 hxq
  have hfactorNonneg : (0 : Q') ≤
      (4 : Q') * (((1 : Q') + -(4 * x)) *
        ((3029697 : Q') * RingNormaliser.qpow x 8 +
          41018 * RingNormaliser.qpow x 7 +
          4554800 * RingNormaliser.qpow x 6 +
          1138700 * RingNormaliser.qpow x 5 +
          749170 * RingNormaliser.qpow x 4 +
          -(2391770 * RingNormaliser.qpow x 3) +
          19095088 * RingNormaliser.qpow x 2 + -(2562228 * x) + 9284625)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hlinear hpoly)
  have hdiff : (0 : Q') ≤
      (458500 : Q') *
          ((81 : Q') + 288 * x + 256 * RingNormaliser.qpow x 2 +
            90 * RingNormaliser.qpow x 4 + 160 * RingNormaliser.qpow x 5 +
            25 * RingNormaliser.qpow x 8) +
        -((1009899 : Q') *
          ((288 : Q') * x + 312 * RingNormaliser.qpow x 3 +
            80 * RingNormaliser.qpow x 5 + 72 * RingNormaliser.qpow x 7 +
            48 * RingNormaliser.qpow x 9)) :=
    Q'.le_trans' _ _ _ hfactorNonneg
      (Q'.le_of_eqv (Q'.eqv_symm (modeThree_factorization x)))
  have hinner :
      (1009899 : Q') *
          ((288 : Q') * x + 312 * RingNormaliser.qpow x 3 +
            80 * RingNormaliser.qpow x 5 + 72 * RingNormaliser.qpow x 7 +
            48 * RingNormaliser.qpow x 9) ≤
        (458500 : Q') *
          ((81 : Q') + 288 * x + 256 * RingNormaliser.qpow x 2 +
            90 * RingNormaliser.qpow x 4 + 160 * RingNormaliser.qpow x 5 +
            25 * RingNormaliser.qpow x 8) :=
    Q'.le_of_sub_nonneg hdiff
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 32) hinner
    (qpow_nonneg w hw0 32)
  have hL : qpow w 32 *
      ((1009899 : Q') *
        ((288 : Q') * x + 312 * RingNormaliser.qpow x 3 +
          80 * RingNormaliser.qpow x 5 + 72 * RingNormaliser.qpow x 7 +
          48 * RingNormaliser.qpow x 9)) ≈
      (1009899 : Q') * (acN w 4 3 * acN w 4 5) := by
    exact Q'.eqv_trans _
      ((1009899 : Q') * (qpow w 32 *
        ((288 : Q') * x + 312 * RingNormaliser.qpow x 3 +
          80 * RingNormaliser.qpow x 5 + 72 * RingNormaliser.qpow x 7 +
          48 * RingNormaliser.qpow x 9))) _
        (Q'.eqv_symm (move_common 1009899 (qpow w 32)
          ((288 : Q') * x + 312 * RingNormaliser.qpow x 3 +
            80 * RingNormaliser.qpow x 5 + 72 * RingNormaliser.qpow x 7 +
            48 * RingNormaliser.qpow x 9)))
      (Q'.mul_eqv_congr_left 1009899 _ _ (Q'.eqv_symm (modeThreeA_factored w)))
  have hR : qpow w 32 *
      ((458500 : Q') *
        ((81 : Q') + 288 * x + 256 * RingNormaliser.qpow x 2 +
          90 * RingNormaliser.qpow x 4 + 160 * RingNormaliser.qpow x 5 +
          25 * RingNormaliser.qpow x 8)) ≈
      (458500 : Q') * (acN w 4 4 * acN w 4 4) := by
    exact Q'.eqv_trans _
      ((458500 : Q') * (qpow w 32 *
        ((81 : Q') + 288 * x + 256 * RingNormaliser.qpow x 2 +
          90 * RingNormaliser.qpow x 4 + 160 * RingNormaliser.qpow x 5 +
          25 * RingNormaliser.qpow x 8))) _
        (Q'.eqv_symm (move_common 458500 (qpow w 32)
          ((81 : Q') + 288 * x + 256 * RingNormaliser.qpow x 2 +
            90 * RingNormaliser.qpow x 4 + 160 * RingNormaliser.qpow x 5 +
            25 * RingNormaliser.qpow x 8)))
      (Q'.mul_eqv_congr_left 458500 _ _ (Q'.eqv_symm (modeThreeM_factored w)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hR))

private theorem modeThree_anchor_ratio :
    (1009899 : Q') * (acN wH 4 3 * acN wH 4 5) ≈
      (458500 : Q') * (acN wH 4 4 * acN wH 4 4) := by
  decide

/-- The complete `s = 3` member of `CrossRatioMonotone.cross`, uniformly on
the full exact-rational interval `[0,wH]`. -/
theorem cross_mode_three {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (acN w 4 3 * acN w 4 5) * (acN wH 4 4 * acN wH 4 4) ≤
      (acN wH 4 3 * acN wH 4 5) * (acN w 4 4 * acN w 4 4) := by
  let Aw := acN w 4 3 * acN w 4 5
  let Mw := acN w 4 4 * acN w 4 4
  let AH := acN wH 4 3 * acN wH 4 5
  let MH := acN wH 4 4 * acN wH 4 4
  have hMH : (0 : Q') ≤ MH := Q'.mul_nonneg _ _
    (acN_nonneg (by decide) 4 4) (acN_nonneg (by decide) 4 4)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ MH
    (modeThree_scaled_ratio hw0 hwH) hMH
  have hL : ((1009899 : Q') * Aw) * MH ≈
      (1009899 : Q') * (Aw * MH) := Q'.mul_assoc_eqv _ _ _
  have hR : ((458500 : Q') * Mw) * MH ≈
      (1009899 : Q') * (AH * Mw) := by
    refine Q'.eqv_trans _ ((458500 : Q') * (Mw * MH)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((458500 : Q') * (MH * Mw)) _
      (Q'.mul_eqv_congr_left 458500 _ _ (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ (((458500 : Q') * MH) * Mw) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ (((1009899 : Q') * AH) * Mw) _
      (Q'.mul_eqv_congr_right _ _ Mw (Q'.eqv_symm modeThree_anchor_ratio)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have h1009899 : (1009899 : Q') * (Aw * MH) ≤
      (1009899 : Q') * (AH * Mw) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hR))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos (by decide) h1009899

end YMGap.Continuum.CoreBModeThree

#print axioms YMGap.Continuum.CoreBModeThree.modeThreeA_formula
#print axioms YMGap.Continuum.CoreBModeThree.modeThreeM_formula
#print axioms YMGap.Continuum.CoreBModeThree.cross_mode_three
