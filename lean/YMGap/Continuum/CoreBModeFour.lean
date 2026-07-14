/-
# Core-B mode-four cross-ratio prefix

This file proves the `s = 4` member of `CrossRatioMonotone.cross` uniformly
for every exact rational coupling `0 ≤ w ≤ wH`.  All range-five
autoconvolutions and endpoint constants are derived from the library
definitions.  With `x = w²`, the endpoint-scaled polynomial difference is
certified reflectively as

  10302201251 M(x) - 21395529800 A(x) = 4 (1 - 4x) P(x),

where

  P(x) = 93605442875x¹² + 221407904x¹¹ + 55351976x¹⁰
       + 149782546594x⁹ + 121690535236x⁸ + 36356088544x⁷
       + 9089022136x⁶ - 183167366984x⁵ + 612120699604x⁴
       + 253850267776x³ + 63462566944x² + 39599460676x
       + 713277907344.

For `0 ≤ x ≤ 1/4`, the sole negative power satisfies `x⁵ ≤ 1`.
Its coefficient `183167366984` is below the constant term `713277907344`;
all other monomials are nonnegative.

Finite-prefix observation (not a general closure claim): for `s = 0,…,4`,
endpoint scaling forces the cross-difference to vanish at `x = 1/4`, and the
checked differences have a factor `1 - 4x`.  The remaining quotient has
case-dependent signed coefficients (already for modes three and four), so
these data do not exhibit a proved uniform positive-coefficient recurrence.
-/

import YMGap.Continuum.CoreBModeThree
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBModeFour

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

private theorem mul_eqv_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## Reflective algebraic layout helpers -/

private def add2E (a b : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add a b

private def add3E (a b c : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (add2E a b) c

private def add4E (a b c d : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (add3E a b c) d

private def add5E (a b c d e : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (add4E a b c d) e

private def add6E (a b c d e f : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add5E a b c d e) f

private def add7E (a b c d e f g : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add6E a b c d e f) g

private def add8E (a b c d e f g h : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add7E a b c d e f g) h

private def add9E (a b c d e f g h i : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add8E a b c d e f g h) i

private def add10E (a b c d e f g h i j : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add9E a b c d e f g h i) j

private def add11E (a b c d e f g h i j k : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add10E a b c d e f g h i j) k

private def add12E (a b c d e f g h i j k l : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add11E a b c d e f g h i j k) l

private def add13E (a b c d e f g h i j k l m : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add12E a b c d e f g h i j k l) m

private def mul33L : RingNormaliser.PolyExpr :=
  .mul (add3E (.var 0) (.var 1) (.var 2))
    (add3E (.var 3) (.var 4) (.var 5))

private def mul33R : RingNormaliser.PolyExpr :=
  add9E
    (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4))
    (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 3))
    (.mul (.var 1) (.var 4)) (.mul (.var 1) (.var 5))
    (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 4))
    (.mul (.var 2) (.var 5))

private theorem mul33_normal : RingNormaliser.normalize mul33L =
    RingNormaliser.normalize mul33R := by
  decide

private theorem mul_three_by_three (a b c d e f : Q') :
    (a + b + c) * (d + e + f) ≈
      a * d + a * e + a * f + b * d + b * e + b * f +
        c * d + c * e + c * f := by
  have hn := RingNormaliser.poly_identity_of_normal_eq mul33L mul33R mul33_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f)
  simpa [RingNormaliser.eval, mul33L, mul33R, add2E, add3E, add4E, add5E,
    add6E, add7E, add8E, add9E] using hn

private def mul34L : RingNormaliser.PolyExpr :=
  .mul (add3E (.var 0) (.var 1) (.var 2))
    (add4E (.var 3) (.var 4) (.var 5) (.var 6))

private def mul34R : RingNormaliser.PolyExpr :=
  add12E
    (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4))
    (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 6))
    (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 4))
    (.mul (.var 1) (.var 5)) (.mul (.var 1) (.var 6))
    (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 4))
    (.mul (.var 2) (.var 5)) (.mul (.var 2) (.var 6))

private theorem mul34_normal : RingNormaliser.normalize mul34L =
    RingNormaliser.normalize mul34R := by
  decide

private theorem mul_three_by_four (a b c d e f g : Q') :
    (a + b + c) * (d + e + f + g) ≈
      a * d + a * e + a * f + a * g +
        b * d + b * e + b * f + b * g +
        c * d + c * e + c * f + c * g := by
  have hn := RingNormaliser.poly_identity_of_normal_eq mul34L mul34R mul34_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g)
  simpa [RingNormaliser.eval, mul34L, mul34R, add2E, add3E, add4E, add5E,
    add6E, add7E, add8E, add9E, add10E, add11E, add12E] using hn

private def zeroAddFourL : RingNormaliser.PolyExpr :=
  add5E (.const 0) (.var 0) (.var 1) (.var 2) (.var 3)

private def zeroAddFourMiddleR : RingNormaliser.PolyExpr :=
  add3E (.var 2) (.add (.var 1) (.var 3)) (.var 0)

private def zeroAddFourLastR : RingNormaliser.PolyExpr :=
  add4E (.var 2) (.var 3) (.var 1) (.var 0)

private def zeroAddFourReverseR : RingNormaliser.PolyExpr :=
  add4E (.var 3) (.var 2) (.var 1) (.var 0)

private theorem zeroAddFour_middle_normal : RingNormaliser.normalize zeroAddFourL =
    RingNormaliser.normalize zeroAddFourMiddleR := by
  decide

private theorem zeroAddFour_last_normal : RingNormaliser.normalize zeroAddFourL =
    RingNormaliser.normalize zeroAddFourLastR := by
  decide

private theorem zeroAddFour_reverse_normal : RingNormaliser.normalize zeroAddFourL =
    RingNormaliser.normalize zeroAddFourReverseR := by
  decide

private theorem zero_add_four_middle (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ c + (b + d) + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFourL zeroAddFourMiddleR
    zeroAddFour_middle_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, zeroAddFourL, zeroAddFourMiddleR, add2E, add3E,
    add4E, add5E] using hn

private theorem zero_add_four_last (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ c + d + b + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFourL zeroAddFourLastR
    zeroAddFour_last_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, zeroAddFourL, zeroAddFourLastR, add2E, add3E,
    add4E, add5E] using hn

private theorem zero_add_four_reverse (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ d + c + b + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFourL zeroAddFourReverseR
    zeroAddFour_reverse_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, zeroAddFourL, zeroAddFourReverseR, add2E, add3E,
    add4E, add5E] using hn

private def zeroAddFiveL : RingNormaliser.PolyExpr :=
  add6E (.const 0) (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)

private def zeroAddFiveFourR : RingNormaliser.PolyExpr :=
  add3E (.var 2) (.add (.var 1) (.var 3)) (.add (.var 0) (.var 4))

private def zeroAddFiveFiveR : RingNormaliser.PolyExpr :=
  add3E (.add (.var 2) (.var 3)) (.add (.var 1) (.var 4)) (.var 0)

private def zeroAddFiveSixR : RingNormaliser.PolyExpr :=
  add4E (.var 3) (.add (.var 2) (.var 4)) (.var 1) (.var 0)

private theorem zeroAddFive_four_normal : RingNormaliser.normalize zeroAddFiveL =
    RingNormaliser.normalize zeroAddFiveFourR := by
  decide

private theorem zeroAddFive_five_normal : RingNormaliser.normalize zeroAddFiveL =
    RingNormaliser.normalize zeroAddFiveFiveR := by
  decide

private theorem zeroAddFive_six_normal : RingNormaliser.normalize zeroAddFiveL =
    RingNormaliser.normalize zeroAddFiveSixR := by
  decide

private theorem zero_add_five_four (a b c d e : Q') :
    (0 : Q') + a + b + c + d + e ≈ c + (b + d) + (a + e) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFiveL zeroAddFiveFourR
    zeroAddFive_four_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e)
  simpa [RingNormaliser.eval, zeroAddFiveL, zeroAddFiveFourR, add2E, add3E,
    add4E, add5E, add6E] using hn

private theorem zero_add_five_five (a b c d e : Q') :
    (0 : Q') + a + b + c + d + e ≈ (c + d) + (b + e) + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFiveL zeroAddFiveFiveR
    zeroAddFive_five_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e)
  simpa [RingNormaliser.eval, zeroAddFiveL, zeroAddFiveFiveR, add2E, add3E,
    add4E, add5E, add6E] using hn

private theorem zero_add_five_six (a b c d e : Q') :
    (0 : Q') + a + b + c + d + e ≈ d + (c + e) + b + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddFiveL zeroAddFiveSixR
    zeroAddFive_six_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e)
  simpa [RingNormaliser.eval, zeroAddFiveL, zeroAddFiveSixR, add2E, add3E,
    add4E, add5E, add6E] using hn

private def addNineL : RingNormaliser.PolyExpr :=
  add9E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
    (.var 7) (.var 8)

private def addNineGroupedR : RingNormaliser.PolyExpr :=
  add6E (.var 0) (.add (.var 1) (.var 3)) (.var 4)
    (.add (.var 2) (.var 6)) (.add (.var 5) (.var 7)) (.var 8)

private theorem addNine_grouped_normal : RingNormaliser.normalize addNineL =
    RingNormaliser.normalize addNineGroupedR := by
  decide

private theorem add_nine_grouped (a b c d e f g h i : Q') :
    a + b + c + d + e + f + g + h + i ≈
      a + (b + d) + e + (c + g) + (f + h) + i := by
  have hn := RingNormaliser.poly_identity_of_normal_eq addNineL addNineGroupedR
    addNine_grouped_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
      | 5 => f | 6 => g | 7 => h | _ => i)
  simpa [RingNormaliser.eval, addNineL, addNineGroupedR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E] using hn

private def addTwelveL : RingNormaliser.PolyExpr :=
  add12E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
    (.var 6) (.var 7) (.var 8) (.var 9) (.var 10) (.var 11)

private def addTwelveGroupedR : RingNormaliser.PolyExpr :=
  add9E (.var 0) (.add (.var 1) (.var 4)) (.var 5)
    (.add (.var 2) (.var 8)) (.add (.var 6) (.var 9)) (.var 10)
    (.var 3) (.var 7) (.var 11)

private theorem addTwelve_grouped_normal : RingNormaliser.normalize addTwelveL =
    RingNormaliser.normalize addTwelveGroupedR := by
  decide

private theorem add_twelve_grouped
    (a b c d e f g h i j k l : Q') :
    a + b + c + d + e + f + g + h + i + j + k + l ≈
      a + (b + e) + f + (c + i) + (g + j) + k + d + h + l := by
  have hn := RingNormaliser.poly_identity_of_normal_eq addTwelveL addTwelveGroupedR
    addTwelve_grouped_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f
      | 6 => g | 7 => h | 8 => i | 9 => j | 10 => k | _ => l)
  simpa [RingNormaliser.eval, addTwelveL, addTwelveGroupedR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E] using hn

private theorem move_common (c q m : Q') : c * (q * m) ≈ q * (c * m) := by
  refine Q'.eqv_trans _ ((c * q) * m) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv c q m)) ?_
  refine Q'.eqv_trans _ ((q * c) * m) _
    (Q'.mul_eqv_congr_right _ _ m (Q'.mul_comm_eqv c q)) ?_
  exact Q'.mul_assoc_eqv q c m

private def factorSixL : RingNormaliser.PolyExpr :=
  add6E (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))
    (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4))
    (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 6))

private def factorSixR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (add6E (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6))

private theorem factorSix_normal : RingNormaliser.normalize factorSixL =
    RingNormaliser.normalize factorSixR := by
  decide

private theorem factor_six (q a b c d e f : Q') :
    q * a + q * b + q * c + q * d + q * e + q * f ≈
      q * (a + b + c + d + e + f) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq factorSixL factorSixR factorSix_normal
    (fun n => match n with
      | 0 => q | 1 => a | 2 => b | 3 => c | 4 => d | 5 => e | _ => f)
  simpa [RingNormaliser.eval, factorSixL, factorSixR, add2E, add3E, add4E,
    add5E, add6E] using hn

private def factorNineL : RingNormaliser.PolyExpr :=
  add9E (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))
    (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4))
    (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 6))
    (.mul (.var 0) (.var 7)) (.mul (.var 0) (.var 8))
    (.mul (.var 0) (.var 9))

private def factorNineR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (add9E (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
    (.var 6) (.var 7) (.var 8) (.var 9))

private theorem factorNine_normal : RingNormaliser.normalize factorNineL =
    RingNormaliser.normalize factorNineR := by
  decide

private theorem factor_nine (q a b c d e f g h i : Q') :
    q * a + q * b + q * c + q * d + q * e + q * f + q * g + q * h + q * i ≈
      q * (a + b + c + d + e + f + g + h + i) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq factorNineL factorNineR factorNine_normal
    (fun n => match n with
      | 0 => q | 1 => a | 2 => b | 3 => c | 4 => d | 5 => e
      | 6 => f | 7 => g | 8 => h | _ => i)
  simpa [RingNormaliser.eval, factorNineL, factorNineR, add2E, add3E, add4E,
    add5E, add6E, add7E, add8E, add9E] using hn

/-! ## 1. Exact range-four autoconvolutions -/

private theorem acN_five_four (w : Q') :
    acN w 5 4 ≈
      (9 : Q') * qpow w 16 + (16 : Q') * qpow w 18 +
        (10 : Q') * qpow w 24 := by
  have h04 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 4
  have h13 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 3
  have h22 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 2
  have h31 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 1
  have h40 := LaplaceMarginDeep.coeffW_mul_ofNat w 4 0
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((5 : Q') * qpow w 24) + ((8 : Q') * qpow w 18) +
      ((9 : Q') * qpow w 16) + ((8 : Q') * qpow w 18) +
      ((5 : Q') * qpow w 24)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h04))
            (by simpa only [c4] using h13))
          (by simpa only [c4] using h22))
        (by simpa only [c4] using h31))
      (by simpa only [c4] using h40)
  · have h18 :
        (8 : Q') * qpow w 18 + (8 : Q') * qpow w 18 ≈
          (16 : Q') * qpow w 18 := by
      refine Q'.eqv_trans _ (((8 : Q') + 8) * qpow w 18) _
        (Q'.eqv_symm (Q'.add_mul_eqv 8 8 (qpow w 18))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h24 :
        (5 : Q') * qpow w 24 + (5 : Q') * qpow w 24 ≈
          (10 : Q') * qpow w 24 := by
      refine Q'.eqv_trans _ (((5 : Q') + 5) * qpow w 24) _
        (Q'.eqv_symm (Q'.add_mul_eqv 5 5 (qpow w 24))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((9 : Q') * qpow w 16 +
        ((8 : Q') * qpow w 18 + (8 : Q') * qpow w 18) +
        ((5 : Q') * qpow w 24 + (5 : Q') * qpow w 24)) _
      (zero_add_five_four _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left ((9 : Q') * qpow w 16) _ _ h18)
      h24

private theorem acN_five_five (w : Q') :
    acN w 5 5 ≈
      (24 : Q') * qpow w 23 + (20 : Q') * qpow w 27 +
        (6 : Q') * qpow w 35 := by
  have h05 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 5
  have h14 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 4
  have h23 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 3
  have h32 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 2
  have h41 := LaplaceMarginDeep.coeffW_mul_ofNat w 4 1
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((6 : Q') * qpow w 35) + ((10 : Q') * qpow w 27) +
      ((12 : Q') * qpow w 23) + ((12 : Q') * qpow w 23) +
      ((10 : Q') * qpow w 27)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h05))
            (by simpa only [c4] using h14))
          (by simpa only [c4] using h23))
        (by simpa only [c4] using h32))
      (by simpa only [c4] using h41)
  · have h23 :
        (12 : Q') * qpow w 23 + (12 : Q') * qpow w 23 ≈
          (24 : Q') * qpow w 23 := by
      refine Q'.eqv_trans _ (((12 : Q') + 12) * qpow w 23) _
        (Q'.eqv_symm (Q'.add_mul_eqv 12 12 (qpow w 23))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h27 :
        (10 : Q') * qpow w 27 + (10 : Q') * qpow w 27 ≈
          (20 : Q') * qpow w 27 := by
      refine Q'.eqv_trans _ (((10 : Q') + 10) * qpow w 27) _
        (Q'.eqv_symm (Q'.add_mul_eqv 10 10 (qpow w 27))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      (((12 : Q') * qpow w 23 + (12 : Q') * qpow w 23) +
        ((10 : Q') * qpow w 27 + (10 : Q') * qpow w 27) +
        (6 : Q') * qpow w 35) _
      (zero_add_five_five _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' h23 h27)
      (Q'.eqv_refl _)

private theorem acN_five_six (w : Q') :
    acN w 5 6 ≈
      (16 : Q') * qpow w 30 + (30 : Q') * qpow w 32 +
        (12 : Q') * qpow w 38 + (7 : Q') * qpow w 48 := by
  have h06 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 6
  have h15 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 5
  have h24 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 4
  have h33 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 3
  have h42 := LaplaceMarginDeep.coeffW_mul_ofNat w 4 2
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((7 : Q') * qpow w 48) + ((12 : Q') * qpow w 38) +
      ((15 : Q') * qpow w 32) + ((16 : Q') * qpow w 30) +
      ((15 : Q') * qpow w 32)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h06))
            (by simpa only [c4] using h15))
          (by simpa only [c4] using h24))
        (by simpa only [c4] using h33))
      (by simpa only [c4] using h42)
  · have h32 :
        (15 : Q') * qpow w 32 + (15 : Q') * qpow w 32 ≈
          (30 : Q') * qpow w 32 := by
      refine Q'.eqv_trans _ (((15 : Q') + 15) * qpow w 32) _
        (Q'.eqv_symm (Q'.add_mul_eqv 15 15 (qpow w 32))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((16 : Q') * qpow w 30 +
        ((15 : Q') * qpow w 32 + (15 : Q') * qpow w 32) +
        (12 : Q') * qpow w 38 + (7 : Q') * qpow w 48) _
      (zero_add_five_six _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left ((16 : Q') * qpow w 30) _ _ h32)
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)

/-! ## 2. Derived off-diagonal and diagonal products -/

private def modeACombineL : RingNormaliser.PolyExpr :=
  add12E
    (.mul (.const 144) (.var 0)) (.mul (.const 270) (.var 1))
    (.mul (.const 108) (.var 3)) (.mul (.const 63) (.var 6))
    (.mul (.const 256) (.var 1)) (.mul (.const 480) (.var 2))
    (.mul (.const 192) (.var 4)) (.mul (.const 112) (.var 7))
    (.mul (.const 160) (.var 3)) (.mul (.const 300) (.var 4))
    (.mul (.const 120) (.var 5)) (.mul (.const 70) (.var 8))

private def modeACombineR : RingNormaliser.PolyExpr :=
  add9E
    (.mul (.const 144) (.var 0)) (.mul (.const 526) (.var 1))
    (.mul (.const 480) (.var 2)) (.mul (.const 268) (.var 3))
    (.mul (.const 492) (.var 4)) (.mul (.const 120) (.var 5))
    (.mul (.const 63) (.var 6)) (.mul (.const 112) (.var 7))
    (.mul (.const 70) (.var 8))

private theorem modeACombine_normal : RingNormaliser.normalize modeACombineL =
    RingNormaliser.normalize modeACombineR := by
  decide

private theorem modeA_combine (a b c d e f g h i : Q') :
    (144 : Q') * a + 270 * b + 108 * d + 63 * g + 256 * b + 480 * c +
        192 * e + 112 * h + 160 * d + 300 * e + 120 * f + 70 * i ≈
      (144 : Q') * a + 526 * b + 480 * c + 268 * d + 492 * e +
        120 * f + 63 * g + 112 * h + 70 * i := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeACombineL modeACombineR
    modeACombine_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
      | 5 => f | 6 => g | 7 => h | _ => i)
  simpa [RingNormaliser.eval, modeACombineL, modeACombineR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E] using hn

/-- Exact mode-four off-diagonal product. -/
theorem modeFourA_formula (w : Q') :
    acN w 5 4 * acN w 5 6 ≈
      (144 : Q') * qpow w 46 + (526 : Q') * qpow w 48 +
        (480 : Q') * qpow w 50 + (268 : Q') * qpow w 54 +
        (492 : Q') * qpow w 56 + (120 : Q') * qpow w 62 +
        (63 : Q') * qpow w 64 + (112 : Q') * qpow w 66 +
        (70 : Q') * qpow w 72 := by
  refine Q'.eqv_trans _
    (((9 : Q') * qpow w 16 + (16 : Q') * qpow w 18 + (10 : Q') * qpow w 24) *
      ((16 : Q') * qpow w 30 + (30 : Q') * qpow w 32 +
        (12 : Q') * qpow w 38 + (7 : Q') * qpow w 48)) _
    (mul_eqv_congr₂ (acN_five_four w) (acN_five_six w)) ?_
  refine Q'.eqv_trans _
    (((9 : Q') * qpow w 16) * ((16 : Q') * qpow w 30) +
      ((9 : Q') * qpow w 16) * ((30 : Q') * qpow w 32) +
      ((9 : Q') * qpow w 16) * ((12 : Q') * qpow w 38) +
      ((9 : Q') * qpow w 16) * ((7 : Q') * qpow w 48) +
      ((16 : Q') * qpow w 18) * ((16 : Q') * qpow w 30) +
      ((16 : Q') * qpow w 18) * ((30 : Q') * qpow w 32) +
      ((16 : Q') * qpow w 18) * ((12 : Q') * qpow w 38) +
      ((16 : Q') * qpow w 18) * ((7 : Q') * qpow w 48) +
      ((10 : Q') * qpow w 24) * ((16 : Q') * qpow w 30) +
      ((10 : Q') * qpow w 24) * ((30 : Q') * qpow w 32) +
      ((10 : Q') * qpow w 24) * ((12 : Q') * qpow w 38) +
      ((10 : Q') * qpow w 24) * ((7 : Q') * qpow w 48)) _
    (mul_three_by_four _ _ _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    (((9 : Q') * 16) * (qpow w 16 * qpow w 30) +
      ((9 : Q') * 30) * (qpow w 16 * qpow w 32) +
      ((9 : Q') * 12) * (qpow w 16 * qpow w 38) +
      ((9 : Q') * 7) * (qpow w 16 * qpow w 48) +
      ((16 : Q') * 16) * (qpow w 18 * qpow w 30) +
      ((16 : Q') * 30) * (qpow w 18 * qpow w 32) +
      ((16 : Q') * 12) * (qpow w 18 * qpow w 38) +
      ((16 : Q') * 7) * (qpow w 18 * qpow w 48) +
      ((10 : Q') * 16) * (qpow w 24 * qpow w 30) +
      ((10 : Q') * 30) * (qpow w 24 * qpow w 32) +
      ((10 : Q') * 12) * (qpow w 24 * qpow w 38) +
      ((10 : Q') * 7) * (qpow w 24 * qpow w 48)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (Q'.add_eqv_congr'
                      (Q'.add_eqv_congr'
                        (Q'.add_eqv_congr'
                          (mul_swap4 9 (qpow w 16) 16 (qpow w 30))
                          (mul_swap4 9 (qpow w 16) 30 (qpow w 32)))
                        (mul_swap4 9 (qpow w 16) 12 (qpow w 38)))
                      (mul_swap4 9 (qpow w 16) 7 (qpow w 48)))
                    (mul_swap4 16 (qpow w 18) 16 (qpow w 30)))
                  (mul_swap4 16 (qpow w 18) 30 (qpow w 32)))
                (mul_swap4 16 (qpow w 18) 12 (qpow w 38)))
              (mul_swap4 16 (qpow w 18) 7 (qpow w 48)))
            (mul_swap4 10 (qpow w 24) 16 (qpow w 30)))
          (mul_swap4 10 (qpow w 24) 30 (qpow w 32)))
        (mul_swap4 10 (qpow w 24) 12 (qpow w 38)))
      (mul_swap4 10 (qpow w 24) 7 (qpow w 48))
  · have h46 := Q'.eqv_symm (qpow_add w 16 30)
    have h48a := Q'.eqv_symm (qpow_add w 16 32)
    have h54a := Q'.eqv_symm (qpow_add w 16 38)
    have h64 := Q'.eqv_symm (qpow_add w 16 48)
    have h48b := Q'.eqv_symm (qpow_add w 18 30)
    have h50 := Q'.eqv_symm (qpow_add w 18 32)
    have h56a := Q'.eqv_symm (qpow_add w 18 38)
    have h66 := Q'.eqv_symm (qpow_add w 18 48)
    have h54b := Q'.eqv_symm (qpow_add w 24 30)
    have h56b := Q'.eqv_symm (qpow_add w 24 32)
    have h62 := Q'.eqv_symm (qpow_add w 24 38)
    have h72 := Q'.eqv_symm (qpow_add w 24 48)
    refine Q'.eqv_trans _
      ((144 : Q') * qpow w 46 + 270 * qpow w 48 + 108 * qpow w 54 +
        63 * qpow w 64 + 256 * qpow w 48 + 480 * qpow w 50 +
        192 * qpow w 56 + 112 * qpow w 66 + 160 * qpow w 54 +
        300 * qpow w 56 + 120 * qpow w 62 + 70 * qpow w 72) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (Q'.add_eqv_congr'
                      (Q'.add_eqv_congr'
                        (Q'.add_eqv_congr'
                          (Q'.add_eqv_congr'
                            (mul_eqv_congr₂ (by decide) h46)
                            (mul_eqv_congr₂ (by decide) h48a))
                          (mul_eqv_congr₂ (by decide) h54a))
                        (mul_eqv_congr₂ (by decide) h64))
                      (mul_eqv_congr₂ (by decide) h48b))
                    (mul_eqv_congr₂ (by decide) h50))
                  (mul_eqv_congr₂ (by decide) h56a))
                (mul_eqv_congr₂ (by decide) h66))
              (mul_eqv_congr₂ (by decide) h54b))
            (mul_eqv_congr₂ (by decide) h56b))
          (mul_eqv_congr₂ (by decide) h62))
        (mul_eqv_congr₂ (by decide) h72)
    · exact modeA_combine _ _ _ _ _ _ _ _ _

private def modeMCombineL : RingNormaliser.PolyExpr :=
  add9E
    (.mul (.const 576) (.var 0)) (.mul (.const 480) (.var 1))
    (.mul (.const 144) (.var 3)) (.mul (.const 480) (.var 1))
    (.mul (.const 400) (.var 2)) (.mul (.const 120) (.var 4))
    (.mul (.const 144) (.var 3)) (.mul (.const 120) (.var 4))
    (.mul (.const 36) (.var 5))

private def modeMCombineR : RingNormaliser.PolyExpr :=
  add6E
    (.mul (.const 576) (.var 0)) (.mul (.const 960) (.var 1))
    (.mul (.const 400) (.var 2)) (.mul (.const 288) (.var 3))
    (.mul (.const 240) (.var 4)) (.mul (.const 36) (.var 5))

private theorem modeMCombine_normal : RingNormaliser.normalize modeMCombineL =
    RingNormaliser.normalize modeMCombineR := by
  decide

private theorem modeM_combine (a b c d e f : Q') :
    (576 : Q') * a + 480 * b + 144 * d + 480 * b + 400 * c +
        120 * e + 144 * d + 120 * e + 36 * f ≈
      (576 : Q') * a + 960 * b + 400 * c + 288 * d + 240 * e + 36 * f := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeMCombineL modeMCombineR
    modeMCombine_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f)
  simpa [RingNormaliser.eval, modeMCombineL, modeMCombineR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E] using hn

/-- Exact mode-four diagonal square. -/
theorem modeFourM_formula (w : Q') :
    acN w 5 5 * acN w 5 5 ≈
      (576 : Q') * qpow w 46 + (960 : Q') * qpow w 50 +
        (400 : Q') * qpow w 54 + (288 : Q') * qpow w 58 +
        (240 : Q') * qpow w 62 + (36 : Q') * qpow w 70 := by
  refine Q'.eqv_trans _
    (((24 : Q') * qpow w 23 + (20 : Q') * qpow w 27 + (6 : Q') * qpow w 35) *
      ((24 : Q') * qpow w 23 + (20 : Q') * qpow w 27 +
        (6 : Q') * qpow w 35)) _
    (mul_eqv_congr₂ (acN_five_five w) (acN_five_five w)) ?_
  refine Q'.eqv_trans _
    (((24 : Q') * qpow w 23) * ((24 : Q') * qpow w 23) +
      ((24 : Q') * qpow w 23) * ((20 : Q') * qpow w 27) +
      ((24 : Q') * qpow w 23) * ((6 : Q') * qpow w 35) +
      ((20 : Q') * qpow w 27) * ((24 : Q') * qpow w 23) +
      ((20 : Q') * qpow w 27) * ((20 : Q') * qpow w 27) +
      ((20 : Q') * qpow w 27) * ((6 : Q') * qpow w 35) +
      ((6 : Q') * qpow w 35) * ((24 : Q') * qpow w 23) +
      ((6 : Q') * qpow w 35) * ((20 : Q') * qpow w 27) +
      ((6 : Q') * qpow w 35) * ((6 : Q') * qpow w 35)) _
    (mul_three_by_three _ _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    (((24 : Q') * 24) * (qpow w 23 * qpow w 23) +
      ((24 : Q') * 20) * (qpow w 23 * qpow w 27) +
      ((24 : Q') * 6) * (qpow w 23 * qpow w 35) +
      ((20 : Q') * 24) * (qpow w 27 * qpow w 23) +
      ((20 : Q') * 20) * (qpow w 27 * qpow w 27) +
      ((20 : Q') * 6) * (qpow w 27 * qpow w 35) +
      ((6 : Q') * 24) * (qpow w 35 * qpow w 23) +
      ((6 : Q') * 20) * (qpow w 35 * qpow w 27) +
      ((6 : Q') * 6) * (qpow w 35 * qpow w 35)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (mul_swap4 24 (qpow w 23) 24 (qpow w 23))
                    (mul_swap4 24 (qpow w 23) 20 (qpow w 27)))
                  (mul_swap4 24 (qpow w 23) 6 (qpow w 35)))
                (mul_swap4 20 (qpow w 27) 24 (qpow w 23)))
              (mul_swap4 20 (qpow w 27) 20 (qpow w 27)))
            (mul_swap4 20 (qpow w 27) 6 (qpow w 35)))
          (mul_swap4 6 (qpow w 35) 24 (qpow w 23)))
        (mul_swap4 6 (qpow w 35) 20 (qpow w 27)))
      (mul_swap4 6 (qpow w 35) 6 (qpow w 35))
  · have h46 := Q'.eqv_symm (qpow_add w 23 23)
    have h50a := Q'.eqv_symm (qpow_add w 23 27)
    have h58a := Q'.eqv_symm (qpow_add w 23 35)
    have h50b := Q'.eqv_symm (qpow_add w 27 23)
    have h54 := Q'.eqv_symm (qpow_add w 27 27)
    have h62a := Q'.eqv_symm (qpow_add w 27 35)
    have h58b := Q'.eqv_symm (qpow_add w 35 23)
    have h62b := Q'.eqv_symm (qpow_add w 35 27)
    have h70 := Q'.eqv_symm (qpow_add w 35 35)
    refine Q'.eqv_trans _
      ((576 : Q') * qpow w 46 + 480 * qpow w 50 + 144 * qpow w 58 +
        480 * qpow w 50 + 400 * qpow w 54 + 120 * qpow w 62 +
        144 * qpow w 58 + 120 * qpow w 62 + 36 * qpow w 70) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (Q'.add_eqv_congr'
                      (mul_eqv_congr₂ (by decide) h46)
                      (mul_eqv_congr₂ (by decide) h50a))
                    (mul_eqv_congr₂ (by decide) h58a))
                  (mul_eqv_congr₂ (by decide) h50b))
                (mul_eqv_congr₂ (by decide) h54))
              (mul_eqv_congr₂ (by decide) h62a))
            (mul_eqv_congr₂ (by decide) h58b))
          (mul_eqv_congr₂ (by decide) h62b))
        (mul_eqv_congr₂ (by decide) h70)
    · exact modeM_combine _ _ _ _ _ _

/-! ## 3. Reflective endpoint factorization -/

private def xE : RingNormaliser.PolyExpr := .var 0
private def xPowE (n : Nat) : RingNormaliser.PolyExpr := .pow xE n

private def factorLHS : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 10302201251)
      (add6E (.const 576) (.mul (.const 960) (xPowE 2))
        (.mul (.const 400) (xPowE 4)) (.mul (.const 288) (xPowE 6))
        (.mul (.const 240) (xPowE 8)) (.mul (.const 36) (xPowE 12))))
    (.neg (.mul (.const 21395529800)
      (add9E (.const 144) (.mul (.const 526) xE)
        (.mul (.const 480) (xPowE 2)) (.mul (.const 268) (xPowE 4))
        (.mul (.const 492) (xPowE 5)) (.mul (.const 120) (xPowE 8))
        (.mul (.const 63) (xPowE 9)) (.mul (.const 112) (xPowE 10))
        (.mul (.const 70) (xPowE 13)))))

private def factorRHS : RingNormaliser.PolyExpr :=
  .mul (.const 4)
    (.mul (.add (.const 1) (.neg (.mul (.const 4) xE)))
      (add13E
        (.mul (.const 93605442875) (xPowE 12))
        (.mul (.const 221407904) (xPowE 11))
        (.mul (.const 55351976) (xPowE 10))
        (.mul (.const 149782546594) (xPowE 9))
        (.mul (.const 121690535236) (xPowE 8))
        (.mul (.const 36356088544) (xPowE 7))
        (.mul (.const 9089022136) (xPowE 6))
        (.neg (.mul (.const 183167366984) (xPowE 5)))
        (.mul (.const 612120699604) (xPowE 4))
        (.mul (.const 253850267776) (xPowE 3))
        (.mul (.const 63462566944) (xPowE 2))
        (.mul (.const 39599460676) xE)
        (.const 713277907344)))

private theorem factor_normal : RingNormaliser.normalize factorLHS =
    RingNormaliser.normalize factorRHS := by
  decide

private theorem modeFour_factorization (x : Q') :
    (10302201251 : Q') *
        ((576 : Q') + 960 * RingNormaliser.qpow x 2 +
          400 * RingNormaliser.qpow x 4 + 288 * RingNormaliser.qpow x 6 +
          240 * RingNormaliser.qpow x 8 + 36 * RingNormaliser.qpow x 12) +
      -((21395529800 : Q') *
        ((144 : Q') + 526 * x + 480 * RingNormaliser.qpow x 2 +
          268 * RingNormaliser.qpow x 4 + 492 * RingNormaliser.qpow x 5 +
          120 * RingNormaliser.qpow x 8 + 63 * RingNormaliser.qpow x 9 +
          112 * RingNormaliser.qpow x 10 + 70 * RingNormaliser.qpow x 13)) ≈
      (4 : Q') * (((1 : Q') + -(4 * x)) *
        ((93605442875 : Q') * RingNormaliser.qpow x 12 +
          221407904 * RingNormaliser.qpow x 11 +
          55351976 * RingNormaliser.qpow x 10 +
          149782546594 * RingNormaliser.qpow x 9 +
          121690535236 * RingNormaliser.qpow x 8 +
          36356088544 * RingNormaliser.qpow x 7 +
          9089022136 * RingNormaliser.qpow x 6 +
          -(183167366984 * RingNormaliser.qpow x 5) +
          612120699604 * RingNormaliser.qpow x 4 +
          253850267776 * RingNormaliser.qpow x 3 +
          63462566944 * RingNormaliser.qpow x 2 + 39599460676 * x +
          713277907344)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq factorLHS factorRHS factor_normal
    (fun _ => x)
  simpa [RingNormaliser.eval, factorLHS, factorRHS, xE, xPowE, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E,
    add13E] using h

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

private theorem qpow_from_fortySix_as_xpow (w : Q') (n : Nat) :
    qpow w (46 + 2 * n) ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) n := by
  exact Q'.eqv_trans _ _ _ (qpow_add w 46 (2 * n))
    (Q'.mul_eqv_congr_left (qpow w 46) _ _ (qpow_even_as_xpow w n))

private def modeAFactorL : RingNormaliser.PolyExpr :=
  add9E
    (.mul (.const 144) (.var 0))
    (.mul (.const 526) (.mul (.var 0) (.var 1)))
    (.mul (.const 480) (.mul (.var 0) (.var 2)))
    (.mul (.const 268) (.mul (.var 0) (.var 3)))
    (.mul (.const 492) (.mul (.var 0) (.var 4)))
    (.mul (.const 120) (.mul (.var 0) (.var 5)))
    (.mul (.const 63) (.mul (.var 0) (.var 6)))
    (.mul (.const 112) (.mul (.var 0) (.var 7)))
    (.mul (.const 70) (.mul (.var 0) (.var 8)))

private def modeAFactorR : RingNormaliser.PolyExpr :=
  .mul (.var 0)
    (add9E (.const 144) (.mul (.const 526) (.var 1))
      (.mul (.const 480) (.var 2)) (.mul (.const 268) (.var 3))
      (.mul (.const 492) (.var 4)) (.mul (.const 120) (.var 5))
      (.mul (.const 63) (.var 6)) (.mul (.const 112) (.var 7))
      (.mul (.const 70) (.var 8)))

private theorem modeAFactor_normal : RingNormaliser.normalize modeAFactorL =
    RingNormaliser.normalize modeAFactorR := by
  decide

private theorem modeA_factor (q a b c d e f g h : Q') :
    (144 : Q') * q + 526 * (q * a) + 480 * (q * b) + 268 * (q * c) +
        492 * (q * d) + 120 * (q * e) + 63 * (q * f) + 112 * (q * g) +
        70 * (q * h) ≈
      q * ((144 : Q') + 526 * a + 480 * b + 268 * c + 492 * d +
        120 * e + 63 * f + 112 * g + 70 * h) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeAFactorL modeAFactorR
    modeAFactor_normal
    (fun n => match n with
      | 0 => q | 1 => a | 2 => b | 3 => c | 4 => d
      | 5 => e | 6 => f | 7 => g | _ => h)
  simpa [RingNormaliser.eval, modeAFactorL, modeAFactorR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E] using hn

private theorem modeFourA_factored (w : Q') :
    acN w 5 4 * acN w 5 6 ≈
      qpow w 46 *
        ((144 : Q') + 526 * qpow w 2 +
          480 * RingNormaliser.qpow (qpow w 2) 2 +
          268 * RingNormaliser.qpow (qpow w 2) 4 +
          492 * RingNormaliser.qpow (qpow w 2) 5 +
          120 * RingNormaliser.qpow (qpow w 2) 8 +
          63 * RingNormaliser.qpow (qpow w 2) 9 +
          112 * RingNormaliser.qpow (qpow w 2) 10 +
          70 * RingNormaliser.qpow (qpow w 2) 13) := by
  refine Q'.eqv_trans _ _ _ (modeFourA_formula w) ?_
  have h48a := qpow_from_fortySix_as_xpow w 1
  have h48 : qpow w 48 ≈ qpow w 46 * qpow w 2 := by
    exact Q'.eqv_trans _ _ _ (by simpa only using h48a)
      (Q'.mul_eqv_congr_left (qpow w 46) _ _ (rpow_one (qpow w 2)))
  have h50 : qpow w 50 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 2 := by
    simpa only using qpow_from_fortySix_as_xpow w 2
  have h54 : qpow w 54 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 4 := by
    simpa only using qpow_from_fortySix_as_xpow w 4
  have h56 : qpow w 56 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 5 := by
    simpa only using qpow_from_fortySix_as_xpow w 5
  have h62 : qpow w 62 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 8 := by
    simpa only using qpow_from_fortySix_as_xpow w 8
  have h64 : qpow w 64 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 9 := by
    simpa only using qpow_from_fortySix_as_xpow w 9
  have h66 : qpow w 66 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 10 := by
    simpa only using qpow_from_fortySix_as_xpow w 10
  have h72 : qpow w 72 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 13 := by
    simpa only using qpow_from_fortySix_as_xpow w 13
  refine Q'.eqv_trans _
    ((144 : Q') * qpow w 46 + 526 * (qpow w 46 * qpow w 2) +
      480 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 2) +
      268 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 4) +
      492 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 5) +
      120 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 8) +
      63 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 9) +
      112 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 10) +
      70 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 13)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr_left ((144 : Q') * qpow w 46) _ _
                    (Q'.mul_eqv_congr_left 526 _ _ h48))
                  (Q'.mul_eqv_congr_left 480 _ _ h50))
                (Q'.mul_eqv_congr_left 268 _ _ h54))
              (Q'.mul_eqv_congr_left 492 _ _ h56))
            (Q'.mul_eqv_congr_left 120 _ _ h62))
          (Q'.mul_eqv_congr_left 63 _ _ h64))
        (Q'.mul_eqv_congr_left 112 _ _ h66))
      (Q'.mul_eqv_congr_left 70 _ _ h72)
  · exact modeA_factor _ _ _ _ _ _ _ _ _

private def modeMFactorL : RingNormaliser.PolyExpr :=
  add6E
    (.mul (.const 576) (.var 0))
    (.mul (.const 960) (.mul (.var 0) (.var 1)))
    (.mul (.const 400) (.mul (.var 0) (.var 2)))
    (.mul (.const 288) (.mul (.var 0) (.var 3)))
    (.mul (.const 240) (.mul (.var 0) (.var 4)))
    (.mul (.const 36) (.mul (.var 0) (.var 5)))

private def modeMFactorR : RingNormaliser.PolyExpr :=
  .mul (.var 0)
    (add6E (.const 576) (.mul (.const 960) (.var 1))
      (.mul (.const 400) (.var 2)) (.mul (.const 288) (.var 3))
      (.mul (.const 240) (.var 4)) (.mul (.const 36) (.var 5)))

private theorem modeMFactor_normal : RingNormaliser.normalize modeMFactorL =
    RingNormaliser.normalize modeMFactorR := by
  decide

private theorem modeM_factor (q a b c d e : Q') :
    (576 : Q') * q + 960 * (q * a) + 400 * (q * b) + 288 * (q * c) +
        240 * (q * d) + 36 * (q * e) ≈
      q * ((576 : Q') + 960 * a + 400 * b + 288 * c + 240 * d + 36 * e) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeMFactorL modeMFactorR
    modeMFactor_normal
    (fun n => match n with
      | 0 => q | 1 => a | 2 => b | 3 => c | 4 => d | _ => e)
  simpa [RingNormaliser.eval, modeMFactorL, modeMFactorR, add2E, add3E,
    add4E, add5E, add6E] using hn

private theorem modeFourM_factored (w : Q') :
    acN w 5 5 * acN w 5 5 ≈
      qpow w 46 *
        ((576 : Q') + 960 * RingNormaliser.qpow (qpow w 2) 2 +
          400 * RingNormaliser.qpow (qpow w 2) 4 +
          288 * RingNormaliser.qpow (qpow w 2) 6 +
          240 * RingNormaliser.qpow (qpow w 2) 8 +
          36 * RingNormaliser.qpow (qpow w 2) 12) := by
  refine Q'.eqv_trans _ _ _ (modeFourM_formula w) ?_
  have h50 : qpow w 50 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 2 := by
    simpa only using qpow_from_fortySix_as_xpow w 2
  have h54 : qpow w 54 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 4 := by
    simpa only using qpow_from_fortySix_as_xpow w 4
  have h58 : qpow w 58 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 6 := by
    simpa only using qpow_from_fortySix_as_xpow w 6
  have h62 : qpow w 62 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 8 := by
    simpa only using qpow_from_fortySix_as_xpow w 8
  have h70 : qpow w 70 ≈
      qpow w 46 * RingNormaliser.qpow (qpow w 2) 12 := by
    simpa only using qpow_from_fortySix_as_xpow w 12
  refine Q'.eqv_trans _
    ((576 : Q') * qpow w 46 +
      960 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 2) +
      400 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 4) +
      288 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 6) +
      240 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 8) +
      36 * (qpow w 46 * RingNormaliser.qpow (qpow w 2) 12)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr_left ((576 : Q') * qpow w 46) _ _
              (Q'.mul_eqv_congr_left 960 _ _ h50))
            (Q'.mul_eqv_congr_left 400 _ _ h54))
          (Q'.mul_eqv_congr_left 288 _ _ h58))
        (Q'.mul_eqv_congr_left 240 _ _ h62))
      (Q'.mul_eqv_congr_left 36 _ _ h70)
  · exact modeM_factor _ _ _ _ _ _

/-! ## 5. Positivity of the signed degree-twelve factor -/

private def polyPartitionL : RingNormaliser.PolyExpr :=
  add13E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
    (.var 7) (.var 8) (.var 9) (.var 10) (.var 11) (.var 12)

private def polyPartitionR : RingNormaliser.PolyExpr :=
  .add
    (add11E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
      (.var 6) (.var 8) (.var 9) (.var 10) (.var 11))
    (.add (.var 7) (.var 12))

private theorem polyPartition_normal : RingNormaliser.normalize polyPartitionL =
    RingNormaliser.normalize polyPartitionR := by
  decide

private theorem poly_partition
    (a b c d e f g h i j k l m : Q') :
    a + b + c + d + e + f + g + h + i + j + k + l + m ≈
      (a + b + c + d + e + f + g + i + j + k + l) + (h + m) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq polyPartitionL polyPartitionR
    polyPartition_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g
      | 7 => h | 8 => i | 9 => j | 10 => k | 11 => l | _ => m)
  simpa [RingNormaliser.eval, polyPartitionL, polyPartitionR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E,
    add13E] using hn

private theorem modeFour_poly_nonneg {x : Q'}
    (hx0 : (0 : Q') ≤ x) (hxq : x ≤ Q'.mkPos 1 4 (by decide)) :
    (0 : Q') ≤
      (93605442875 : Q') * RingNormaliser.qpow x 12 +
        221407904 * RingNormaliser.qpow x 11 +
        55351976 * RingNormaliser.qpow x 10 +
        149782546594 * RingNormaliser.qpow x 9 +
        121690535236 * RingNormaliser.qpow x 8 +
        36356088544 * RingNormaliser.qpow x 7 +
        9089022136 * RingNormaliser.qpow x 6 +
        -(183167366984 * RingNormaliser.qpow x 5) +
        612120699604 * RingNormaliser.qpow x 4 +
        253850267776 * RingNormaliser.qpow x 3 +
        63462566944 * RingNormaliser.qpow x 2 + 39599460676 * x +
        713277907344 := by
  have hx1 : x ≤ (1 : Q') :=
    Q'.le_trans' _ (Q'.mkPos 1 4 (by decide)) _ hxq (by decide)
  have hx5one : RingNormaliser.qpow x 5 ≤ (1 : Q') := by
    refine Q'.le_trans' _ (RingNormaliser.qpow (1 : Q') 5) _
      (rpow_mono hx0 hx1 5) ?_
    exact Q'.le_of_eqv (by decide)
  have hcost : (183167366984 : Q') * RingNormaliser.qpow x 5 ≤
      (713277907344 : Q') := by
    refine Q'.le_trans' _ ((183167366984 : Q') * 1) _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hx5one (by decide)) ?_
    decide
  have hneg : (0 : Q') ≤
      -(183167366984 * RingNormaliser.qpow x 5) + 713277907344 := by
    have hb : (0 : Q') ≤
        (713277907344 : Q') +
          -((183167366984 : Q') * RingNormaliser.qpow x 5) :=
      Q'.sub_nonneg_of_le hcost
    exact Q'.le_trans' _ _ _ hb
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have h0 : (0 : Q') ≤
      (93605442875 : Q') * RingNormaliser.qpow x 12 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 12)
  have h1 : (0 : Q') ≤
      (221407904 : Q') * RingNormaliser.qpow x 11 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 11)
  have h2 : (0 : Q') ≤
      (55351976 : Q') * RingNormaliser.qpow x 10 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 10)
  have h3 : (0 : Q') ≤
      (149782546594 : Q') * RingNormaliser.qpow x 9 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 9)
  have h4 : (0 : Q') ≤
      (121690535236 : Q') * RingNormaliser.qpow x 8 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 8)
  have h5 : (0 : Q') ≤
      (36356088544 : Q') * RingNormaliser.qpow x 7 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 7)
  have h6 : (0 : Q') ≤
      (9089022136 : Q') * RingNormaliser.qpow x 6 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 6)
  have h8 : (0 : Q') ≤
      (612120699604 : Q') * RingNormaliser.qpow x 4 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 4)
  have h9 : (0 : Q') ≤
      (253850267776 : Q') * RingNormaliser.qpow x 3 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 3)
  have h10 : (0 : Q') ≤
      (63462566944 : Q') * RingNormaliser.qpow x 2 :=
    Q'.mul_nonneg _ _ (by decide) (rpow_nonneg x hx0 2)
  have h11 : (0 : Q') ≤ (39599460676 : Q') * x :=
    Q'.mul_nonneg _ _ (by decide) hx0
  have hp01 := Q'.zero_le_add _ _ h0 h1
  have hp012 := Q'.zero_le_add _ _ hp01 h2
  have hp0123 := Q'.zero_le_add _ _ hp012 h3
  have hp01234 := Q'.zero_le_add _ _ hp0123 h4
  have hp012345 := Q'.zero_le_add _ _ hp01234 h5
  have hp0123456 := Q'.zero_le_add _ _ hp012345 h6
  have hp01234568 := Q'.zero_le_add _ _ hp0123456 h8
  have hp012345689 := Q'.zero_le_add _ _ hp01234568 h9
  have hp01234568910 := Q'.zero_le_add _ _ hp012345689 h10
  have hpos := Q'.zero_le_add _ _ hp01234568910 h11
  have hsum := Q'.zero_le_add _ _ hpos hneg
  have hpolyEq :
      (93605442875 : Q') * RingNormaliser.qpow x 12 +
          221407904 * RingNormaliser.qpow x 11 +
          55351976 * RingNormaliser.qpow x 10 +
          149782546594 * RingNormaliser.qpow x 9 +
          121690535236 * RingNormaliser.qpow x 8 +
          36356088544 * RingNormaliser.qpow x 7 +
          9089022136 * RingNormaliser.qpow x 6 +
          -(183167366984 * RingNormaliser.qpow x 5) +
          612120699604 * RingNormaliser.qpow x 4 +
          253850267776 * RingNormaliser.qpow x 3 +
          63462566944 * RingNormaliser.qpow x 2 + 39599460676 * x +
          713277907344 ≈
        ((93605442875 : Q') * RingNormaliser.qpow x 12 +
          221407904 * RingNormaliser.qpow x 11 +
          55351976 * RingNormaliser.qpow x 10 +
          149782546594 * RingNormaliser.qpow x 9 +
          121690535236 * RingNormaliser.qpow x 8 +
          36356088544 * RingNormaliser.qpow x 7 +
          9089022136 * RingNormaliser.qpow x 6 +
          612120699604 * RingNormaliser.qpow x 4 +
          253850267776 * RingNormaliser.qpow x 3 +
          63462566944 * RingNormaliser.qpow x 2 + 39599460676 * x) +
        (-(183167366984 * RingNormaliser.qpow x 5) + 713277907344) := by
    exact poly_partition _ _ _ _ _ _ _ _ _ _ _ _ _
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hpolyEq))

/-! ## 6. Uniform scaled ratio and the cross-ratio member -/

private theorem modeFour_scaled_ratio {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (21395529800 : Q') * (acN w 5 4 * acN w 5 6) ≤
      (10302201251 : Q') * (acN w 5 5 * acN w 5 5) := by
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
  have hpoly := modeFour_poly_nonneg hx0 hxq
  have hfactorNonneg : (0 : Q') ≤
      (4 : Q') * (((1 : Q') + -(4 * x)) *
        ((93605442875 : Q') * RingNormaliser.qpow x 12 +
          221407904 * RingNormaliser.qpow x 11 +
          55351976 * RingNormaliser.qpow x 10 +
          149782546594 * RingNormaliser.qpow x 9 +
          121690535236 * RingNormaliser.qpow x 8 +
          36356088544 * RingNormaliser.qpow x 7 +
          9089022136 * RingNormaliser.qpow x 6 +
          -(183167366984 * RingNormaliser.qpow x 5) +
          612120699604 * RingNormaliser.qpow x 4 +
          253850267776 * RingNormaliser.qpow x 3 +
          63462566944 * RingNormaliser.qpow x 2 + 39599460676 * x +
          713277907344)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hlinear hpoly)
  have hdiff : (0 : Q') ≤
      (10302201251 : Q') *
          ((576 : Q') + 960 * RingNormaliser.qpow x 2 +
            400 * RingNormaliser.qpow x 4 + 288 * RingNormaliser.qpow x 6 +
            240 * RingNormaliser.qpow x 8 + 36 * RingNormaliser.qpow x 12) +
        -((21395529800 : Q') *
          ((144 : Q') + 526 * x + 480 * RingNormaliser.qpow x 2 +
            268 * RingNormaliser.qpow x 4 + 492 * RingNormaliser.qpow x 5 +
            120 * RingNormaliser.qpow x 8 + 63 * RingNormaliser.qpow x 9 +
            112 * RingNormaliser.qpow x 10 + 70 * RingNormaliser.qpow x 13)) :=
    Q'.le_trans' _ _ _ hfactorNonneg
      (Q'.le_of_eqv (Q'.eqv_symm (modeFour_factorization x)))
  have hinner :
      (21395529800 : Q') *
          ((144 : Q') + 526 * x + 480 * RingNormaliser.qpow x 2 +
            268 * RingNormaliser.qpow x 4 + 492 * RingNormaliser.qpow x 5 +
            120 * RingNormaliser.qpow x 8 + 63 * RingNormaliser.qpow x 9 +
            112 * RingNormaliser.qpow x 10 + 70 * RingNormaliser.qpow x 13) ≤
        (10302201251 : Q') *
          ((576 : Q') + 960 * RingNormaliser.qpow x 2 +
            400 * RingNormaliser.qpow x 4 + 288 * RingNormaliser.qpow x 6 +
            240 * RingNormaliser.qpow x 8 + 36 * RingNormaliser.qpow x 12) :=
    Q'.le_of_sub_nonneg hdiff
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 46) hinner
    (qpow_nonneg w hw0 46)
  have hL : qpow w 46 *
      ((21395529800 : Q') *
        ((144 : Q') + 526 * x + 480 * RingNormaliser.qpow x 2 +
          268 * RingNormaliser.qpow x 4 + 492 * RingNormaliser.qpow x 5 +
          120 * RingNormaliser.qpow x 8 + 63 * RingNormaliser.qpow x 9 +
          112 * RingNormaliser.qpow x 10 + 70 * RingNormaliser.qpow x 13)) ≈
      (21395529800 : Q') * (acN w 5 4 * acN w 5 6) := by
    exact Q'.eqv_trans _
      ((21395529800 : Q') * (qpow w 46 *
        ((144 : Q') + 526 * x + 480 * RingNormaliser.qpow x 2 +
          268 * RingNormaliser.qpow x 4 + 492 * RingNormaliser.qpow x 5 +
          120 * RingNormaliser.qpow x 8 + 63 * RingNormaliser.qpow x 9 +
          112 * RingNormaliser.qpow x 10 + 70 * RingNormaliser.qpow x 13))) _
        (Q'.eqv_symm (move_common 21395529800 (qpow w 46)
          ((144 : Q') + 526 * x + 480 * RingNormaliser.qpow x 2 +
            268 * RingNormaliser.qpow x 4 + 492 * RingNormaliser.qpow x 5 +
            120 * RingNormaliser.qpow x 8 + 63 * RingNormaliser.qpow x 9 +
            112 * RingNormaliser.qpow x 10 + 70 * RingNormaliser.qpow x 13)))
      (Q'.mul_eqv_congr_left 21395529800 _ _ (Q'.eqv_symm (modeFourA_factored w)))
  have hR : qpow w 46 *
      ((10302201251 : Q') *
        ((576 : Q') + 960 * RingNormaliser.qpow x 2 +
          400 * RingNormaliser.qpow x 4 + 288 * RingNormaliser.qpow x 6 +
          240 * RingNormaliser.qpow x 8 + 36 * RingNormaliser.qpow x 12)) ≈
      (10302201251 : Q') * (acN w 5 5 * acN w 5 5) := by
    exact Q'.eqv_trans _
      ((10302201251 : Q') * (qpow w 46 *
        ((576 : Q') + 960 * RingNormaliser.qpow x 2 +
          400 * RingNormaliser.qpow x 4 + 288 * RingNormaliser.qpow x 6 +
          240 * RingNormaliser.qpow x 8 + 36 * RingNormaliser.qpow x 12))) _
        (Q'.eqv_symm (move_common 10302201251 (qpow w 46)
          ((576 : Q') + 960 * RingNormaliser.qpow x 2 +
            400 * RingNormaliser.qpow x 4 + 288 * RingNormaliser.qpow x 6 +
            240 * RingNormaliser.qpow x 8 + 36 * RingNormaliser.qpow x 12)))
      (Q'.mul_eqv_congr_left 10302201251 _ _ (Q'.eqv_symm (modeFourM_factored w)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hR))

private theorem modeFour_anchor_ratio :
    (21395529800 : Q') * (acN wH 5 4 * acN wH 5 6) ≈
      (10302201251 : Q') * (acN wH 5 5 * acN wH 5 5) := by
  decide

/-- The complete `s = 4` member of `CrossRatioMonotone.cross`, uniformly on
the full exact-rational interval `[0,wH]`. -/
theorem cross_mode_four {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (acN w 5 4 * acN w 5 6) * (acN wH 5 5 * acN wH 5 5) ≤
      (acN wH 5 4 * acN wH 5 6) * (acN w 5 5 * acN w 5 5) := by
  let Aw := acN w 5 4 * acN w 5 6
  let Mw := acN w 5 5 * acN w 5 5
  let AH := acN wH 5 4 * acN wH 5 6
  let MH := acN wH 5 5 * acN wH 5 5
  have hMH : (0 : Q') ≤ MH := Q'.mul_nonneg _ _
    (acN_nonneg (by decide) 5 5) (acN_nonneg (by decide) 5 5)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ MH
    (modeFour_scaled_ratio hw0 hwH) hMH
  have hL : ((21395529800 : Q') * Aw) * MH ≈
      (21395529800 : Q') * (Aw * MH) := Q'.mul_assoc_eqv _ _ _
  have hR : ((10302201251 : Q') * Mw) * MH ≈
      (21395529800 : Q') * (AH * Mw) := by
    refine Q'.eqv_trans _ ((10302201251 : Q') * (Mw * MH)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((10302201251 : Q') * (MH * Mw)) _
      (Q'.mul_eqv_congr_left 10302201251 _ _ (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ (((10302201251 : Q') * MH) * Mw) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ (((21395529800 : Q') * AH) * Mw) _
      (Q'.mul_eqv_congr_right _ _ Mw (Q'.eqv_symm modeFour_anchor_ratio)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have h21395529800 : (21395529800 : Q') * (Aw * MH) ≤
      (21395529800 : Q') * (AH * Mw) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hR))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos (by decide) h21395529800

end YMGap.Continuum.CoreBModeFour

#print axioms YMGap.Continuum.CoreBModeFour.modeFourA_formula
#print axioms YMGap.Continuum.CoreBModeFour.modeFourM_formula
#print axioms YMGap.Continuum.CoreBModeFour.cross_mode_four
