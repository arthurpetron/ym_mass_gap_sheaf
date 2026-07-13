/-
# Core-B mode-five cross-ratio prefix

This file proves the `s = 5` member of `CrossRatioMonotone.cross` uniformly
for every exact rational coupling `0 ≤ w ≤ wH`.  The indexing is audited
at range six: the three entries are `acN w 6 5`, `acN w 6 6`, and
`acN w 6 7`.

With `x = w²`, exact endpoint reduction gives

  A(1/4) / M(1/4) = 18331308771352 / 38253816791089,

and reflective normalization certifies

  18331308771352 M(x) - 38253816791089 A(x)
    = 8 (1 - 4x) Q(x).

The signed quotient `Q` is proved nonnegative on `0 ≤ x ≤ 1/4` by
bounding each of its four negative powers by `1/4`; their total endpoint
cost is below the constant term.

Structural endpoint-factor note (not a positivity extrapolation): if
`F(x) = a₀ + … + aₙxⁿ` and `F(1/4) = 0`, synthetic division by
`1 - 4x` uses the exact recurrence `b₀ = a₀`,
`bₖ = aₖ + 4bₖ₋₁`, with the terminal equation
`aₙ = -4bₙ₋₁`.  Here the endpoint equality and the resulting
factorization are both checked exactly below.  Nothing in that structural
divisibility statement supplies uniform positivity of the quotient.
-/

import YMGap.Continuum.CoreBModeFour
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBModeFive

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
private def add6E (a b c d e f : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (add5E a b c d e) f
private def add7E (a b c d e f g : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
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
private def add14E (a b c d e f g h i j k l m n : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add13E a b c d e f g h i j k l m) n
private def add15E (a b c d e f g h i j k l m n o : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add14E a b c d e f g h i j k l m n) o
private def add16E (a b c d e f g h i j k l m n o p : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add15E a b c d e f g h i j k l m n o) p
private def add17E (a b c d e f g h i j k l m n o p q : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add16E a b c d e f g h i j k l m n o p) q
private def add18E (a b c d e f g h i j k l m n o p q r : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add17E a b c d e f g h i j k l m n o p q) r
private def add19E (a b c d e f g h i j k l m n o p q r s :
    RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (add18E a b c d e f g h i j k l m n o p q r) s

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
    RingNormaliser.normalize mul34R := by decide

private theorem mul_three_by_four (a b c d e f g : Q') :
    (a + b + c) * (d + e + f + g) ≈
      a * d + a * e + a * f + a * g + b * d + b * e + b * f + b * g +
        c * d + c * e + c * f + c * g := by
  have hn := RingNormaliser.poly_identity_of_normal_eq mul34L mul34R mul34_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g)
  simpa [RingNormaliser.eval, mul34L, mul34R, add2E, add3E, add4E, add5E,
    add6E, add7E, add8E, add9E, add10E, add11E, add12E] using hn

private def mul44L : RingNormaliser.PolyExpr :=
  .mul (add4E (.var 0) (.var 1) (.var 2) (.var 3))
    (add4E (.var 4) (.var 5) (.var 6) (.var 7))

private def mul44R : RingNormaliser.PolyExpr :=
  add16E
    (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 5))
    (.mul (.var 0) (.var 6)) (.mul (.var 0) (.var 7))
    (.mul (.var 1) (.var 4)) (.mul (.var 1) (.var 5))
    (.mul (.var 1) (.var 6)) (.mul (.var 1) (.var 7))
    (.mul (.var 2) (.var 4)) (.mul (.var 2) (.var 5))
    (.mul (.var 2) (.var 6)) (.mul (.var 2) (.var 7))
    (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 5))
    (.mul (.var 3) (.var 6)) (.mul (.var 3) (.var 7))

private theorem mul44_normal : RingNormaliser.normalize mul44L =
    RingNormaliser.normalize mul44R := by decide

private theorem mul_four_by_four (a b c d e f g h : Q') :
    (a + b + c + d) * (e + f + g + h) ≈
      a * e + a * f + a * g + a * h + b * e + b * f + b * g + b * h +
        c * e + c * f + c * g + c * h + d * e + d * f + d * g + d * h := by
  have hn := RingNormaliser.poly_identity_of_normal_eq mul44L mul44R mul44_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h)
  simpa [RingNormaliser.eval, mul44L, mul44R, add2E, add3E, add4E, add5E,
    add6E, add7E, add8E, add9E, add10E, add11E, add12E, add13E, add14E,
    add15E, add16E] using hn

private def zeroAddSixL : RingNormaliser.PolyExpr :=
  add7E (.const 0) (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)

private def zeroAddSixFiveR : RingNormaliser.PolyExpr :=
  add3E (.add (.var 2) (.var 3)) (.add (.var 1) (.var 4))
    (.add (.var 0) (.var 5))

private def zeroAddSixSixR : RingNormaliser.PolyExpr :=
  add4E (.var 3) (.add (.var 2) (.var 4)) (.add (.var 1) (.var 5)) (.var 0)

private def zeroAddSixSevenR : RingNormaliser.PolyExpr :=
  add4E (.add (.var 3) (.var 4)) (.add (.var 2) (.var 5)) (.var 1) (.var 0)

private theorem zeroAddSix_five_normal : RingNormaliser.normalize zeroAddSixL =
    RingNormaliser.normalize zeroAddSixFiveR := by decide
private theorem zeroAddSix_six_normal : RingNormaliser.normalize zeroAddSixL =
    RingNormaliser.normalize zeroAddSixSixR := by decide
private theorem zeroAddSix_seven_normal : RingNormaliser.normalize zeroAddSixL =
    RingNormaliser.normalize zeroAddSixSevenR := by decide

private theorem zero_add_six_five (a b c d e f : Q') :
    (0 : Q') + a + b + c + d + e + f ≈ (c + d) + (b + e) + (a + f) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddSixL zeroAddSixFiveR
    zeroAddSix_five_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f)
  simpa [RingNormaliser.eval, zeroAddSixL, zeroAddSixFiveR, add2E, add3E,
    add4E, add5E, add6E, add7E] using hn

private theorem zero_add_six_six (a b c d e f : Q') :
    (0 : Q') + a + b + c + d + e + f ≈ d + (c + e) + (b + f) + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddSixL zeroAddSixSixR
    zeroAddSix_six_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f)
  simpa [RingNormaliser.eval, zeroAddSixL, zeroAddSixSixR, add2E, add3E,
    add4E, add5E, add6E, add7E] using hn

private theorem zero_add_six_seven (a b c d e f : Q') :
    (0 : Q') + a + b + c + d + e + f ≈ (d + e) + (c + f) + b + a := by
  have hn := RingNormaliser.poly_identity_of_normal_eq zeroAddSixL zeroAddSixSevenR
    zeroAddSix_seven_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f)
  simpa [RingNormaliser.eval, zeroAddSixL, zeroAddSixSevenR, add2E, add3E,
    add4E, add5E, add6E, add7E] using hn

private theorem move_common (c q m : Q') : c * (q * m) ≈ q * (c * m) := by
  refine Q'.eqv_trans _ ((c * q) * m) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv c q m)) ?_
  refine Q'.eqv_trans _ ((q * c) * m) _
    (Q'.mul_eqv_congr_right _ _ m (Q'.mul_comm_eqv c q)) ?_
  exact Q'.mul_assoc_eqv q c m

/-! ## 1. Exact range-six autoconvolutions -/

private theorem acN_six_five (w : Q') :
    acN w 6 5 ≈
      (24 : Q') * qpow w 23 + (20 : Q') * qpow w 27 +
        (12 : Q') * qpow w 35 := by
  have h05 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 5
  have h14 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 4
  have h23 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 3
  have h32 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 2
  have h41 := LaplaceMarginDeep.coeffW_mul_ofNat w 4 1
  have h50 := LaplaceMarginDeep.coeffW_mul_ofNat w 5 0
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + 6 * qpow w 35 + 10 * qpow w 27 + 12 * qpow w 23 +
      12 * qpow w 23 + 10 * qpow w 27 + 6 * qpow w 35) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h05))
              (by simpa only [c4] using h14))
            (by simpa only [c4] using h23))
          (by simpa only [c4] using h32))
        (by simpa only [c4] using h41))
      (by simpa only [c4] using h50)
  · have h23c : 12 * qpow w 23 + 12 * qpow w 23 ≈
        (24 : Q') * qpow w 23 := by
      refine Q'.eqv_trans _ (((12 : Q') + 12) * qpow w 23) _
        (Q'.eqv_symm (Q'.add_mul_eqv 12 12 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h27c : 10 * qpow w 27 + 10 * qpow w 27 ≈
        (20 : Q') * qpow w 27 := by
      refine Q'.eqv_trans _ (((10 : Q') + 10) * qpow w 27) _
        (Q'.eqv_symm (Q'.add_mul_eqv 10 10 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h35c : 6 * qpow w 35 + 6 * qpow w 35 ≈
        (12 : Q') * qpow w 35 := by
      refine Q'.eqv_trans _ (((6 : Q') + 6) * qpow w 35) _
        (Q'.eqv_symm (Q'.add_mul_eqv 6 6 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((12 * qpow w 23 + 12 * qpow w 23) +
        (10 * qpow w 27 + 10 * qpow w 27) +
        (6 * qpow w 35 + 6 * qpow w 35)) _
      (zero_add_six_five _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.add_eqv_congr' h23c h27c) h35c

private theorem acN_six_six (w : Q') :
    acN w 6 6 ≈
      (16 : Q') * qpow w 30 + (30 : Q') * qpow w 32 +
        (24 : Q') * qpow w 38 + (7 : Q') * qpow w 48 := by
  have h06 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 6
  have h15 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 5
  have h24 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 4
  have h33 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 3
  have h42 := LaplaceMarginDeep.coeffW_mul_ofNat w 4 2
  have h51 := LaplaceMarginDeep.coeffW_mul_ofNat w 5 1
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + 7 * qpow w 48 + 12 * qpow w 38 + 15 * qpow w 32 +
      16 * qpow w 30 + 15 * qpow w 32 + 12 * qpow w 38) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h06))
              (by simpa only [c4] using h15))
            (by simpa only [c4] using h24))
          (by simpa only [c4] using h33))
        (by simpa only [c4] using h42))
      (by simpa only [c4] using h51)
  · have h32c : 15 * qpow w 32 + 15 * qpow w 32 ≈
        (30 : Q') * qpow w 32 := by
      refine Q'.eqv_trans _ (((15 : Q') + 15) * qpow w 32) _
        (Q'.eqv_symm (Q'.add_mul_eqv 15 15 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h38c : 12 * qpow w 38 + 12 * qpow w 38 ≈
        (24 : Q') * qpow w 38 := by
      refine Q'.eqv_trans _ (((12 : Q') + 12) * qpow w 38) _
        (Q'.eqv_symm (Q'.add_mul_eqv 12 12 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      (16 * qpow w 30 + (15 * qpow w 32 + 15 * qpow w 32) +
        (12 * qpow w 38 + 12 * qpow w 38) + 7 * qpow w 48) _
      (zero_add_six_six _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left (16 * qpow w 30) _ _ h32c) h38c)
      (Q'.eqv_refl _)

private theorem acN_six_seven (w : Q') :
    acN w 6 7 ≈
      (40 : Q') * qpow w 39 + (36 : Q') * qpow w 43 +
        (14 : Q') * qpow w 51 + (8 : Q') * qpow w 63 := by
  have h07 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 7
  have h16 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 6
  have h25 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 5
  have h34 := LaplaceMarginDeep.coeffW_mul_ofNat w 3 4
  have h43 := LaplaceMarginDeep.coeffW_mul_ofNat w 4 3
  have h52 := LaplaceMarginDeep.coeffW_mul_ofNat w 5 2
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + 8 * qpow w 63 + 14 * qpow w 51 + 18 * qpow w 43 +
      20 * qpow w 39 + 20 * qpow w 39 + 18 * qpow w 43) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h07))
              (by simpa only [c4] using h16))
            (by simpa only [c4] using h25))
          (by simpa only [c4] using h34))
        (by simpa only [c4] using h43))
      (by simpa only [c4] using h52)
  · have h39c : 20 * qpow w 39 + 20 * qpow w 39 ≈
        (40 : Q') * qpow w 39 := by
      refine Q'.eqv_trans _ (((20 : Q') + 20) * qpow w 39) _
        (Q'.eqv_symm (Q'.add_mul_eqv 20 20 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have h43c : 18 * qpow w 43 + 18 * qpow w 43 ≈
        (36 : Q') * qpow w 43 := by
      refine Q'.eqv_trans _ (((18 : Q') + 18) * qpow w 43) _
        (Q'.eqv_symm (Q'.add_mul_eqv 18 18 _)) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((20 * qpow w 39 + 20 * qpow w 39) +
        (18 * qpow w 43 + 18 * qpow w 43) + 14 * qpow w 51 +
        8 * qpow w 63) _ (zero_add_six_seven _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' h39c h43c) (Q'.eqv_refl _))
      (Q'.eqv_refl _)

/-! ## 2. Derived off-diagonal and diagonal products -/

private theorem coeff_power_mul (w : Q') (a b : Q') (m n : Nat) (c : Q')
    (hc : a * b ≈ c) :
    (a * qpow w m) * (b * qpow w n) ≈ c * qpow w (m + n) := by
  exact Q'.eqv_trans _ _ _ (mul_swap4 a (qpow w m) b (qpow w n))
    (mul_eqv_congr₂ hc (Q'.eqv_symm (qpow_add w m n)))

private def modeACombineL : RingNormaliser.PolyExpr :=
  add12E
    (.mul (.const 960) (.var 0)) (.mul (.const 864) (.var 1))
    (.mul (.const 336) (.var 3)) (.mul (.const 192) (.var 5))
    (.mul (.const 800) (.var 1)) (.mul (.const 720) (.var 2))
    (.mul (.const 280) (.var 4)) (.mul (.const 160) (.var 6))
    (.mul (.const 480) (.var 3)) (.mul (.const 432) (.var 4))
    (.mul (.const 168) (.var 5)) (.mul (.const 96) (.var 7))

private def modeACombineR : RingNormaliser.PolyExpr :=
  add8E
    (.mul (.const 960) (.var 0)) (.mul (.const 1664) (.var 1))
    (.mul (.const 720) (.var 2)) (.mul (.const 816) (.var 3))
    (.mul (.const 712) (.var 4)) (.mul (.const 360) (.var 5))
    (.mul (.const 160) (.var 6)) (.mul (.const 96) (.var 7))

private theorem modeACombine_normal : RingNormaliser.normalize modeACombineL =
    RingNormaliser.normalize modeACombineR := by decide

private theorem modeA_combine (a b c d e f g h : Q') :
    (960 : Q') * a + 864 * b + 336 * d + 192 * f + 800 * b + 720 * c +
        280 * e + 160 * g + 480 * d + 432 * e + 168 * f + 96 * h ≈
      (960 : Q') * a + 1664 * b + 720 * c + 816 * d + 712 * e +
        360 * f + 160 * g + 96 * h := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeACombineL modeACombineR
    modeACombine_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h)
  simpa [RingNormaliser.eval, modeACombineL, modeACombineR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E] using hn

/-- Exact mode-five off-diagonal product. -/
theorem modeFiveA_formula (w : Q') :
    acN w 6 5 * acN w 6 7 ≈
      (960 : Q') * qpow w 62 + (1664 : Q') * qpow w 66 +
        (720 : Q') * qpow w 70 + (816 : Q') * qpow w 74 +
        (712 : Q') * qpow w 78 + (360 : Q') * qpow w 86 +
        (160 : Q') * qpow w 90 + (96 : Q') * qpow w 98 := by
  refine Q'.eqv_trans _
    (((24 : Q') * qpow w 23 + 20 * qpow w 27 + 12 * qpow w 35) *
      ((40 : Q') * qpow w 39 + 36 * qpow w 43 + 14 * qpow w 51 +
        8 * qpow w 63)) _
    (mul_eqv_congr₂ (acN_six_five w) (acN_six_seven w)) ?_
  refine Q'.eqv_trans _
    (((24 : Q') * qpow w 23) * (40 * qpow w 39) +
      ((24 : Q') * qpow w 23) * (36 * qpow w 43) +
      ((24 : Q') * qpow w 23) * (14 * qpow w 51) +
      ((24 : Q') * qpow w 23) * (8 * qpow w 63) +
      (20 * qpow w 27) * (40 * qpow w 39) +
      (20 * qpow w 27) * (36 * qpow w 43) +
      (20 * qpow w 27) * (14 * qpow w 51) +
      (20 * qpow w 27) * (8 * qpow w 63) +
      (12 * qpow w 35) * (40 * qpow w 39) +
      (12 * qpow w 35) * (36 * qpow w 43) +
      (12 * qpow w 35) * (14 * qpow w 51) +
      (12 * qpow w 35) * (8 * qpow w 63)) _
    (mul_three_by_four _ _ _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    ((960 : Q') * qpow w 62 + 864 * qpow w 66 + 336 * qpow w 74 +
      192 * qpow w 86 + 800 * qpow w 66 + 720 * qpow w 70 +
      280 * qpow w 78 + 160 * qpow w 90 + 480 * qpow w 74 +
      432 * qpow w 78 + 168 * qpow w 86 + 96 * qpow w 98) _ ?_ ?_
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
                          (coeff_power_mul w 24 40 23 39 960 (by decide))
                          (coeff_power_mul w 24 36 23 43 864 (by decide)))
                        (coeff_power_mul w 24 14 23 51 336 (by decide)))
                      (coeff_power_mul w 24 8 23 63 192 (by decide)))
                    (coeff_power_mul w 20 40 27 39 800 (by decide)))
                  (coeff_power_mul w 20 36 27 43 720 (by decide)))
                (coeff_power_mul w 20 14 27 51 280 (by decide)))
              (coeff_power_mul w 20 8 27 63 160 (by decide)))
            (coeff_power_mul w 12 40 35 39 480 (by decide)))
          (coeff_power_mul w 12 36 35 43 432 (by decide)))
        (coeff_power_mul w 12 14 35 51 168 (by decide)))
      (coeff_power_mul w 12 8 35 63 96 (by decide))
  · exact modeA_combine _ _ _ _ _ _ _ _

private def modeMCombineL : RingNormaliser.PolyExpr :=
  add16E
    (.mul (.const 256) (.var 0)) (.mul (.const 480) (.var 1))
    (.mul (.const 384) (.var 3)) (.mul (.const 112) (.var 6))
    (.mul (.const 480) (.var 1)) (.mul (.const 900) (.var 2))
    (.mul (.const 720) (.var 4)) (.mul (.const 210) (.var 7))
    (.mul (.const 384) (.var 3)) (.mul (.const 720) (.var 4))
    (.mul (.const 576) (.var 5)) (.mul (.const 168) (.var 8))
    (.mul (.const 112) (.var 6)) (.mul (.const 210) (.var 7))
    (.mul (.const 168) (.var 8)) (.mul (.const 49) (.var 9))

private def modeMCombineR : RingNormaliser.PolyExpr :=
  add10E
    (.mul (.const 256) (.var 0)) (.mul (.const 960) (.var 1))
    (.mul (.const 900) (.var 2)) (.mul (.const 768) (.var 3))
    (.mul (.const 1440) (.var 4)) (.mul (.const 576) (.var 5))
    (.mul (.const 224) (.var 6)) (.mul (.const 420) (.var 7))
    (.mul (.const 336) (.var 8)) (.mul (.const 49) (.var 9))

private theorem modeMCombine_normal : RingNormaliser.normalize modeMCombineL =
    RingNormaliser.normalize modeMCombineR := by decide

private theorem modeM_combine (a b c d e f g h i j : Q') :
    (256 : Q') * a + 480 * b + 384 * d + 112 * g + 480 * b + 900 * c +
        720 * e + 210 * h + 384 * d + 720 * e + 576 * f + 168 * i +
        112 * g + 210 * h + 168 * i + 49 * j ≈
      (256 : Q') * a + 960 * b + 900 * c + 768 * d + 1440 * e +
        576 * f + 224 * g + 420 * h + 336 * i + 49 * j := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeMCombineL modeMCombineR
    modeMCombine_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f
      | 6 => g | 7 => h | 8 => i | _ => j)
  simpa [RingNormaliser.eval, modeMCombineL, modeMCombineR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E,
    add13E, add14E, add15E, add16E] using hn

/-- Exact mode-five diagonal square. -/
theorem modeFiveM_formula (w : Q') :
    acN w 6 6 * acN w 6 6 ≈
      (256 : Q') * qpow w 60 + (960 : Q') * qpow w 62 +
        (900 : Q') * qpow w 64 + (768 : Q') * qpow w 68 +
        (1440 : Q') * qpow w 70 + (576 : Q') * qpow w 76 +
        (224 : Q') * qpow w 78 + (420 : Q') * qpow w 80 +
        (336 : Q') * qpow w 86 + (49 : Q') * qpow w 96 := by
  refine Q'.eqv_trans _
    (((16 : Q') * qpow w 30 + 30 * qpow w 32 + 24 * qpow w 38 +
      7 * qpow w 48) *
      ((16 : Q') * qpow w 30 + 30 * qpow w 32 + 24 * qpow w 38 +
        7 * qpow w 48)) _
    (mul_eqv_congr₂ (acN_six_six w) (acN_six_six w)) ?_
  refine Q'.eqv_trans _
    (((16 : Q') * qpow w 30) * (16 * qpow w 30) +
      ((16 : Q') * qpow w 30) * (30 * qpow w 32) +
      ((16 : Q') * qpow w 30) * (24 * qpow w 38) +
      ((16 : Q') * qpow w 30) * (7 * qpow w 48) +
      (30 * qpow w 32) * (16 * qpow w 30) +
      (30 * qpow w 32) * (30 * qpow w 32) +
      (30 * qpow w 32) * (24 * qpow w 38) +
      (30 * qpow w 32) * (7 * qpow w 48) +
      (24 * qpow w 38) * (16 * qpow w 30) +
      (24 * qpow w 38) * (30 * qpow w 32) +
      (24 * qpow w 38) * (24 * qpow w 38) +
      (24 * qpow w 38) * (7 * qpow w 48) +
      (7 * qpow w 48) * (16 * qpow w 30) +
      (7 * qpow w 48) * (30 * qpow w 32) +
      (7 * qpow w 48) * (24 * qpow w 38) +
      (7 * qpow w 48) * (7 * qpow w 48)) _
    (mul_four_by_four _ _ _ _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    ((256 : Q') * qpow w 60 + 480 * qpow w 62 + 384 * qpow w 68 +
      112 * qpow w 78 + 480 * qpow w 62 + 900 * qpow w 64 +
      720 * qpow w 70 + 210 * qpow w 80 + 384 * qpow w 68 +
      720 * qpow w 70 + 576 * qpow w 76 + 168 * qpow w 86 +
      112 * qpow w 78 + 210 * qpow w 80 + 168 * qpow w 86 +
      49 * qpow w 96) _ ?_ ?_
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
                          (Q'.add_eqv_congr'
                            (Q'.add_eqv_congr'
                              (Q'.add_eqv_congr'
                                (Q'.add_eqv_congr'
                                  (coeff_power_mul w 16 16 30 30 256 (by decide))
                                  (coeff_power_mul w 16 30 30 32 480 (by decide)))
                                (coeff_power_mul w 16 24 30 38 384 (by decide)))
                              (coeff_power_mul w 16 7 30 48 112 (by decide)))
                            (coeff_power_mul w 30 16 32 30 480 (by decide)))
                          (coeff_power_mul w 30 30 32 32 900 (by decide)))
                        (coeff_power_mul w 30 24 32 38 720 (by decide)))
                      (coeff_power_mul w 30 7 32 48 210 (by decide)))
                    (coeff_power_mul w 24 16 38 30 384 (by decide)))
                  (coeff_power_mul w 24 30 38 32 720 (by decide)))
                (coeff_power_mul w 24 24 38 38 576 (by decide)))
              (coeff_power_mul w 24 7 38 48 168 (by decide)))
            (coeff_power_mul w 7 16 48 30 112 (by decide)))
          (coeff_power_mul w 7 30 48 32 210 (by decide)))
        (coeff_power_mul w 7 24 48 38 168 (by decide)))
      (coeff_power_mul w 7 7 48 48 49 (by decide))
  · exact modeM_combine _ _ _ _ _ _ _ _ _ _

/-! ## 3. Exact endpoint factorization -/

private def xE : RingNormaliser.PolyExpr := .var 0
private def xPowE (n : Nat) : RingNormaliser.PolyExpr := .pow xE n

private def quotientE : RingNormaliser.PolyExpr :=
  add19E
    (.mul (.const 114761450373267) (xPowE 18))
    (.mul (.const 620546037184) (xPowE 17))
    (.mul (.const 155136509296) (xPowE 16))
    (.mul (.const 38784127324) (xPowE 15))
    (.mul (.const 191278779987276) (xPowE 14))
    (.mul (.const 47819694996819) (xPowE 13))
    (.mul (.const 249831620549760) (xPowE 12))
    (.mul (.const 62457905137440) (xPowE 11))
    (.mul (.const 15614476284360) (xPowE 10))
    (.neg (.mul (.const 236694808552905) (xPowE 9)))
    (.mul (.const 663654560064040) (xPowE 8))
    (.neg (.mul (.const 164049917868326) (xPowE 7)))
    (.mul (.const 934459848705688) (xPowE 6))
    (.mul (.const 233614962176422) (xPowE 5))
    (.mul (.const 94205723632768) (xPowE 4))
    (.neg (.mul (.const 416399979604256) (xPowE 3)))
    (.mul (.const 1885098478235564) (xPowE 2))
    (.neg (.mul (.const 44293439635384) xE))
    (.const 586601880683264)

private def factorLHS : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 18331308771352)
      (add10E (.const 256) (.mul (.const 960) xE)
        (.mul (.const 900) (xPowE 2)) (.mul (.const 768) (xPowE 4))
        (.mul (.const 1440) (xPowE 5)) (.mul (.const 576) (xPowE 8))
        (.mul (.const 224) (xPowE 9)) (.mul (.const 420) (xPowE 10))
        (.mul (.const 336) (xPowE 13)) (.mul (.const 49) (xPowE 18))))
    (.neg (.mul (.const 38253816791089)
      (add8E (.mul (.const 960) xE) (.mul (.const 1664) (xPowE 3))
        (.mul (.const 720) (xPowE 5)) (.mul (.const 816) (xPowE 7))
        (.mul (.const 712) (xPowE 9)) (.mul (.const 360) (xPowE 13))
        (.mul (.const 160) (xPowE 15)) (.mul (.const 96) (xPowE 19)))))

private def factorRHS : RingNormaliser.PolyExpr :=
  .mul (.const 8)
    (.mul (.add (.const 1) (.neg (.mul (.const 4) xE))) quotientE)

private theorem factor_normal : RingNormaliser.normalize factorLHS =
    RingNormaliser.normalize factorRHS := by decide

private theorem modeFive_factorization (x : Q') :
    (18331308771352 : Q') *
        ((256 : Q') + 960 * x + 900 * RingNormaliser.qpow x 2 +
          768 * RingNormaliser.qpow x 4 + 1440 * RingNormaliser.qpow x 5 +
          576 * RingNormaliser.qpow x 8 + 224 * RingNormaliser.qpow x 9 +
          420 * RingNormaliser.qpow x 10 + 336 * RingNormaliser.qpow x 13 +
          49 * RingNormaliser.qpow x 18) +
      -((38253816791089 : Q') *
        ((960 : Q') * x + 1664 * RingNormaliser.qpow x 3 +
          720 * RingNormaliser.qpow x 5 + 816 * RingNormaliser.qpow x 7 +
          712 * RingNormaliser.qpow x 9 + 360 * RingNormaliser.qpow x 13 +
          160 * RingNormaliser.qpow x 15 + 96 * RingNormaliser.qpow x 19)) ≈
      (8 : Q') * (((1 : Q') + -(4 * x)) *
        ((114761450373267 : Q') * RingNormaliser.qpow x 18 +
          620546037184 * RingNormaliser.qpow x 17 +
          155136509296 * RingNormaliser.qpow x 16 +
          38784127324 * RingNormaliser.qpow x 15 +
          191278779987276 * RingNormaliser.qpow x 14 +
          47819694996819 * RingNormaliser.qpow x 13 +
          249831620549760 * RingNormaliser.qpow x 12 +
          62457905137440 * RingNormaliser.qpow x 11 +
          15614476284360 * RingNormaliser.qpow x 10 +
          -(236694808552905 * RingNormaliser.qpow x 9) +
          663654560064040 * RingNormaliser.qpow x 8 +
          -(164049917868326 * RingNormaliser.qpow x 7) +
          934459848705688 * RingNormaliser.qpow x 6 +
          233614962176422 * RingNormaliser.qpow x 5 +
          94205723632768 * RingNormaliser.qpow x 4 +
          -(416399979604256 * RingNormaliser.qpow x 3) +
          1885098478235564 * RingNormaliser.qpow x 2 +
          -(44293439635384 * x) + 586601880683264)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq factorLHS factorRHS factor_normal
    (fun _ => x)
  simpa [RingNormaliser.eval, factorLHS, factorRHS, quotientE, xE, xPowE,
    add2E, add3E, add4E, add5E, add6E, add7E, add8E, add9E, add10E,
    add11E, add12E, add13E, add14E, add15E, add16E, add17E, add18E,
    add19E] using h

/- The endpoint root which structurally triggers the synthetic-division
recurrence described in the module header. -/
private theorem modeFive_endpoint_root :
    (18331308771352 : Q') *
        ((256 : Q') + 960 * Q'.mkPos 1 4 (by decide) +
          900 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 2 +
          768 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 4 +
          1440 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 5 +
          576 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 8 +
          224 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 9 +
          420 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 10 +
          336 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 13 +
          49 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 18) ≈
      (38253816791089 : Q') *
        ((960 : Q') * Q'.mkPos 1 4 (by decide) +
          1664 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 3 +
          720 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 5 +
          816 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 7 +
          712 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 9 +
          360 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 13 +
          160 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 15 +
          96 * RingNormaliser.qpow (Q'.mkPos 1 4 (by decide)) 19) := by
  decide

/-! ## 4. Powers of `x = w²` and common-factor extraction -/

private theorem rpow_nonneg (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ n, (0 : Q') ≤ RingNormaliser.qpow x n
  | 0 => by change (0 : Q') ≤ 1; decide
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

private theorem qpow_from_sixty_as_xpow (w : Q') (n : Nat) :
    qpow w (60 + 2 * n) ≈
      qpow w 60 * RingNormaliser.qpow (qpow w 2) n := by
  exact Q'.eqv_trans _ _ _ (qpow_add w 60 (2 * n))
    (Q'.mul_eqv_congr_left (qpow w 60) _ _ (qpow_even_as_xpow w n))

private def modeAFactorL : RingNormaliser.PolyExpr :=
  add8E
    (.mul (.const 960) (.mul (.var 0) (.var 1)))
    (.mul (.const 1664) (.mul (.var 0) (.var 2)))
    (.mul (.const 720) (.mul (.var 0) (.var 3)))
    (.mul (.const 816) (.mul (.var 0) (.var 4)))
    (.mul (.const 712) (.mul (.var 0) (.var 5)))
    (.mul (.const 360) (.mul (.var 0) (.var 6)))
    (.mul (.const 160) (.mul (.var 0) (.var 7)))
    (.mul (.const 96) (.mul (.var 0) (.var 8)))

private def modeAFactorR : RingNormaliser.PolyExpr :=
  .mul (.var 0)
    (add8E (.mul (.const 960) (.var 1)) (.mul (.const 1664) (.var 2))
      (.mul (.const 720) (.var 3)) (.mul (.const 816) (.var 4))
      (.mul (.const 712) (.var 5)) (.mul (.const 360) (.var 6))
      (.mul (.const 160) (.var 7)) (.mul (.const 96) (.var 8)))

private theorem modeAFactor_normal : RingNormaliser.normalize modeAFactorL =
    RingNormaliser.normalize modeAFactorR := by decide

private theorem modeA_factor (q a b c d e f g h : Q') :
    (960 : Q') * (q * a) + 1664 * (q * b) + 720 * (q * c) +
        816 * (q * d) + 712 * (q * e) + 360 * (q * f) +
        160 * (q * g) + 96 * (q * h) ≈
      q * ((960 : Q') * a + 1664 * b + 720 * c + 816 * d + 712 * e +
        360 * f + 160 * g + 96 * h) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeAFactorL modeAFactorR
    modeAFactor_normal
    (fun n => match n with
      | 0 => q | 1 => a | 2 => b | 3 => c | 4 => d | 5 => e
      | 6 => f | 7 => g | _ => h)
  simpa [RingNormaliser.eval, modeAFactorL, modeAFactorR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E] using hn

private theorem modeFiveA_factored (w : Q') :
    acN w 6 5 * acN w 6 7 ≈
      qpow w 60 *
        ((960 : Q') * qpow w 2 +
          1664 * RingNormaliser.qpow (qpow w 2) 3 +
          720 * RingNormaliser.qpow (qpow w 2) 5 +
          816 * RingNormaliser.qpow (qpow w 2) 7 +
          712 * RingNormaliser.qpow (qpow w 2) 9 +
          360 * RingNormaliser.qpow (qpow w 2) 13 +
          160 * RingNormaliser.qpow (qpow w 2) 15 +
          96 * RingNormaliser.qpow (qpow w 2) 19) := by
  refine Q'.eqv_trans _ _ _ (modeFiveA_formula w) ?_
  have h62a := qpow_from_sixty_as_xpow w 1
  have h62 : qpow w 62 ≈ qpow w 60 * qpow w 2 := by
    exact Q'.eqv_trans _ _ _ (by simpa only using h62a)
      (Q'.mul_eqv_congr_left (qpow w 60) _ _ (rpow_one (qpow w 2)))
  have h66 : qpow w 66 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 3 := by
    simpa only using qpow_from_sixty_as_xpow w 3
  have h70 : qpow w 70 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 5 := by
    simpa only using qpow_from_sixty_as_xpow w 5
  have h74 : qpow w 74 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 7 := by
    simpa only using qpow_from_sixty_as_xpow w 7
  have h78 : qpow w 78 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 9 := by
    simpa only using qpow_from_sixty_as_xpow w 9
  have h86 : qpow w 86 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 13 := by
    simpa only using qpow_from_sixty_as_xpow w 13
  have h90 : qpow w 90 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 15 := by
    simpa only using qpow_from_sixty_as_xpow w 15
  have h98 : qpow w 98 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 19 := by
    simpa only using qpow_from_sixty_as_xpow w 19
  refine Q'.eqv_trans _
    ((960 : Q') * (qpow w 60 * qpow w 2) +
      1664 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 3) +
      720 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 5) +
      816 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 7) +
      712 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 9) +
      360 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 13) +
      160 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 15) +
      96 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 19)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.mul_eqv_congr_left 960 _ _ h62)
                  (Q'.mul_eqv_congr_left 1664 _ _ h66))
                (Q'.mul_eqv_congr_left 720 _ _ h70))
              (Q'.mul_eqv_congr_left 816 _ _ h74))
            (Q'.mul_eqv_congr_left 712 _ _ h78))
          (Q'.mul_eqv_congr_left 360 _ _ h86))
        (Q'.mul_eqv_congr_left 160 _ _ h90))
      (Q'.mul_eqv_congr_left 96 _ _ h98)
  · exact modeA_factor _ _ _ _ _ _ _ _ _

private def modeMFactorL : RingNormaliser.PolyExpr :=
  add10E
    (.mul (.const 256) (.var 0))
    (.mul (.const 960) (.mul (.var 0) (.var 1)))
    (.mul (.const 900) (.mul (.var 0) (.var 2)))
    (.mul (.const 768) (.mul (.var 0) (.var 3)))
    (.mul (.const 1440) (.mul (.var 0) (.var 4)))
    (.mul (.const 576) (.mul (.var 0) (.var 5)))
    (.mul (.const 224) (.mul (.var 0) (.var 6)))
    (.mul (.const 420) (.mul (.var 0) (.var 7)))
    (.mul (.const 336) (.mul (.var 0) (.var 8)))
    (.mul (.const 49) (.mul (.var 0) (.var 9)))

private def modeMFactorR : RingNormaliser.PolyExpr :=
  .mul (.var 0)
    (add10E (.const 256) (.mul (.const 960) (.var 1))
      (.mul (.const 900) (.var 2)) (.mul (.const 768) (.var 3))
      (.mul (.const 1440) (.var 4)) (.mul (.const 576) (.var 5))
      (.mul (.const 224) (.var 6)) (.mul (.const 420) (.var 7))
      (.mul (.const 336) (.var 8)) (.mul (.const 49) (.var 9)))

private theorem modeMFactor_normal : RingNormaliser.normalize modeMFactorL =
    RingNormaliser.normalize modeMFactorR := by decide

private theorem modeM_factor (q a b c d e f g h i : Q') :
    (256 : Q') * q + 960 * (q * a) + 900 * (q * b) + 768 * (q * c) +
        1440 * (q * d) + 576 * (q * e) + 224 * (q * f) + 420 * (q * g) +
        336 * (q * h) + 49 * (q * i) ≈
      q * ((256 : Q') + 960 * a + 900 * b + 768 * c + 1440 * d +
        576 * e + 224 * f + 420 * g + 336 * h + 49 * i) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq modeMFactorL modeMFactorR
    modeMFactor_normal
    (fun n => match n with
      | 0 => q | 1 => a | 2 => b | 3 => c | 4 => d | 5 => e
      | 6 => f | 7 => g | 8 => h | _ => i)
  simpa [RingNormaliser.eval, modeMFactorL, modeMFactorR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E] using hn

private theorem modeFiveM_factored (w : Q') :
    acN w 6 6 * acN w 6 6 ≈
      qpow w 60 *
        ((256 : Q') + 960 * qpow w 2 +
          900 * RingNormaliser.qpow (qpow w 2) 2 +
          768 * RingNormaliser.qpow (qpow w 2) 4 +
          1440 * RingNormaliser.qpow (qpow w 2) 5 +
          576 * RingNormaliser.qpow (qpow w 2) 8 +
          224 * RingNormaliser.qpow (qpow w 2) 9 +
          420 * RingNormaliser.qpow (qpow w 2) 10 +
          336 * RingNormaliser.qpow (qpow w 2) 13 +
          49 * RingNormaliser.qpow (qpow w 2) 18) := by
  refine Q'.eqv_trans _ _ _ (modeFiveM_formula w) ?_
  have h62a := qpow_from_sixty_as_xpow w 1
  have h62 : qpow w 62 ≈ qpow w 60 * qpow w 2 := by
    exact Q'.eqv_trans _ _ _ (by simpa only using h62a)
      (Q'.mul_eqv_congr_left (qpow w 60) _ _ (rpow_one (qpow w 2)))
  have h64 : qpow w 64 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 2 := by
    simpa only using qpow_from_sixty_as_xpow w 2
  have h68 : qpow w 68 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 4 := by
    simpa only using qpow_from_sixty_as_xpow w 4
  have h70 : qpow w 70 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 5 := by
    simpa only using qpow_from_sixty_as_xpow w 5
  have h76 : qpow w 76 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 8 := by
    simpa only using qpow_from_sixty_as_xpow w 8
  have h78 : qpow w 78 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 9 := by
    simpa only using qpow_from_sixty_as_xpow w 9
  have h80 : qpow w 80 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 10 := by
    simpa only using qpow_from_sixty_as_xpow w 10
  have h86 : qpow w 86 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 13 := by
    simpa only using qpow_from_sixty_as_xpow w 13
  have h96 : qpow w 96 ≈ qpow w 60 * RingNormaliser.qpow (qpow w 2) 18 := by
    simpa only using qpow_from_sixty_as_xpow w 18
  refine Q'.eqv_trans _
    ((256 : Q') * qpow w 60 + 960 * (qpow w 60 * qpow w 2) +
      900 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 2) +
      768 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 4) +
      1440 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 5) +
      576 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 8) +
      224 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 9) +
      420 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 10) +
      336 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 13) +
      49 * (qpow w 60 * RingNormaliser.qpow (qpow w 2) 18)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr'
                (Q'.add_eqv_congr'
                  (Q'.add_eqv_congr'
                    (Q'.add_eqv_congr_left ((256 : Q') * qpow w 60) _ _
                      (Q'.mul_eqv_congr_left 960 _ _ h62))
                    (Q'.mul_eqv_congr_left 900 _ _ h64))
                  (Q'.mul_eqv_congr_left 768 _ _ h68))
                (Q'.mul_eqv_congr_left 1440 _ _ h70))
              (Q'.mul_eqv_congr_left 576 _ _ h76))
            (Q'.mul_eqv_congr_left 224 _ _ h78))
          (Q'.mul_eqv_congr_left 420 _ _ h80))
        (Q'.mul_eqv_congr_left 336 _ _ h86))
      (Q'.mul_eqv_congr_left 49 _ _ h96)
  · exact modeM_factor _ _ _ _ _ _ _ _ _ _

/-! ## 5. Positivity of the signed degree-eighteen quotient -/

private def negGroupL : RingNormaliser.PolyExpr :=
  add5E (.neg (.var 0)) (.neg (.var 1)) (.neg (.var 2)) (.neg (.var 3))
    (.var 4)

private def negGroupR : RingNormaliser.PolyExpr :=
  .add (.var 4) (.neg (add4E (.var 0) (.var 1) (.var 2) (.var 3)))

private theorem negGroup_normal : RingNormaliser.normalize negGroupL =
    RingNormaliser.normalize negGroupR := by decide

private theorem neg_group (a b c d e : Q') :
    -a + -b + -c + -d + e ≈ e + -(a + b + c + d) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq negGroupL negGroupR
    negGroup_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e)
  simpa [RingNormaliser.eval, negGroupL, negGroupR, add2E, add3E, add4E,
    add5E] using hn

private def polyPartitionL : RingNormaliser.PolyExpr :=
  add19E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
    (.var 7) (.var 8) (.var 9) (.var 10) (.var 11) (.var 12) (.var 13)
    (.var 14) (.var 15) (.var 16) (.var 17) (.var 18)

private def polyPartitionR : RingNormaliser.PolyExpr :=
  .add
    (add14E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
      (.var 6) (.var 7) (.var 8) (.var 10) (.var 12) (.var 13)
      (.var 14) (.var 16))
    (add5E (.var 9) (.var 11) (.var 15) (.var 17) (.var 18))

private theorem polyPartition_normal : RingNormaliser.normalize polyPartitionL =
    RingNormaliser.normalize polyPartitionR := by decide

private theorem poly_partition
    (a b c d e f g h i j k l m n o p q r s : Q') :
    a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s ≈
      (a + b + c + d + e + f + g + h + i + k + m + n + o + q) +
        (j + l + p + r + s) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq polyPartitionL polyPartitionR
    polyPartition_normal
    (fun t => match t with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g
      | 7 => h | 8 => i | 9 => j | 10 => k | 11 => l | 12 => m
      | 13 => n | 14 => o | 15 => p | 16 => q | 17 => r | _ => s)
  simpa [RingNormaliser.eval, polyPartitionL, polyPartitionR, add2E, add3E,
    add4E, add5E, add6E, add7E, add8E, add9E, add10E, add11E, add12E,
    add13E, add14E, add15E, add16E, add17E, add18E, add19E] using hn

private theorem modeFive_poly_nonneg {x : Q'}
    (hx0 : (0 : Q') ≤ x) (hxq : x ≤ Q'.mkPos 1 4 (by decide)) :
    (0 : Q') ≤
      (114761450373267 : Q') * RingNormaliser.qpow x 18 +
        620546037184 * RingNormaliser.qpow x 17 +
        155136509296 * RingNormaliser.qpow x 16 +
        38784127324 * RingNormaliser.qpow x 15 +
        191278779987276 * RingNormaliser.qpow x 14 +
        47819694996819 * RingNormaliser.qpow x 13 +
        249831620549760 * RingNormaliser.qpow x 12 +
        62457905137440 * RingNormaliser.qpow x 11 +
        15614476284360 * RingNormaliser.qpow x 10 +
        -(236694808552905 * RingNormaliser.qpow x 9) +
        663654560064040 * RingNormaliser.qpow x 8 +
        -(164049917868326 * RingNormaliser.qpow x 7) +
        934459848705688 * RingNormaliser.qpow x 6 +
        233614962176422 * RingNormaliser.qpow x 5 +
        94205723632768 * RingNormaliser.qpow x 4 +
        -(416399979604256 * RingNormaliser.qpow x 3) +
        1885098478235564 * RingNormaliser.qpow x 2 +
        -(44293439635384 * x) + 586601880683264 := by
  let q4 : Q' := Q'.mkPos 1 4 (by decide)
  have hx9q : RingNormaliser.qpow x 9 ≤ q4 := by
    refine Q'.le_trans' _ (RingNormaliser.qpow q4 9) _
      (rpow_mono hx0 hxq 9) ?_
    decide
  have hx7q : RingNormaliser.qpow x 7 ≤ q4 := by
    refine Q'.le_trans' _ (RingNormaliser.qpow q4 7) _
      (rpow_mono hx0 hxq 7) ?_
    decide
  have hx3q : RingNormaliser.qpow x 3 ≤ q4 := by
    refine Q'.le_trans' _ (RingNormaliser.qpow q4 3) _
      (rpow_mono hx0 hxq 3) ?_
    decide
  have hc9 : (236694808552905 : Q') * RingNormaliser.qpow x 9 ≤
      (236694808552905 : Q') * q4 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hx9q (by decide)
  have hc7 : (164049917868326 : Q') * RingNormaliser.qpow x 7 ≤
      (164049917868326 : Q') * q4 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hx7q (by decide)
  have hc3 : (416399979604256 : Q') * RingNormaliser.qpow x 3 ≤
      (416399979604256 : Q') * q4 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hx3q (by decide)
  have hc1 : (44293439635384 : Q') * x ≤
      (44293439635384 : Q') * q4 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hxq (by decide)
  have hcostStep :
      (236694808552905 : Q') * RingNormaliser.qpow x 9 +
          164049917868326 * RingNormaliser.qpow x 7 +
          416399979604256 * RingNormaliser.qpow x 3 + 44293439635384 * x ≤
        (236694808552905 : Q') * q4 + 164049917868326 * q4 +
          416399979604256 * q4 + 44293439635384 * q4 := by
    have h97 := Q'.le_trans' _
      ((236694808552905 : Q') * q4 +
        164049917868326 * RingNormaliser.qpow x 7) _
      (Q'.add_le_add_right _ _ _ hc9) (Q'.add_le_add_left _ _ _ hc7)
    have h973 := Q'.le_trans' _
      (((236694808552905 : Q') * q4 + 164049917868326 * q4) +
        416399979604256 * RingNormaliser.qpow x 3) _
      (Q'.add_le_add_right _ _ _ h97) (Q'.add_le_add_left _ _ _ hc3)
    exact Q'.le_trans' _
      (((236694808552905 : Q') * q4 + 164049917868326 * q4 +
        416399979604256 * q4) + 44293439635384 * x) _
      (Q'.add_le_add_right _ _ _ h973) (Q'.add_le_add_left _ _ _ hc1)
  have hcost :
      (236694808552905 : Q') * RingNormaliser.qpow x 9 +
          164049917868326 * RingNormaliser.qpow x 7 +
          416399979604256 * RingNormaliser.qpow x 3 + 44293439635384 * x ≤
        (586601880683264 : Q') :=
    Q'.le_trans' _ _ _ hcostStep (by decide)
  have hbase : (0 : Q') ≤
      (586601880683264 : Q') +
        -((236694808552905 : Q') * RingNormaliser.qpow x 9 +
          164049917868326 * RingNormaliser.qpow x 7 +
          416399979604256 * RingNormaliser.qpow x 3 + 44293439635384 * x) :=
    Q'.sub_nonneg_of_le hcost
  have hnegEq :
      -(236694808552905 * RingNormaliser.qpow x 9) +
          -(164049917868326 * RingNormaliser.qpow x 7) +
          -(416399979604256 * RingNormaliser.qpow x 3) + -(44293439635384 * x) +
          586601880683264 ≈
        (586601880683264 : Q') +
          -((236694808552905 : Q') * RingNormaliser.qpow x 9 +
            164049917868326 * RingNormaliser.qpow x 7 +
            416399979604256 * RingNormaliser.qpow x 3 + 44293439635384 * x) :=
    neg_group _ _ _ _ _
  have hneg : (0 : Q') ≤
      -(236694808552905 * RingNormaliser.qpow x 9) +
        -(164049917868326 * RingNormaliser.qpow x 7) +
        -(416399979604256 * RingNormaliser.qpow x 3) + -(44293439635384 * x) +
        586601880683264 :=
    Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv (Q'.eqv_symm hnegEq))
  have h0 := Q'.mul_nonneg (114761450373267 : Q') _ (by decide)
    (rpow_nonneg x hx0 18)
  have h1 := Q'.mul_nonneg (620546037184 : Q') _ (by decide)
    (rpow_nonneg x hx0 17)
  have h2 := Q'.mul_nonneg (155136509296 : Q') _ (by decide)
    (rpow_nonneg x hx0 16)
  have h3 := Q'.mul_nonneg (38784127324 : Q') _ (by decide)
    (rpow_nonneg x hx0 15)
  have h4 := Q'.mul_nonneg (191278779987276 : Q') _ (by decide)
    (rpow_nonneg x hx0 14)
  have h5 := Q'.mul_nonneg (47819694996819 : Q') _ (by decide)
    (rpow_nonneg x hx0 13)
  have h6 := Q'.mul_nonneg (249831620549760 : Q') _ (by decide)
    (rpow_nonneg x hx0 12)
  have h7 := Q'.mul_nonneg (62457905137440 : Q') _ (by decide)
    (rpow_nonneg x hx0 11)
  have h8 := Q'.mul_nonneg (15614476284360 : Q') _ (by decide)
    (rpow_nonneg x hx0 10)
  have h10 := Q'.mul_nonneg (663654560064040 : Q') _ (by decide)
    (rpow_nonneg x hx0 8)
  have h12 := Q'.mul_nonneg (934459848705688 : Q') _ (by decide)
    (rpow_nonneg x hx0 6)
  have h13 := Q'.mul_nonneg (233614962176422 : Q') _ (by decide)
    (rpow_nonneg x hx0 5)
  have h14 := Q'.mul_nonneg (94205723632768 : Q') _ (by decide)
    (rpow_nonneg x hx0 4)
  have h16 := Q'.mul_nonneg (1885098478235564 : Q') _ (by decide)
    (rpow_nonneg x hx0 2)
  have hp01 := Q'.zero_le_add _ _ h0 h1
  have hp012 := Q'.zero_le_add _ _ hp01 h2
  have hp0123 := Q'.zero_le_add _ _ hp012 h3
  have hp01234 := Q'.zero_le_add _ _ hp0123 h4
  have hp012345 := Q'.zero_le_add _ _ hp01234 h5
  have hp0123456 := Q'.zero_le_add _ _ hp012345 h6
  have hp01234567 := Q'.zero_le_add _ _ hp0123456 h7
  have hp012345678 := Q'.zero_le_add _ _ hp01234567 h8
  have hp01234567810 := Q'.zero_le_add _ _ hp012345678 h10
  have hp0123456781012 := Q'.zero_le_add _ _ hp01234567810 h12
  have hp012345678101213 := Q'.zero_le_add _ _ hp0123456781012 h13
  have hp01234567810121314 := Q'.zero_le_add _ _ hp012345678101213 h14
  have hpos := Q'.zero_le_add _ _ hp01234567810121314 h16
  have hsum := Q'.zero_le_add _ _ hpos hneg
  have hpolyEq :
      (114761450373267 : Q') * RingNormaliser.qpow x 18 +
          620546037184 * RingNormaliser.qpow x 17 +
          155136509296 * RingNormaliser.qpow x 16 +
          38784127324 * RingNormaliser.qpow x 15 +
          191278779987276 * RingNormaliser.qpow x 14 +
          47819694996819 * RingNormaliser.qpow x 13 +
          249831620549760 * RingNormaliser.qpow x 12 +
          62457905137440 * RingNormaliser.qpow x 11 +
          15614476284360 * RingNormaliser.qpow x 10 +
          -(236694808552905 * RingNormaliser.qpow x 9) +
          663654560064040 * RingNormaliser.qpow x 8 +
          -(164049917868326 * RingNormaliser.qpow x 7) +
          934459848705688 * RingNormaliser.qpow x 6 +
          233614962176422 * RingNormaliser.qpow x 5 +
          94205723632768 * RingNormaliser.qpow x 4 +
          -(416399979604256 * RingNormaliser.qpow x 3) +
          1885098478235564 * RingNormaliser.qpow x 2 +
          -(44293439635384 * x) + 586601880683264 ≈
        ((114761450373267 : Q') * RingNormaliser.qpow x 18 +
          620546037184 * RingNormaliser.qpow x 17 +
          155136509296 * RingNormaliser.qpow x 16 +
          38784127324 * RingNormaliser.qpow x 15 +
          191278779987276 * RingNormaliser.qpow x 14 +
          47819694996819 * RingNormaliser.qpow x 13 +
          249831620549760 * RingNormaliser.qpow x 12 +
          62457905137440 * RingNormaliser.qpow x 11 +
          15614476284360 * RingNormaliser.qpow x 10 +
          663654560064040 * RingNormaliser.qpow x 8 +
          934459848705688 * RingNormaliser.qpow x 6 +
          233614962176422 * RingNormaliser.qpow x 5 +
          94205723632768 * RingNormaliser.qpow x 4 +
          1885098478235564 * RingNormaliser.qpow x 2) +
        (-(236694808552905 * RingNormaliser.qpow x 9) +
          -(164049917868326 * RingNormaliser.qpow x 7) +
          -(416399979604256 * RingNormaliser.qpow x 3) +
          -(44293439635384 * x) + 586601880683264) :=
    poly_partition _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hpolyEq))

/-! ## 6. Uniform scaled ratio and the cross-ratio member -/

private theorem modeFive_scaled_ratio {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (38253816791089 : Q') * (acN w 6 5 * acN w 6 7) ≤
      (18331308771352 : Q') * (acN w 6 6 * acN w 6 6) := by
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
  have hpoly := modeFive_poly_nonneg hx0 hxq
  have hfactorNonneg : (0 : Q') ≤
      (8 : Q') * (((1 : Q') + -(4 * x)) *
        ((114761450373267 : Q') * RingNormaliser.qpow x 18 +
          620546037184 * RingNormaliser.qpow x 17 +
          155136509296 * RingNormaliser.qpow x 16 +
          38784127324 * RingNormaliser.qpow x 15 +
          191278779987276 * RingNormaliser.qpow x 14 +
          47819694996819 * RingNormaliser.qpow x 13 +
          249831620549760 * RingNormaliser.qpow x 12 +
          62457905137440 * RingNormaliser.qpow x 11 +
          15614476284360 * RingNormaliser.qpow x 10 +
          -(236694808552905 * RingNormaliser.qpow x 9) +
          663654560064040 * RingNormaliser.qpow x 8 +
          -(164049917868326 * RingNormaliser.qpow x 7) +
          934459848705688 * RingNormaliser.qpow x 6 +
          233614962176422 * RingNormaliser.qpow x 5 +
          94205723632768 * RingNormaliser.qpow x 4 +
          -(416399979604256 * RingNormaliser.qpow x 3) +
          1885098478235564 * RingNormaliser.qpow x 2 +
          -(44293439635384 * x) + 586601880683264)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hlinear hpoly)
  have hdiff : (0 : Q') ≤
      (18331308771352 : Q') *
          ((256 : Q') + 960 * x + 900 * RingNormaliser.qpow x 2 +
            768 * RingNormaliser.qpow x 4 + 1440 * RingNormaliser.qpow x 5 +
            576 * RingNormaliser.qpow x 8 + 224 * RingNormaliser.qpow x 9 +
            420 * RingNormaliser.qpow x 10 + 336 * RingNormaliser.qpow x 13 +
            49 * RingNormaliser.qpow x 18) +
        -((38253816791089 : Q') *
          ((960 : Q') * x + 1664 * RingNormaliser.qpow x 3 +
            720 * RingNormaliser.qpow x 5 + 816 * RingNormaliser.qpow x 7 +
            712 * RingNormaliser.qpow x 9 + 360 * RingNormaliser.qpow x 13 +
            160 * RingNormaliser.qpow x 15 + 96 * RingNormaliser.qpow x 19)) :=
    Q'.le_trans' _ _ _ hfactorNonneg
      (Q'.le_of_eqv (Q'.eqv_symm (modeFive_factorization x)))
  have hinner :
      (38253816791089 : Q') *
          ((960 : Q') * x + 1664 * RingNormaliser.qpow x 3 +
            720 * RingNormaliser.qpow x 5 + 816 * RingNormaliser.qpow x 7 +
            712 * RingNormaliser.qpow x 9 + 360 * RingNormaliser.qpow x 13 +
            160 * RingNormaliser.qpow x 15 + 96 * RingNormaliser.qpow x 19) ≤
        (18331308771352 : Q') *
          ((256 : Q') + 960 * x + 900 * RingNormaliser.qpow x 2 +
            768 * RingNormaliser.qpow x 4 + 1440 * RingNormaliser.qpow x 5 +
            576 * RingNormaliser.qpow x 8 + 224 * RingNormaliser.qpow x 9 +
            420 * RingNormaliser.qpow x 10 + 336 * RingNormaliser.qpow x 13 +
            49 * RingNormaliser.qpow x 18) :=
    Q'.le_of_sub_nonneg hdiff
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 60) hinner
    (qpow_nonneg w hw0 60)
  have hL : qpow w 60 *
      ((38253816791089 : Q') *
        ((960 : Q') * x + 1664 * RingNormaliser.qpow x 3 +
          720 * RingNormaliser.qpow x 5 + 816 * RingNormaliser.qpow x 7 +
          712 * RingNormaliser.qpow x 9 + 360 * RingNormaliser.qpow x 13 +
          160 * RingNormaliser.qpow x 15 + 96 * RingNormaliser.qpow x 19)) ≈
      (38253816791089 : Q') * (acN w 6 5 * acN w 6 7) := by
    exact Q'.eqv_trans _
      ((38253816791089 : Q') * (qpow w 60 *
        ((960 : Q') * x + 1664 * RingNormaliser.qpow x 3 +
          720 * RingNormaliser.qpow x 5 + 816 * RingNormaliser.qpow x 7 +
          712 * RingNormaliser.qpow x 9 + 360 * RingNormaliser.qpow x 13 +
          160 * RingNormaliser.qpow x 15 + 96 * RingNormaliser.qpow x 19))) _
        (Q'.eqv_symm (move_common 38253816791089 (qpow w 60)
          ((960 : Q') * x + 1664 * RingNormaliser.qpow x 3 +
            720 * RingNormaliser.qpow x 5 + 816 * RingNormaliser.qpow x 7 +
            712 * RingNormaliser.qpow x 9 + 360 * RingNormaliser.qpow x 13 +
            160 * RingNormaliser.qpow x 15 + 96 * RingNormaliser.qpow x 19)))
      (Q'.mul_eqv_congr_left 38253816791089 _ _ (Q'.eqv_symm (modeFiveA_factored w)))
  have hR : qpow w 60 *
      ((18331308771352 : Q') *
        ((256 : Q') + 960 * x + 900 * RingNormaliser.qpow x 2 +
          768 * RingNormaliser.qpow x 4 + 1440 * RingNormaliser.qpow x 5 +
          576 * RingNormaliser.qpow x 8 + 224 * RingNormaliser.qpow x 9 +
          420 * RingNormaliser.qpow x 10 + 336 * RingNormaliser.qpow x 13 +
          49 * RingNormaliser.qpow x 18)) ≈
      (18331308771352 : Q') * (acN w 6 6 * acN w 6 6) := by
    exact Q'.eqv_trans _
      ((18331308771352 : Q') * (qpow w 60 *
        ((256 : Q') + 960 * x + 900 * RingNormaliser.qpow x 2 +
          768 * RingNormaliser.qpow x 4 + 1440 * RingNormaliser.qpow x 5 +
          576 * RingNormaliser.qpow x 8 + 224 * RingNormaliser.qpow x 9 +
          420 * RingNormaliser.qpow x 10 + 336 * RingNormaliser.qpow x 13 +
          49 * RingNormaliser.qpow x 18))) _
        (Q'.eqv_symm (move_common 18331308771352 (qpow w 60)
          ((256 : Q') + 960 * x + 900 * RingNormaliser.qpow x 2 +
            768 * RingNormaliser.qpow x 4 + 1440 * RingNormaliser.qpow x 5 +
            576 * RingNormaliser.qpow x 8 + 224 * RingNormaliser.qpow x 9 +
            420 * RingNormaliser.qpow x 10 + 336 * RingNormaliser.qpow x 13 +
            49 * RingNormaliser.qpow x 18)))
      (Q'.mul_eqv_congr_left 18331308771352 _ _ (Q'.eqv_symm (modeFiveM_factored w)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hR))

private theorem modeFive_anchor_ratio :
    (38253816791089 : Q') * (acN wH 6 5 * acN wH 6 7) ≈
      (18331308771352 : Q') * (acN wH 6 6 * acN wH 6 6) := by
  decide

/-- The complete `s = 5` member of `CrossRatioMonotone.cross`, uniformly on
the full exact-rational interval `[0,wH]`. -/
theorem cross_mode_five {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (acN w 6 5 * acN w 6 7) * (acN wH 6 6 * acN wH 6 6) ≤
      (acN wH 6 5 * acN wH 6 7) * (acN w 6 6 * acN w 6 6) := by
  let Aw := acN w 6 5 * acN w 6 7
  let Mw := acN w 6 6 * acN w 6 6
  let AH := acN wH 6 5 * acN wH 6 7
  let MH := acN wH 6 6 * acN wH 6 6
  have hMH : (0 : Q') ≤ MH := Q'.mul_nonneg _ _
    (acN_nonneg (by decide) 6 6) (acN_nonneg (by decide) 6 6)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ MH
    (modeFive_scaled_ratio hw0 hwH) hMH
  have hL : ((38253816791089 : Q') * Aw) * MH ≈
      (38253816791089 : Q') * (Aw * MH) := Q'.mul_assoc_eqv _ _ _
  have hR : ((18331308771352 : Q') * Mw) * MH ≈
      (38253816791089 : Q') * (AH * Mw) := by
    refine Q'.eqv_trans _ ((18331308771352 : Q') * (Mw * MH)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((18331308771352 : Q') * (MH * Mw)) _
      (Q'.mul_eqv_congr_left 18331308771352 _ _ (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ (((18331308771352 : Q') * MH) * Mw) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ (((38253816791089 : Q') * AH) * Mw) _
      (Q'.mul_eqv_congr_right _ _ Mw (Q'.eqv_symm modeFive_anchor_ratio)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have h38253816791089 : (38253816791089 : Q') * (Aw * MH) ≤
      (38253816791089 : Q') * (AH * Mw) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hR))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos (by decide)
    h38253816791089

end YMGap.Continuum.CoreBModeFive

#print axioms YMGap.Continuum.CoreBModeFive.modeFiveA_formula
#print axioms YMGap.Continuum.CoreBModeFive.modeFiveM_formula
#print axioms YMGap.Continuum.CoreBModeFive.cross_mode_five
