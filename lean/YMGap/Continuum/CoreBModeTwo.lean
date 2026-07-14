/-
# Core-B mode-two cross-ratio prefix

This file proves the `s = 2` member of `CrossRatioMonotone.cross` uniformly
for every exact rational coupling `0 ≤ w ≤ wH`.  The three-term finite
autoconvolutions and their products are derived exactly from `acN` and
`coeffW_mul_ofNat`.  After extracting the common factor `w^22`, the
endpoint-scaled difference is certified by the reflective factorization

  31031 M(x) - 76832 A(x)
    = 112 (1 - 4x)
        (5145x⁴ + 3608x³ + 902x² + 1808x + 15201),

where `x = w²`,

  A(x) = 36 + 86x + 48x² + 20x⁴ + 30x⁵,
  M(x) = 144 + 96x² + 16x⁴.

Every coefficient is kernel-derived; the scouting calculation is not used as
an assumption.
-/

import YMGap.Continuum.CoreBModeOne
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBModeTwo

set_option maxHeartbeats 3000000

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

private theorem mul_two_by_two (a b c d : Q') :
    (a + b) * (c + d) ≈ a * c + a * d + b * c + b * d := by
  refine Q'.eqv_trans _ (a * (c + d) + b * (c + d)) _
    (Q'.add_mul_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _ ((a * c + a * d) + (b * c + b * d)) _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv a c d) (Q'.mul_add_eqv b c d)) ?_
  ring_qeqv

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

/-! ## 1. Exact range-three autoconvolutions -/

private theorem acN_three_two (w : Q') :
    acN w 3 2 ≈ (4 : Q') * qpow w 6 + (6 : Q') * qpow w 8 := by
  have h02 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 2
  have h11 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 1
  have h20 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 0
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero, Nat.sub_self]
  refine Q'.eqv_trans _
    ((0 : Q') + ((3 : Q') * qpow w 8) + ((4 : Q') * qpow w 6) +
      ((3 : Q') * qpow w 8)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h02))
        (by simpa only [c4] using h11))
      (by simpa only [c4] using h20)
  · refine Q'.eqv_trans _
      ((4 : Q') * qpow w 6 +
        ((3 : Q') * qpow w 8 + (3 : Q') * qpow w 8)) _
      (by ring_qeqv) ?_
    refine Q'.add_eqv_congr_left ((4 : Q') * qpow w 6) _ _ ?_
    refine Q'.eqv_trans _ (((3 : Q') + 3) * qpow w 8) _
      (Q'.eqv_symm (Q'.add_mul_eqv 3 3 (qpow w 8))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)

private theorem acN_three_three (w : Q') :
    acN w 3 3 ≈ (12 : Q') * qpow w 11 + (4 : Q') * qpow w 15 := by
  have h03 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 3
  have h12 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 2
  have h21 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 1
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((4 : Q') * qpow w 15) + ((6 : Q') * qpow w 11) +
      ((6 : Q') * qpow w 11)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h03))
        (by simpa only [c4] using h12))
      (by simpa only [c4] using h21)
  · refine Q'.eqv_trans _
      (((6 : Q') * qpow w 11 + (6 : Q') * qpow w 11) +
        (4 : Q') * qpow w 15) _ (by ring_qeqv) ?_
    refine Q'.add_eqv_congr_right _ _ ((4 : Q') * qpow w 15) ?_
    refine Q'.eqv_trans _ (((6 : Q') + 6) * qpow w 11) _
      (Q'.eqv_symm (Q'.add_mul_eqv 6 6 (qpow w 11))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)

private theorem acN_three_four (w : Q') :
    acN w 3 4 ≈
      (9 : Q') * qpow w 16 + (8 : Q') * qpow w 18 +
        (5 : Q') * qpow w 24 := by
  have h04 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 4
  have h13 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 3
  have h22 := LaplaceMarginDeep.coeffW_mul_ofNat w 2 2
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((5 : Q') * qpow w 24) + ((8 : Q') * qpow w 18) +
      ((9 : Q') * qpow w 16)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h04))
        (by simpa only [c4] using h13))
      (by simpa only [c4] using h22)
  · let a := (5 : Q') * qpow w 24
    let b := (8 : Q') * qpow w 18
    let c := (9 : Q') * qpow w 16
    refine Q'.eqv_trans _ ((a + b) + c) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ c
        (Q'.add_eqv_congr_right _ _ b
          (Q'.eqv_of_eq (Q'.zero_add' a)))
    · refine Q'.eqv_trans _ (c + (a + b)) _ (Q'.add_comm_eqv (a + b) c) ?_
      refine Q'.eqv_trans _ (c + (b + a)) _
        (Q'.add_eqv_congr_left c _ _ (Q'.add_comm_eqv a b)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv c b a)

/-! ## 2. Derived off-diagonal and diagonal products -/

/-- Exact mode-two off-diagonal product, derived from the three `acN` summands. -/
theorem modeTwoA_formula (w : Q') :
    acN w 3 2 * acN w 3 4 ≈
      (36 : Q') * qpow w 22 + (86 : Q') * qpow w 24 +
        (48 : Q') * qpow w 26 + (20 : Q') * qpow w 30 +
          (30 : Q') * qpow w 32 := by
  refine Q'.eqv_trans _
    (((4 : Q') * qpow w 6 + (6 : Q') * qpow w 8) *
      ((9 : Q') * qpow w 16 + (8 : Q') * qpow w 18 +
        (5 : Q') * qpow w 24)) _
    (mul_eqv_congr₂ (acN_three_two w) (acN_three_four w)) ?_
  have h22 := Q'.eqv_symm (qpow_add w 6 16)
  have h24a := Q'.eqv_symm (qpow_add w 6 18)
  have h30 := Q'.eqv_symm (qpow_add w 6 24)
  have h24b := Q'.eqv_symm (qpow_add w 8 16)
  have h26 := Q'.eqv_symm (qpow_add w 8 18)
  have h32 := Q'.eqv_symm (qpow_add w 8 24)
  refine Q'.eqv_trans _
    (((4 : Q') * 9) * (qpow w 6 * qpow w 16) +
      ((4 : Q') * 8) * (qpow w 6 * qpow w 18) +
      ((4 : Q') * 5) * (qpow w 6 * qpow w 24) +
      ((6 : Q') * 9) * (qpow w 8 * qpow w 16) +
      ((6 : Q') * 8) * (qpow w 8 * qpow w 18) +
      ((6 : Q') * 5) * (qpow w 8 * qpow w 24)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (((4 : Q') * qpow w 6) * ((9 : Q') * qpow w 16) +
        ((4 : Q') * qpow w 6) * ((8 : Q') * qpow w 18) +
        ((4 : Q') * qpow w 6) * ((5 : Q') * qpow w 24) +
        ((6 : Q') * qpow w 8) * ((9 : Q') * qpow w 16) +
        ((6 : Q') * qpow w 8) * ((8 : Q') * qpow w 18) +
        ((6 : Q') * qpow w 8) * ((5 : Q') * qpow w 24)) _
      (mul_two_by_three _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (mul_swap4 4 (qpow w 6) 9 (qpow w 16))
              (mul_swap4 4 (qpow w 6) 8 (qpow w 18)))
            (mul_swap4 4 (qpow w 6) 5 (qpow w 24)))
          (mul_swap4 6 (qpow w 8) 9 (qpow w 16)))
        (mul_swap4 6 (qpow w 8) 8 (qpow w 18)))
      (mul_swap4 6 (qpow w 8) 5 (qpow w 24))
  refine Q'.eqv_trans _
    ((36 : Q') * qpow w 22 + (32 : Q') * qpow w 24 +
      (20 : Q') * qpow w 30 + (54 : Q') * qpow w 24 +
      (48 : Q') * qpow w 26 + (30 : Q') * qpow w 32) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (mul_eqv_congr₂ (by decide) h22)
              (mul_eqv_congr₂ (by decide) h24a))
            (mul_eqv_congr₂ (by decide) h30))
          (mul_eqv_congr₂ (by decide) h24b))
        (mul_eqv_congr₂ (by decide) h26))
      (mul_eqv_congr₂ (by decide) h32)
  · have hsum :
        (32 : Q') * qpow w 24 + (54 : Q') * qpow w 24 ≈
          (86 : Q') * qpow w 24 := by
      refine Q'.eqv_trans _ (((32 : Q') + 54) * qpow w 24) _
        (Q'.eqv_symm (Q'.add_mul_eqv 32 54 (qpow w 24))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((36 : Q') * qpow w 22 +
        ((32 : Q') * qpow w 24 + (54 : Q') * qpow w 24) +
        (48 : Q') * qpow w 26 + (20 : Q') * qpow w 30 +
        (30 : Q') * qpow w 32) _
      (add_six_reorder _ _ _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left ((36 : Q') * qpow w 22) _ _ hsum)
          (Q'.eqv_refl _))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _)

/-- Exact mode-two diagonal square, derived from the three `acN` summands. -/
theorem modeTwoM_formula (w : Q') :
    acN w 3 3 * acN w 3 3 ≈
      (144 : Q') * qpow w 22 + (96 : Q') * qpow w 26 +
        (16 : Q') * qpow w 30 := by
  refine Q'.eqv_trans _
    (((12 : Q') * qpow w 11 + (4 : Q') * qpow w 15) *
      ((12 : Q') * qpow w 11 + (4 : Q') * qpow w 15)) _
    (mul_eqv_congr₂ (acN_three_three w) (acN_three_three w)) ?_
  have h22 := Q'.eqv_symm (qpow_add w 11 11)
  have h26a := Q'.eqv_symm (qpow_add w 11 15)
  have h26b := Q'.eqv_symm (qpow_add w 15 11)
  have h30 := Q'.eqv_symm (qpow_add w 15 15)
  refine Q'.eqv_trans _
    (((12 : Q') * 12) * (qpow w 11 * qpow w 11) +
      ((12 : Q') * 4) * (qpow w 11 * qpow w 15) +
      ((4 : Q') * 12) * (qpow w 15 * qpow w 11) +
      ((4 : Q') * 4) * (qpow w 15 * qpow w 15)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (((12 : Q') * qpow w 11) * ((12 : Q') * qpow w 11) +
        ((12 : Q') * qpow w 11) * ((4 : Q') * qpow w 15) +
        ((4 : Q') * qpow w 15) * ((12 : Q') * qpow w 11) +
        ((4 : Q') * qpow w 15) * ((4 : Q') * qpow w 15)) _
      (mul_two_by_two _ _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (mul_swap4 12 (qpow w 11) 12 (qpow w 11))
          (mul_swap4 12 (qpow w 11) 4 (qpow w 15)))
        (mul_swap4 4 (qpow w 15) 12 (qpow w 11)))
      (mul_swap4 4 (qpow w 15) 4 (qpow w 15))
  refine Q'.eqv_trans _
    ((144 : Q') * qpow w 22 + (48 : Q') * qpow w 26 +
      (48 : Q') * qpow w 26 + (16 : Q') * qpow w 30) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (mul_eqv_congr₂ (by decide) h22)
          (mul_eqv_congr₂ (by decide) h26a))
        (mul_eqv_congr₂ (by decide) h26b))
      (mul_eqv_congr₂ (by decide) h30)
  · have hsum :
        (48 : Q') * qpow w 26 + (48 : Q') * qpow w 26 ≈
          (96 : Q') * qpow w 26 := by
      refine Q'.eqv_trans _ (((48 : Q') + 48) * qpow w 26) _
        (Q'.eqv_symm (Q'.add_mul_eqv 48 48 (qpow w 26))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _
      ((144 : Q') * qpow w 22 +
        ((48 : Q') * qpow w 26 + (48 : Q') * qpow w 26) +
        (16 : Q') * qpow w 30) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ ((16 : Q') * qpow w 30)
        (Q'.add_assoc_eqv ((144 : Q') * qpow w 22)
          ((48 : Q') * qpow w 26) ((48 : Q') * qpow w 26))
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left ((144 : Q') * qpow w 22) _ _ hsum)
      (Q'.eqv_refl _)

/-! ## 3. Reflective endpoint factorization -/

private def factorLHS : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 31031)
      (.add
        (.add (.const 144)
          (.mul (.const 96) (.mul (.var 0) (.var 0))))
        (.mul (.const 16)
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))))
    (.neg (.mul (.const 76832)
      (.add
        (.add
          (.add
            (.add (.const 36) (.mul (.const 86) (.var 0)))
            (.mul (.const 48) (.mul (.var 0) (.var 0))))
          (.mul (.const 20)
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))))
        (.mul (.const 30)
          (.mul (.var 0)
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))))))

private def factorRHS : RingNormaliser.PolyExpr :=
  .mul (.const 112)
    (.mul (.add (.const 1) (.neg (.mul (.const 4) (.var 0))))
      (.add
        (.add
          (.add
            (.add
              (.mul (.const 5145)
                (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
              (.mul (.const 3608)
                (.mul (.var 0) (.mul (.var 0) (.var 0)))))
            (.mul (.const 902) (.mul (.var 0) (.var 0))))
          (.mul (.const 1808) (.var 0)))
        (.const 15201)))

private theorem factor_normal : RingNormaliser.normalize factorLHS =
    RingNormaliser.normalize factorRHS := by
  decide

private theorem modeTwo_factorization (x : Q') :
    (31031 : Q') *
        ((144 : Q') + 96 * (x * x) + 16 * ((x * x) * (x * x))) +
      -((76832 : Q') *
        ((36 : Q') + 86 * x + 48 * (x * x) +
          20 * ((x * x) * (x * x)) +
          30 * (x * ((x * x) * (x * x))))) ≈
      (112 : Q') * (((1 : Q') + -(4 * x)) *
        ((5145 : Q') * ((x * x) * (x * x)) +
          3608 * (x * (x * x)) + 902 * (x * x) + 1808 * x + 15201)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq factorLHS factorRHS factor_normal
    (fun _ => x)
  simpa [RingNormaliser.eval, factorLHS, factorRHS,
    RingNormaliser.qpow] using h

/-! ## 4. Extraction of the common `w^22` factor -/

private theorem qpow_four_as_xsq (w : Q') :
    qpow w 4 ≈ qpow w 2 * qpow w 2 := qpow_add w 2 2

private theorem qpow_eight_as_xfour (w : Q') :
    qpow w 8 ≈
      (qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2) := by
  exact Q'.eqv_trans _ _ _ (qpow_add w 4 4)
    (mul_eqv_congr₂ (qpow_four_as_xsq w) (qpow_four_as_xsq w))

private theorem qpow_ten_as_xfive (w : Q') :
    qpow w 10 ≈
      qpow w 2 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)) := by
  exact Q'.eqv_trans _ _ _ (qpow_add w 2 8)
    (Q'.mul_eqv_congr_left (qpow w 2) _ _ (qpow_eight_as_xfour w))

private theorem modeTwoA_factored (w : Q') :
    acN w 3 2 * acN w 3 4 ≈
      qpow w 22 *
        ((36 : Q') + 86 * qpow w 2 +
          48 * (qpow w 2 * qpow w 2) +
          20 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)) +
          30 * (qpow w 2 *
            ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))) := by
  refine Q'.eqv_trans _ _ _ (modeTwoA_formula w) ?_
  have h24 : qpow w 24 ≈ qpow w 22 * qpow w 2 := by
    simpa only using qpow_add w 22 2
  have h26a : qpow w 26 ≈ qpow w 22 * qpow w 4 := by
    simpa only using qpow_add w 22 4
  have h26 : qpow w 26 ≈
      qpow w 22 * (qpow w 2 * qpow w 2) :=
    Q'.eqv_trans _ _ _ h26a
      (Q'.mul_eqv_congr_left (qpow w 22) _ _ (qpow_four_as_xsq w))
  have h30a : qpow w 30 ≈ qpow w 22 * qpow w 8 := by
    simpa only using qpow_add w 22 8
  have h30 : qpow w 30 ≈
      qpow w 22 *
        ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)) :=
    Q'.eqv_trans _ _ _ h30a
      (Q'.mul_eqv_congr_left (qpow w 22) _ _ (qpow_eight_as_xfour w))
  have h32a : qpow w 32 ≈ qpow w 22 * qpow w 10 := by
    simpa only using qpow_add w 22 10
  have h32 : qpow w 32 ≈
      qpow w 22 *
        (qpow w 2 *
          ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))) :=
    Q'.eqv_trans _ _ _ h32a
      (Q'.mul_eqv_congr_left (qpow w 22) _ _ (qpow_ten_as_xfive w))
  refine Q'.eqv_trans _
    ((36 : Q') * qpow w 22 +
      (86 : Q') * (qpow w 22 * qpow w 2) +
      (48 : Q') * (qpow w 22 * (qpow w 2 * qpow w 2)) +
      (20 : Q') * (qpow w 22 *
        ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))) +
      (30 : Q') * (qpow w 22 *
        (qpow w 2 *
          ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left ((36 : Q') * qpow w 22) _ _
            (Q'.mul_eqv_congr_left 86 _ _ h24))
          (Q'.mul_eqv_congr_left 48 _ _ h26))
        (Q'.mul_eqv_congr_left 20 _ _ h30))
      (Q'.mul_eqv_congr_left 30 _ _ h32)
  · refine Q'.eqv_trans _
      (qpow w 22 * (36 : Q') +
        qpow w 22 * (86 * qpow w 2) +
        qpow w 22 * (48 * (qpow w 2 * qpow w 2)) +
        qpow w 22 * (20 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))) +
        qpow w 22 * (30 * (qpow w 2 *
          ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))) ) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.mul_comm_eqv 36 (qpow w 22))
              (move_common 86 (qpow w 22) (qpow w 2)))
            (move_common 48 (qpow w 22) (qpow w 2 * qpow w 2)))
          (move_common 20 (qpow w 22)
            ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))))
        (move_common 30 (qpow w 22)
          (qpow w 2 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))))
    · exact factor_five (qpow w 22) 36
        (86 * qpow w 2) (48 * (qpow w 2 * qpow w 2))
        (20 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))
        (30 * (qpow w 2 *
          ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))))

private theorem modeTwoM_factored (w : Q') :
    acN w 3 3 * acN w 3 3 ≈
      qpow w 22 *
        ((144 : Q') + 96 * (qpow w 2 * qpow w 2) +
          16 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2))) := by
  refine Q'.eqv_trans _ _ _ (modeTwoM_formula w) ?_
  have h26a : qpow w 26 ≈ qpow w 22 * qpow w 4 := by
    simpa only using qpow_add w 22 4
  have h26 : qpow w 26 ≈
      qpow w 22 * (qpow w 2 * qpow w 2) :=
    Q'.eqv_trans _ _ _ h26a
      (Q'.mul_eqv_congr_left (qpow w 22) _ _ (qpow_four_as_xsq w))
  have h30a : qpow w 30 ≈ qpow w 22 * qpow w 8 := by
    simpa only using qpow_add w 22 8
  have h30 : qpow w 30 ≈
      qpow w 22 *
        ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)) :=
    Q'.eqv_trans _ _ _ h30a
      (Q'.mul_eqv_congr_left (qpow w 22) _ _ (qpow_eight_as_xfour w))
  refine Q'.eqv_trans _
    ((144 : Q') * qpow w 22 +
      (96 : Q') * (qpow w 22 * (qpow w 2 * qpow w 2)) +
      (16 : Q') * (qpow w 22 *
        ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left ((144 : Q') * qpow w 22) _ _
        (Q'.mul_eqv_congr_left 96 _ _ h26))
      (Q'.mul_eqv_congr_left 16 _ _ h30)
  · refine Q'.eqv_trans _
      (qpow w 22 * (144 : Q') +
        qpow w 22 * (96 * (qpow w 2 * qpow w 2)) +
        qpow w 22 * (16 *
          ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_comm_eqv 144 (qpow w 22))
          (move_common 96 (qpow w 22) (qpow w 2 * qpow w 2)))
        (move_common 16 (qpow w 22)
          ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))
    · exact factor_three (qpow w 22) 144
        (96 * (qpow w 2 * qpow w 2))
        (16 * ((qpow w 2 * qpow w 2) * (qpow w 2 * qpow w 2)))

/-! ## 5. The uniform scaled ratio and cross-ratio member -/

private theorem modeTwo_scaled_ratio {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (76832 : Q') * (acN w 3 2 * acN w 3 4) ≤
      (31031 : Q') * (acN w 3 3 * acN w 3 3) := by
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
  have hx2 : (0 : Q') ≤ x * x := Q'.mul_nonneg _ _ hx0 hx0
  have hx3 : (0 : Q') ≤ x * (x * x) := Q'.mul_nonneg _ _ hx0 hx2
  have hx4 : (0 : Q') ≤ (x * x) * (x * x) := Q'.mul_nonneg _ _ hx2 hx2
  have hpoly : (0 : Q') ≤
      (5145 : Q') * ((x * x) * (x * x)) +
        3608 * (x * (x * x)) + 902 * (x * x) + 1808 * x + 15201 := by
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (by decide) hx4)
            (Q'.mul_nonneg _ _ (by decide) hx3))
          (Q'.mul_nonneg _ _ (by decide) hx2))
        (Q'.mul_nonneg _ _ (by decide) hx0))
      (by decide)
  have hfactorNonneg : (0 : Q') ≤
      (112 : Q') * (((1 : Q') + -(4 * x)) *
        ((5145 : Q') * ((x * x) * (x * x)) +
          3608 * (x * (x * x)) + 902 * (x * x) + 1808 * x + 15201)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hlinear hpoly)
  have hdiff : (0 : Q') ≤
      (31031 : Q') *
          ((144 : Q') + 96 * (x * x) + 16 * ((x * x) * (x * x))) +
        -((76832 : Q') *
          ((36 : Q') + 86 * x + 48 * (x * x) +
            20 * ((x * x) * (x * x)) +
            30 * (x * ((x * x) * (x * x))))) :=
    Q'.le_trans' _ _ _ hfactorNonneg
      (Q'.le_of_eqv (Q'.eqv_symm (modeTwo_factorization x)))
  have hinner :
      (76832 : Q') *
          ((36 : Q') + 86 * x + 48 * (x * x) +
            20 * ((x * x) * (x * x)) +
            30 * (x * ((x * x) * (x * x)))) ≤
        (31031 : Q') *
          ((144 : Q') + 96 * (x * x) + 16 * ((x * x) * (x * x))) :=
    Q'.le_of_sub_nonneg hdiff
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 22) hinner
    (qpow_nonneg w hw0 22)
  have hL : qpow w 22 *
      ((76832 : Q') *
        ((36 : Q') + 86 * x + 48 * (x * x) +
          20 * ((x * x) * (x * x)) +
          30 * (x * ((x * x) * (x * x))))) ≈
      (76832 : Q') * (acN w 3 2 * acN w 3 4) := by
    exact Q'.eqv_trans _
      ((76832 : Q') * (qpow w 22 *
        ((36 : Q') + 86 * x + 48 * (x * x) +
          20 * ((x * x) * (x * x)) +
          30 * (x * ((x * x) * (x * x)))))) _
      (Q'.eqv_symm (move_common 76832 (qpow w 22)
        ((36 : Q') + 86 * x + 48 * (x * x) +
          20 * ((x * x) * (x * x)) +
          30 * (x * ((x * x) * (x * x))))))
      (Q'.mul_eqv_congr_left 76832 _ _ (Q'.eqv_symm (modeTwoA_factored w)))
  have hR : qpow w 22 *
      ((31031 : Q') *
        ((144 : Q') + 96 * (x * x) + 16 * ((x * x) * (x * x)))) ≈
      (31031 : Q') * (acN w 3 3 * acN w 3 3) := by
    exact Q'.eqv_trans _
      ((31031 : Q') * (qpow w 22 *
        ((144 : Q') + 96 * (x * x) + 16 * ((x * x) * (x * x))))) _
      (Q'.eqv_symm (move_common 31031 (qpow w 22)
        ((144 : Q') + 96 * (x * x) + 16 * ((x * x) * (x * x)))))
      (Q'.mul_eqv_congr_left 31031 _ _ (Q'.eqv_symm (modeTwoM_factored w)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hR))

private theorem modeTwo_anchor_ratio :
    (76832 : Q') * (acN wH 3 2 * acN wH 3 4) ≈
      (31031 : Q') * (acN wH 3 3 * acN wH 3 3) := by
  decide

/-- The complete `s = 2` member of `CrossRatioMonotone.cross`, uniformly on
the full exact-rational interval `[0,wH]`. -/
theorem cross_mode_two {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (acN w 3 2 * acN w 3 4) * (acN wH 3 3 * acN wH 3 3) ≤
      (acN wH 3 2 * acN wH 3 4) * (acN w 3 3 * acN w 3 3) := by
  let Aw := acN w 3 2 * acN w 3 4
  let Mw := acN w 3 3 * acN w 3 3
  let AH := acN wH 3 2 * acN wH 3 4
  let MH := acN wH 3 3 * acN wH 3 3
  have hMH : (0 : Q') ≤ MH := Q'.mul_nonneg _ _
    (acN_nonneg (by decide) 3 3) (acN_nonneg (by decide) 3 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ MH
    (modeTwo_scaled_ratio hw0 hwH) hMH
  have hL : ((76832 : Q') * Aw) * MH ≈
      (76832 : Q') * (Aw * MH) := Q'.mul_assoc_eqv _ _ _
  have hR : ((31031 : Q') * Mw) * MH ≈
      (76832 : Q') * (AH * Mw) := by
    refine Q'.eqv_trans _ ((31031 : Q') * (Mw * MH)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((31031 : Q') * (MH * Mw)) _
      (Q'.mul_eqv_congr_left 31031 _ _ (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ (((31031 : Q') * MH) * Mw) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ (((76832 : Q') * AH) * Mw) _
      (Q'.mul_eqv_congr_right _ _ Mw (Q'.eqv_symm modeTwo_anchor_ratio)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have h76832 : (76832 : Q') * (Aw * MH) ≤
      (76832 : Q') * (AH * Mw) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hR))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos (by decide) h76832

end YMGap.Continuum.CoreBModeTwo

#print axioms YMGap.Continuum.CoreBModeTwo.modeTwoA_formula
#print axioms YMGap.Continuum.CoreBModeTwo.modeTwoM_formula
#print axioms YMGap.Continuum.CoreBModeTwo.cross_mode_two
