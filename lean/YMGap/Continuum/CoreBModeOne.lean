/-
# Core-B mode-one cross-ratio prefix

This file proves the `s = 1` member of `CrossRatioMonotone.cross` uniformly
for every exact rational coupling `0 ≤ w ≤ wH`.  The finite
autoconvolutions are evaluated exactly, and the remaining one-variable
inequality is signed by the factorization

  100 (16 + 24 x + 9 x²) - 361 x (24 + 16 x²)
    = 4 (1 - 4 x) (361 x² + 34 x + 400),

at `x = w² ∈ [0,1/4]`.
-/

import YMGap.Continuum.CoreBModePrefix
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBModeOne

set_option maxHeartbeats 2000000

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

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

private theorem mul_eqv_congr₂ {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem acN_two_one (w : Q') :
    acN w 2 1 ≈ (4 : Q') * qpow w 3 := by
  have h01 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 1
  have h10 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 0
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero, Nat.sub_self]
  refine Q'.eqv_trans _
    ((0 : Q') + ((2 : Q') * qpow w 3) + ((2 : Q') * qpow w 3)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h01))
      (by simpa only [c4] using h10)
  · refine Q'.eqv_trans _
      ((2 : Q') * qpow w 3 + 2 * qpow w 3) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' ((2 : Q') * qpow w 3)))
    · refine Q'.eqv_trans _ (((2 : Q') + 2) * qpow w 3) _
        (Q'.eqv_symm (Q'.add_mul_eqv 2 2 (qpow w 3))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)

private theorem acN_two_two (w : Q') :
    acN w 2 2 ≈ (4 : Q') * qpow w 6 + (3 : Q') * qpow w 8 := by
  have h02 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 2
  have h11 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 1
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero, Nat.sub_self]
  refine Q'.eqv_trans _
    ((0 : Q') + ((3 : Q') * qpow w 8) + ((4 : Q') * qpow w 6)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h02))
      (by simpa only [c4] using h11)
  · refine Q'.eqv_trans _
      ((3 : Q') * qpow w 8 + (4 : Q') * qpow w 6) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' ((3 : Q') * qpow w 8)))
    · exact Q'.add_comm_eqv _ _

private theorem acN_two_three (w : Q') :
    acN w 2 3 ≈ (6 : Q') * qpow w 11 + (4 : Q') * qpow w 15 := by
  have h03 := LaplaceMarginDeep.coeffW_mul_ofNat w 0 3
  have h12 := LaplaceMarginDeep.coeffW_mul_ofNat w 1 2
  unfold acN
  simp only [fsum_succ, fsum_zero, Nat.sub_zero]
  refine Q'.eqv_trans _
    ((0 : Q') + ((4 : Q') * qpow w 15) + ((6 : Q') * qpow w 11)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left 0 _ _ (by simpa only [c4] using h03))
      (by simpa only [c4] using h12)
  · refine Q'.eqv_trans _
      ((4 : Q') * qpow w 15 + (6 : Q') * qpow w 11) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' ((4 : Q') * qpow w 15)))
    · exact Q'.add_comm_eqv _ _

/-- Exact mode-one off-diagonal product. -/
theorem modeOneA_formula (w : Q') :
    acN w 2 1 * acN w 2 3 ≈
      (24 : Q') * qpow w 14 + (16 : Q') * qpow w 18 := by
  refine Q'.eqv_trans _
    (((4 : Q') * qpow w 3) *
      ((6 : Q') * qpow w 11 + (4 : Q') * qpow w 15)) _
    (mul_eqv_congr₂ (acN_two_one w) (acN_two_three w)) ?_
  have h14 := Q'.eqv_symm (qpow_add w 3 11)
  have h18 := Q'.eqv_symm (qpow_add w 3 15)
  refine Q'.eqv_trans _
    (((4 : Q') * 6) * (qpow w 3 * qpow w 11) +
      ((4 : Q') * 4) * (qpow w 3 * qpow w 15)) _ (by ring_qeqv) ?_
  exact Q'.add_eqv_congr'
    (mul_eqv_congr₂ (by decide) h14)
    (mul_eqv_congr₂ (by decide) h18)

/-- Exact mode-one diagonal square. -/
theorem modeOneM_formula (w : Q') :
    acN w 2 2 * acN w 2 2 ≈
      (16 : Q') * qpow w 12 + (24 : Q') * qpow w 14 +
        (9 : Q') * qpow w 16 := by
  refine Q'.eqv_trans _
    (((4 : Q') * qpow w 6 + (3 : Q') * qpow w 8) *
      ((4 : Q') * qpow w 6 + (3 : Q') * qpow w 8)) _
    (mul_eqv_congr₂ (acN_two_two w) (acN_two_two w)) ?_
  have h12 := Q'.eqv_symm (qpow_add w 6 6)
  have h14a := Q'.eqv_symm (qpow_add w 6 8)
  have h14b := Q'.eqv_symm (qpow_add w 8 6)
  have h16 := Q'.eqv_symm (qpow_add w 8 8)
  refine Q'.eqv_trans _
    (((4 : Q') * 4) * (qpow w 6 * qpow w 6) +
      ((4 : Q') * 3) * (qpow w 6 * qpow w 8) +
      ((3 : Q') * 4) * (qpow w 8 * qpow w 6) +
      ((3 : Q') * 3) * (qpow w 8 * qpow w 8)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    ((16 : Q') * qpow w 12 + (12 : Q') * qpow w 14 +
      (12 : Q') * qpow w 14 + (9 : Q') * qpow w 16) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (mul_eqv_congr₂ (by decide) h12)
          (mul_eqv_congr₂ (by decide) h14a))
        (mul_eqv_congr₂ (by decide) h14b))
      (mul_eqv_congr₂ (by decide) h16)
  · refine Q'.eqv_trans _
      ((16 : Q') * qpow w 12 + (((12 : Q') + 12) * qpow w 14) +
        (9 : Q') * qpow w 16) _ (by ring_qeqv) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left ((16 : Q') * qpow w 12) _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide)))

private def factorLHS : RingNormaliser.PolyExpr :=
  .add
    (.mul (.const 100)
      (.add (.add (.const 16) (.mul (.const 24) (.var 0)))
        (.mul (.const 9) (.mul (.var 0) (.var 0)))))
    (.neg (.mul (.const 361)
      (.mul (.var 0)
        (.add (.const 24) (.mul (.const 16) (.mul (.var 0) (.var 0)))))))

private def factorRHS : RingNormaliser.PolyExpr :=
  .mul (.const 4)
    (.mul (.add (.const 1) (.neg (.mul (.const 4) (.var 0))))
      (.add
        (.add (.mul (.const 361) (.mul (.var 0) (.var 0)))
          (.mul (.const 34) (.var 0)))
        (.const 400)))

private theorem factor_normal : RingNormaliser.normalize factorLHS =
    RingNormaliser.normalize factorRHS := by
  decide

private theorem modeOne_factorization (x : Q') :
    (100 : Q') * ((16 : Q') + 24 * x + 9 * (x * x)) +
        -((361 : Q') * (x * ((24 : Q') + 16 * (x * x)))) ≈
      (4 : Q') * (((1 : Q') + -(4 * x)) *
        ((361 : Q') * (x * x) + 34 * x + 400)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq factorLHS factorRHS factor_normal
    (fun _ => x)
  simpa [RingNormaliser.eval, factorLHS, factorRHS,
    RingNormaliser.qpow] using h

private theorem qpow_four_as_xsq (w : Q') :
    qpow w 4 ≈ qpow w 2 * qpow w 2 := qpow_add w 2 2

private theorem qpow_six_as_xcube (w : Q') :
    qpow w 6 ≈ qpow w 2 * (qpow w 2 * qpow w 2) := by
  exact Q'.eqv_trans _ _ _ (qpow_add w 2 4)
    (Q'.mul_eqv_congr_left (qpow w 2) _ _ (qpow_four_as_xsq w))

private theorem modeOneA_factored (w : Q') :
    acN w 2 1 * acN w 2 3 ≈
      qpow w 12 * (qpow w 2 *
        ((24 : Q') + 16 * (qpow w 2 * qpow w 2))) := by
  refine Q'.eqv_trans _ _ _ (modeOneA_formula w) ?_
  have h14 : qpow w 14 ≈ qpow w 12 * qpow w 2 := by
    simpa only using qpow_add w 12 2
  have h18a : qpow w 18 ≈ qpow w 12 * qpow w 6 := by
    simpa only using qpow_add w 12 6
  have h18 : qpow w 18 ≈
      qpow w 12 * (qpow w 2 * (qpow w 2 * qpow w 2)) :=
    Q'.eqv_trans _ _ _ h18a
      (Q'.mul_eqv_congr_left (qpow w 12) _ _ (qpow_six_as_xcube w))
  refine Q'.eqv_trans _
    ((24 : Q') * (qpow w 12 * qpow w 2) +
      (16 : Q') * (qpow w 12 *
        (qpow w 2 * (qpow w 2 * qpow w 2)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 24 _ _ h14)
      (Q'.mul_eqv_congr_left 16 _ _ h18)
  · ring_qeqv

private theorem modeOneM_factored (w : Q') :
    acN w 2 2 * acN w 2 2 ≈
      qpow w 12 * ((16 : Q') + 24 * qpow w 2 +
        9 * (qpow w 2 * qpow w 2)) := by
  refine Q'.eqv_trans _ _ _ (modeOneM_formula w) ?_
  have h14 : qpow w 14 ≈ qpow w 12 * qpow w 2 := by
    simpa only using qpow_add w 12 2
  have h16a : qpow w 16 ≈ qpow w 12 * qpow w 4 := by
    simpa only using qpow_add w 12 4
  have h16 : qpow w 16 ≈
      qpow w 12 * (qpow w 2 * qpow w 2) :=
    Q'.eqv_trans _ _ _ h16a
      (Q'.mul_eqv_congr_left (qpow w 12) _ _ (qpow_four_as_xsq w))
  refine Q'.eqv_trans _
    ((16 : Q') * qpow w 12 +
      (24 : Q') * (qpow w 12 * qpow w 2) +
      (9 : Q') * (qpow w 12 * (qpow w 2 * qpow w 2))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left ((16 : Q') * qpow w 12) _ _
        (Q'.mul_eqv_congr_left 24 _ _ h14))
      (Q'.mul_eqv_congr_left 9 _ _ h16)
  · ring_qeqv

private theorem modeOne_scaled_ratio {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (361 : Q') * (acN w 2 1 * acN w 2 3) ≤
      (100 : Q') * (acN w 2 2 * acN w 2 2) := by
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
  have hquad : (0 : Q') ≤
      (361 : Q') * (x * x) + 34 * x + 400 := by
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ hx0 hx0))
        (Q'.mul_nonneg _ _ (by decide) hx0))
      (by decide)
  have hfactorNonneg : (0 : Q') ≤
      (4 : Q') * (((1 : Q') + -(4 * x)) *
        ((361 : Q') * (x * x) + 34 * x + 400)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hlinear hquad)
  have hdiff : (0 : Q') ≤
      (100 : Q') * ((16 : Q') + 24 * x + 9 * (x * x)) +
        -((361 : Q') * (x * ((24 : Q') + 16 * (x * x)))) :=
    Q'.le_trans' _ _ _ hfactorNonneg
      (Q'.le_of_eqv (Q'.eqv_symm (modeOne_factorization x)))
  have hinner : (361 : Q') * (x * ((24 : Q') + 16 * (x * x))) ≤
      (100 : Q') * ((16 : Q') + 24 * x + 9 * (x * x)) :=
    Q'.le_of_sub_nonneg hdiff
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 12) hinner
    (qpow_nonneg w hw0 12)
  have hL : qpow w 12 *
      ((361 : Q') * (x * ((24 : Q') + 16 * (x * x)))) ≈
      (361 : Q') * (acN w 2 1 * acN w 2 3) := by
    exact Q'.eqv_trans _
      ((361 : Q') * (qpow w 12 *
        (x * ((24 : Q') + 16 * (x * x))))) _ (by ring_qeqv)
      (Q'.mul_eqv_congr_left 361 _ _ (Q'.eqv_symm (modeOneA_factored w)))
  have hR : qpow w 12 *
      ((100 : Q') * ((16 : Q') + 24 * x + 9 * (x * x))) ≈
      (100 : Q') * (acN w 2 2 * acN w 2 2) := by
    exact Q'.eqv_trans _
      ((100 : Q') * (qpow w 12 *
        ((16 : Q') + 24 * x + 9 * (x * x)))) _ (by ring_qeqv)
      (Q'.mul_eqv_congr_left 100 _ _ (Q'.eqv_symm (modeOneM_factored w)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hR))

private theorem modeOne_anchor_ratio :
    (361 : Q') * (acN wH 2 1 * acN wH 2 3) ≈
      (100 : Q') * (acN wH 2 2 * acN wH 2 2) := by
  decide

/-- The complete `s = 1` member of `CrossRatioMonotone.cross`, uniformly on
the full exact-rational interval `[0,wH]`. -/
theorem cross_mode_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (acN w 2 1 * acN w 2 3) * (acN wH 2 2 * acN wH 2 2) ≤
      (acN wH 2 1 * acN wH 2 3) * (acN w 2 2 * acN w 2 2) := by
  let Aw := acN w 2 1 * acN w 2 3
  let Mw := acN w 2 2 * acN w 2 2
  let AH := acN wH 2 1 * acN wH 2 3
  let MH := acN wH 2 2 * acN wH 2 2
  have hMH : (0 : Q') ≤ MH := Q'.mul_nonneg _ _
    (acN_nonneg (by decide) 2 2) (acN_nonneg (by decide) 2 2)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ MH
    (modeOne_scaled_ratio hw0 hwH) hMH
  have hL : ((361 : Q') * Aw) * MH ≈
      (361 : Q') * (Aw * MH) := Q'.mul_assoc_eqv _ _ _
  have hR : ((100 : Q') * Mw) * MH ≈
      (361 : Q') * (AH * Mw) := by
    refine Q'.eqv_trans _ ((100 : Q') * (Mw * MH)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ ((100 : Q') * (MH * Mw)) _
      (Q'.mul_eqv_congr_left 100 _ _ (Q'.mul_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _ (((100 : Q') * MH) * Mw) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ (((361 : Q') * AH) * Mw) _
      (Q'.mul_eqv_congr_right _ _ Mw (Q'.eqv_symm modeOne_anchor_ratio)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have h361 : (361 : Q') * (Aw * MH) ≤ (361 : Q') * (AH * Mw) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hR))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos (by decide) h361

end YMGap.Continuum.CoreBModeOne

#print axioms YMGap.Continuum.CoreBModeOne.modeOneA_formula
#print axioms YMGap.Continuum.CoreBModeOne.modeOneM_formula
#print axioms YMGap.Continuum.CoreBModeOne.cross_mode_one
