/-
# Convexity sandwich: early window ⇒ late step ratio (REFORMULATION ONLY)

Companion to `audits/AUDIT-STEP-RATIO-WINDOW-SURVIVAL-2026-10-06.md` §14. ADDITIVE.

THIS IS A REFORMULATION ONLY. It makes NO progress on the open input, which is a bounded
intermediate-lag step-ratio rate (equivalently, a window bound). It shows that the
window and step-ratio forms of that input are equivalent up to a factor-2 lag shift and a
LOSS OF CONSTANTS. The equivalence is not exact.

* `response_diff_antitone`: `D(n) = R(n) − R(n+1)` is nonincreasing. This uses the second
  Hausdorff difference `∇²R(n) = mixedMoment x n 2 ≥ 0`, via
  `mixedMoment_eq_hausdorffDiff` and `mixedMoment_nonnegative_via_hankel`.
* `diff_sandwich` (`m ≤ k`): `(k−m+1)·D(k) ≤ Σ_{i=m}^{k} D(i) = R(m) − R(k+1)`.
  `diff_sandwich_le` adds `R(m) − R(k+1) ≤ R(m)`, since `R ≥ 0`.
* `side_le_four_window`: `s ≤ 4·(s/2 − s/4 + 1)` for every Nat `s`, so
  `s/((s/2 − s/4 + 1)θ) ≤ 4/θ`.
* `lagEnergy_of_window`: `θ R(s/4) ≤ R(s/2)`, `0 ≤ c` and `4 ≤ cθ` give
  `s·(R(s/2) − R(s/2+1)) ≤ c·R(s/2)`. No sign condition on `θ` is needed.
  The smallest admissible `c` is `4/θ` (`four_div_spec`).
* Expr layer, early window ⇒ step ratio:
  `ExprEarlyWindow tr θ j0` (for `j ≥ j0`, `j ≥ 1`) gives
  `ExprStepRatio tr (propagatedRate c j0) (side/2)` (`stepRatio_of_earlyWindow`).
  * The rate is `ρ_j = 1 − c/side_j`, so `side_j(1−ρ_j) = c`.
  * NO CLAMP and no extra hypothesis are needed. Below `j0` the rate is `0`, which is
    trivial since `R ≥ 0`. In the package, `ρ_j ≥ 0` follows from `c ≤ C ≤ side_j`.
* Converse, up to the factor-2 lag shift: `expr_earlyWindow_of_stepRatio_anyC`.
  A step ratio at lag `k_j ≤ side_j/4` with `side_j(1−ρ_j) ≤ c ≤ C` gives
  `ExprEarlyWindow tr θ_C j0`, with `θ_C = (1/2)^(2C+2)`, by block Bernoulli.
* Package: `expr_normalized_anchor_of_hvar_hray_earlyWindow_anyC`, built on
  `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC` at lag `k_j = side_j/2`.
  * Lag `side_j/2` meets the package's `k_j ≤ side_j/2` with equality.
  * Constants: the window `θ` and the package's `θ_C` are DIFFERENT numbers.
    The survival constant is `c ≥ 4/θ`, it must satisfy `c ≤ C`, and the output window
    constant is `θ_C = (1/2)^(2C+2)`.
  * The chain is: step ratio at lag ≤ s/4 ⇒ window [s/4, s/2] ⇒ step ratio at s/2 ⇒
    window [s/2, s+1]. Each arrow loses constants.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprPropagatedEnergy
import YMGap.Continuum.BF4WilsonAllNomeResponseHankelPositivity
import YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BF4WilsonAllNomeExprConvexitySandwich

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_nonnegative response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeResponseHankelPositivity
  (mixedMoment_nonnegative_via_hankel mixedMoment_eq_hausdorffDiff)
open YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
  (response_shifted_step_lower response_shifted_geometric_lower)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage (ExprShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
  (expr_normalized_anchor_of_hvar_hray_stepRatio_anyC block_pow_floor thetaC)
open YMGap.Continuum.BF4WilsonAllNomeExprPropagatedEnergy
  (propagatedRate propagatedRate_side propagatedRate_le_one propagatedRate_nonneg)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Helpers -/

private theorem cs_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem cs_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem cs_ofNat_pos (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int)*1 < (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem cs_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem cs_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem cs_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem cs_sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (C.approx n)))

private theorem cs_le_of_sub_nonneg {a b : RC} (h : RCnonneg (RCsub a b)) : RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [cs_zero_add, cs_sub_add] at h'

private theorem cs_sub_nonneg_of_le {a b : RC} (h : RCle b a) : RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [cs_sub_self] at h'

private theorem cs_sub_le_self (a b : RC) (hb : RCnonneg b) : RCle (RCsub a b) a := by
  apply cs_le_of_sub_nonneg
  have e : RCsub a (RCsub a b) = b := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B'
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1) (by decide)
        (fun | 0 => A.approx n | _ => B'.approx n)))
  rw [e]
  exact hb

private theorem cs_scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem cs_scale_succ (s : Q') (a : RC) :
    RCscale (s + 1) a = RCadd (RCscale s a) a := by
  have e : RCscale (s + 1) a = RCadd (RCscale s a) (RCscale 1 a) := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => s | 1 => (1 : Q') | _ => A.approx n)))
  rw [e, RCscale_one]

private theorem cs_telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | _ => D.approx n)))

private theorem cs_scale_one_sub (x : Q') (a : RC) :
    RCscale ((1 : Q') - x) a = RCsub a (RCscale x a) := by
  have e : RCscale ((1 : Q') - x) a = RCsub (RCscale 1 a) (RCscale x a) := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
        (fun | 0 => (1 : Q') | 1 => x | _ => A.approx n)))
  rw [e, RCscale_one]

/-- `a − b ≤ d` ⇒ `a − d ≤ b`. -/
private theorem cs_rearrange (a b d : RC) (h : RCle (RCsub a b) d) : RCle (RCsub a d) b := by
  have h' := RCadd_le_add h (RCle_refl (RCsub b d))
  rw [cs_telescope] at h'
  have e2 : RCadd d (RCsub b d) = b := by
    refine Quotient.inductionOn₂ b d ?_
    intro B' D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0) (by decide)
        (fun | 0 => B'.approx n | _ => D.approx n)))
  rw [e2] at h'
  exact h'

private theorem cs_pow_antitone (rho : Q') (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) (a : Nat) :
    ∀ d, rho^(a+d) ≤ rho^a
  | 0 => Q'.le_refl' _
  | d+1 => Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right rho 1 (rho^(a+d)) h1 (Q'.pow_nonneg rho h0 (a+d)))
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))
      (cs_pow_antitone rho h0 h1 a d)

private theorem cs_pow_le_of_le (rho : Q') (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) {a b : Nat}
    (hab : a ≤ b) : rho^b ≤ rho^a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact cs_pow_antitone rho h0 h1 a d

/-! ## 1. Scalar facts -/

/-- **Nat-division bound.** `s ≤ 4·(s/2 − s/4 + 1)` for every `s`; hence
`s/((s/2 − s/4 + 1)θ) ≤ 4/θ`. -/
theorem side_le_four_window (s : Nat) : s ≤ 4 * (s/2 - s/4 + 1) := by omega

/-- **Lag-energy ⇒ lag ratio** (pure algebra). `L ≥ 1`, `L(a − b) ≤ c a` ⇒ `(1 − c/L) a ≤ b`. -/
theorem lagRatio_of_lagEnergy (a b : RC) (L : Nat) (hL : 0 < L) (c : Q')
    (hE : RCle (RCscale (Q'.ofNat L) (RCsub a b)) (RCscale c a)) :
    RCle (RCscale ((1 : Q') - c * Q'.recipPos (Q'.ofNat L) (cs_ofNat_pos L hL)) a) b := by
  have hr0 := Q'.le_of_lt (Q'.recipPos_pos (Q'.ofNat L) (cs_ofNat_pos L hL))
  have h1 := RCscale_mono hr0 hE
  rw [RCscale_RCscale, RCscale_RCscale,
    RCSignedPairBudget.scale_congr (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv (Q'.ofNat L) (cs_ofNat_pos L hL))),
    RCscale_one, RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv _ c)] at h1
  rw [cs_scale_one_sub]
  exact cs_rearrange _ _ _ h1

/-- `c = 4/θ` is admissible: `4 ≤ (4/θ)·θ` and `0 ≤ 4/θ` (`θ > 0`). -/
theorem four_div_spec (theta : Q') (hth : (0 : Q') < theta) :
    Q'.ofNat 4 ≤ (Q'.ofNat 4 * Q'.recipPos theta hth) * theta ∧
      (0 : Q') ≤ Q'.ofNat 4 * Q'.recipPos theta hth :=
  ⟨Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.mul (.var 2) (.var 1)))
        (by decide) (fun | 0 => Q'.ofNat 4 | 1 => Q'.recipPos theta hth | _ => theta))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv theta hth))
        (Q'.mul_one_eqv _))),
   Q'.mul_nonneg _ _ (cs_ofNat_nonneg 4) (Q'.le_of_lt (Q'.recipPos_pos theta hth))⟩

/-! ## 2. Generic carrier: convexity sandwich -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- **Convexity.** `D(n+1) ≤ D(n)` for `D(n) = R(n) − R(n+1)`, from `∇²R(n) ≥ 0`
(second Hausdorff difference = `mixedMoment x n 2`). -/
theorem response_diff_antitone (x : V) (n : Nat) :
    RCle (RCsub (B x (T (n+1) x)) (B x (T (n+1+1) x)))
      (RCsub (B x (T n x)) (B x (T (n+1) x))) := by
  have h := mixedMoment_nonnegative_via_hankel hw0 hw1 x n 2
  rw [mixedMoment_eq_hausdorffDiff] at h
  change RCnonneg (RCsub (RCsub (B x (T n x)) (B x (T (n+1) x)))
    (RCsub (B x (T (n+1) x)) (B x (T (n+1+1) x)))) at h
  exact cs_le_of_sub_nonneg h

theorem diff_sandwich_aux (x : V) (m : Nat) : ∀ d : Nat,
    RCle (RCscale (Q'.ofNat (d+1)) (RCsub (B x (T (m+d) x)) (B x (T (m+d+1) x))))
      (RCsub (B x (T m x)) (B x (T (m+d+1) x)))
  | 0 => by
      rw [RCSignedPairBudget.scale_congr (by decide : (Q'.ofNat (0+1)).eqv 1), RCscale_one,
        Nat.add_zero]
      exact RCle_refl _
  | d+1 => by
      have hA := response_diff_antitone hw0 hw1 width x (m+d)
      have hI := diff_sandwich_aux x m d
      show RCle (RCscale (Q'.ofNat (d+1+1))
          (RCsub (B x (T (m+d+1) x)) (B x (T (m+d+1+1) x))))
        (RCsub (B x (T m x)) (B x (T (m+d+1+1) x)))
      rw [RCSignedPairBudget.scale_congr (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (d+1) 1)
          (Q'.add_eqv_congr_left (Q'.ofNat (d+1)) (Q'.ofNat 1) 1 (by decide))),
        cs_scale_succ,
        ← cs_telescope (B x (T m x)) (B x (T (m+d+1) x)) (B x (T (m+d+1+1) x))]
      exact RCadd_le_add (RCle_trans (RCscale_mono (cs_ofNat_nonneg _) hA) hI) (RCle_refl _)

/-- **Convexity sandwich.** `m ≤ k` ⇒ `(k−m+1)(R(k) − R(k+1)) ≤ R(m) − R(k+1)`
(telescoping `Σ_{i=m}^{k} D(i)` with `D` nonincreasing). -/
theorem diff_sandwich (x : V) (m k : Nat) (hmk : m ≤ k) :
    RCle (RCscale (Q'.ofNat (k-m+1)) (RCsub (B x (T k x)) (B x (T (k+1) x))))
      (RCsub (B x (T m x)) (B x (T (k+1) x))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [show m + d - m = d by omega]
  exact diff_sandwich_aux hw0 hw1 width x m d

/-- `(k−m+1)(R(k) − R(k+1)) ≤ R(m)` (`R(k+1) ≥ 0`). -/
theorem diff_sandwich_le (x : V) (m k : Nat) (hmk : m ≤ k) :
    RCle (RCscale (Q'.ofNat (k-m+1)) (RCsub (B x (T k x)) (B x (T (k+1) x))))
      (B x (T m x)) :=
  RCle_trans (diff_sandwich hw0 hw1 width x m k hmk)
    (cs_sub_le_self _ _ (response_nonnegative hw0 hw1 width x (k+1)))

/-- **Early window ⇒ lag-energy at `s/2`.** `θ R(s/4) ≤ R(s/2)`, `0 ≤ c`, `4 ≤ cθ` ⇒
`s (R(s/2) − R(s/2+1)) ≤ c R(s/2)`. -/
theorem lagEnergy_of_window (x : V) (s : Nat) (theta c : Q') (hc0 : (0 : Q') ≤ c)
    (hthc : Q'.ofNat 4 ≤ c * theta)
    (hW : RCle (RCscale theta (B x (T (s/4) x))) (B x (T (s/2) x))) :
    RCle (RCscale (Q'.ofNat s) (RCsub (B x (T (s/2) x)) (B x (T (s/2+1) x))))
      (RCscale c (B x (T (s/2) x))) := by
  have hD : RCnonneg (RCsub (B x (T (s/2) x)) (B x (T (s/2+1) x))) :=
    cs_sub_nonneg_of_le (response_le_of_le hw0 hw1 width x (Nat.le_succ _))
  have h1 := RCscale_scalar_mono (cs_ofNat_le (side_le_four_window s)) hD
  rw [RCSignedPairBudget.scale_congr (cs_ofNat_mul 4 _), ← RCscale_RCscale] at h1
  have h2 := diff_sandwich_le hw0 hw1 width x (s/4) (s/2) (by omega)
  have h3 := RCscale_mono (cs_ofNat_nonneg 4) h2
  have h4 := RCscale_scalar_mono hthc (response_nonnegative hw0 hw1 width x (s/4))
  rw [← RCscale_RCscale] at h4
  have h5 := RCscale_mono hc0 hW
  exact RCle_trans h1 (RCle_trans h3 (RCle_trans h4 h5))

end Generic

/-! ## 3. Expr layer -/

/-- **Early window (OPEN; a reformulation of the step-ratio input).** For `j ≥ j0`, `j ≥ 1`:
`θ R_j(side_j/4) ≤ R_j(side_j/2)` on the smoothed window response. -/
def ExprEarlyWindow (tr : ExprAnchorTrajectory) (theta : Q') (j0 : Nat) : Prop :=
  ∀ j, j0 ≤ j → 1 ≤ j →
    RCle (RCscale theta (tr.response j (side j / 4))) (tr.response j (side j / 2))

/-- **Early window ⇒ step ratio at lag `side_j/2`**, rate `propagatedRate c j0`
(`1 − c/side_j` for `j ≥ j0`, `0` below; no clamp). Needs `0 ≤ c`, `4 ≤ cθ`. -/
theorem stepRatio_of_earlyWindow (tr : ExprAnchorTrajectory) (theta c : Q') (j0 : Nat)
    (hc0 : (0 : Q') ≤ c) (hthc : Q'.ofNat 4 ≤ c * theta) (HW : ExprEarlyWindow tr theta j0) :
    ExprStepRatio tr (propagatedRate c j0) (fun j => side j / 2) := by
  intro j hj
  show RCle (RCscale (propagatedRate c j0 j) (tr.response j (side j / 2)))
    (tr.response j (side j / 2 + 1))
  rcases Nat.lt_or_ge j j0 with h | h
  · rw [propagatedRate, if_neg (by omega), cs_scale_zero]
    exact response_nonnegative (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (tr.state j) (side j / 2 + 1)
  · rw [propagatedRate, if_pos h]
    exact lagRatio_of_lagEnergy _ _ (side j) (side_positive j) c
      (lagEnergy_of_window (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
        (tr.state j) (side j) theta c hc0 hthc (HW j h hj))

/-- **Converse up to the factor-2 lag shift.** A step ratio at lag `k_j ≤ side_j/4` with
`0 ≤ ρ_j ≤ 1` and `side_j(1−ρ_j) ≤ c ≤ C` (for `j ≥ j0`, `2C ≤ side_{j0}`) gives the early
window with `θ_C = (1/2)^(2C+2)` (block Bernoulli). -/
theorem expr_earlyWindow_of_stepRatio_anyC (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (k : Nat → Nat) (c : Q') (C j0 : Nat) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j)
    (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1) (hk : ∀ j, 1 ≤ j → k j ≤ side j / 4)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k) : ExprEarlyWindow tr (thetaC C) j0 := by
  intro j hj hj1
  have hs : 2*C ≤ side j := Nat.le_trans hj0 (Nat.pow_le_pow_right (by decide) hj)
  have hstep := response_shifted_step_lower (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.state j) (rho j) (hrho0 j hj1) (k j) (H j hj1)
  have hmid := hstep (side j / 4 - k j)
  rw [show k j + (side j / 4 - k j) = side j / 4 by have := hk j hj1; omega] at hmid
  have hgeo := response_shifted_geometric_lower (tr.schedule.nome_pos j)
    (tr.schedule.nome_lt_one j) (tr.state j) (rho j) (hrho0 j hj1) (side j / 4) hmid
    (side j / 2 - side j / 4)
  rw [show side j / 4 + (side j / 2 - side j / 4) = side j / 2 by omega] at hgeo
  have hpow : thetaC C ≤ rho j ^ (side j / 2 - side j / 4) :=
    Q'.le_trans' _ _ _
      (block_pow_floor (rho j) c C (side j) hC hs (hrho0 j hj1) (hrho1 j hj) hcC (hc j hj))
      (cs_pow_le_of_le (rho j) (hrho0 j hj1) (hrho1 j hj)
        (by omega : side j / 2 - side j / 4 ≤ side j / 2 + 1))
  exact RCle_trans (RCscale_scalar_mono hpow (response_nonnegative (tr.schedule.nome_pos j)
    (tr.schedule.nome_lt_one j) (tr.width j) (tr.state j) (side j / 4))) hgeo

/-- **Package corollary (reformulated input).** H-var + H-ray (any `ρ_j > 0`) for
nondegeneracy, and the early window `ExprEarlyWindow tr θ j0` with `0 ≤ c`, `4 ≤ cθ`, `c ≤ C`
for survival, at lag `k_j = side_j/2` (meets `k_j ≤ side_j/2` with equality). Other constants
and side conditions as in `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC`. The input
window `θ` and the output `θ_C = (1/2)^(2C+2)` are DIFFERENT numbers (constants are lost).
REFORMULATION ONLY. -/
theorem expr_normalized_anchor_of_hvar_hray_earlyWindow_anyC (tr : ExprAnchorTrajectory)
    (theta c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hc0 : (0 : Q') ≤ c)
    (hthc : Q'.ofNat 4 ≤ c * theta)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (HW : ExprEarlyWindow tr theta j0) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
      (exprNondegFloor_pos tr v rho Hv Hr) :=
  expr_normalized_anchor_of_hvar_hray_stepRatio_anyC tr c delta C j0 a ha hC hcC hj0 hj0'
    hdelta0 hdelta hcd v rho Hv Hr (propagatedRate c j0) (fun j => side j / 2)
    (fun j _ => propagatedRate_nonneg c j0 j (fun h => Q'.le_trans' _ _ _ hcC
      (cs_ofNat_le (Nat.le_trans (by omega : C ≤ 2*C)
        (Nat.le_trans hj0 (Nat.pow_le_pow_right (by decide) h))))))
    (fun j h => propagatedRate_le_one c hc0 j0 j h)
    (fun j _ => Nat.le_refl _)
    (fun j h => propagatedRate_side c j0 j h)
    (stepRatio_of_earlyWindow tr theta c j0 hc0 hthc HW)

#print axioms side_le_four_window
#print axioms lagRatio_of_lagEnergy
#print axioms four_div_spec
#print axioms response_diff_antitone
#print axioms diff_sandwich
#print axioms diff_sandwich_le
#print axioms lagEnergy_of_window
#print axioms ExprEarlyWindow
#print axioms stepRatio_of_earlyWindow
#print axioms expr_earlyWindow_of_stepRatio_anyC
#print axioms expr_normalized_anchor_of_hvar_hray_earlyWindow_anyC

end YMGap.Continuum.BF4WilsonAllNomeExprConvexitySandwich
