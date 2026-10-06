/-
# Even-lag step ratio = lag-0 energy bound on the propagated state (REFORMULATION ONLY)

Companion to `audits/AUDIT-STEP-RATIO-WINDOW-SURVIVAL-2026-10-06.md` §13. ADDITIVE.

THIS IS A REFORMULATION ONLY. It makes NO progress on the open input, which is a bounded
intermediate-lag step-ratio rate. It restates the same input in an equivalent form.

* `propagated_response`: by self-adjointness of `T`,
  `B(φ, T^n φ) = R_ψ(2m+n)` where `φ = T^m ψ`. This is the existing `shift_response_pin`
  with the index order swapped.
* So the step ratio of `R_ψ` at the EVEN lag `2m` is the lag-0 Rayleigh ratio of `φ`.
* Multiplied-out lag-0 energy bound, with no division:
  `side·(B(φ,φ) − B(φ,Tφ)) ≤ c·B(φ,φ)`. This is literally `OneStepEpsBound φ side c`.
* `stepRatio_of_energy` (`L ≥ 1`): energy `c` ⇒ ratio `ρ' = 1 − c/L`, and `L(1−ρ') = c` exactly.
* `energy_of_stepRatio`: ratio `ρ'` with `L(1−ρ') ≤ c` ⇒ energy `c`.
  Together these give the equivalence.
* Expr layer: `ExprPropagatedEnergy tr m c j0` uses `φ_j = T^(m_j) Y_j` on the smoothed state.
  * `stepRatio_of_propagatedEnergy`: it gives `ExprStepRatio tr (propagatedRate c j0) (2 m_j)`.
    The rate is `1 − c/side_j` for `j ≥ j0` and `0` below, which is trivial since `R ≥ 0`.
  * `propagatedEnergy_of_stepRatio` is the converse.
* Package: `expr_normalized_anchor_of_hvar_hray_propagatedEnergy_anyC`, built on
  `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC`.
  * `m_j ≤ side_j/4` gives `2 m_j ≤ side_j/2`, using Nat division with no adjustment.
  * It needs `0 ≤ c`, so that `ρ' ≤ 1`.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC

namespace YMGap.Continuum.BF4WilsonAllNomeExprPropagatedEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedTime_zero)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (OneStepEpsBound shift_response_pin)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage (ExprShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
  (expr_normalized_anchor_of_hvar_hray_stepRatio_anyC)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Helpers -/

private theorem pe_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem pe_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem pe_ofNat_pos (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int)*1 < (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem pe_one_sub_nonneg {x : Q'} (h1 : x ≤ 1) : (0 : Q') ≤ (1 : Q') - x :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv x))
    (Q'.add_le_add_right x 1 (-x) h1)

private theorem pe_one_sub_le_one {x : Q'} (h0 : (0 : Q') ≤ x) : (1 : Q') - x ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv ((1 : Q') - x)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left ((1 : Q') - x) 0 x h0)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
        (fun | 0 => (1 : Q') | _ => x))))

private theorem pe_scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem pe_scale_one_sub (x : Q') (a : RC) :
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
private theorem pe_rearrange (a b d : RC) (h : RCle (RCsub a b) d) : RCle (RCsub a d) b := by
  have h' := RCadd_le_add h (RCle_refl (RCsub b d))
  have e1 : RCadd (RCsub a b) (RCsub b d) = RCsub a d := by
    refine Quotient.inductionOn₃ a b d ?_
    intro A B' D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
        (.add (.var 0) (.neg (.var 2))) (by decide)
        (fun | 0 => A.approx n | 1 => B'.approx n | _ => D.approx n)))
  have e2 : RCadd d (RCsub b d) = b := by
    refine Quotient.inductionOn₂ b d ?_
    intro B' D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0) (by decide)
        (fun | 0 => B'.approx n | _ => D.approx n)))
  rw [e1, e2] at h'
  exact h'

/-- `b' ≤ b` ⇒ `a − b ≤ a − b'`. -/
private theorem pe_sub_anti (a b b' : RC) (h : RCle b' b) : RCle (RCsub a b) (RCsub a b') := by
  have h1 := RCadd_le_add (RCadd_le_add (RCle_refl (RCsub a b)) h) (RCle_refl (RCneg b'))
  have e1 : RCadd (RCadd (RCsub a b) b') (RCneg b') = RCsub a b := by
    refine Quotient.inductionOn₃ a b b' ?_
    intro A B' B''
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.add (.var 0) (.neg (.var 1))) (.var 2)) (.neg (.var 2)))
        (.add (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => A.approx n | 1 => B'.approx n | _ => B''.approx n)))
  have e2 : RCadd (RCadd (RCsub a b) b) (RCneg b') = RCsub a b' := by
    refine Quotient.inductionOn₃ a b b' ?_
    intro A B' B''
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.neg (.var 2)))
        (.add (.var 0) (.neg (.var 2))) (by decide)
        (fun | 0 => A.approx n | 1 => B'.approx n | _ => B''.approx n)))
  rw [e1, e2] at h1
  exact h1

/-! ## 1. Generic carrier: shift identity and energy ⇔ ratio -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- **Shift identity** (self-adjointness): `B(T^m ψ, T^n T^m ψ) = R_ψ(2m+n)`. -/
theorem propagated_response (x : V) (m n : Nat) :
    B (T m x) (T n (T m x)) = B x (T (2*m+n) x) := by
  rw [shift_response_pin hw0 hw1 width x m n, Nat.add_comm n (2*m)]

/-- Lag-0 pins of the propagated state: `B(φ,φ) = R(2m)`, `B(φ,Tφ) = R(2m+1)`. -/
theorem propagated_norm (x : V) (m : Nat) : B (T m x) (T m x) = B x (T (2*m) x) := by
  have h := propagated_response hw0 hw1 width x m 0
  rw [completedTime_zero, Nat.add_zero] at h
  exact h

/-- **Energy ⇒ ratio.** `L ≥ 1` and `L(B(x,x) − B(x,Tx)) ≤ c B(x,x)` give
`(1 − c/L) B(x,x) ≤ B(x,Tx)`. -/
theorem stepRatio_of_energy (x : V) (L : Nat) (hL : 0 < L) (c : Q')
    (hE : OneStepEpsBound hw0 hw1 width x L c) :
    RCle (RCscale ((1 : Q') - c * Q'.recipPos (Q'.ofNat L) (pe_ofNat_pos L hL)) (B x x))
      (B x (T 1 x)) := by
  have hr0 := Q'.le_of_lt (Q'.recipPos_pos (Q'.ofNat L) (pe_ofNat_pos L hL))
  have h1 := RCscale_mono hr0 hE
  rw [RCscale_RCscale, RCscale_RCscale,
    RCSignedPairBudget.scale_congr (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv (Q'.ofNat L) (pe_ofNat_pos L hL))),
    RCscale_one, RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv _ c)] at h1
  rw [pe_scale_one_sub]
  exact pe_rearrange _ _ _ h1

/-- **Ratio ⇒ energy.** `ρ B(x,x) ≤ B(x,Tx)` and `L(1−ρ) ≤ c` give the energy bound. -/
theorem energy_of_stepRatio (x : V) (L : Nat) (rho c : Q')
    (hR : RCle (RCscale rho (B x x)) (B x (T 1 x)))
    (hc : Q'.ofNat L * ((1 : Q') - rho) ≤ c) :
    OneStepEpsBound hw0 hw1 width x L c := by
  unfold OneStepEpsBound
  have h1 := pe_sub_anti (B x x) _ _ hR
  rw [← pe_scale_one_sub] at h1
  have h2 := RCscale_mono (pe_ofNat_nonneg L) h1
  rw [RCscale_RCscale] at h2
  exact RCle_trans h2 (RCscale_scalar_mono hc (completedInner_nonnegative hw0 hw1 x))

/-- `L(1 − (1 − c/L)) ≤ c` (indeed `= c`). -/
theorem energy_rate_side (L : Nat) (hL : 0 < L) (c : Q') :
    Q'.ofNat L * ((1 : Q') - ((1 : Q') - c * Q'.recipPos (Q'.ofNat L) (pe_ofNat_pos L hL))) ≤ c :=
  Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.var 1) (.add (.var 0) (.neg (.add (.var 0) (.neg (.mul (.var 2) (.var 3)))))))
      (.mul (.var 2) (.mul (.var 1) (.var 3))) (by decide)
      (fun | 0 => (1 : Q') | 1 => Q'.ofNat L | 2 => c
           | _ => Q'.recipPos (Q'.ofNat L) (pe_ofNat_pos L hL)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_recipPos_eqv (Q'.ofNat L) (pe_ofNat_pos L hL))) (Q'.mul_one_eqv c)))

end Generic

/-! ## 2. Expr layer -/

/-- **Propagated lag-0 energy (OPEN, = the even-lag step-ratio input).** For `j ≥ j0`, `j ≥ 1`:
`side_j (B(φ_j,φ_j) − B(φ_j,Tφ_j)) ≤ c B(φ_j,φ_j)`, `φ_j = T^(m_j) Y_j` (smoothed state). -/
def ExprPropagatedEnergy (tr : ExprAnchorTrajectory) (m : Nat → Nat) (c : Q') (j0 : Nat) : Prop :=
  ∀ j, j0 ≤ j → 1 ≤ j →
    OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (m j) (tr.state j))
      (side j) c

/-- The induced step-ratio rate: `1 − c/side_j` for `j ≥ j0`, `0` below. -/
def propagatedRate (c : Q') (j0 j : Nat) : Q' :=
  if j0 ≤ j then (1 : Q') - c * Q'.recipPos (Q'.ofNat (side j)) (pe_ofNat_pos _ (side_positive j))
  else 0

/-- **Energy ⇒ `ExprStepRatio` at the even lags `2 m_j`.** -/
theorem stepRatio_of_propagatedEnergy (tr : ExprAnchorTrajectory) (m : Nat → Nat) (c : Q')
    (j0 : Nat) (HE : ExprPropagatedEnergy tr m c j0) :
    ExprStepRatio tr (propagatedRate c j0) (fun j => 2 * m j) := by
  intro j hj
  show RCle (RCscale (propagatedRate c j0 j) (tr.response j (2 * m j)))
    (tr.response j (2 * m j + 1))
  rcases Nat.lt_or_ge j j0 with h | h
  · rw [propagatedRate, if_neg (by omega), pe_scale_zero]
    exact response_nonnegative (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (tr.state j) (2 * m j + 1)
  · rw [propagatedRate, if_pos h]
    have hs := stepRatio_of_energy (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) _ (side j) (side_positive j) c (HE j h hj)
    rw [propagated_norm, propagated_response] at hs
    exact hs

/-- **`ExprStepRatio` at the even lags ⇒ energy** (converse; with `side_j(1−ρ'_j) ≤ c`). -/
theorem propagatedEnergy_of_stepRatio (tr : ExprAnchorTrajectory) (rho' : Nat → Q')
    (m : Nat → Nat) (c : Q') (j0 : Nat) (H : ExprStepRatio tr rho' (fun j => 2 * m j))
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c) :
    ExprPropagatedEnergy tr m c j0 := by
  intro j hj hj1
  have hR : RCle (RCscale (rho' j) (tr.response j (2 * m j))) (tr.response j (2 * m j + 1)) :=
    H j hj1
  apply energy_of_stepRatio (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j) _
    (side j) (rho' j) c _ (hc j hj)
  rw [propagated_norm, propagated_response]
  exact hR

theorem propagatedRate_side (c : Q') (j0 j : Nat) (hj : j0 ≤ j) :
    Q'.ofNat (side j) * ((1 : Q') - propagatedRate c j0 j) ≤ c := by
  rw [propagatedRate, if_pos hj]
  exact energy_rate_side (side j) (side_positive j) c

theorem propagatedRate_le_one (c : Q') (hc0 : (0 : Q') ≤ c) (j0 j : Nat) (hj : j0 ≤ j) :
    propagatedRate c j0 j ≤ 1 := by
  rw [propagatedRate, if_pos hj]
  exact pe_one_sub_le_one (Q'.mul_nonneg _ _ hc0
    (Q'.le_of_lt (Q'.recipPos_pos _ _)))

theorem propagatedRate_nonneg (c : Q') (j0 j : Nat)
    (hcs : j0 ≤ j → c ≤ Q'.ofNat (side j)) : (0 : Q') ≤ propagatedRate c j0 j := by
  rcases Nat.lt_or_ge j j0 with h | h
  · rw [propagatedRate, if_neg (by omega)]
    exact Q'.le_refl' _
  · rw [propagatedRate, if_pos h]
    exact pe_one_sub_nonneg (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hcs h) (Q'.le_of_lt (Q'.recipPos_pos _ _)))
      (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ _)))

/-- **Package corollary (reformulated input).** H-var + H-ray (any `ρ_j > 0`) for
nondegeneracy, and the propagated lag-0 energy bound `ExprPropagatedEnergy tr m c j0` with
`m_j ≤ side_j/4` and `0 ≤ c ≤ C` for survival. Same constants and side conditions as
`expr_normalized_anchor_of_hvar_hray_stepRatio_anyC`. REFORMULATION ONLY. -/
theorem expr_normalized_anchor_of_hvar_hray_propagatedEnergy_anyC (tr : ExprAnchorTrajectory)
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hc0 : (0 : Q') ≤ c)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho)
    (m : Nat → Nat) (hm : ∀ j, 1 ≤ j → m j ≤ side j / 4)
    (HE : ExprPropagatedEnergy tr m c j0) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
      (exprNondegFloor_pos tr v rho Hv Hr) :=
  expr_normalized_anchor_of_hvar_hray_stepRatio_anyC tr c delta C j0 a ha hC hcC hj0 hj0'
    hdelta0 hdelta hcd v rho Hv Hr (propagatedRate c j0) (fun j => 2 * m j)
    (fun j _ => propagatedRate_nonneg c j0 j (fun h => Q'.le_trans' _ _ _ hcC
      (pe_ofNat_le (Nat.le_trans (by omega : C ≤ 2*C)
        (Nat.le_trans hj0 (Nat.pow_le_pow_right (by decide) h))))))
    (fun j h => propagatedRate_le_one c hc0 j0 j h)
    (fun j hj => by show 2 * m j ≤ side j / 2; have := hm j hj; omega)
    (fun j h => propagatedRate_side c j0 j h)
    (stepRatio_of_propagatedEnergy tr m c j0 HE)

#print axioms propagated_response
#print axioms propagated_norm
#print axioms stepRatio_of_energy
#print axioms energy_of_stepRatio
#print axioms energy_rate_side
#print axioms ExprPropagatedEnergy
#print axioms stepRatio_of_propagatedEnergy
#print axioms propagatedEnergy_of_stepRatio
#print axioms propagatedRate_side
#print axioms propagatedRate_le_one
#print axioms propagatedRate_nonneg
#print axioms expr_normalized_anchor_of_hvar_hray_propagatedEnergy_anyC

end YMGap.Continuum.BF4WilsonAllNomeExprPropagatedEnergy
