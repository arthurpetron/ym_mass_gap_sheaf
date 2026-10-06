/-
# Shifted H1 from backward-window survival (moment-only compiler)

Companion to `audits/AUDIT-SHIFTED-WINDOW-SURVIVAL-2026-10-06.md`.

On the completed carrier, `R(k) = B(x, T^k x) = mixedMoment x k 0` and the
one-step energy at lag `k` is `e(k) = R(k) - R(k+1) = mixedMoment x k 1`.
The exact Hausdorff split `m(k,l) = m(k+1,l) + m(k,l+1)` together with
`m(k,2) ≥ 0` makes `e` NONINCREASING. This is convexity of `R`, which is
weaker than log-convexity and needs no spectral measure, `exp` or `log`.
Hence for `p + n = s`:

  `R(p) ≥ R(s+1) + (n+1)·e(s)`                         (`window_telescope`)

and a BACKWARD-window survival `θ R(p) ≤ R(s+1)`, with `0 < θ ≤ 1`, gives

  `θ (n+1) (R(s) - R(s+1)) ≤ (1-θ) R(s+1) ≤ (1-θ) R(s)`  (`window_energy_bound`),

which is the cleared H1 shape (`window_epsBound`).

Path form: with `p = side_j/2` and `n = side_j - side_j/2`,
`PathShiftedWindowSurvival tr θ`
(`θ R_j(side_j/2) ≤ R_j(side_j+1)` for `j ≥ 1`) gives `PathShiftedEpsBound tr c0`
whenever `2(1-θ) ≤ θ c0` and `1 ≤ c0` (`pathShiftedEpsBound_of_windowSurvival`).
With `PathShiftedNondegenerate` this yields the full A03 package
(`path_normalized_anchor_of_windowSurvival`).

The FORWARD ratio `R(2s) ≥ θ R(s)` cannot replace the backward window. Every
`q_k = R(k+1)/R(k) ≤ 1`, so forward survival gives only `q_s ≥ θ`, an O(1)
eps bound. The two-mode sequence `R(n) = 1 + 2^(s-n)` has `R(2s) ≥ R(s)/2`
and `s(1 - q_s) = s/4`. See the audit.

No `sorry`, no axioms.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor

namespace YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (mixedMoment mixedMoment_nonnegative mixedMoment_split)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory.DyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (OneStepEpsBound PathShiftedEpsBound PathShiftedNondegenerate ShiftedAnchorPackage
   pathShiftedEpsBound_iff_response path_normalized_anchor_shifted)

local infix:50 " ≈ " => Q'.eqv

/-! ## Local helpers -/

private theorem ws_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.eqv_of_eq (Q'.zero_add' (A.approx n)))))

private theorem ws_sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem ws_sub_le_self {a b : RC} (hb : RCnonneg b) : RCle (RCsub a b) a := by
  have h := RCadd_le_add (RCle_refl (RCsub a b)) hb
  rwa [ws_add_zero, ws_sub_add_cancel] at h

private theorem ws_add_assoc (a b c : RC) : RCadd a (RCadd b c) = RCadd (RCadd a b) c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.var 1) (.var 2))) (.add (.add (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => A.approx n | 1 => B'.approx n | _ => C.approx n)))

private theorem ws_add_cancel_left (a b : RC) : RCadd (RCadd a b) (RCneg a) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem ws_add_sub_left (a b : RC) : RCsub (RCadd a b) a = b :=
  ws_add_cancel_left a b

private theorem ws_scale_add (q : Q') (a b : RC) :
    RCscale q (RCadd a b) = RCadd (RCscale q a) (RCscale q b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.var 2)))
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => q | 1 => A.approx n | _ => B'.approx n)))

private theorem ws_scale_add_one (q : Q') (a : RC) :
    RCscale (q + 1) a = RCadd (RCscale q a) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.const 1)) (.var 1))
      (.add (.mul (.var 0) (.var 1)) (.var 1))
      (by decide) (fun | 0 => q | _ => A.approx n)))

private theorem ws_ofNat_succ (k : Nat) : Q'.ofNat (k + 1) ≈ Q'.ofNat k + 1 :=
  Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv k 1)
    (Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1 (Q'.eqv_of_eq rfl))

private theorem ws_scale_succ (k : Nat) (a : RC) :
    RCscale (Q'.ofNat (k+1)) a = RCadd (RCscale (Q'.ofNat k) a) a := by
  rw [RCSignedPairBudget.scale_congr (ws_ofNat_succ k), ws_scale_add_one]

private theorem ws_scale_sub (a b : Q') (x : RC) :
    RCscale (a + -b) x = RCsub (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => a | 1 => b | _ => X.approx n)))

private theorem ws_ofNat_pos (L : Nat) (hL : 0 < L) : (0 : Q') < Q'.ofNat L := by
  change (0 : Int)*1 < (L : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ws_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ws_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ws_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem ws_scale_cancel {k : Q'} (hk : (0 : Q') < k) {a b : RC}
    (h : RCle (RCscale k a) (RCscale k b)) : RCle a b := by
  have h' := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos k hk)) h
  rw [RCscale_RCscale, RCscale_RCscale] at h'
  have e : Q'.recipPos k hk * k ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv k hk)
  rw [RCSignedPairBudget.scale_congr e, RCSignedPairBudget.scale_congr e,
    RCscale_one, RCscale_one] at h'
  exact h'

private theorem ws_one_sub_nonneg {theta : Q'} (h1 : theta ≤ 1) : (0 : Q') ≤ 1 + -theta := by
  have h' := Q'.add_le_add_right _ _ (-theta) h1
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv theta)) h'

/-- Scalar bookkeeping for the path window `p = S/2`, `n = S - S/2`. -/
private theorem ws_coeff (S n : Nat) (hS : S ≤ 2*(n+1)) (theta c0 : Q') (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) :
    Q'.ofNat S * (1 + -theta) ≤ theta * Q'.ofNat (n+1) * c0 := by
  have hd := ws_one_sub_nonneg h1
  have a1 : Q'.ofNat S * (1 + -theta) ≤ Q'.ofNat (2*(n+1)) * (1 + -theta) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (ws_ofNat_le hS) hd
  have a2 : Q'.ofNat (2*(n+1)) * (1 + -theta) ≈
      Q'.ofNat (n+1) * ((1 + -theta) * Q'.ofNat 2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ws_ofNat_mul 2 (n+1)))
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
        (fun | 0 => Q'.ofNat 2 | 1 => Q'.ofNat (n+1) | _ => 1 + -theta))
  have a3 : Q'.ofNat (n+1) * ((1 + -theta) * Q'.ofNat 2) ≤ Q'.ofNat (n+1) * (theta * c0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hc0 (ws_ofNat_nonneg _)
  have a4 : Q'.ofNat (n+1) * (theta * c0) ≈ theta * Q'.ofNat (n+1) * c0 :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => Q'.ofNat (n+1) | 1 => theta | _ => c0)
  exact Q'.le_trans' _ _ _ a1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv a2)
    (Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv a4)))

/-! ## 1. Moment-only compiler on an arbitrary carrier vector -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "MM" => mixedMoment hw0 hw1

/-- **Convexity.** The lag-`k` one-step energy `e(k) = m(k,1)` is nonincreasing. -/
theorem window_energy_antitone (x : V) : ∀ n k : Nat, RCle (MM x (k+n) 1) (MM x k 1)
  | 0, _ => RCle_refl _
  | n+1, k => by
      have hs := mixedMoment_split hw0 hw1 x (k+n) 1
      have h0 := mixedMoment_nonnegative hw0 hw1 x (k+n) 2
      have hle : RCle (MM x (k+n+1) 1) (MM x (k+n) 1) := by
        rw [hs]
        have h := RCadd_le_add (RCle_refl (MM x (k+n+1) 1)) h0
        rwa [ws_add_zero] at h
      exact RCle_trans hle (window_energy_antitone x n k)

/-- **Backward telescope.** `R(p+n+1) + (n+1)·e(p+n) ≤ R(p)`. -/
theorem window_telescope (x : V) : ∀ n p : Nat,
    RCle (RCadd (MM x (p+n+1) 0) (RCscale (Q'.ofNat (n+1)) (MM x (p+n) 1))) (MM x p 0)
  | 0, p => by
      have hs := mixedMoment_split hw0 hw1 x p 0
      show RCle (RCadd (MM x (p+1) 0) (RCscale (Q'.ofNat 1) (MM x p 1))) (MM x p 0)
      have e1 : RCscale (Q'.ofNat 1) (MM x p 1) = MM x p 1 := RCscale_one _
      rw [e1, hs]
      exact RCle_refl _
  | n+1, p => by
      have ih := window_telescope x n (p+1)
      have hanti := window_energy_antitone hw0 hw1 width x (1+n) p
      have hs := mixedMoment_split hw0 hw1 x p 0
      rw [show p + (1+n) = p+1+n by omega] at hanti
      rw [show p + (n+1) = p+1+n by omega, ws_scale_succ, ws_add_assoc, hs]
      exact RCadd_le_add ih hanti

/-- **Window energy bound.** If `θ R(p) ≤ R(p+n+1)` with `0 ≤ θ ≤ 1`, then
`θ (n+1) e(p+n) ≤ (1-θ) R(p+n)`. -/
theorem window_energy_bound (x : V) (p n : Nat) (theta : Q')
    (h0 : (0 : Q') ≤ theta) (h1 : theta ≤ 1)
    (hsurv : RCle (RCscale theta (MM x p 0)) (MM x (p+n+1) 0)) :
    RCle (RCscale (theta * Q'.ofNat (n+1)) (MM x (p+n) 1))
      (RCscale (1 + -theta) (MM x (p+n) 0)) := by
  have ht := window_telescope hw0 hw1 width x n p
  have h2 := RCle_trans (RCscale_mono h0 ht) hsurv
  rw [ws_scale_add, RCscale_RCscale] at h2
  have h3 := RCadd_le_add h2 (RCle_refl (RCneg (RCscale theta (MM x (p+n+1) 0))))
  rw [ws_add_cancel_left] at h3
  have e5 : RCscale (1 + -theta) (MM x (p+n+1) 0) =
      RCadd (MM x (p+n+1) 0) (RCneg (RCscale theta (MM x (p+n+1) 0))) := by
    show RCscale (1 + -theta) (MM x (p+n+1) 0) =
      RCsub (MM x (p+n+1) 0) (RCscale theta (MM x (p+n+1) 0))
    rw [ws_scale_sub, RCscale_one]
  rw [← e5] at h3
  have hmono : RCle (MM x (p+n+1) 0) (MM x (p+n) 0) := by
    have hs := mixedMoment_split hw0 hw1 x (p+n) 0
    have hn := mixedMoment_nonnegative hw0 hw1 x (p+n) 1
    rw [hs]
    have h := RCadd_le_add (RCle_refl (MM x (p+n+1) 0)) hn
    rwa [ws_add_zero] at h
  exact RCle_trans h3 (RCscale_mono (ws_one_sub_nonneg h1) hmono)

/-- **Window survival ⟹ cleared eps bound at lag `s`.** If `p + n = s`,
`0 < θ ≤ 1`, `θ R(p) ≤ R(s+1)` and `L (1-θ) ≤ θ (n+1) c0`, then
`L (R(s) - R(s+1)) ≤ c0 R(s)`. -/
theorem window_epsBound (x : V) (p n s L : Nat) (hpn : p + n = s) (theta c0 : Q')
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc : Q'.ofNat L * (1 + -theta) ≤ theta * Q'.ofNat (n+1) * c0)
    (hsurv : RCle (RCscale theta (MM x p 0)) (MM x (s+1) 0)) :
    RCle (RCscale (Q'.ofNat L) (RCsub (MM x s 0) (MM x (s+1) 0)))
      (RCscale c0 (MM x s 0)) := by
  subst hpn
  have hs := mixedMoment_split hw0 hw1 x (p+n) 0
  have hE : RCsub (MM x (p+n) 0) (MM x (p+n+1) 0) = MM x (p+n) 1 := by
    rw [hs]
    exact ws_add_sub_left _ _
  rw [hE]
  have hk : (0 : Q') < theta * Q'.ofNat (n+1) :=
    Q'.mul_pos h0 (ws_ofNat_pos (n+1) (Nat.succ_pos n))
  apply ws_scale_cancel hk
  rw [RCscale_RCscale, RCscale_RCscale]
  have hb := window_energy_bound hw0 hw1 width x p n theta (Q'.le_of_lt h0) h1 hsurv
  have hb' := RCscale_mono (ws_ofNat_nonneg L) hb
  rw [RCscale_RCscale, RCscale_RCscale] at hb'
  have hR := mixedMoment_nonnegative hw0 hw1 x (p+n) 0
  have hsc := RCscale_scalar_mono hc hR
  rw [RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv (theta * Q'.ofNat (n+1)) (Q'.ofNat L))]
  exact RCle_trans hb' hsc

/-- Lag-0 / `L = 1` triviality: `1·(B(x,x) - B(x,Tx)) ≤ c0 B(x,x)` once `1 ≤ c0`. -/
theorem oneStepEpsBound_one (x : V) (c0 : Q') (hc : (1 : Q') ≤ c0) :
    OneStepEpsBound hw0 hw1 width x 1 c0 := by
  unfold OneStepEpsBound
  have hnn : RCnonneg (B x (T 1 x)) := mixedMoment_nonnegative hw0 hw1 x 1 0
  have h := ws_sub_le_self (a := B x x) hnn
  have hB := completedInner_nonnegative hw0 hw1 x
  have hsc := RCscale_scalar_mono hc hB
  rw [RCscale_one] at hsc
  have e1 : RCscale (Q'.ofNat 1) (RCsub (B x x) (B x (T 1 x))) =
      RCsub (B x x) (B x (T 1 x)) := RCscale_one _
  rw [e1]
  exact RCle_trans h hsc

end Generic

/-! ## 2. The reduced path Prop and the path theorems -/

/-- **Backward-window survival (OPEN).** For `j ≥ 1`:
`θ R_j(side_j/2) ≤ R_j(side_j + 1)`, i.e. survival of the `T^(side_j/4)`-shifted
anchor over `side_j/2 + 1` steps. -/
def PathShiftedWindowSurvival (tr : DyadicSmoothedTrajectory) (theta : Q') : Prop :=
  ∀ j, 1 ≤ j → RCle (RCscale theta (tr.response j (side j / 2))) (tr.response j (side j + 1))

/-- Unshifted lag survival `θ R_j(0) ≤ R_j(side_j + 1)` (STRONGER; heuristically
false for box-smoothed local families, see audit). -/
def PathLagSurvival (tr : DyadicSmoothedTrajectory) (theta : Q') : Prop :=
  ∀ j, 1 ≤ j → RCle (RCscale theta (tr.response j 0)) (tr.response j (side j + 1))

/-- Unshifted lag survival implies backward-window survival (monotone `R`). -/
theorem pathShiftedWindowSurvival_of_lagSurvival (tr : DyadicSmoothedTrajectory) (theta : Q')
    (h0 : (0 : Q') ≤ theta) (H : PathLagSurvival tr theta) :
    PathShiftedWindowSurvival tr theta := by
  intro j hj
  have hR := response_le_of_le (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (tr.state j) (Nat.zero_le (side j / 2))
  exact RCle_trans (RCscale_mono h0 hR) (H j hj)

/-- **Compiler, path form.** Backward-window survival with `0 < θ ≤ 1`,
`2(1-θ) ≤ θ c0` and `1 ≤ c0` gives the shifted H1 with constant `c0`. -/
theorem pathShiftedEpsBound_of_windowSurvival (tr : DyadicSmoothedTrajectory) (c0 theta : Q')
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (Hw : PathShiftedWindowSurvival tr theta) : PathShiftedEpsBound tr c0 := by
  intro j
  match j with
  | 0 =>
      exact oneStepEpsBound_one (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0)
        (trajWidth 0) _ c0 hc1
  | j+1 =>
      have hj : 1 ≤ j+1 := Nat.succ_pos j
      rw [pathShiftedEpsBound_iff_response tr c0 (j+1) hj]
      have hpn : side (j+1) / 2 + (side (j+1) - side (j+1) / 2) = side (j+1) := by omega
      have hS : side (j+1) ≤ 2 * ((side (j+1) - side (j+1) / 2) + 1) := by omega
      exact window_epsBound (tr.schedule.nome_pos (j+1)) (tr.schedule.nome_lt_one (j+1))
        (trajWidth (j+1)) (tr.state (j+1)) (side (j+1) / 2) (side (j+1) - side (j+1) / 2)
        (side (j+1)) (side (j+1)) hpn theta c0 h0 h1
        (ws_coeff (side (j+1)) (side (j+1) - side (j+1) / 2) hS theta c0 h1 hc0)
        (Hw (j+1) hj)

/-- **Shifted A03 package from backward-window survival.** -/
theorem path_normalized_anchor_of_windowSurvival (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : PathShiftedWindowSurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl) :
    ShiftedAnchorPackage tr delta hdelta a fl hfl :=
  path_normalized_anchor_shifted tr c0 delta a ha hdelta0 hdelta hcd fl hfl
    (pathShiftedEpsBound_of_windowSurvival tr c0 theta h0 h1 hc0 hc1 Hw) Hnd

#print axioms window_energy_antitone
#print axioms window_telescope
#print axioms window_energy_bound
#print axioms window_epsBound
#print axioms oneStepEpsBound_one
#print axioms PathShiftedWindowSurvival
#print axioms PathLagSurvival
#print axioms pathShiftedWindowSurvival_of_lagSurvival
#print axioms pathShiftedEpsBound_of_windowSurvival
#print axioms path_normalized_anchor_of_windowSurvival

end YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival
