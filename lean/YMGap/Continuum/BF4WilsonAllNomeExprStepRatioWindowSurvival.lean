/-
# Window survival from a step-ratio bound (SUFFICIENT condition, Expr layer)

Companion to `audits/AUDIT-STEP-RATIO-WINDOW-SURVIVAL-2026-10-06.md`. ADDITIVE.

The repo has no prior "ray floor ⇒ window survival" theorem. It does have the pieces,
which are reused here and not reproved:
* `response_step_lower` / `response_shifted_step_lower`: a floor `ρ R(k) ≤ R(k+1)` with
  `0 ≤ ρ` propagates to `ρ R(n) ≤ R(n+1)` for every `n ≥ k`. The proof is division-free
  and uses the positivity `B(x, T^n (T-ρ)² x) ≥ 0`, so the case `R(n-1) = 0` never arises.
* `response_shifted_geometric_lower`: `ρ^l R(k) ≤ R(k+l)`.
* `BondMovingRetuneFix.bernoulli_oneSub`: constructive Bernoulli over `Q'`.

Results:
* `bernoulli_pow`: `1 - n(1-ρ) ≤ ρ^n` for `0 ≤ ρ ≤ 1`.
* `expr_window_pow_of_stepRatio`: for `j ≥ 1`, from `ρ_j R_j(k_j) ≤ R_j(k_j+1)` with
  `k_j ≤ side_j/2`, `ρ_j^(side_j/2+1) R_j(side_j/2) ≤ R_j(side_j+1)`.
* **`expr_windowSurvival_of_stepRatio`**: if also `0 ≤ ρ_j ≤ 1` and
  `side_j (1-ρ_j) ≤ c`, then `ExprShiftedWindowSurvival tr (1 - c)`, i.e. θ = 1 - c.
  This uses `side_j/2 + 1 ≤ side_j` for `j ≥ 1`. θ > 0 iff c < 1 (`theta_pos`).

WHICH OBJECT. `ExprStepRatio` is stated on the window response
`R_j(n) = B(Y_j, T^n Y_j)` of the smoothed state `Y_j = tr.state j`, the same `R_j` as in
`ExprShiftedWindowSurvival`. Lag data on the centered vector `x_j` DOES transfer:
* `exprResponse_step_of_lagRatio`: `ρ R_x(k) ≤ R_x(k+1)` ⇒ `ρ R_Y(n) ≤ R_Y(n+1)` for all
  `n ≥ k`, because the box kernel has nonnegative weights and `R_Y(n)` is a
  nonnegative combination of `R_x(m+i+n)`.
* `expr_stepRatio_of_hray`: `ExprHRay tr ρ` (on `x_j`) gives `ExprStepRatio tr ρ 0`.
* `expr_windowSurvival_of_hray`: so `ExprHRay` plus `side_j(1-ρ_j) ≤ c` gives
  window survival with θ = 1 - c.

Compatibility with the gap side:
* `expr_stepRatio_forces_rate_c0`: composing with `expr_windowSurvival_forces_rate_c0`,
  the hypotheses plus nondegeneracy and an orbit contraction `r_j` give
  `side_j (1-r_j) ≤ c0` whenever `2c ≤ (1-c) c0`. This is consistent, not a contradiction.
* `expr_stepRatio_zero_contraction`: lag-0 ratio plus contraction give
  `ρ_j² R_j(0) ≤ r_j² R_j(0)`. With `R_j(0) > 0` that means `ρ_j ≤ r_j`, hence
  `side_j(1-r_j) ≤ side_j(1-ρ_j) ≤ c`. The cancellation of `R_j(0)` is NOT formalized.

HONEST SCOPE. This is a SUFFICIENT condition only. It moves the open input from a
lag-`side_j` correlator lower bound (window survival) to a one-step, or lag-`k_j`, ratio
bound `side_j(1-ρ_j) ≤ c < 1`. That ratio bound is still the nontriviality core and is
NOT proved for any YM trajectory here.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility
import YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
import YMGap.Continuum.BondMovingRetuneFix

namespace YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredExcitation)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (responseSum)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothingWeight smoothingWeight_nonneg boxKernel timeKernel)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeResponseLower (response_step_lower)
open YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
  (response_shifted_step_lower response_shifted_geometric_lower)
open YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility (orbit_even_contraction)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility
  (ExprPathOrbitContraction expr_windowSurvival_forces_rate_c0)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational helpers and Bernoulli -/

private theorem sr_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem sr_qpow_eqv_pow (y : Q') : ∀ n, (RGTransport.qpow y n).eqv (y^n)
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ y (sr_qpow_eqv_pow y n))
      (Q'.mul_comm_eqv _ _)

private theorem sr_side_halves (j : Nat) (hj : 1 ≤ j) : side j/2 + side j/2 = side j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

private theorem sr_two_le_side (j : Nat) (hj : 1 ≤ j) : 2 ≤ side j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
  simp only [side, Nat.pow_succ]
  have := Nat.two_pow_pos i
  omega

private theorem sr_one_sub_one_sub (rho : Q') : (1 : Q') - ((1 : Q') - rho) ≈ rho :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1) (by decide)
    (fun | 0 => (1 : Q') | _ => rho)

private theorem sr_one_sub_add (rho : Q') : ((1 : Q') - rho) + rho ≈ (1 : Q') :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
    (fun | 0 => (1 : Q') | _ => rho)

private theorem sr_one_sub_nonneg {rho : Q'} (h1 : rho ≤ 1) : (0 : Q') ≤ (1 : Q') - rho :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv rho))
    (Q'.add_le_add_right rho 1 (-rho) h1)

private theorem sr_one_sub_le_one {rho : Q'} (h0 : (0 : Q') ≤ rho) : (1 : Q') - rho ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv ((1 : Q') - rho)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left ((1 : Q') - rho) 0 rho h0)
      (Q'.le_of_eqv (sr_one_sub_add rho)))

/-- **Bernoulli** over the repo rationals: `1 - n(1-ρ) ≤ ρ^n` for `0 ≤ ρ ≤ 1`
(via the constructive `BondMovingRetuneFix.bernoulli_oneSub`). -/
theorem bernoulli_pow (rho : Q') (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) (n : Nat) :
    (1 : Q') - Q'.ofNat n * ((1 : Q') - rho) ≤ rho^n := by
  have e := sr_one_sub_one_sub rho
  have hb := BondMovingRetuneFix.bernoulli_oneSub ((1 : Q') - rho)
    (sr_one_sub_nonneg h1) (sr_one_sub_le_one h0) n
  have hbase : (0 : Q') ≤ (1 : Q') - ((1 : Q') - rho) :=
    Q'.le_trans' _ _ _ h0 (Q'.ge_of_eqv e)
  exact Q'.le_trans' _ _ _ hb
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sr_qpow_eqv_pow _ n))
      (CRealLog.pow_le_pow_base _ _ hbase (Q'.le_of_eqv e) n))

/-- Window constant: `side(1-ρ) ≤ c`, `2 ≤ side` ⇒ `1 - c ≤ ρ^(side/2+1)`. -/
theorem theta_le_window_pow (rho c : Q') (s : Nat) (hs : 2 ≤ s)
    (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) (hc : Q'.ofNat s * ((1 : Q') - rho) ≤ c) :
    (1 : Q') - c ≤ rho^(s/2+1) := by
  have hq : Q'.ofNat (s/2+1) * ((1 : Q') - rho) ≤ c :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (sr_ofNat_le (by omega)) (sr_one_sub_nonneg h1)) hc
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hq))
    (bernoulli_pow rho h0 h1 (s/2+1))

theorem theta_pos (c : Q') (hc : c < 1) : (0 : Q') < (1 : Q') - c := HKPos.one_sub_pos hc

/-! ## 1. Nonnegative-weight sums preserve a step ratio -/

private theorem sr_scale_distrib (rho c : Q') (a s : RC) :
    RCscale rho (RCadd (RCscale c a) s) = RCadd (RCscale c (RCscale rho a)) (RCscale rho s) := by
  refine Quotient.inductionOn₂ a s ?_
  intro A S
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2))) (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => rho | 1 => c | 2 => A.approx n | _ => S.approx n)))

theorem responseSum_ratio_mono (K : List (Q' × Nat)) (hK : ∀ p ∈ K, (0 : Q') ≤ p.1)
    (f g : Nat → RC) (rho : Q') (h : ∀ n, RCle (RCscale rho (f n)) (g n)) :
    RCle (RCscale rho (responseSum K f)) (responseSum K g) := by
  induction K with
  | nil =>
      show RCle (RCscale rho RCzero) RCzero
      rw [RCscale_RCzero]
      exact RCle_refl _
  | cons a K ih =>
      rcases a with ⟨c, n⟩
      show RCle (RCscale rho (RCadd (RCscale c (f n)) (responseSum K f)))
        (RCadd (RCscale c (g n)) (responseSum K g))
      rw [sr_scale_distrib]
      exact RCadd_le_add (RCscale_mono (hK (c, n) (by simp)) (h n))
        (ih (fun p hp => hK p (by simp [hp])))

theorem boxKernel_nonneg {r : Q'} (hr : (0 : Q') ≤ r) :
    ∀ M, ∀ p ∈ boxKernel r M, (0 : Q') ≤ p.1
  | 0, p, hp => by
      simp only [boxKernel, List.mem_singleton] at hp
      rw [hp]; exact hr
  | M+1, p, hp => by
      simp only [boxKernel, List.mem_cons] at hp
      rcases hp with hp | hp
      · rw [hp]; exact hr
      · exact boxKernel_nonneg hr M p hp

theorem timeKernel_nonneg (M : Nat) : ∀ p ∈ timeKernel M, (0 : Q') ≤ p.1 :=
  boxKernel_nonneg (smoothingWeight_nonneg M) M

/-! ## 2. Transfer from the centered vector `x` to the smoothed response `R_Y` -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (ψ : IntrinsicExpression width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "x0" => Subtype.val (centeredExcitation hw0 hw1 ψ)

/-- A lag-`k` ratio on the centered vector `x` gives the ratio of the smoothed response
`R_Y` at every lag `n ≥ k`. -/
theorem exprResponse_step_of_lagRatio (M k : Nat) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x0 (T k x0))) (B x0 (T (k+1) x0)))
    (n : Nat) (hn : k ≤ n) :
    RCle (RCscale rho (exprResponse hw0 hw1 width ψ M n))
      (exprResponse hw0 hw1 width ψ M (n+1)) := by
  rw [exprResponse_orbit_expand, exprResponse_orbit_expand]
  have hst := response_shifted_step_lower hw0 hw1 x0 rho hrho k hfloor
  refine responseSum_ratio_mono (timeKernel M) (timeKernel_nonneg M) _ _ rho (fun m => ?_)
  refine responseSum_ratio_mono (timeKernel M) (timeKernel_nonneg M) _ _ rho (fun i => ?_)
  have h := hst (m+i+n-k)
  rw [show k + (m+i+n-k) = m+i+n by omega] at h
  exact h

/-- The H-ray floor on `x` gives the ratio of `R_Y` at every lag. -/
theorem exprResponse_step_of_ray (M : Nat) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hray : RCle (RCscale rho (B x0 x0)) (B x0 (T 1 x0))) (n : Nat) :
    RCle (RCscale rho (exprResponse hw0 hw1 width ψ M n))
      (exprResponse hw0 hw1 width ψ M (n+1)) := by
  rw [exprResponse_orbit_expand, exprResponse_orbit_expand]
  have hst := response_step_lower hw0 hw1 x0 rho hrho hray
  refine responseSum_ratio_mono (timeKernel M) (timeKernel_nonneg M) _ _ rho (fun m => ?_)
  exact responseSum_ratio_mono (timeKernel M) (timeKernel_nonneg M) _ _ rho
    (fun i => hst (m+i+n))

end Generic

/-! ## 3. Expr layer -/

/-- **Step-ratio hypothesis (OPEN), on the window response** `R_j(n) = B(Y_j, T^n Y_j)`:
`ρ_j R_j(k_j) ≤ R_j(k_j+1)` for `j ≥ 1`. -/
def ExprStepRatio (tr : ExprAnchorTrajectory) (rho : Nat → Q') (k : Nat → Nat) : Prop :=
  ∀ j, 1 ≤ j → RCle (RCscale (rho j) (tr.response j (k j))) (tr.response j (k j + 1))

/-- Geometric window: `ρ_j^(side_j/2+1) R_j(side_j/2) ≤ R_j(side_j+1)`. -/
theorem expr_window_pow_of_stepRatio (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (k : Nat → Nat) (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2) (H : ExprStepRatio tr rho k)
    (j : Nat) (hj : 1 ≤ j) :
    RCle (RCscale (rho j ^ (side j / 2 + 1)) (tr.response j (side j / 2)))
      (tr.response j (side j + 1)) := by
  have hstep := response_shifted_step_lower (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.state j) (rho j) (hrho0 j hj) (k j) (H j hj)
  have hmid := hstep (side j / 2 - k j)
  rw [show k j + (side j / 2 - k j) = side j / 2 by have := hk j hj; omega] at hmid
  have hgeo := response_shifted_geometric_lower (tr.schedule.nome_pos j)
    (tr.schedule.nome_lt_one j) (tr.state j) (rho j) (hrho0 j hj) (side j / 2) hmid
    (side j / 2 + 1)
  rw [show side j / 2 + (side j / 2 + 1) = side j + 1 by
    have := sr_side_halves j hj; omega] at hgeo
  exact hgeo

/-- **Window survival from a step ratio (SUFFICIENT condition).** For `j ≥ 1`:
`0 ≤ ρ_j ≤ 1`, `k_j ≤ side_j/2`, `side_j (1-ρ_j) ≤ c` and `ρ_j R_j(k_j) ≤ R_j(k_j+1)` give
`ExprShiftedWindowSurvival tr (1 - c)`, i.e. `(1-c) R_j(side_j/2) ≤ R_j(side_j+1)`. -/
theorem expr_windowSurvival_of_stepRatio (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (k : Nat → Nat) (c : Q') (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j)
    (hrho1 : ∀ j, 1 ≤ j → rho j ≤ 1) (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, 1 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k) :
    ExprShiftedWindowSurvival tr ((1 : Q') - c) := by
  intro j hj
  have hs : 2 ≤ side j := sr_two_le_side j hj
  exact RCle_trans
    (RCscale_scalar_mono (theta_le_window_pow (rho j) c (side j) hs (hrho0 j hj) (hrho1 j hj)
      (hc j hj))
      (response_nonnegative (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
        (tr.state j) (side j / 2)))
    (expr_window_pow_of_stepRatio tr rho k hrho0 hk H j hj)

/-- `ExprHRay` (lag-one floor on the CENTERED vector `x_j`) gives the step ratio of the
smoothed window response at lag `k_j = 0`. -/
theorem expr_stepRatio_of_hray (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (Hr : ExprHRay tr rho) : ExprStepRatio tr rho (fun _ => 0) := fun j _ =>
  exprResponse_step_of_ray (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.expr j) (tr.radius j) (rho j) (Q'.le_of_lt (Hr j).1) (Hr j).2 0

/-- **H-ray form.** `ExprHRay tr ρ`, `ρ_j ≤ 1` and `side_j (1-ρ_j) ≤ c` give window
survival with `θ = 1 - c`. -/
theorem expr_windowSurvival_of_hray (tr : ExprAnchorTrajectory) (rho : Nat → Q') (c : Q')
    (Hr : ExprHRay tr rho) (hrho1 : ∀ j, 1 ≤ j → rho j ≤ 1)
    (hc : ∀ j, 1 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c) :
    ExprShiftedWindowSurvival tr ((1 : Q') - c) :=
  expr_windowSurvival_of_stepRatio tr rho (fun _ => 0) c (fun j _ => Q'.le_of_lt (Hr j).1)
    hrho1 (fun _ _ => Nat.zero_le _) hc (expr_stepRatio_of_hray tr rho Hr)

/-! ## 4. Compatibility with the gap side -/

/-- Composed with the gap-side necessary condition: step ratio (θ = 1 - c, `c < 1`),
nondegeneracy and an orbit contraction give `side_j(1-r_j) ≤ c0` for `j ≥ 2`, whenever
`2(1-θ) ≤ θ c0`. -/
theorem expr_stepRatio_forces_rate_c0 (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (k : Nat → Nat) (c c0 : Q') (r fl : Nat → Q') (hc1 : c < 1)
    (hc0 : (1 + -((1 : Q') - c)) * Q'.ofNat 2 ≤ ((1 : Q') - c) * c0)
    (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j) (hrho1 : ∀ j, 1 ≤ j → rho j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, 1 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k)
    (hfl : ∀ j, (0 : Q') < fl j) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 :=
  expr_windowSurvival_forces_rate_c0 tr ((1 : Q') - c) c0 r fl hfl (theta_pos c hc1) hc0
    (expr_windowSurvival_of_stepRatio tr rho k c hrho0 hrho1 hk hc H) Hnd Hc hr0 hr1 j hj

/-- Lag-0 ratio plus orbit contraction: `ρ_j² R_j(0) ≤ r_j² R_j(0)` (so `ρ_j ≤ r_j` when
`R_j(0) > 0`; that cancellation is not formalized here). -/
theorem expr_stepRatio_zero_contraction (tr : ExprAnchorTrajectory) (rho r : Nat → Q')
    (j : Nat) (hrho0 : (0 : Q') ≤ rho j)
    (H0 : RCle (RCscale (rho j) (tr.response j 0)) (tr.response j 1))
    (Hc : ExprPathOrbitContraction tr r) :
    RCle (RCscale (rho j ^ 2) (tr.response j 0)) (RCscale (r j * r j) (tr.response j 0)) := by
  have hg := response_shifted_geometric_lower (tr.schedule.nome_pos j)
    (tr.schedule.nome_lt_one j) (tr.state j) (rho j) hrho0 0 H0 2
  have hc := orbit_even_contraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.width j) (tr.state j) (r j) (Hc j) 0
  exact RCle_trans hg hc

#print axioms bernoulli_pow
#print axioms theta_le_window_pow
#print axioms theta_pos
#print axioms responseSum_ratio_mono
#print axioms boxKernel_nonneg
#print axioms timeKernel_nonneg
#print axioms exprResponse_step_of_lagRatio
#print axioms exprResponse_step_of_ray
#print axioms ExprStepRatio
#print axioms expr_window_pow_of_stepRatio
#print axioms expr_windowSurvival_of_stepRatio
#print axioms expr_stepRatio_of_hray
#print axioms expr_windowSurvival_of_hray
#print axioms expr_stepRatio_forces_rate_c0
#print axioms expr_stepRatio_zero_contraction

end YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival
