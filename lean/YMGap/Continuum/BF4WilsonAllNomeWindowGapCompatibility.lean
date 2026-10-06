/-
# Window survival vs. a gap contraction: a NECESSARY compatibility condition

Companion to `audits/AUDIT-WINDOW-GAP-COMPATIBILITY-2026-10-06.md`.

Moment-only, generic over a carrier vector `x`. Write `R(n) = B(x, T^n x)`.
Hypothesis: a norm-form sector contraction on the orbit of `x`,
`B(T y, T y) ≤ r² B(y, y)` for every `y = T^k x` (`OrbitContraction`). By the lag
pin `B(T^h x, T^h x) = R(2h)` this is `R(2k+2) ≤ r² R(2k)`, which iterates to
`R(2(m+q)) ≤ (r²)^q R(2m)`. Odd lags are not orbit norms
(`R(2m+1) = B(T^m x, T^(m+1) x)`), so the parity step uses only antitonicity of
`R` (`response_le_of_le`, unconditional on this carrier).

Result (`window_contraction_compat`): if `θ R(p) ≤ R(s+1)` and `R(p)` has a
positive rational floor, then `θ ≤ (r²)^q` for every `q` with
`2⌈p/2⌉ + 2q ≤ s+1`. The explicit exponent (`window_contraction_compat_floor`)
is `q = ⌊(s+1)/2⌋ - ⌈p/2⌉`.
* This equals `⌊(s+1-p)/2⌋` when `p` is even, or when `s+1-p` is odd.
* It is ONE LESS than `⌊(s+1-p)/2⌋` when `p` is odd and `s+1-p` is even.
  Antitonicity alone loses one factor `r²` in that parity case. The sharper
  exponent there would also need log-convexity plus a positivity cancellation,
  and is NOT proved here.
* For the path window (`p = side_j/2`, `s = side_j`, `side_j = 2^j`, `j ≥ 2`),
  `p` is even and `q = side_j/4`, so no loss occurs.

Path form: `PathShiftedWindowSurvival tr θ` together with `PathShiftedNondegenerate`
(the floor at `side_j` passes down to `side_j/2` by antitonicity) and a contraction
`r_j` on the anchor's orbit gives:
* `θ ≤ (r_j²)^(side_j/4)`, i.e. `θ ≤ r_j^(side_j/2)`;
* by Bernoulli, `r^n (1 + n(1-r)) ≤ 1`, the bound `θ · side_j (1-r_j) ≤ 2(1-θ)`;
* equivalently `side_j (1-r_j) ≤ c0` for any `c0` with `2(1-θ) ≤ θ c0`. The least
  such `c0` is `C(θ) = 2(1-θ)/θ`, the same constant that turns window survival
  into shifted H1 (`pathShiftedEpsBound_of_windowSurvival`).

HONEST SCOPE. This is a NECESSARY COMPATIBILITY CONDITION between the
nontriviality branch (window survival of the anchor) and the gap branch (a
contraction `r_j < 1` on the anchor's orbit). Both can hold at scale `j` only if
`side_j (1 - r_j) = O(1)`, i.e. `side_j ≲` the correlation length in lattice
units. It proves NEITHER branch:
* window survival stays OPEN;
* no contraction `r_j < 1` is constructed;
* no mass gap and no nontriviality follow.

Constructive and Mathlib-free; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival

namespace YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory.DyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (shift_norm_pin PathShiftedNondegenerate)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (PathShiftedWindowSurvival)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Local helpers (copies of the standard private lemmas) -/

private theorem wg_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem wg_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem wg_scale_sub (a b : Q') (x : RC) :
    RCscale (a + -b) x = RCsub (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => a | 1 => b | _ => X.approx n)))

private theorem wg_le_total (a b : Q') : a ≤ b ∨ b ≤ a := by
  rcases Int.le_total (a.num * (b.den : Int)) (b.num * (a.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem wg_rational_nonpos {x : Q'} (h : RCle (Rq x) RCzero) : x ≤ (0 : Q') := by
  refine Q'.le_of_forall_pos_add (fun epsilon he => ?_)
  obtain ⟨index, hN⟩ := h epsilon he
  exact hN index (Nat.le_refl index)

private theorem wg_nonpos_of_mul_nonpos {x q : Q'} (hq : (0 : Q') < q)
    (h : x*q ≤ (0 : Q')) : x ≤ (0 : Q') := by
  have hr := Q'.le_of_lt (Q'.recipPos_pos q hq)
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos q hq) h hr
  have hx : x*q*Q'.recipPos q hq ≈ x :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => x | 1 => q | _ => Q'.recipPos q hq))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ (Q'.mul_recipPos_eqv q hq))
        (poly_identity_of_normal_eq (.mul (.var 0) (.const 1)) (.var 0) (by decide)
          (fun _ => x)))
  have h0 : (0 : Q')*Q'.recipPos q hq ≈ 0 := Q'.zero_mul_eqv _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hx) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h0))

/-- Rational coefficients compare once the common RC factor has a positive
rational floor. -/
private theorem wg_coeff_le_of_scale_le {a b q : Q'} (hq : (0 : Q') < q) {N : RC}
    (hN : RCle (Rq q) N) (h : RCle (RCscale a N) (RCscale b N)) : a ≤ b := by
  rcases wg_le_total a b with hab | hba
  · exact hab
  · have hd : (0 : Q') ≤ a + -b := by
      have h' := Q'.add_le_add_right _ _ (-b) hba
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv b)) h'
    have hlow := RCscale_mono hd hN
    rw [wg_scale_rational, wg_scale_sub] at hlow
    have hup := RCadd_le_add h (RCle_refl (RCneg (RCscale b N)))
    change RCle (RCsub (RCscale a N) (RCscale b N)) (RCsub (RCscale b N) (RCscale b N)) at hup
    rw [wg_sub_self] at hup
    have hx := wg_nonpos_of_mul_nonpos hq (wg_rational_nonpos (RCle_trans hlow hup))
    have h2 := Q'.add_le_add_right _ _ b hx
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => a | _ => b)))
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' b))))

private theorem wg_mul_self_nonneg (r : Q') : (0 : Q') ≤ r * r := by
  rcases wg_le_total 0 r with h | h
  · exact Q'.mul_nonneg r r h h
  · have hn : (0 : Q') ≤ -r := by
      have h' := Q'.add_le_add_right _ _ (-r) h
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv r))
        (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-r)))))
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hn hn) (Q'.le_of_eqv
      (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => r)))

/-! ## 1. Moment-only core (any response sequence) -/

section Sequence

variable (R : Nat → RC)

/-- Even-lag iteration of the norm-form contraction:
`R(2(m+q)) ≤ (r²)^q R(2m)`. -/
theorem even_contraction_iterate (r : Q')
    (hc : ∀ k, RCle (R (2*k+2)) (RCscale (r*r) (R (2*k)))) (m : Nat) :
    ∀ q : Nat, RCle (R (2*(m+q))) (RCscale ((r*r)^q) (R (2*m)))
  | 0 => by
      rw [Nat.add_zero, Q'.pow_zero, RCscale_one]
      exact RCle_refl _
  | q+1 => by
      have h := hc (m+q)
      rw [show 2*(m+q)+2 = 2*(m+(q+1)) by omega] at h
      have ih := RCscale_mono (wg_mul_self_nonneg r) (even_contraction_iterate r hc m q)
      rw [RCscale_RCscale] at ih
      rw [Q'.pow_succ]
      exact RCle_trans h ih

/-- **Window/contraction compatibility (sequence form).** For a nonincreasing
sequence `R` with even-lag contraction `R(2k+2) ≤ r² R(2k)`, a window survival
`θ R(p) ≤ R(s+1)` with a positive floor under `R(p)` forces `θ ≤ (r²)^q` for every
`q` with `2⌈p/2⌉ + 2q ≤ s+1`. -/
theorem window_contraction_compat (r theta fl : Q') (hfl : (0 : Q') < fl) (p s q : Nat)
    (hq : 2*((p+1)/2) + 2*q ≤ s+1)
    (hmono : ∀ a b, a ≤ b → RCle (R b) (R a))
    (hc : ∀ k, RCle (R (2*k+2)) (RCscale (r*r) (R (2*k))))
    (hnd : RCle (Rq fl) (R p))
    (hw : RCle (RCscale theta (R p)) (R (s+1))) :
    theta ≤ (r*r)^q := by
  have h1 := hmono (2*((p+1)/2 + q)) (s+1) (by omega)
  have h2 := even_contraction_iterate R r hc ((p+1)/2) q
  have h3 := RCscale_mono (Q'.pow_nonneg _ (wg_mul_self_nonneg r) q)
    (hmono p (2*((p+1)/2)) (by omega))
  exact wg_coeff_le_of_scale_le hfl hnd (RCle_trans hw (RCle_trans h1 (RCle_trans h2 h3)))

/-- Explicit exponent `q = ⌊(s+1)/2⌋ - ⌈p/2⌉`. It equals `⌊(s+1-p)/2⌋` when `p` is
even or `s+1-p` is odd, and is one less when `p` is odd and `s+1-p` is even. -/
theorem window_contraction_compat_floor (r theta fl : Q') (hfl : (0 : Q') < fl) (p s : Nat)
    (hps : p ≤ s+1)
    (hmono : ∀ a b, a ≤ b → RCle (R b) (R a))
    (hc : ∀ k, RCle (R (2*k+2)) (RCscale (r*r) (R (2*k))))
    (hnd : RCle (Rq fl) (R p))
    (hw : RCle (RCscale theta (R p)) (R (s+1))) :
    theta ≤ (r*r)^((s+1)/2 - (p+1)/2) := by
  by_cases hle : (p+1)/2 ≤ (s+1)/2
  · exact window_contraction_compat R r theta fl hfl p s _ (by omega) hmono hc hnd hw
  · have hz : (s+1)/2 - (p+1)/2 = 0 := by omega
    rw [hz, Q'.pow_zero]
    have h1 := hmono p (s+1) hps
    rw [← RCscale_one (R p)] at h1
    exact wg_coeff_le_of_scale_le hfl hnd (RCle_trans hw h1)

end Sequence


/-! ## 2. Scalar Bernoulli step (rational, constructive) -/

private theorem wg_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem wg_ofNat_succ (n : Nat) : Q'.ofNat (n+1) ≈ Q'.ofNat n + 1 := by
  have hd1 : ((Q'.ofNat n + 1).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (n+1)).den : Int) = 1 := rfl
  have hn : (Q'.ofNat n + 1).num = (n : Int) * 1 + 1 * 1 := rfl
  show ((n+1 : Nat) : Int) * ((Q'.ofNat n + 1).den : Int)
    = (Q'.ofNat n + 1).num * ((Q'.ofNat (n+1)).den : Int)
  rw [hd1, hd2, hn]
  push_cast
  omega

private theorem wg_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem wg_one_sub_nonneg {r : Q'} (h1 : r ≤ 1) : (0 : Q') ≤ 1 + -r := by
  have h' := Q'.add_le_add_right _ _ (-r) h1
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv r)) h'

/-- One Bernoulli step: `r (1 + (n+1)(1-r)) ≤ 1 + n(1-r)`; the gap is
`(n+1)(1-r)^2 ≥ 0`. -/
private theorem wg_bernoulli_step (r : Q') (n : Nat) :
    r * (1 + Q'.ofNat (n+1) * (1 + -r)) ≤ 1 + Q'.ofNat n * (1 + -r) := by
  have hX : r * (1 + Q'.ofNat (n+1) * (1 + -r)) ≈
      r * (1 + (Q'.ofNat n + 1) * (1 + -r)) :=
    Q'.mul_eqv_congr_left r _ _ (Q'.add_eqv_congr_left 1 _ _
      (Q'.mul_eqv_congr_right _ _ (1 + -r) (wg_ofNat_succ n)))
  have hc : (0 : Q') ≤ (Q'.ofNat n + 1) * ((1 + -r) * (1 + -r)) :=
    Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ (wg_ofNat_nonneg n) Q'.zero_le_one)
      (wg_mul_self_nonneg (1 + -r))
  have hid : r * (1 + (Q'.ofNat n + 1) * (1 + -r)) +
      (Q'.ofNat n + 1) * ((1 + -r) * (1 + -r)) ≈ 1 + Q'.ofNat n * (1 + -r) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.const 1) (.mul (.add (.var 1) (.const 1))
          (.add (.const 1) (.neg (.var 0))))))
        (.mul (.add (.var 1) (.const 1))
          (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))))
      (.add (.const 1) (.mul (.var 1) (.add (.const 1) (.neg (.var 0)))))
      (by decide) (fun | 0 => r | _ => Q'.ofNat n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hX)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hc) (Q'.le_of_eqv hid))

/-- Bernoulli in cleared form: `r^n (1 + n(1-r)) ≤ 1` for `0 ≤ r ≤ 1`
(i.e. `r^n ≤ 1/(1+n(1-r))`). -/
theorem bernoulli_cleared (r : Q') (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) :
    ∀ n : Nat, r^n * (1 + Q'.ofNat n * (1 + -r)) ≤ 1
  | 0 => Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.const 1) (.add (.const 1) (.mul (.const 0) (.add (.const 1) (.neg (.var 0))))))
        (.const 1) (by decide) (fun _ => r))
  | n+1 => by
      rw [Q'.pow_succ]
      have hstep := Q'.mul_le_mul_of_nonneg_left _ _ (r^n) (wg_bernoulli_step r n)
        (Q'.pow_nonneg r h0 n)
      have hassoc : r * r^n * (1 + Q'.ofNat (n+1) * (1 + -r)) ≈
          r^n * (r * (1 + Q'.ofNat (n+1) * (1 + -r))) :=
        poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => r | 1 => r^n | _ => 1 + Q'.ofNat (n+1) * (1 + -r))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc)
        (Q'.le_trans' _ _ _ hstep (bernoulli_cleared r h0 h1 n))

private theorem wg_sq_pow (r : Q') : ∀ q : Nat, (r*r)^q ≈ r^(2*q)
  | 0 => Q'.eqv_refl _
  | q+1 => by
      rw [Q'.pow_succ, show 2*(q+1) = (2*q+1)+1 by omega, Q'.pow_succ, Q'.pow_succ]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (r*r) _ _ (wg_sq_pow r q))
        (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 0)) (.var 1))
          (.mul (.var 0) (.mul (.var 0) (.var 1))) (by decide)
          (fun | 0 => r | _ => r^(2*q)))

/-- From `θ ≤ (r²)^q` with `0 ≤ r ≤ 1`, `0 ≤ θ`: `θ · 2q(1-r) ≤ 1 - θ`. -/
theorem rate_of_contraction_power (theta r : Q') (q : Nat) (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1)
    (ht : theta ≤ (r*r)^q) :
    theta * (Q'.ofNat (2*q) * (1 + -r)) ≤ 1 + -theta := by
  have hD : (0 : Q') ≤ 1 + Q'.ofNat (2*q) * (1 + -r) :=
    Q'.zero_le_add _ _ Q'.zero_le_one
      (Q'.mul_nonneg _ _ (wg_ofNat_nonneg _) (wg_one_sub_nonneg h1))
  have hP : theta ≤ r^(2*q) := Q'.le_trans' _ _ _ ht (Q'.le_of_eqv (wg_sq_pow r q))
  have hb := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hP hD)
    (bernoulli_cleared r h0 h1 (2*q))
  have h2 := Q'.add_le_add_right _ _ (-theta) hb
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.const 1) (.mul (.var 1) (.var 2)))) (.neg (.var 0)))
      (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
      (fun | 0 => theta | 1 => Q'.ofNat (2*q) | _ => 1 + -r))) h2

/-- Side form: if `L = 2·(2q)` then `θ · L(1-r) ≤ 2(1-θ)`. -/
theorem side_rate_of_contraction_power (theta r : Q') (q L : Nat) (hL : L = 2*(2*q))
    (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) (ht : theta ≤ (r*r)^q) :
    theta * (Q'.ofNat L * (1 + -r)) ≤ (1 + -theta) * Q'.ofNat 2 := by
  subst hL
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    (rate_of_contraction_power theta r q h0 h1 ht) (wg_ofNat_nonneg 2)
  have e1 : theta * (Q'.ofNat (2*(2*q)) * (1 + -r)) ≈
      theta * ((Q'.ofNat 2 * Q'.ofNat (2*q)) * (1 + -r)) :=
    Q'.mul_eqv_congr_left theta _ _ (Q'.mul_eqv_congr_right _ _ _ (wg_ofNat_mul 2 (2*q)))
  have e2 : theta * ((Q'.ofNat 2 * Q'.ofNat (2*q)) * (1 + -r)) ≈
      Q'.ofNat 2 * (theta * (Q'.ofNat (2*q) * (1 + -r))) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 1) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (by decide)
      (fun | 0 => theta | 1 => Q'.ofNat 2 | 2 => Q'.ofNat (2*q) | _ => 1 + -r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ e1 e2))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

private theorem wg_cancel_left {t u v : Q'} (ht : (0 : Q') < t) (h : t * u ≤ t * v) : u ≤ v := by
  have hr := Q'.le_of_lt (Q'.recipPos_pos t ht)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.recipPos t ht) h hr
  have e : ∀ x : Q', Q'.recipPos t ht * (t * x) ≈ x := fun x =>
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
        (fun | 0 => Q'.recipPos t ht | 1 => t | _ => x))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x (Q'.mul_recipPos_eqv t ht))
        (Q'.one_mul_eqv x))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (e u)) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (e v)))

/-- `c0` form: with `0 < θ` and `2(1-θ) ≤ θ c0`, `L(1-r) ≤ c0`.
The least admissible `c0` is `C(θ) = 2(1-θ)/θ`. -/
theorem side_rate_le_c0 (theta r c0 : Q') (q L : Nat) (hL : L = 2*(2*q))
    (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) (ht0 : (0 : Q') < theta) (ht : theta ≤ (r*r)^q)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) :
    Q'.ofNat L * (1 + -r) ≤ c0 :=
  wg_cancel_left ht0 (Q'.le_trans' _ _ _
    (side_rate_of_contraction_power theta r q L hL h0 h1 ht) hc0)

/-! ## 3. The completed carrier (generic over `x : V`) -/

section Carrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Norm-form sector contraction on the orbit of `x`:
`B(T y, T y) ≤ r² B(y, y)` for `y = T^k x`, every `k`. (A hypothesis; not proved
for any carrier vector here.) -/
def OrbitContraction (x : V) (r : Q') : Prop :=
  ∀ k : Nat, RCle (B (T (k+1) x) (T (k+1) x)) (RCscale (r*r) (B (T k x) (T k x)))

/-- Lag form of the contraction: `R(2k+2) ≤ r² R(2k)`. -/
theorem orbit_even_contraction (x : V) (r : Q') (Hc : OrbitContraction hw0 hw1 width x r)
    (k : Nat) : RCle (B x (T (2*k+2) x)) (RCscale (r*r) (B x (T (2*k) x))) := by
  have h := Hc k
  rw [shift_norm_pin hw0 hw1 width x (k+1), shift_norm_pin hw0 hw1 width x k] at h
  rw [show 2*k+2 = 2*(k+1) by omega]
  exact h

/-- **Window/gap compatibility on the carrier.** `θ R(p) ≤ R(s+1)`, a floor
`fl ≤ R(p)` with `0 < fl`, and an orbit contraction `r` give
`θ ≤ (r²)^(⌊(s+1)/2⌋ - ⌈p/2⌉)`. NECESSARY condition only; proves neither
survival nor a gap. -/
theorem window_gap_compat (x : V) (r theta fl : Q') (hfl : (0 : Q') < fl) (p s : Nat)
    (hps : p ≤ s+1) (Hc : OrbitContraction hw0 hw1 width x r)
    (hnd : RCle (Rq fl) (B x (T p x)))
    (hw : RCle (RCscale theta (B x (T p x))) (B x (T (s+1) x))) :
    theta ≤ (r*r)^((s+1)/2 - (p+1)/2) :=
  window_contraction_compat_floor (fun n => B x (T n x)) r theta fl hfl p s hps
    (fun _ _ hab => response_le_of_le hw0 hw1 width x hab)
    (orbit_even_contraction hw0 hw1 width x r Hc) hnd hw

end Carrier

/-! ## 4. Path form -/

/-- A contraction `r_j` on the orbit of the anchor `Y_j` at every scale
(hypothesis; the gap branch). -/
def PathOrbitContraction (tr : DyadicSmoothedTrajectory) (r : Nat → Q') : Prop :=
  ∀ j, OrbitContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (tr.state j) (r j)

private theorem wg_side_quarter (j : Nat) (hj : 2 ≤ j) : side j = 2*(2*(side j/4)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+2 := ⟨j-2, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

/-- **Path exponent.** For `j ≥ 2`, window survival, nondegeneracy and an orbit
contraction force `θ ≤ (r_j²)^(side_j/4)` (`= r_j^(side_j/2)`). Here
`q = ⌊(side_j+1-side_j/2)/2⌋ = side_j/4` exactly, so there is no parity loss. The case
`j = 1` (`side = 2`, `p = 1` odd) is omitted: antitonicity gives only the
exponent 0 there. NECESSARY compatibility condition; proves neither branch. -/
theorem path_windowSurvival_contraction_exponent (tr : DyadicSmoothedTrajectory) (theta : Q')
    (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : PathShiftedWindowSurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl)
    (Hc : PathOrbitContraction tr r) (j : Nat) (hj : 2 ≤ j) :
    theta ≤ (r j * r j)^(side j / 4) := by
  have hq := wg_side_quarter j hj
  have hnd : RCle (Rq (fl j)) (tr.response j (side j / 2)) :=
    RCle_trans (Hnd j) (response_le_of_le (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (tr.state j) (Nat.div_le_self (side j) 2))
  have h := window_gap_compat (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (tr.state j) (r j) theta (fl j) (hfl j) (side j / 2) (side j) (by omega) (Hc j) hnd
    (Hw j (by omega))
  rwa [show (side j + 1)/2 - (side j/2 + 1)/2 = side j / 4 by omega] at h

/-- **Path rate, cleared form.** For `j ≥ 2` and `0 ≤ r_j ≤ 1`:
`θ · side_j (1 - r_j) ≤ 2 (1 - θ)`. NECESSARY compatibility condition
(`side_j ≲` correlation length); proves neither window survival nor a gap. -/
theorem path_windowSurvival_forces_rate (tr : DyadicSmoothedTrajectory) (theta : Q')
    (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : PathShiftedWindowSurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl)
    (Hc : PathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    theta * (Q'.ofNat (side j) * (1 + -r j)) ≤ (1 + -theta) * Q'.ofNat 2 :=
  side_rate_of_contraction_power theta (r j) (side j / 4) (side j) (wg_side_quarter j hj)
    (hr0 j) (hr1 j) (path_windowSurvival_contraction_exponent tr theta r fl hfl Hw Hnd Hc j hj)

/-- **Path rate, `C(θ)` form.** With `0 < θ` and `2(1-θ) ≤ θ c0` (least choice
`c0 = C(θ) = 2(1-θ)/θ`): `side_j (1 - r_j) ≤ c0` for every `j ≥ 2`. NECESSARY
compatibility condition between the nontriviality and gap branches; proves
neither. -/
theorem path_windowSurvival_forces_rate_c0 (tr : DyadicSmoothedTrajectory) (theta c0 : Q')
    (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (ht0 : (0 : Q') < theta)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0)
    (Hw : PathShiftedWindowSurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl)
    (Hc : PathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 :=
  side_rate_le_c0 theta (r j) c0 (side j / 4) (side j) (wg_side_quarter j hj) (hr0 j) (hr1 j) ht0
    (path_windowSurvival_contraction_exponent tr theta r fl hfl Hw Hnd Hc j hj) hc0

#print axioms even_contraction_iterate
#print axioms window_contraction_compat
#print axioms window_contraction_compat_floor
#print axioms bernoulli_cleared
#print axioms rate_of_contraction_power
#print axioms side_rate_of_contraction_power
#print axioms side_rate_le_c0
#print axioms orbit_even_contraction
#print axioms window_gap_compat
#print axioms path_windowSurvival_contraction_exponent
#print axioms path_windowSurvival_forces_rate
#print axioms path_windowSurvival_forces_rate_c0

end YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility
