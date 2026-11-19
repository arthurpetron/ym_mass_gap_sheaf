/-
# Infinite-horizon log-convex gap on Q' (N→∞ corollary)

Additive.  Reuses finite-horizon `SU2LogConvexGap` on each truncated window.
Proves the N→∞ corollary that `gap_finite` left open:

  PosInf + LogConvexInf + ∀ n, G n ≤ C·q^n + q ≥ 0
  ⇒  G 1 ≤ q · G 0.

Growth engine: `ClusteringImpliesGap.term_exceeds_envelope` (Bernoulli +
Archimedean). Mathlib-free; U(1)-true as pure Q' arithmetic; not gap evidence.
-/

import YMGap.Continuum.SU2LogConvexGap
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Constructive.TrigAdd
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.SU2LogConvexGapInfinite

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2LogConvexGap (le_e e_le)
open YMGap.Continuum.ClusteringImpliesGap
  (sub_pos_of_lt term_exceeds_envelope lt_of_lt_of_le lt_irrefl' pow_eqv_congr)
open YMGap.Constructive.TrigAdd (eqv_of_le_of_le)

/-- Unbounded cross-multiplied log-convexity. -/
def LogConvexInf (G : Nat → Q') : Prop :=
  ∀ j, G (j + 1) * G (j + 1) ≤ G j * G (j + 2)

/-- Strict positivity at every index. -/
def PosInf (G : Nat → Q') : Prop :=
  ∀ j, (0 : Q') < G j

theorem nn {G : Nat → Q'} (hp : PosInf G) (j : Nat) : (0 : Q') ≤ G j :=
  Q'.le_of_lt (hp j)

/-- `¬ a ≤ b → b < a` on `Q'`. -/
theorem lt_of_not_le {a b : Q'} (h : ¬ a ≤ b) : b < a := by
  show b.num * (a.den : Int) < a.num * (b.den : Int)
  exact Int.not_le.mp h

theorem logConvex_of_inf {G : Nat → Q'} (hc : LogConvexInf G) (L : Nat) :
    SU2LogConvexGap.LogConvex G L := fun j _ => hc j

theorem pos_of_inf {G : Nat → Q'} (hp : PosInf G) (L : Nat) :
    SU2LogConvexGap.Pos G L := fun j _ => hp j

/-- Finite power form on an unbounded positive log-convex sequence. -/
theorem ratio_pow_inf {G : Nat → Q'} (hp : PosInf G) (hc : LogConvexInf G)
    (k d : Nat) :
    G (k + 1) ^ d * G k ≤ G (k + d) * G k ^ d :=
  SU2LogConvexGap.ratio_pow (pos_of_inf hp (k + d)) (logConvex_of_inf hc (k + d))
    k d (Nat.le_refl _)

/-- Finite gap bound at every window. -/
theorem gap_finite_inf {G : Nat → Q'} (hp : PosInf G) (hc : LogConvexInf G)
    {C q : Q'} (hcl : ∀ n, G n ≤ C * q ^ n) (k d : Nat) :
    G (k + 1) ^ d * G k ≤ C * q ^ (k + d) * G k ^ d :=
  Q'.le_trans' _ _ _ (ratio_pow_inf hp hc k d)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (hcl (k + d))
      (Q'.pow_nonneg _ (nn hp k) d))

/-- `(a * b) ^ n ≃ a ^ n * b ^ n`. -/
theorem mul_pow_eqv (a b : Q') : ∀ n : Nat, ((a * b) ^ n).eqv (a ^ n * b ^ n)
  | 0 => by
      refine Q'.eqv_trans _ _ _
        (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')) ?_
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (a ^ 0) (1 : Q') (b ^ 0)
          (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (1 : Q') (b ^ 0) (1 : Q')
            (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
          (Q'.one_mul_eqv (1 : Q'))))
  | n + 1 => by
      -- Goal: ((a*b)*((a*b)^n)).eqv ((a*a^n)*(b*b^n))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) _ _ (mul_pow_eqv a b n)) ?_
      -- (a*b)*(a^n*b^n) ≃ a*(b*(a^n*b^n))
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (a ^ n * b ^ n)) ?_
      -- b*(a^n*b^n) ≃ b*a^n*b^n ≃ a^n*b*b^n ≃ a^n*(b*b^n)
      have hmid : (b * (a ^ n * b ^ n)).eqv (a ^ n * (b * b ^ n)) := by
        have e1 : (b * (a ^ n * b ^ n)).eqv ((b * a ^ n) * b ^ n) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv b (a ^ n) (b ^ n))
        have e2 : ((b * a ^ n) * b ^ n).eqv ((a ^ n * b) * b ^ n) :=
          Q'.mul_eqv_congr_right _ _ (b ^ n) (Q'.mul_comm_eqv b (a ^ n))
        have e3 : ((a ^ n * b) * b ^ n).eqv (a ^ n * (b * b ^ n)) :=
          Q'.mul_assoc_eqv (a ^ n) b (b ^ n)
        exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ hmid) ?_
      -- a*(a^n*(b*b^n)) ≃ (a*a^n)*(b*b^n)
      exact Q'.eqv_symm (Q'.mul_assoc_eqv a (a ^ n) (b * b ^ n))

/-- `q ^ (0 + n) ≃ q ^ n`. -/
theorem pow_zero_add (q : Q') (n : Nat) : (q ^ (0 + n)).eqv (q ^ n) := by
  rw [Nat.zero_add]
  exact Q'.eqv_refl (q ^ n)

/-- **N→∞ corollary.** Positivity + log-convexity + geometric envelope at every
scale ⇒ `G 1 ≤ q · G 0`. -/
theorem gap_infinite {G : Nat → Q'} (hp : PosInf G) (hc : LogConvexInf G)
    {C q : Q'} (hq : (0 : Q') ≤ q) (hcl : ∀ n, G n ≤ C * q ^ n) :
    G 1 ≤ q * G 0 := by
  by_cases hle : G 1 ≤ q * G 0
  · exact hle
  · exfalso
    have hG0 : (0 : Q') < G 0 := hp 0
    have hG1 : (0 : Q') < G 1 := hp 1
    have hC0 : G 0 ≤ C * q ^ 0 := hcl 0
    have hCbound : G 0 ≤ C := by
      have e : (C * q ^ 0).eqv C :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left C (q ^ 0) (1 : Q')
            (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
          (Q'.mul_one_eqv C)
      exact Q'.le_trans' _ _ _ hC0 (Q'.le_of_eqv e)
    have hCpos : (0 : Q') < C := lt_of_lt_of_le hG0 hCbound
    by_cases hqle0 : q ≤ (0 : Q')
    · have heq : q.eqv (0 : Q') := eqv_of_le_of_le hqle0 hq
      have henv : G 1 ≤ C * q ^ 1 := hcl 1
      have hq1 : (q ^ 1).eqv q :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left q (q ^ 0) (1 : Q')
            (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
          (Q'.mul_one_eqv q)
      have hrhs : (C * q ^ 1).eqv (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left C (q ^ 1) q hq1)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left C q (0 : Q') heq)
            (Q'.mul_zero_eqv C))
      have hG1le0 : G 1 ≤ (0 : Q') :=
        Q'.le_trans' _ _ _ henv (Q'.le_of_eqv hrhs)
      exact lt_irrefl' (0 : Q') (lt_of_lt_of_le hG1 hG1le0)
    · have hqpos : (0 : Q') < q := lt_of_not_le hqle0
      have hlt : q * G 0 < G 1 := by
        show (q * G 0).num * ((G 1).den : Int) < (G 1).num * ((q * G 0).den : Int)
        have h' : ¬ ((G 1).num * ((q * G 0).den : Int)
            ≤ (q * G 0).num * ((G 1).den : Int)) := hle
        exact Int.not_le.mp h'
      let d : Q' := G 1 - q * G 0
      have hdpos : (0 : Q') < d := sub_pos_of_lt hlt
      have hμpos : (0 : Q') < q * G 0 := Q'.mul_pos hqpos hG0
      have hsum : ((q * G 0) + d).eqv (G 1) :=
        Q'.eqv_symm (Q'.add_sub_cancel_eqv (G 1) (q * G 0))
      obtain ⟨n, hn⟩ :=
        term_exceeds_envelope (G 0) C (q * G 0) d hG0 hCpos hμpos hdpos
      have hpow_lam : (((q * G 0) + d) ^ n).eqv (G 1 ^ n) :=
        pow_eqv_congr _ _ hsum n
      have hn1 : C * (q * G 0) ^ n < G 0 * G 1 ^ n :=
        lt_of_lt_of_le hn
          (Q'.mul_le_mul_of_nonneg_left _ _ (G 0)
            (Q'.le_of_eqv hpow_lam) (Q'.le_of_lt hG0))
      have hpowμ : ((q * G 0) ^ n).eqv (q ^ n * G 0 ^ n) := mul_pow_eqv q (G 0) n
      have hn2 : C * (q ^ n * G 0 ^ n) < G 0 * G 1 ^ n :=
        Q'.lt_of_le_of_lt
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _ (Q'.eqv_symm hpowμ))) hn1
      have henv := gap_finite_inf hp hc hcl 0 n
      -- henv : G 1 ^ n * G 0 ≤ C * q ^ (0 + n) * G 0 ^ n
      have henv' : G 0 * G 1 ^ n ≤ C * (q ^ n * G 0 ^ n) := by
        have e1 : (G 1 ^ n * G 0).eqv (G 0 * G 1 ^ n) := Q'.mul_comm_eqv _ _
        have e2 : (C * q ^ (0 + n) * G 0 ^ n).eqv (C * (q ^ n * G 0 ^ n)) := by
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (C * q ^ (0 + n)) (C * q ^ n) (G 0 ^ n)
              (Q'.mul_eqv_congr_left C _ _ (pow_zero_add q n))) ?_
          exact Q'.mul_assoc_eqv C (q ^ n) (G 0 ^ n)
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm e1))
          (Q'.le_trans' _ _ _ henv (Q'.le_of_eqv e2))
      have hcontr : C * (q ^ n * G 0 ^ n) < C * (q ^ n * G 0 ^ n) :=
        lt_of_lt_of_le hn2 henv'
      exact lt_irrefl' _ hcontr

/-- **N→∞ from power bounds.**  `∀ k, b1^(k+1) ≤ b0^k · C · r2^(k+1)` with
`0 < b0` and `0 ≤ r2` yields `b1 ≤ r2 · b0`. Bernoulli engine via
`term_exceeds_envelope`. -/
theorem gap_of_power_bounds {b0 b1 C r2 : Q'}
    (hb0 : (0 : Q') < b0) (hr2 : (0 : Q') ≤ r2)
    (h : ∀ k : Nat, b1 ^ (k + 1) ≤ b0 ^ k * C * r2 ^ (k + 1)) :
    b1 ≤ r2 * b0 := by
  by_cases hle : b1 ≤ r2 * b0
  · exact hle
  · exfalso
    have hlt : r2 * b0 < b1 := by
      show (r2 * b0).num * (b1.den : Int) < b1.num * ((r2 * b0).den : Int)
      exact Int.not_le.mp hle
    by_cases hr2le0 : r2 ≤ (0 : Q')
    · have heq : r2.eqv (0 : Q') := eqv_of_le_of_le hr2le0 hr2
      have hμ0 : (r2 * b0).eqv (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right r2 (0 : Q') b0 heq) (Q'.zero_mul_eqv b0)
      have hb1pos : (0 : Q') < b1 :=
        Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.eqv_symm hμ0)) hlt
      have h0 := h 0
      have eL : (b1 ^ (0 + 1)).eqv b1 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left b1 (b1 ^ 0) (1 : Q')
            (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
          (Q'.mul_one_eqv b1)
      have eR : (b0 ^ 0 * C * r2 ^ (0 + 1)).eqv (0 : Q') := by
        have e0 : (b0 ^ 0).eqv (1 : Q') := by
          rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')
        have e1 : (r2 ^ (0 + 1)).eqv (0 : Q') :=
          Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left r2 (r2 ^ 0) (1 : Q')
              (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
            (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv r2) heq)
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (b0 ^ 0 * C) C (r2 ^ (0 + 1))
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right (b0 ^ 0) (1 : Q') C e0)
              (Q'.one_mul_eqv C))) ?_
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left C _ _ e1) (Q'.mul_zero_eqv C)
      have hb1le0 : b1 ≤ (0 : Q') :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eL))
          (Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv eR))
      exact lt_irrefl' _ (lt_of_lt_of_le hb1pos hb1le0)
    · have hr2pos : (0 : Q') < r2 := lt_of_not_le hr2le0
      let d : Q' := b1 - r2 * b0
      have hdpos : (0 : Q') < d := sub_pos_of_lt hlt
      have hμpos : (0 : Q') < r2 * b0 := Q'.mul_pos hr2pos hb0
      have hb1pos : (0 : Q') < b1 := Q'.lt_of_le_of_lt (Q'.le_of_lt hμpos) hlt
      have h0 := h 0
      have hb1_le_Cr2 : b1 ≤ C * r2 := by
        have eL : (b1 ^ (0 + 1)).eqv b1 :=
          Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left b1 (b1 ^ 0) (1 : Q')
              (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
            (Q'.mul_one_eqv b1)
        have eR : (b0 ^ 0 * C * r2 ^ (0 + 1)).eqv (C * r2) := by
          have e0 : (b0 ^ 0).eqv (1 : Q') := by
            rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')
          have e1 : (r2 ^ (0 + 1)).eqv r2 :=
            Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left r2 (r2 ^ 0) (1 : Q')
                (by rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')))
              (Q'.mul_one_eqv r2)
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (b0 ^ 0 * C) C (r2 ^ (0 + 1))
              (Q'.eqv_trans _ _ _
                (Q'.mul_eqv_congr_right (b0 ^ 0) (1 : Q') C e0)
                (Q'.one_mul_eqv C))) ?_
          exact Q'.mul_eqv_congr_left C _ _ e1
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eL))
          (Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv eR))
      have hCpos : (0 : Q') < C := by
        by_cases hCle : C ≤ (0 : Q')
        · exfalso
          have hprod : C * r2 ≤ (0 : Q') * r2 :=
            Q'.mul_le_mul_of_nonneg_right _ _ r2 hCle hr2
          have hCr2le0 : C * r2 ≤ (0 : Q') :=
            Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv (Q'.zero_mul_eqv r2))
          exact lt_irrefl' _
            (lt_of_lt_of_le hb1pos (Q'.le_trans' _ _ _ hb1_le_Cr2 hCr2le0))
        · exact lt_of_not_le hCle
      have hsum : ((r2 * b0) + d).eqv b1 :=
        Q'.eqv_symm (Q'.add_sub_cancel_eqv b1 (r2 * b0))
      obtain ⟨n, hn⟩ :=
        term_exceeds_envelope b0 C (r2 * b0) d hb0 hCpos hμpos hdpos
      have hpow_lam : (((r2 * b0) + d) ^ n).eqv (b1 ^ n) :=
        pow_eqv_congr _ _ hsum n
      have hn1 : C * (r2 * b0) ^ n < b0 * b1 ^ n :=
        lt_of_lt_of_le hn
          (Q'.mul_le_mul_of_nonneg_left _ _ b0
            (Q'.le_of_eqv hpow_lam) (Q'.le_of_lt hb0))
      have hpowμ : ((r2 * b0) ^ n).eqv (r2 ^ n * b0 ^ n) := mul_pow_eqv r2 b0 n
      have hn2 : C * (r2 ^ n * b0 ^ n) < b0 * b1 ^ n :=
        Q'.lt_of_le_of_lt
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _ (Q'.eqv_symm hpowμ))) hn1
      match n with
      | 0 =>
          have eL : (C * (r2 ^ 0 * b0 ^ 0)).eqv C := by
            have e1 : (r2 ^ 0).eqv (1 : Q') := by
              rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')
            have e2 : (b0 ^ 0).eqv (1 : Q') := by
              rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')
            refine Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left C _ _
                (Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_right (r2 ^ 0) (1 : Q') (b0 ^ 0) e1)
                  (Q'.eqv_trans _ _ _
                    (Q'.mul_eqv_congr_left (1 : Q') _ _ e2)
                    (Q'.one_mul_eqv (1 : Q')))))
              (Q'.mul_one_eqv C)
          have eR : (b0 * b1 ^ 0).eqv b0 := by
            have e : (b1 ^ 0).eqv (1 : Q') := by
              rw [Q'.pow_zero]; exact Q'.eqv_refl (1 : Q')
            exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left b0 _ _ e) (Q'.mul_one_eqv b0)
          have hltC : C < b0 :=
            Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.eqv_symm eL))
              (lt_of_lt_of_le hn2 (Q'.le_of_eqv eR))
          have hgt : r2 * b0 < C * r2 := lt_of_lt_of_le hlt hb1_le_Cr2
          have hweak : r2 * b0 ≤ r2 * C := by
            refine Q'.le_trans' _ _ _ (Q'.le_of_lt hgt) ?_
            exact Q'.le_of_eqv (Q'.mul_comm_eqv C r2)
          have hb0leC : b0 ≤ C := Q'.le_of_mul_le_mul_left hweak hr2pos
          exact lt_irrefl' _ (lt_of_lt_of_le hltC hb0leC)
      | n' + 1 =>
          have hbound := h n'
          have step1 :
              b0 * b1 ^ (n' + 1) ≤ b0 * (b0 ^ n' * C * r2 ^ (n' + 1)) :=
            Q'.mul_le_mul_of_nonneg_left _ _ b0 hbound (Q'.le_of_lt hb0)
          have e :
              (b0 * (b0 ^ n' * C * r2 ^ (n' + 1))).eqv
                (C * (r2 ^ (n' + 1) * b0 ^ (n' + 1))) := by
            refine Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left b0 _ _
                (Q'.mul_assoc_eqv (b0 ^ n') C (r2 ^ (n' + 1)))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.mul_assoc_eqv b0 (b0 ^ n') (C * r2 ^ (n' + 1)))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.mul_comm_eqv (b0 * b0 ^ n') (C * r2 ^ (n' + 1))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.mul_assoc_eqv C (r2 ^ (n' + 1)) (b0 * b0 ^ n')) ?_
            exact Q'.mul_eqv_congr_left C _ _
              (Q'.mul_eqv_congr_left (r2 ^ (n' + 1)) _ _ (Q'.eqv_refl _))
          have henv' :
              b0 * b1 ^ (n' + 1) ≤ C * (r2 ^ (n' + 1) * b0 ^ (n' + 1)) :=
            Q'.le_trans' _ _ _ step1 (Q'.le_of_eqv e)
          have hcontr :
              C * (r2 ^ (n' + 1) * b0 ^ (n' + 1))
                < C * (r2 ^ (n' + 1) * b0 ^ (n' + 1)) :=
            lt_of_lt_of_le hn2 henv'
          exact lt_irrefl' _ hcontr

end YMGap.Continuum.SU2LogConvexGapInfinite

/-! ## Axiom audit -/

#print axioms YMGap.Continuum.SU2LogConvexGapInfinite.ratio_pow_inf
#print axioms YMGap.Continuum.SU2LogConvexGapInfinite.gap_finite_inf
#print axioms YMGap.Continuum.SU2LogConvexGapInfinite.mul_pow_eqv
#print axioms YMGap.Continuum.SU2LogConvexGapInfinite.gap_infinite
#print axioms YMGap.Continuum.SU2LogConvexGapInfinite.gap_of_power_bounds
