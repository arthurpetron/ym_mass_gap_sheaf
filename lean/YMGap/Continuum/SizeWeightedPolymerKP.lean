/-
# Weighted (Dobrushin-form) Kotecký–Preiss bound for the signed polymer gas, with Z4 numbers

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: strong-coupling KP holds for U(1), so this is
not gap evidence by itself).  It generalizes `SignedPolymerKP` from one constant `M` and a
degree bound to per-polymer weights `m γ ≥ 1`, which permits unbounded degree.

Hypotheses, over the FINITE list Λ:
* `|z a| ≤ e a`, stated as `0 ≤ z a + e a` and `0 ≤ e a − z a`, with `e ≥ 0`;
* `Cond Λ`: `∀ a, m a · (e a · Π_{x ∈ Λ, x ≁ a} m x) ≤ m a − 1`.  This is the rational
  Dobrushin condition; `m = e^{a(γ)}` in the classical form;
* `Cond2 Λ`: `∀ a, e a · Π_{x ∈ Λ, x ≁ a} m x ≤ 1`.

PROVED:
* `kpw_main`: `0 ≤ Ξ Λ`, and `Ξ(Λ∖b) ≤ m b · Ξ Λ` for every `b` at any position.
* `kpw_filter`: `Ξ(Λ.filter q) ≤ Π_{removed} m · Ξ Λ`.
* `kpw_lower`: `1 ≤ (Π_{x∈Λ} m x) · Ξ Λ`.
* `prod_le_sum`: `Π(1+δ) ≤ 1 + 2Σδ` when `2Σδ ≤ 1`.  This is the exp-free product-to-sum step.
* Numbers (Z4, K = 625):
  - `geom_quarter`: `Σ_{n=1}^N (1/4)^n ≤ 1/3`, i.e. the per-plaquette sum `Σ 625^n η^n` with
    `η = 1/2500`.
  - `z4_cond`: with `e γ = (1/10000)^{|γ|}`, `m γ = 1 + (1/2500)^{|γ|}` and `|γ| ≥ 1`, IF
    `Π_{x≁a}(1+δ x) ≤ (5/3)^{|a|}` (the hypothesis `hgroup`), THEN `Cond` and `Cond2` hold.

OPEN (stated, not proved):
* the grouping step `Π_{x≁a}(1+δx) ≤ Π_{p∈a}(1 + 2Σ_{x∋p} δx)`;
* the identification of the per-plaquette sum with `z4ClusterCountBound` (625^n), i.e. a
  duplicate-free enumeration of the box polymers through `p`;
* the ratio-Lipschitz decay.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SignedPolymerKP

namespace YMGap.Continuum.SizeWeightedPolymerKP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable {α : Type}

def prodm (m : α → Q') : List α → Q'
  | [] => 1
  | x :: l => m x * prodm m l

section prod
variable (m : α → Q') (hm : ∀ x, (1 : Q') ≤ m x)
include hm

theorem m_nonneg (x : α) : (0 : Q') ≤ m x := Q'.le_trans' _ _ _ (by decide) (hm x)

theorem prodm_ge_one : ∀ l : List α, (1 : Q') ≤ prodm m l
  | [] => Q'.le_refl' 1
  | x :: l => Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 1 * 1)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (hm x) (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (prodm_ge_one l) (m_nonneg m hm x)))

theorem prodm_nonneg (l : List α) : (0 : Q') ≤ prodm m l :=
  Q'.le_trans' _ _ _ (by decide) (prodm_ge_one m hm l)

theorem prodm_sub {l₁ l₂ : List α} (h : l₁.Sublist l₂) : prodm m l₁ ≤ prodm m l₂ := by
  induction h with
  | slnil => exact Q'.le_refl' _
  | cons a _ ih =>
    exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hm a) (prodm_nonneg m hm _)))
  | cons₂ a _ ih => exact Q'.mul_le_mul_of_nonneg_left _ _ _ ih (m_nonneg m hm a)

end prod

theorem sub_refl' : ∀ l : List α, l.Sublist l
  | [] => .slnil
  | a :: l => .cons₂ a (sub_refl' l)

theorem sub_filter (f : α → Bool) {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    (l₁.filter f).Sublist (l₂.filter f) := by
  induction h with
  | slnil => exact .slnil
  | cons a _ ih =>
    cases hf : f a
    · simp only [List.filter, hf]; exact ih
    · simp only [List.filter, hf]; exact .cons a ih
  | cons₂ a _ ih =>
    cases hf : f a
    · simp only [List.filter, hf]; exact ih
    · simp only [List.filter, hf]; exact .cons₂ a ih

theorem sub_filter_self (q : α → Bool) : ∀ l : List α, (l.filter q).Sublist l
  | [] => .slnil
  | a :: l => by
    cases hq : q a
    · simp only [List.filter, hq]; exact .cons a (sub_filter_self q l)
    · simp only [List.filter, hq]; exact .cons₂ a (sub_filter_self q l)

theorem sub_remove (b : α) (r : List α) : ∀ p : List α, (p ++ r).Sublist (p ++ b :: r)
  | [] => .cons b (sub_refl' r)
  | a :: p => .cons₂ a (sub_remove b r p)

/-! ## Conditions and the weighted KP induction -/

variable (z : α → Q') (inc : α → α → Bool) (e m : α → Q')

def Cond (l : List α) : Prop :=
  ∀ a, m a * (e a * prodm m (l.filter (inc a))) ≤ m a + -1

def Cond2 (l : List α) : Prop := ∀ a, e a * prodm m (l.filter (inc a)) ≤ 1

section KPW
variable (hsym : ∀ a b, inc a b = inc b a) (hm : ∀ x, (1 : Q') ≤ m x)
variable (he : ∀ a, (0 : Q') ≤ e a) (hz1 : ∀ a, (0 : Q') ≤ z a + e a)

include hm he in
theorem cond_mono {l₁ l₂ : List α} (h : l₁.Sublist l₂) (H : Cond inc e m l₂) :
    Cond inc e m l₁ := fun a =>
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (prodm_sub m hm (sub_filter (inc a) h)) (he a))
    (m_nonneg m hm a)) (H a)

include hm he in
theorem cond2_mono {l₁ l₂ : List α} (h : l₁.Sublist l₂) (H : Cond2 inc e m l₂) :
    Cond2 inc e m l₁ := fun a =>
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (prodm_sub m hm (sub_filter (inc a) h)) (he a)) (H a)

def GW (n : Nat) : Prop :=
  ∀ Λ : List α, Λ.length ≤ n → Cond inc e m Λ → Cond2 inc e m Λ →
    (0 : Q') ≤ Xi z inc Λ ∧
    ∀ p b r, Λ = p ++ b :: r → Xi z inc (p ++ r) ≤ m b * Xi z inc Λ

include hm he in
theorem BW {n : Nat} (hG : GW z inc e m n) (q : α → Bool) :
    ∀ (l pre : List α), (pre ++ l).length ≤ n → Cond inc e m (pre ++ l) →
      Cond2 inc e m (pre ++ l) →
      Xi z inc (pre ++ l.filter q) ≤ prodm m (l.filter (fun x => !q x)) * Xi z inc (pre ++ l)
  | [], pre, _, _, _ => by
    simp only [List.filter, prodm]
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  | b :: l, pre, hlen, hc, hc2 => by
    cases hq : q b
    · have hlen' : (pre ++ l).length ≤ n := by
        simp only [List.length_append, List.length_cons] at hlen ⊢; omega
      have hs := sub_remove b l pre
      have ih := BW hG q l pre hlen' (cond_mono inc e m hm he hs hc)
        (cond2_mono inc e m hm he hs hc2)
      have hrem := (hG (pre ++ b :: l) hlen hc hc2).2 pre b l rfl
      have hk := prodm_nonneg m hm (l.filter (fun x => !q x))
      simp only [List.filter, hq, Bool.not_false, prodm]
      refine Q'.le_trans' _ _ _ ih ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hrem hk) (Q'.le_of_eqv ?_)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) ((V 1 * V 0) * V 2) (by decide)
        (fun | 0 => prodm m (l.filter (fun x => !q x)) | 1 => m b
             | _ => Xi z inc (pre ++ b :: l))
    · have e1 : pre ++ b :: l = (pre ++ [b]) ++ l := by simp
      have ih := BW hG q l (pre ++ [b]) (by rw [← e1]; exact hlen) (by rw [← e1]; exact hc)
        (by rw [← e1]; exact hc2)
      simp only [List.filter, hq, Bool.not_true]
      rw [e1]
      have e2 : pre ++ b :: l.filter q = (pre ++ [b]) ++ l.filter q := by simp
      rw [e2]
      exact ih

include hsym hm he hz1 in
theorem GW_succ (n : Nat) (hG : GW z inc e m n) : GW z inc e m (n + 1) := by
  have step : ∀ (b : α) (s : List α), s.length ≤ n → Cond inc e m s → Cond2 inc e m s →
      Xi z inc s ≤ m b * Xi z inc (b :: s) ∧ (0 : Q') ≤ Xi z inc (b :: s) := by
    intro b s hs hc hc2
    have hsub := sub_filter_self (cpt inc b) s
    have hX := (hG s hs hc hc2).1
    have hY := (hG _ (Nat.le_trans (flen _ _) hs) (cond_mono inc e m hm he hsub hc)
      (cond2_mono inc e m hm he hsub hc2)).1
    have hB := BW z inc e m hm he hG (cpt inc b) s [] hs hc hc2
    simp only [List.nil_append] at hB
    have hfe : s.filter (fun x => !cpt inc b x) = s.filter (inc b) :=
      filter_congr' (fun x => !cpt inc b x) (inc b) (fun x => by simp [cpt]) s
    rw [hfe] at hB
    have hd0 := Q'.sub_nonneg_of_le hB
    rw [Xi_cons]
    let V := PolyExpr.var
    let X := Xi z inc s
    let Y := Xi z inc (s.filter (cpt inc b))
    let P := prodm m (s.filter (inc b))
    have h0M := m_nonneg m hm b
    constructor
    · refine le_of_eqv_add (S := m b * ((z b + e b) * Y) + m b * (e b * (P * X + -Y)) +
        (m b + -1 + -(m b * (e b * P))) * X) ?_ ?_
      · exact poly_identity_of_normal_eq (V 0 * (V 1 + V 2 * V 3))
          (V 1 + (V 0 * ((V 2 + V 4) * V 3) + V 0 * (V 4 * (V 5 * V 1 + -V 3)) +
            (V 0 + -PolyExpr.const 1 + -(V 0 * (V 4 * V 5))) * V 1)) (by decide)
          (fun | 0 => m b | 1 => X | 2 => z b | 3 => Y | 4 => e b | _ => P)
      · exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ h0M (Q'.mul_nonneg _ _ (hz1 b) hY))
          (Q'.mul_nonneg _ _ h0M (Q'.mul_nonneg _ _ (he b) hd0)))
          (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (hc b)) hX)
    · refine le_of_eqv_add (B := 0) (S := (z b + e b) * Y + (e b * (P * X + -Y) +
        (1 + -(e b * P)) * X)) ?_ ?_
      · exact poly_identity_of_normal_eq (V 1 + V 2 * V 3)
          (PolyExpr.const 0 + ((V 2 + V 4) * V 3 + (V 4 * (V 5 * V 1 + -V 3) +
            (PolyExpr.const 1 + -(V 4 * V 5)) * V 1))) (by decide)
          (fun | 0 => m b | 1 => X | 2 => z b | 3 => Y | 4 => e b | _ => P)
      · exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (hz1 b) hY)
          (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (he b) hd0)
            (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (hc2 b)) hX))
  intro Λ hlen hc hc2
  constructor
  · cases Λ with
    | nil => rw [Xi_nil]; decide
    | cons b s =>
      have hs : s.length ≤ n := by simp only [List.length_cons] at hlen; omega
      have hsub := sub_remove b s []
      exact (step b s hs (cond_mono inc e m hm he hsub hc)
        (cond2_mono inc e m hm he hsub hc2)).2
  · intro p b r hΛ
    subst hΛ
    have hs : (p ++ r).length ≤ n := by
      simp only [List.length_append, List.length_cons] at hlen ⊢; omega
    have hsub := sub_remove b r p
    have h1 := (step b (p ++ r) hs (cond_mono inc e m hm he hsub hc)
      (cond2_mono inc e m hm he hsub hc2)).1
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Xi_front z inc hsym p b r))))

include hsym hm he hz1 in
theorem GW_all : ∀ n, GW z inc e m n
  | 0 => fun Λ hlen _ _ => by
    cases Λ with
    | nil => exact ⟨by rw [Xi_nil]; decide, fun p b r h => by cases p <;> simp at h⟩
    | cons _ _ => simp at hlen
  | n + 1 => GW_succ z inc e m hsym hm he hz1 n (GW_all n)

include hsym hm he hz1 in
/-- **Weighted KP main (PROVED).** -/
theorem kpw_main (Λ : List α) (hc : Cond inc e m Λ) (hc2 : Cond2 inc e m Λ) :
    (0 : Q') ≤ Xi z inc Λ ∧
    ∀ p b r, Λ = p ++ b :: r → Xi z inc (p ++ r) ≤ m b * Xi z inc Λ :=
  GW_all z inc e m hsym hm he hz1 Λ.length Λ (Nat.le_refl _) hc hc2

include hsym hm he hz1 in
theorem kpw_filter (Λ : List α) (hc : Cond inc e m Λ) (hc2 : Cond2 inc e m Λ)
    (q : α → Bool) :
    Xi z inc (Λ.filter q) ≤ prodm m (Λ.filter (fun x => !q x)) * Xi z inc Λ :=
  BW z inc e m hm he (GW_all z inc e m hsym hm he hz1 Λ.length) q Λ [] (Nat.le_refl _) hc hc2

include hsym hm he hz1 in
/-- Volume lower bound `Ξ(Λ) ≥ 1/Π m`. -/
theorem kpw_lower (Λ : List α) (hc : Cond inc e m Λ) (hc2 : Cond2 inc e m Λ) :
    (1 : Q') ≤ prodm m Λ * Xi z inc Λ := by
  have h := kpw_filter z inc e m hsym hm he hz1 Λ hc hc2 (fun _ => false)
  rw [filter_false_nil, filter_true_self, Xi_nil] at h
  exact h

end KPW

/-! ## Exp-free product-to-sum -/

def sumd (δ : α → Q') : List α → Q'
  | [] => 0
  | x :: l => δ x + sumd δ l

theorem sumd_nonneg (δ : α → Q') (hδ : ∀ x, (0 : Q') ≤ δ x) : ∀ l, (0 : Q') ≤ sumd δ l
  | [] => Q'.le_refl' 0
  | x :: l => Q'.zero_le_add _ _ (hδ x) (sumd_nonneg δ hδ l)

/-- `Π(1+δ) ≤ 1 + 2Σδ` whenever `2Σδ ≤ 1`. -/
theorem prod_le_sum (δ : α → Q') (hδ : ∀ x, (0 : Q') ≤ δ x) :
    ∀ l : List α, sumd δ l + sumd δ l ≤ 1 →
      prodm (fun x => 1 + δ x) l ≤ 1 + (sumd δ l + sumd δ l)
  | [], _ => by
    show (1 : Q') ≤ 1 + (0 + 0)
    decide
  | x :: l, h => by
    have hS := sumd_nonneg δ hδ l
    have hl : sumd δ l + sumd δ l ≤ 1 := Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.add_le_self_of_nonneg _ _ (hδ x))
        (Q'.add_le_self_of_nonneg _ _ (hδ x)))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq ((V 0 + V 1) + (V 0 + V 1))
          ((V 1 + V 0) + (V 1 + V 0)) (by decide)
          (fun | 0 => sumd δ l | _ => δ x))) h)
    have ih := prod_le_sum δ hδ l hl
    have h1x : (0 : Q') ≤ 1 + δ x := Q'.zero_le_add _ _ (by decide) (hδ x)
    show (1 + δ x) * prodm (fun x => 1 + δ x) l ≤ 1 + ((δ x + sumd δ l) + (δ x + sumd δ l))
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih h1x) ?_
    refine le_of_eqv_add (S := δ x * (1 + -(sumd δ l + sumd δ l))) ?_
      (Q'.mul_nonneg _ _ (hδ x) (Q'.sub_nonneg_of_le hl))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq
      (PolyExpr.const 1 + ((V 0 + V 1) + (V 0 + V 1)))
      ((PolyExpr.const 1 + V 0) * (PolyExpr.const 1 + (V 1 + V 1)) +
        V 0 * (PolyExpr.const 1 + -(V 1 + V 1))) (by decide)
      (fun | 0 => δ x | _ => sumd δ l)

/-! ## Z4 numbers -/

def quarter : Q' := Q'.mkPos 1 4 (by decide)
def third : Q' := Q'.mkPos 1 3 (by decide)

def geoS : Nat → Q'
  | 0 => 0
  | n + 1 => geoS n + quarter ^ (n + 1)

/-- Exact closed form `Σ_{k=1}^n (1/4)^k + (1/3)(1/4)^n = 1/3`. -/
theorem geoS_closed : ∀ n, (geoS n + third * quarter ^ n).eqv third
  | 0 => by decide
  | n + 1 => by
    have ih := geoS_closed n
    have key : (geoS n + quarter ^ (n + 1) + third * quarter ^ (n + 1)).eqv
        (geoS n + third * quarter ^ n) := by
      show (geoS n + quarter * quarter ^ n + third * (quarter * quarter ^ n)).eqv
        (geoS n + third * quarter ^ n)
      let V := PolyExpr.var
      have hq : (quarter + third * quarter).eqv third := by decide
      have := poly_identity_of_normal_eq
        (V 0 + V 1 * V 2 + V 3 * (V 1 * V 2)) (V 0 + (V 1 + V 3 * V 1) * V 2) (by decide)
        (fun | 0 => geoS n | 1 => quarter | 2 => quarter ^ n | _ => third)
      exact Q'.eqv_trans _ _ _ this (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_right _ _ _ hq))
    exact Q'.eqv_trans _ _ _ key ih

/-- Per-plaquette geometric closure: `Σ_{n=1}^N (625·η)^n ≤ 1/3` at `η = 1/2500`. -/
theorem geom_quarter (n : Nat) : geoS n ≤ third := by
  have hnn : (0 : Q') ≤ third * quarter ^ n :=
    Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) n)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hnn) (Q'.le_of_eqv (geoS_closed n))

def epsZ : Q' := Q'.mkPos 1 10000 (by decide)
def etaZ : Q' := Q'.mkPos 1 2500 (by decide)

theorem pow_le_pow_base' {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) : ∀ k : Nat, a ^ k ≤ b ^ k
  | 0 => Q'.le_refl' 1
  | k + 1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hab (Q'.pow_nonneg a ha k))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_le_pow_base' ha hab k)
        (Q'.le_trans' _ _ _ ha hab))

/-- `(1 + η^k)·(ε^k·(5/3)^k) ≤ η^k` for `k ≥ 1`. -/
theorem z4_scalar (k : Nat) (hk : 1 ≤ k) :
    (1 + etaZ ^ k) * (epsZ ^ k * (Q'.mkPos 5 3 (by decide)) ^ k) ≤ etaZ ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let a : Q' := Q'.mkPos 1 6000 (by decide)
  have h0e : (0 : Q') ≤ etaZ := by decide
  have hA : (epsZ ^ (j+1) * (Q'.mkPos 5 3 (by decide)) ^ (j+1)).eqv
      ((epsZ * Q'.mkPos 5 3 (by decide)) ^ (j+1)) := by
    have : ∀ i : Nat, (epsZ ^ i * (Q'.mkPos 5 3 (by decide)) ^ i).eqv
        ((epsZ * Q'.mkPos 5 3 (by decide)) ^ i) := by
      intro i
      induction i with
      | zero => decide
      | succ i ih =>
        show (epsZ * epsZ ^ i * (Q'.mkPos 5 3 (by decide) * (Q'.mkPos 5 3 (by decide)) ^ i)).eqv
          (epsZ * Q'.mkPos 5 3 (by decide) * (epsZ * Q'.mkPos 5 3 (by decide)) ^ i)
        let V := PolyExpr.var
        refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
          (V 0 * V 1 * (V 2 * V 3)) (V 0 * V 2 * (V 1 * V 3)) (by decide)
          (fun | 0 => epsZ | 1 => epsZ ^ i | 2 => Q'.mkPos 5 3 (by decide)
               | _ => (Q'.mkPos 5 3 (by decide)) ^ i)) ?_
        exact Q'.mul_eqv_congr_left _ _ _ ih
    exact this (j+1)
  have hB : (epsZ * Q'.mkPos 5 3 (by decide)) ^ (j+1) ≤ a ^ (j+1) :=
    pow_le_pow_base' (by decide) (by decide) (j+1)
  have hη1 : etaZ ^ (j+1) ≤ 1 := by
    have := pow_le_pow_base' h0e (by decide : etaZ ≤ 1) (j+1)
    refine Q'.le_trans' _ _ _ this ?_
    have hone : ∀ i : Nat, ((1 : Q') ^ i) ≤ 1 := by
      intro i; induction i with
      | zero => exact Q'.le_refl' 1
      | succ i ih =>
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) ih
    exact hone (j+1)
  -- 2·a^{j+1} ≤ η^{j+1}
  have ha0 : (0 : Q') ≤ a := by decide
  have haη : a ≤ etaZ := by decide
  have h2 : ∀ i : Nat, (2 : Q') * a ^ (i+1) ≤ etaZ ^ (i+1) := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
      show (2 : Q') * (a * a ^ (i+1)) ≤ etaZ * etaZ ^ (i+1)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * (V 0 * V 2)) (by decide)
          (fun | 0 => (2 : Q') | 1 => a | _ => a ^ (i+1)))) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih ha0) ?_
      exact Q'.mul_le_mul_of_nonneg_right _ _ _ haη (Q'.pow_nonneg _ h0e _)
  have hpos : (0 : Q') ≤ epsZ ^ (j+1) * (Q'.mkPos 5 3 (by decide)) ^ (j+1) :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _) (Q'.pow_nonneg _ (by decide) _)
  have h1η : 1 + etaZ ^ (j+1) ≤ 2 := Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.le_refl' 1) hη1) (by decide)
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h1η hpos) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hA) hB) (by decide)) (h2 j)

/-- **Z4 numbers discharge `Cond`/`Cond2` (PROVED, given the grouping hypothesis).**
`e γ = ε^{|γ|}` with `ε = 1/10000`; `m γ = 1 + η^{|γ|}` with `η = 1/2500`. -/
theorem z4_cond (inc : α → α → Bool) (size : α → Nat) (hsize : ∀ a, 1 ≤ size a)
    (Λ : List α)
    (hgroup : ∀ a, prodm (fun x => 1 + etaZ ^ size x) (Λ.filter (inc a)) ≤
      (Q'.mkPos 5 3 (by decide)) ^ size a) :
    Cond inc (fun a => epsZ ^ size a) (fun x => 1 + etaZ ^ size x) Λ ∧
    Cond2 inc (fun a => epsZ ^ size a) (fun x => 1 + etaZ ^ size x) Λ := by
  have he : ∀ a, (0 : Q') ≤ epsZ ^ size a := fun a => Q'.pow_nonneg _ (by decide) _
  have hm0 : ∀ a, (0 : Q') ≤ 1 + etaZ ^ size a :=
    fun a => Q'.zero_le_add _ _ (by decide) (Q'.pow_nonneg _ (by decide) _)
  have core : ∀ a, epsZ ^ size a * prodm (fun x => 1 + etaZ ^ size x) (Λ.filter (inc a)) ≤
      epsZ ^ size a * (Q'.mkPos 5 3 (by decide)) ^ size a :=
    fun a => Q'.mul_le_mul_of_nonneg_left _ _ _ (hgroup a) (he a)
  constructor
  · intro a
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (core a) (hm0 a)) ?_
    refine Q'.le_trans' _ _ _ (z4_scalar (size a) (hsize a)) (Q'.le_of_eqv ?_)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0) (PolyExpr.const 1 + V 0 + -PolyExpr.const 1)
      (by decide) (fun _ => etaZ ^ size a)
  · intro a
    refine Q'.le_trans' _ _ _ (core a) ?_
    have hs := z4_scalar (size a) (hsize a)
    have hx : (0 : Q') ≤ epsZ ^ size a * (Q'.mkPos 5 3 (by decide)) ^ size a :=
      Q'.mul_nonneg _ _ (he a) (Q'.pow_nonneg _ (by decide) _)
    -- x ≤ (1+η^k)·x ≤ η^k ≤ 1
    have h1 : epsZ ^ size a * (Q'.mkPos 5 3 (by decide)) ^ size a ≤
        (1 + etaZ ^ size a) * (epsZ ^ size a * (Q'.mkPos 5 3 (by decide)) ^ size a) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)) hx)
    have hη : etaZ ^ size a ≤ 1 := by
      have := pow_le_pow_base' (by decide : (0 : Q') ≤ etaZ) (by decide : etaZ ≤ 1) (size a)
      refine Q'.le_trans' _ _ _ this ?_
      have hone : ∀ i : Nat, ((1 : Q') ^ i) ≤ 1 := by
        intro i; induction i with
        | zero => exact Q'.le_refl' 1
        | succ i ih => exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) ih
      exact hone _
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ hs hη)

end YMGap.Continuum.SizeWeightedPolymerKP

#print axioms YMGap.Continuum.SizeWeightedPolymerKP.kpw_main
#print axioms YMGap.Continuum.SizeWeightedPolymerKP.kpw_filter
#print axioms YMGap.Continuum.SizeWeightedPolymerKP.kpw_lower
#print axioms YMGap.Continuum.SizeWeightedPolymerKP.prod_le_sum
#print axioms YMGap.Continuum.SizeWeightedPolymerKP.geom_quarter
#print axioms YMGap.Continuum.SizeWeightedPolymerKP.z4_cond
