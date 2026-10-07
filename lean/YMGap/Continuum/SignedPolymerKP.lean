/-
# Finite Kotecký–Preiss / Dobrushin bound for a SIGNED polymer gas over Q'

ADDITIVE.  **GROUP-BLIND PLUMBING.**  Strong-coupling KP holds just as well for U(1), so
this is not gap evidence on its own.  It is the width-uniform replacement for the
per-face Doeblin margin (see `audits/SCOPE-POLYMER-KP-STRONG-COUPLING-2026-10-07.md`).

Abstract finite polymer system:
* any type `α`;
* activities `z : α → Q'`, which may be SIGNED;
* a symmetric incompatibility test `inc : α → α → Bool`;
* `Xi [] = 1` and `Xi (a :: l) = Xi l + z a · Xi (l.filter (compatible with a))`.

This differs from `AbstractPolymerXi.Xi`, whose activities are nonnegative.  For those the
lower bound `Ξ ≥ 1` is trivial.

Hypotheses.  All constants are independent of the list and the volume.
* `|z a| ≤ ε`, stated as `0 ≤ z a + ε` and `0 ≤ ε − z a`;
* every list in play has at most `D` elements incompatible with any given `a` (`DegOK D`);
* `M ≥ 1`, `M·ε·M^D ≤ M − 1`, and `ε·M^D ≤ 1`.

PROVED:
* `Xi_swap`, `Xi_front`: permutation moves.
* `kp_main`: for every `DegOK` list,
  - `0 ≤ Ξ(Λ)`, and
  - the one-polymer removal ratio `Ξ(p ++ r) ≤ M · Ξ(p ++ b :: r)`, i.e.
    `Ξ_Λ / Ξ_{Λ∖γ} ≥ 1/M`.
* `kp_filter`: `Ξ(Λ.filter q) ≤ M^{#removed} · Ξ(Λ)`.
* `kp_lower`: `1 ≤ M^{|Λ|} · Ξ(Λ)`.
* `kp_upper`: `Ξ(Λ) ≤ (1 + ε M^D)^{|Λ|}`.

So `−|Λ|·log M ≤ log Ξ ≤ |Λ|·log(1+εM^D)`, a per-polymer free-energy bound whose
constants depend only on `(ε, D)`.

NEXT (not here): decay of truncated correlations, and size-weighted (unbounded-degree)
activities `a(γ)`.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Geometric
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.SignedPolymerKP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## List filter facts (own, by induction) -/

theorem flen {β : Type} (p : β → Bool) : ∀ l : List β, (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := flen p l
    cases h : p a <;> simp only [List.filter, h, List.length_cons] <;> omega

theorem filter_comm {β : Type} (p q : β → Bool) :
    ∀ l : List β, (l.filter p).filter q = (l.filter q).filter p
  | [] => rfl
  | a :: l => by
    cases hp : p a <;> cases hq : q a <;> simp only [List.filter, hp, hq, filter_comm p q l]

theorem filter_app {β : Type} (f : β → Bool) :
    ∀ p r : List β, (p ++ r).filter f = p.filter f ++ r.filter f
  | [], _ => rfl
  | a :: p, r => by
    cases h : f a <;> simp only [List.cons_append, List.filter, h, filter_app f p r]

theorem filter_congr' {β : Type} (f g : β → Bool) (h : ∀ x, f x = g x) :
    ∀ l : List β, l.filter f = l.filter g
  | [] => rfl
  | a :: l => by simp only [List.filter, h a, filter_congr' f g h l]

theorem filter_filter_len {β : Type} (q f : β → Bool) :
    ∀ l : List β, ((l.filter q).filter f).length ≤ (l.filter f).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := filter_filter_len q f l
    cases hq : q a <;> cases hf : f a <;>
      simp only [List.filter, hq, hf, List.length_cons] <;> omega

theorem filter_false_nil {β : Type} : ∀ l : List β, l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: l => by simp only [List.filter, filter_false_nil l]

theorem filter_true_self {β : Type} : ∀ l : List β, l.filter (fun _ => !false) = l
  | [] => rfl
  | a :: l => congrArg (a :: ·) (filter_true_self l)

/-! ## The signed polymer partition function -/

variable {α : Type} (z : α → Q') (inc : α → α → Bool)

def cpt (a : α) : α → Bool := fun x => !inc a x

def Xi : List α → Q'
  | [] => 1
  | a :: l => Xi l + z a * Xi (l.filter (cpt inc a))
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Nat.lt_succ_of_le (flen _ _)
    | exact Nat.lt_succ_self _

theorem Xi_nil : Xi z inc [] = 1 := by rw [Xi]

theorem Xi_cons (a : α) (l : List α) :
    Xi z inc (a :: l) = Xi z inc l + z a * Xi z inc (l.filter (cpt inc a)) := by
  rw [Xi]

theorem step_congr {A A' B B' : Q'} (c : Q') (h1 : A.eqv A') (h2 : B.eqv B') :
    (A + c * B).eqv (A' + c * B') :=
  Q'.add_eqv_congr' h1 (Q'.mul_eqv_congr_left _ _ _ h2)

section sym
variable (hsym : ∀ a b, inc a b = inc b a)
include hsym

theorem Xi_swap (b x : α) (r : List α) :
    (Xi z inc (b :: x :: r)).eqv (Xi z inc (x :: b :: r)) := by
  let V := PolyExpr.var
  rw [Xi_cons, Xi_cons z inc x r, Xi_cons z inc x (b :: r), Xi_cons z inc b r]
  cases h : inc b x
  · have h' : inc x b = false := (hsym x b).trans h
    have e1 : (x :: r).filter (cpt inc b) = x :: r.filter (cpt inc b) := by
      simp only [List.filter, cpt, h, Bool.not_false]
    have e2 : (b :: r).filter (cpt inc x) = b :: r.filter (cpt inc x) := by
      simp only [List.filter, cpt, h', Bool.not_false]
    rw [e1, e2, Xi_cons z inc x, Xi_cons z inc b, filter_comm (cpt inc b) (cpt inc x) r]
    exact poly_identity_of_normal_eq
      ((V 0 + V 1 * V 2) + V 3 * (V 4 + V 1 * V 5))
      ((V 0 + V 3 * V 4) + V 1 * (V 2 + V 3 * V 5)) (by decide)
      (fun | 0 => Xi z inc r | 1 => z x | 2 => Xi z inc (r.filter (cpt inc x))
           | 3 => z b | 4 => Xi z inc (r.filter (cpt inc b))
           | _ => Xi z inc ((r.filter (cpt inc x)).filter (cpt inc b)))
  · have h' : inc x b = true := (hsym x b).trans h
    have e1 : (x :: r).filter (cpt inc b) = r.filter (cpt inc b) := by
      simp only [List.filter, cpt, h, Bool.not_true]
    have e2 : (b :: r).filter (cpt inc x) = r.filter (cpt inc x) := by
      simp only [List.filter, cpt, h', Bool.not_true]
    rw [e1, e2]
    exact poly_identity_of_normal_eq
      ((V 0 + V 1 * V 2) + V 3 * V 4) ((V 0 + V 3 * V 4) + V 1 * V 2) (by decide)
      (fun | 0 => Xi z inc r | 1 => z x | 2 => Xi z inc (r.filter (cpt inc x))
           | 3 => z b | _ => Xi z inc (r.filter (cpt inc b)))

theorem Xi_front_aux : ∀ n (p : List α), p.length ≤ n → ∀ (y : α) (r : List α),
    (Xi z inc (p ++ y :: r)).eqv (Xi z inc (y :: (p ++ r)))
  | _, [], _, _, _ => Q'.eqv_refl _
  | 0, _ :: _, hp, _, _ => absurd hp (by simp)
  | n + 1, b :: p', hp, y, r => by
    have hl : p'.length ≤ n := by simp only [List.length_cons] at hp; omega
    have hlf : (p'.filter (cpt inc b)).length ≤ n := Nat.le_trans (flen _ _) hl
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Xi_swap z inc hsym y b (p' ++ r)))
    show (Xi z inc (b :: (p' ++ y :: r))).eqv (Xi z inc (b :: y :: (p' ++ r)))
    rw [Xi_cons, Xi_cons z inc b (y :: (p' ++ r)), filter_app]
    cases h : inc b y
    · have e1 : (y :: r).filter (cpt inc b) = y :: r.filter (cpt inc b) := by
        simp only [List.filter, cpt, h, Bool.not_false]
      have e2 : (y :: (p' ++ r)).filter (cpt inc b) =
          y :: (p'.filter (cpt inc b) ++ r.filter (cpt inc b)) := by
        simp only [List.filter, cpt, h, Bool.not_false, filter_app]
      rw [e1, e2]
      exact step_congr (z b) (Xi_front_aux n p' hl y r)
        (Xi_front_aux n _ hlf y _)
    · have e1 : (y :: r).filter (cpt inc b) = r.filter (cpt inc b) := by
        simp only [List.filter, cpt, h, Bool.not_true]
      have e2 : (y :: (p' ++ r)).filter (cpt inc b) =
          p'.filter (cpt inc b) ++ r.filter (cpt inc b) := by
        simp only [List.filter, cpt, h, Bool.not_true, filter_app]
      rw [e1, e2]
      exact step_congr (z b) (Xi_front_aux n p' hl y r) (Q'.eqv_refl _)

theorem Xi_front (p : List α) (y : α) (r : List α) :
    (Xi z inc (p ++ y :: r)).eqv (Xi z inc (y :: (p ++ r))) :=
  Xi_front_aux z inc hsym p.length p (Nat.le_refl _) y r

end sym

/-! ## Degree bound and its stability -/

def DegOK (D : Nat) (l : List α) : Prop := ∀ a, (l.filter (inc a)).length ≤ D

theorem degOK_filter {D : Nat} {l : List α} (h : DegOK inc D l) (q : α → Bool) :
    DegOK inc D (l.filter q) := fun a => Nat.le_trans (filter_filter_len q (inc a) l) (h a)

theorem degOK_remove {D : Nat} (p : List α) (b : α) (r : List α)
    (h : DegOK inc D (p ++ b :: r)) : DegOK inc D (p ++ r) := fun a => by
  have := h a
  rw [filter_app] at this ⊢
  simp only [List.length_append] at this ⊢
  cases hb : inc a b <;> simp only [List.filter, hb, List.length_cons] at this <;> omega

/-! ## Q' helpers -/

theorem le_of_eqv_add {A B S : Q'} (h : A.eqv (B + S)) (hS : (0 : Q') ≤ S) : B ≤ A := by
  have h1 := Q'.add_le_add (Q'.le_refl' B) hS
  rw [Q'.add_zero'] at h1
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.eqv_symm h))

theorem pow_mono_exp {M : Q'} (hM : (1 : Q') ≤ M) : ∀ {k D : Nat}, k ≤ D → M ^ k ≤ M ^ D
  | k, 0, h => by
    have : k = 0 := by omega
    subst this; exact Q'.le_refl' _
  | k, D + 1, h => by
    have h0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (by decide) hM
    by_cases hk : k = D + 1
    · subst hk; exact Q'.le_refl' _
    · have ih : M ^ k ≤ M ^ D := pow_mono_exp hM (by omega)
      have hD : (0 : Q') ≤ M ^ D := Q'.pow_nonneg M h0 D
      have h2 : (1 : Q') * M ^ D ≤ M * M ^ D := Q'.mul_le_mul_of_nonneg_right _ _ _ hM hD
      exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))) h2)

/-! ## The KP induction -/

section KP
variable (hsym : ∀ a b, inc a b = inc b a)
variable (M ε : Q') (D : Nat) (hM : (1 : Q') ≤ M) (hε : (0 : Q') ≤ ε)
variable (hz1 : ∀ a, (0 : Q') ≤ z a + ε) (hz2 : ∀ a, (0 : Q') ≤ ε + -(z a))
variable (hsmall : M * (ε * M ^ D) ≤ M + -1) (hle1 : ε * M ^ D ≤ 1)

def G (n : Nat) : Prop :=
  ∀ Λ : List α, Λ.length ≤ n → DegOK inc D Λ →
    (0 : Q') ≤ Xi z inc Λ ∧
    ∀ p b r, Λ = p ++ b :: r → Xi z inc (p ++ r) ≤ M * Xi z inc Λ

include hM in
theorem B_of_G {n : Nat} (hG : G z inc M D n) (q : α → Bool) :
    ∀ (l pre : List α), (pre ++ l).length ≤ n → DegOK inc D (pre ++ l) →
      Xi z inc (pre ++ l.filter q) ≤
        M ^ (l.filter (fun x => !q x)).length * Xi z inc (pre ++ l)
  | [], pre, _, _ => by
    simp only [List.filter, List.length_nil]
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  | b :: l, pre, hlen, hdeg => by
    cases hq : q b
    · have hlen' : (pre ++ l).length ≤ n := by
        simp only [List.length_append, List.length_cons] at hlen ⊢; omega
      have ih := B_of_G hG q l pre hlen' (degOK_remove inc pre b l hdeg)
      have hrem := (hG (pre ++ b :: l) hlen hdeg).2 pre b l rfl
      have h0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (by decide) hM
      have hk := Q'.pow_nonneg M h0 (l.filter (fun x => !q x)).length
      simp only [List.filter, hq, Bool.not_false, List.length_cons]
      refine Q'.le_trans' _ _ _ ih ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hrem hk) (Q'.le_of_eqv ?_)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) ((V 1 * V 0) * V 2) (by decide)
        (fun | 0 => M ^ (l.filter (fun x => !q x)).length | 1 => M
             | _ => Xi z inc (pre ++ b :: l))
    · have e : pre ++ b :: l = (pre ++ [b]) ++ l := by simp
      have ih := B_of_G hG q l (pre ++ [b]) (by rw [← e]; exact hlen) (by rw [← e]; exact hdeg)
      simp only [List.filter, hq, Bool.not_true]
      rw [e]
      have e2 : pre ++ b :: l.filter q = (pre ++ [b]) ++ l.filter q := by simp
      rw [e2]
      exact ih

include hsym hM hε hz1 hsmall hle1 in
theorem G_succ (n : Nat) (hG : G z inc M D n) : G z inc M D (n + 1) := by
  -- one-polymer step on `b :: s` for any short `s`
  have step : ∀ (b : α) (s : List α), s.length ≤ n → DegOK inc D s →
      Xi z inc s ≤ M * Xi z inc (b :: s) ∧ (0 : Q') ≤ Xi z inc (b :: s) := by
    intro b s hs hd
    have hX := (hG s hs hd).1
    have hY := (hG _ (Nat.le_trans (flen _ _) hs) (degOK_filter inc hd (cpt inc b))).1
    have hB := B_of_G z inc M D hM hG (cpt inc b) s [] hs hd
    simp only [List.nil_append] at hB
    have hk : (s.filter (fun x => !cpt inc b x)).length ≤ D := by
      rw [filter_congr' _ (inc b) (fun x => by simp [cpt]) s]; exact hd b
    have hP : Xi z inc (s.filter (cpt inc b)) ≤ M ^ D * Xi z inc s :=
      Q'.le_trans' _ _ _ hB (Q'.mul_le_mul_of_nonneg_right _ _ _ (pow_mono_exp hM hk) hX)
    have hd0 := Q'.sub_nonneg_of_le hP
    rw [Xi_cons]
    let V := PolyExpr.var
    let X := Xi z inc s
    let Y := Xi z inc (s.filter (cpt inc b))
    let P := M ^ D
    constructor
    · refine le_of_eqv_add (S := M * ((z b + ε) * Y) + M * (ε * (P * X + -Y)) +
        (M + -1 + -(M * (ε * P))) * X) ?_ ?_
      · exact poly_identity_of_normal_eq (V 0 * (V 1 + V 2 * V 3))
          (V 1 + (V 0 * ((V 2 + V 4) * V 3) + V 0 * (V 4 * (V 5 * V 1 + -V 3)) +
            (V 0 + -PolyExpr.const 1 + -(V 0 * (V 4 * V 5))) * V 1)) (by decide)
          (fun | 0 => M | 1 => X | 2 => z b | 3 => Y | 4 => ε | _ => P)
      · have h0M : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (by decide) hM
        exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ h0M (Q'.mul_nonneg _ _ (hz1 b) hY))
          (Q'.mul_nonneg _ _ h0M (Q'.mul_nonneg _ _ hε hd0)))
          (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hsmall) hX)
    · refine le_of_eqv_add (B := 0) (S := (z b + ε) * Y + (ε * (P * X + -Y) +
        (1 + -(ε * P)) * X)) ?_ ?_
      · exact poly_identity_of_normal_eq (V 1 + V 2 * V 3)
          (PolyExpr.const 0 + ((V 2 + V 4) * V 3 + (V 4 * (V 5 * V 1 + -V 3) +
            (PolyExpr.const 1 + -(V 4 * V 5)) * V 1))) (by decide)
          (fun | 0 => M | 1 => X | 2 => z b | 3 => Y | 4 => ε | _ => P)
      · exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (hz1 b) hY)
          (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hε hd0)
            (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hle1) hX))
  intro Λ hlen hdeg
  constructor
  · cases Λ with
    | nil => rw [Xi_nil]; decide
    | cons b s =>
      have hs : s.length ≤ n := by simp only [List.length_cons] at hlen; omega
      exact (step b s hs (degOK_remove inc [] b s hdeg)).2
  · intro p b r hΛ
    subst hΛ
    have hs : (p ++ r).length ≤ n := by
      simp only [List.length_append, List.length_cons] at hlen ⊢; omega
    have h1 := (step b (p ++ r) hs (degOK_remove inc p b r hdeg)).1
    have h0M : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (by decide) hM
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Xi_front z inc hsym p b r))))

include hsym hM hε hz1 hsmall hle1 in
theorem G_all : ∀ n, G z inc M D n
  | 0 => fun Λ hlen _ => by
    cases Λ with
    | nil => exact ⟨by rw [Xi_nil]; decide, fun p b r h => by
        cases p <;> simp at h⟩
    | cons _ _ => simp at hlen
  | n + 1 => G_succ z inc hsym M ε D hM hε hz1 hsmall hle1 n
      (G_all n)

include hsym hM hε hz1 hsmall hle1 in
/-- **KP main (PROVED).** Nonnegativity and the one-polymer removal ratio. -/
theorem kp_main (Λ : List α) (hdeg : DegOK inc D Λ) :
    (0 : Q') ≤ Xi z inc Λ ∧
    ∀ p b r, Λ = p ++ b :: r → Xi z inc (p ++ r) ≤ M * Xi z inc Λ :=
  G_all z inc hsym M ε D hM hε hz1 hsmall hle1 Λ.length Λ (Nat.le_refl _) hdeg

include hsym hM hε hz1 hsmall hle1 in
/-- Removing any set of polymers costs at most a factor `M` each. -/
theorem kp_filter (Λ : List α) (hdeg : DegOK inc D Λ) (q : α → Bool) :
    Xi z inc (Λ.filter q) ≤ M ^ (Λ.filter (fun x => !q x)).length * Xi z inc Λ :=
  B_of_G z inc M D hM (G_all z inc hsym M ε D hM hε hz1 hsmall hle1 Λ.length) q Λ []
    (Nat.le_refl _) hdeg

include hsym hM hε hz1 hsmall hle1 in
/-- Volume lower bound: `Ξ(Λ) ≥ M^{-|Λ|}`. -/
theorem kp_lower (Λ : List α) (hdeg : DegOK inc D Λ) :
    (1 : Q') ≤ M ^ Λ.length * Xi z inc Λ := by
  have h := kp_filter z inc hsym M ε D hM hε hz1 hsmall hle1 Λ hdeg (fun _ => false)
  rw [filter_false_nil, filter_true_self, Xi_nil] at h
  exact h

include hε hz2 in
/-- Volume upper bound: `Ξ(Λ) ≤ (1 + ε M^D)^{|Λ|}` (uses only nonnegativity and filters). -/
theorem kp_upper (hpos : ∀ Λ : List α, DegOK inc D Λ → (0 : Q') ≤ Xi z inc Λ)
    (hfil : ∀ Λ : List α, DegOK inc D Λ → ∀ q : α → Bool,
      Xi z inc (Λ.filter q) ≤ M ^ (Λ.filter (fun x => !q x)).length * Xi z inc Λ)
    (hM : (1 : Q') ≤ M) :
    ∀ Λ : List α, DegOK inc D Λ → Xi z inc Λ ≤ (1 + ε * M ^ D) ^ Λ.length
  | [], _ => by rw [Xi_nil]; exact Q'.le_refl' _
  | b :: s, hdeg => by
    have hd := degOK_remove inc [] b s hdeg
    have ih := kp_upper hpos hfil hM s hd
    have hX := hpos s hd
    have hY := hpos _ (degOK_filter inc hd (cpt inc b))
    have hk : (s.filter (fun x => !cpt inc b x)).length ≤ D := by
      rw [filter_congr' _ (inc b) (fun x => by simp [cpt]) s]; exact hd b
    have hP : Xi z inc (s.filter (cpt inc b)) ≤ M ^ D * Xi z inc s :=
      Q'.le_trans' _ _ _ (hfil s hd (cpt inc b))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (pow_mono_exp hM hk) hX)
    have hd0 := Q'.sub_nonneg_of_le hP
    rw [Xi_cons]
    let V := PolyExpr.var
    let X := Xi z inc s
    let Y := Xi z inc (s.filter (cpt inc b))
    let P := M ^ D
    have h1 : X + z b * Y ≤ (1 + ε * P) * X :=
      le_of_eqv_add (S := (ε + -(z b)) * Y + ε * (P * X + -Y))
        (poly_identity_of_normal_eq ((PolyExpr.const 1 + V 4 * V 5) * V 1)
          ((V 1 + V 2 * V 3) + ((V 4 + -V 2) * V 3 + V 4 * (V 5 * V 1 + -V 3))) (by decide)
          (fun | 0 => M | 1 => X | 2 => z b | 3 => Y | 4 => ε | _ => P))
        (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (hz2 b) hY) (Q'.mul_nonneg _ _ hε hd0))
    have hc : (0 : Q') ≤ 1 + ε * P :=
      Q'.zero_le_add _ _ (by decide)
        (Q'.mul_nonneg _ _ hε (Q'.pow_nonneg M (Q'.le_trans' _ _ _ (by decide) hM) D))
    exact Q'.le_trans' _ _ _ h1 (Q'.mul_le_mul_of_nonneg_left _ _ _ ih hc)

end KP

end YMGap.Continuum.SignedPolymerKP

#print axioms YMGap.Continuum.SignedPolymerKP.Xi_front
#print axioms YMGap.Continuum.SignedPolymerKP.kp_main
#print axioms YMGap.Continuum.SignedPolymerKP.kp_filter
#print axioms YMGap.Continuum.SignedPolymerKP.kp_lower
#print axioms YMGap.Continuum.SignedPolymerKP.kp_upper
