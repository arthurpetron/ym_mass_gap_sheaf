/-
# Exact decoupling of the signed polymer gas (infinite-distance clustering)

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).
This is the strongest honest special case of truncated-correlation decay reached so far.

* `Xi_append_decoupled` (PROVED): if every polymer of `Λ₁` is compatible with every polymer
  of `Λ₂`, then `Ξ(Λ₁ ++ Λ₂) ≈ Ξ(Λ₁)·Ξ(Λ₂)`.  Activities are signed and no smallness is
  needed.
* `truncated_zero_of_decoupled` (PROVED): let `A` (removed by `qA`) touch only `Λ₁` and
  `B` (removed by `qB`) touch only `Λ₂`.  Then the truncated two-point quantity
  `Ξ(Λ∖A∖B)·Ξ(Λ) − Ξ(Λ∖A)·Ξ(Λ∖B)` is ≈ 0.  That is decay at incidence distance d = ∞.

OPEN (NOT proved here): the quantitative bound
`|Ξ(Λ∖A∖B)Ξ(Λ) − Ξ(Λ∖A)Ξ(Λ∖B)| ≤ C (ε M^D)^d · Ξ(Λ)Ξ(Λ∖A∖B)` at finite distance d.
The head-peeling recursion does not close on the truncated quantity (cross terms appear).
A replica (doubled-gas) or ratio-Lipschitz induction is needed.  See
`audits/SCOPE-POLYMER-KP-STRONG-COUPLING-2026-10-07.md`.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SignedPolymerKP

namespace YMGap.Continuum.SignedPolymerDecoupling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

theorem mulc {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') : (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

variable {α : Type} (z : α → Q') (inc : α → α → Bool)

theorem mem_of_mem_filter' {β : Type} (f : β → Bool) {x : β} :
    ∀ {l : List β}, x ∈ l.filter f → x ∈ l
  | [], h => by simp only [List.filter] at h; exact absurd h List.not_mem_nil
  | a :: l, h => by
    cases hf : f a
    · simp only [List.filter, hf] at h; exact List.mem_cons_of_mem _ (mem_of_mem_filter' f h)
    · simp only [List.filter, hf] at h
      cases h with
      | head => exact List.mem_cons_self
      | tail _ h' => exact List.mem_cons_of_mem _ (mem_of_mem_filter' f h')

theorem filter_all {β : Type} (f : β → Bool) :
    ∀ l : List β, (∀ y, y ∈ l → f y = true) → l.filter f = l
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    simp only [List.filter, ha,
      filter_all f l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

def Decoupled (Λ₁ Λ₂ : List α) : Prop := ∀ x, x ∈ Λ₁ → ∀ y, y ∈ Λ₂ → inc x y = false

theorem decoupled_filter_left {Λ₁ Λ₂ : List α} (h : Decoupled inc Λ₁ Λ₂) (q : α → Bool) :
    Decoupled inc (Λ₁.filter q) Λ₂ := fun x hx y hy => h x (mem_of_mem_filter' q hx) y hy

theorem decoupled_filter_right {Λ₁ Λ₂ : List α} (h : Decoupled inc Λ₁ Λ₂) (q : α → Bool) :
    Decoupled inc Λ₁ (Λ₂.filter q) := fun x hx y hy => h x hx y (mem_of_mem_filter' q hy)

theorem Xi_append_aux : ∀ n (Λ₁ Λ₂ : List α), Λ₁.length ≤ n → Decoupled inc Λ₁ Λ₂ →
    (Xi z inc (Λ₁ ++ Λ₂)).eqv (Xi z inc Λ₁ * Xi z inc Λ₂)
  | _, [], Λ₂, _, _ => by
    rw [Xi_nil]; exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | 0, _ :: _, _, h, _ => absurd h (by simp)
  | n + 1, a :: l, Λ₂, hl, hd => by
    have hl' : l.length ≤ n := by simp only [List.length_cons] at hl; omega
    have hdl : Decoupled inc l Λ₂ := fun x hx y hy => hd x (List.mem_cons_of_mem _ hx) y hy
    have hkeep : Λ₂.filter (cpt inc a) = Λ₂ :=
      filter_all _ Λ₂ (fun y hy => by simp [cpt, hd a List.mem_cons_self y hy])
    rw [List.cons_append, Xi_cons, Xi_cons, filter_app, hkeep]
    have h1 := Xi_append_aux n l Λ₂ hl' hdl
    have h2 := Xi_append_aux n (l.filter (cpt inc a)) Λ₂ (Nat.le_trans (flen _ _) hl')
      (decoupled_filter_left inc hdl _)
    refine Q'.eqv_trans _ _ _ (step_congr (z a) h1 h2) ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 + V 2 * (V 3 * V 1))
      ((V 0 + V 2 * V 3) * V 1) (by decide)
      (fun | 0 => Xi z inc l | 1 => Xi z inc Λ₂ | 2 => z a
           | _ => Xi z inc (l.filter (cpt inc a)))

/-- **Exact factorization (PROVED).** -/
theorem Xi_append_decoupled (Λ₁ Λ₂ : List α) (hd : Decoupled inc Λ₁ Λ₂) :
    (Xi z inc (Λ₁ ++ Λ₂)).eqv (Xi z inc Λ₁ * Xi z inc Λ₂) :=
  Xi_append_aux z inc Λ₁.length Λ₁ Λ₂ (Nat.le_refl _) hd

/-- **Truncated two-point quantity vanishes at infinite distance (PROVED).** -/
theorem truncated_zero_of_decoupled (Λ₁ Λ₂ : List α) (hd : Decoupled inc Λ₁ Λ₂)
    (qA qB : α → Bool) (hA : ∀ y, y ∈ Λ₂ → qA y = true) (hB : ∀ y, y ∈ Λ₁ → qB y = true) :
    (Xi z inc (((Λ₁ ++ Λ₂).filter qA).filter qB) * Xi z inc (Λ₁ ++ Λ₂)).eqv
      (Xi z inc ((Λ₁ ++ Λ₂).filter qA) * Xi z inc ((Λ₁ ++ Λ₂).filter qB)) := by
  have hBA : ∀ y, y ∈ Λ₁.filter qA → qB y = true :=
    fun y hy => hB y (mem_of_mem_filter' qA hy)
  have hAB : ∀ y, y ∈ Λ₂.filter qB → qA y = true :=
    fun y hy => hA y (mem_of_mem_filter' qB hy)
  rw [filter_app, filter_app, filter_app, filter_all qA Λ₂ hA, filter_all qB Λ₁ hB,
    filter_all qB _ hBA]
  have e1 := Xi_append_decoupled z inc (Λ₁.filter qA) (Λ₂.filter qB)
    (decoupled_filter_right inc (decoupled_filter_left inc hd qA) qB)
  have e2 := Xi_append_decoupled z inc Λ₁ Λ₂ hd
  have e3 := Xi_append_decoupled z inc (Λ₁.filter qA) Λ₂ (decoupled_filter_left inc hd qA)
  have e4 := Xi_append_decoupled z inc Λ₁ (Λ₂.filter qB) (decoupled_filter_right inc hd qB)
  refine Q'.eqv_trans _ _ _ (mulc e1 e2) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (mulc e3 e4))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq ((V 0 * V 1) * (V 2 * V 3)) ((V 0 * V 3) * (V 2 * V 1))
    (by decide)
    (fun | 0 => Xi z inc (Λ₁.filter qA) | 1 => Xi z inc (Λ₂.filter qB)
         | 2 => Xi z inc Λ₁ | _ => Xi z inc Λ₂)

end YMGap.Continuum.SignedPolymerDecoupling

#print axioms YMGap.Continuum.SignedPolymerDecoupling.Xi_append_decoupled
#print axioms YMGap.Continuum.SignedPolymerDecoupling.truncated_zero_of_decoupled
