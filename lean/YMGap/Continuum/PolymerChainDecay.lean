/-
# Chain iteration for truncated polymer correlations (commit A of the d-decay)

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).

Generic signed polymer gas `Ξ = Xi z inc` with symmetric incompatibility.  Fix a reference
list `Γ`.  A list is `Good` if it is duplicate-free with all its members in `Γ`.

* `Xi_perm`: `Ξ` is invariant under permutation.
* `U y g l := Ξ(y::g::l)Ξ(l) − Ξ(y::l)Ξ(g::l)`: the truncated two-point quantity of y and g.
* `D y A C := Ξ(y::A)Ξ(C) − Ξ(y::C)Ξ(A)`: the cross-multiplied insertion-ratio difference.
* `telescope`: removing the list `R` from `R ++ F` costs at most `Σ_{h∈R} c_h`, where each
  `c_h` is a one-polymer `U` bound.  This is exact telescoping
  `D(A,C)Ξ_B = D(A,B)Ξ_C + D(B,C)Ξ_A`, cancelled with `Ξ_B > 0`.
* `chain_bound` (MAIN): under the explicit KP environment hypotheses
  - `0 < Ξ`,
  - `Ξ(l∖N a) ≤ M_a Ξ(l)`,
  - `Ξ(l) ≤ m_x Ξ(x::l)`,
  - `|z| ≤ ε`,

  every g at incompatibility distance `≥ d` from y (`far y d g`) satisfies
  `|U y g l| ≤ CS d g · Ξ(l)Ξ(g::l)`.  Here `CS` is the explicit chain sum
  - `CS 0 g = ε_g M_g m_g · 2(1+ε_y M_y)`,
  - `CS (d+1) g = ε_g M_g m_g · Σ_{h∈Γ, inc g h} CS d h`.

The geometric bound on `CS` (path count) is commit B.
-/

import YMGap.Continuum.PolymerRatioLipschitz
import YMGap.Constructive.CRealExp
import YMGap.Constructive.CRealAbs
import YMGap.Continuum.TorusWilsonAction

namespace YMGap.Continuum.PolymerChainDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable {α : Type} (z : α → Q') (inc : α → α → Bool)

/-! ## Permutation invariance -/

section perm
variable (hsym : ∀ a b, inc a b = inc b a)
include hsym

theorem Xi_perm_aux : ∀ n (l₁ l₂ : List α), l₁.Perm l₂ → l₁.length ≤ n →
    (Xi z inc l₁).eqv (Xi z inc l₂)
  | 0, l₁, l₂, hp, hl => by
    have h1 : l₁ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst h1
    rw [hp.symm.eq_nil]
    exact Q'.eqv_refl _
  | n + 1, l₁, l₂, hp, hl => by
    revert hl
    induction hp with
    | nil => intro _; exact Q'.eqv_refl _
    | cons x hp' _ =>
      intro hl
      have hl' : _ ≤ n := Nat.le_of_succ_le_succ hl
      rw [Xi_cons, Xi_cons z inc x]
      exact step_congr (z x) (Xi_perm_aux n _ _ hp' hl')
        (Xi_perm_aux n _ _ (hp'.filter _) (Nat.le_trans (flen _ _) hl'))
    | swap x y l => intro _; exact Xi_swap z inc hsym y x l
    | trans h₁ h₂ ih₁ ih₂ =>
      intro hl
      exact Q'.eqv_trans _ _ _ (ih₁ hl) (ih₂ (h₁.length_eq ▸ hl))

theorem Xi_perm {l₁ l₂ : List α} (hp : l₁.Perm l₂) : (Xi z inc l₁).eqv (Xi z inc l₂) :=
  Xi_perm_aux z inc hsym _ l₁ l₂ hp (Nat.le_refl _)

end perm

/-! ## Good lists and sums -/

def Good (Γ l : List α) : Prop := l.Nodup ∧ ∀ x, x ∈ l → x ∈ Γ

theorem good_sub {Γ l₁ l₂ : List α} (h : l₁.Sublist l₂) (hg : Good Γ l₂) : Good Γ l₁ :=
  ⟨hg.1.sublist h, fun x hx => hg.2 x (h.subset hx)⟩

theorem good_perm {Γ l₁ l₂ : List α} (h : l₁.Perm l₂) (hg : Good Γ l₁) : Good Γ l₂ :=
  ⟨h.nodup_iff.mp hg.1, fun x hx => hg.2 x (h.mem_iff.mpr hx)⟩

theorem sumd_perm (f : α → Q') {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (sumd f l₁).eqv (sumd f l₂) := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons x _ ih => exact Q'.add_eqv_congr' (Q'.eqv_refl _) ih
  | swap x y l =>
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + (V 1 + V 2)) (V 1 + (V 0 + V 2)) (by decide)
      (fun | 0 => f y | 1 => f x | _ => sumd f l)
  | trans _ _ ih₁ ih₂ => exact Q'.eqv_trans _ _ _ ih₁ ih₂

theorem sumd_sub_le [DecidableEq α] (f : α → Q') (hf : ∀ x, (0 : Q') ≤ f x) :
    ∀ l₁ l₂ : List α, l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → sumd f l₁ ≤ sumd f l₂
  | [], l₂, _, _ => sumd_nonneg f hf l₂
  | x :: l₁, l₂, hnd, hs => by
    have hx : x ∈ l₂ := hs x List.mem_cons_self
    have hp := YMGap.Continuum.TorusWilsonAction.perm_cons_rem x hx
    have hnx : x ∉ l₁ := (List.nodup_cons.mp hnd).1
    have ih := sumd_sub_le f hf l₁ (YMGap.Continuum.TorusWilsonAction.rem x l₂)
      (List.nodup_cons.mp hnd).2 (fun y hy => by
        have hyx : y ≠ x := fun e => hnx (e ▸ hy)
        exact YMGap.Continuum.TorusWilsonAction.mem_rem_of_ne x y hyx
          (hs y (List.mem_cons_of_mem _ hy)))
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_refl' (f x)) ih) ?_
    exact Q'.le_of_eqv (sumd_perm f hp.symm)

/-! ## Truncated quantities and the telescoping identity -/

def U (y g : α) (l : List α) : Q' :=
  Xi z inc (y :: g :: l) * Xi z inc l + -(Xi z inc (y :: l) * Xi z inc (g :: l))

def D (y : α) (A C : List α) : Q' :=
  Xi z inc (y :: A) * Xi z inc C + -(Xi z inc (y :: C) * Xi z inc A)

theorem tele_id (y : α) (A B C : List α) :
    (D z inc y A C * Xi z inc B).eqv
      (D z inc y A B * Xi z inc C + D z inc y B C * Xi z inc A) := by
  unfold D
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    ((V 0 * V 5 + -(V 4 * V 1)) * V 3)
    ((V 0 * V 3 + -(V 2 * V 1)) * V 5 + (V 2 * V 5 + -(V 4 * V 3)) * V 1) (by decide)
    (fun | 0 => Xi z inc (y :: A) | 1 => Xi z inc A | 2 => Xi z inc (y :: B)
         | 3 => Xi z inc B | 4 => Xi z inc (y :: C) | _ => Xi z inc C)

/-- Cancel a positive factor inside an absolute-value bound. -/
theorem abs_cancel {b x K : Q'} (hb : (0 : Q') < b) (h : Q'.abs (x * b) ≤ b * K) :
    Q'.abs x ≤ K := by
  have h1 : b * x ≤ b * K :=
    Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv b x))
      (Q'.le_abs_self _)) h
  have h2 : b * (-x) ≤ b * K := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) h)
    let V := PolyExpr.var
    exact Q'.le_of_eqv (poly_identity_of_normal_eq (V 0 * -(V 1)) (-(V 1 * V 0)) (by decide)
      (fun | 0 => b | _ => x))
  have hx := Q'.le_of_mul_le_mul_left h1 hb
  have hnx := Q'.le_of_mul_le_mul_left h2 hb
  exact Q'.abs_le (Q'.le_trans' _ _ _ (Q'.neg_le_neg hnx) (Q'.le_of_eqv (Q'.neg_neg_eqv x))) hx

theorem abs_mul_nonneg_le {x b : Q'} (hb : (0 : Q') ≤ b) : Q'.abs (x * b) ≤ Q'.abs x * b :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le x b) (Q'.le_of_eqv
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg hb))))

/-! ## The KP environment and the chain bound -/

section env
variable (hsym : ∀ a b, inc a b = inc b a) (Γ : List α) (ε M m : α → Q')
variable (hpos : ∀ l, Good Γ l → (0 : Q') < Xi z inc l)
variable (hMb : ∀ (l : List α) (a : α), Good Γ l →
  Xi z inc (l.filter (cpt inc a)) ≤ M a * Xi z inc l)
variable (hmb : ∀ (x : α) (l : List α), Good Γ (x :: l) → Xi z inc l ≤ m x * Xi z inc (x :: l))
variable (hzb : ∀ a, Q'.abs (z a) ≤ ε a)
variable (hε0 : ∀ a, (0 : Q') ≤ ε a) (hM0 : ∀ a, (0 : Q') ≤ M a) (hm0 : ∀ a, (0 : Q') ≤ m a)

theorem xi_nn {l : List α} (hg : Good Γ l) (hpos : ∀ l, Good Γ l → (0 : Q') < Xi z inc l) :
    (0 : Q') ≤ Xi z inc l := Q'.le_of_lt (hpos l hg)

include hpos in
/-- **Telescoping (PROVED).** -/
theorem telescope (y : α) (F : List α) (c : α → Q') :
    ∀ R : List α, (∀ h, h ∈ R → ∀ X, Good Γ (y :: h :: X) →
        Q'.abs (U z inc y h X) ≤ c h * (Xi z inc X * Xi z inc (h :: X))) →
      Good Γ (y :: (R ++ F)) →
      Q'.abs (D z inc y F (R ++ F)) ≤ sumd c R * (Xi z inc F * Xi z inc (R ++ F))
  | [], _, hG => by
    have hF : (0 : Q') ≤ Xi z inc F := xi_nn z inc Γ (good_sub (List.sublist_cons_self _ _) hG) hpos
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (show (D z inc y F ([] ++ F)).eqv 0 from by
      unfold D
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 + -(V 0 * V 1)) (PolyExpr.const 0) (by decide)
        (fun | 0 => Xi z inc (y :: F) | _ => Xi z inc F)))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (show Q'.abs 0 = 0 by decide))) ?_
    exact Q'.mul_nonneg _ _ (Q'.le_refl' 0) (Q'.mul_nonneg _ _ hF hF)
  | h :: R, hc, hG => by
    let B := R ++ F
    have hGB : Good Γ (y :: B) := good_sub (List.Sublist.cons₂ y (List.sublist_cons_self h B)) hG
    have hGF : Good Γ F := good_sub (List.Sublist.trans (List.sublist_append_right R F)
      (List.sublist_cons_self y B)) hGB
    have hGC : Good Γ (h :: B) := good_sub (List.sublist_cons_self y _) hG
    have hGB' : Good Γ B := good_sub (List.sublist_cons_self h B) hGC
    have ih := telescope y F c R (fun h' hh' => hc h' (List.mem_cons_of_mem _ hh')) hGB
    have hU := hc h List.mem_cons_self B hG
    have hF0 := xi_nn z inc Γ hGF hpos
    have hB0 := hpos B hGB'
    have hC0 := xi_nn z inc Γ hGC hpos
    have hDBC : Q'.abs (D z inc y B (h :: B)) ≤ c h * (Xi z inc B * Xi z inc (h :: B)) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr ?_)
        (Q'.abs_neg' (U z inc y h B)))) hU
      unfold D U
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 + -(V 2 * V 3)) (-(V 2 * V 3 + -(V 0 * V 1)))
        (by decide)
        (fun | 0 => Xi z inc (y :: B) | 1 => Xi z inc (h :: B)
             | 2 => Xi z inc (y :: h :: B) | _ => Xi z inc B)
    have key : Q'.abs (D z inc y F (h :: B) * Xi z inc B) ≤
        Xi z inc B * ((c h + sumd c R) * (Xi z inc F * Xi z inc (h :: B))) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (tele_id z inc y F B (h :: B)))) ?_
      refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add (abs_mul_nonneg_le hC0) (abs_mul_nonneg_le hF0)) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_right _ _ _ ih hC0)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hDBC hF0)) (Q'.le_of_eqv ?_)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq
        (V 0 * (V 1 * V 2) * V 3 + V 4 * (V 2 * V 3) * V 1)
        (V 2 * ((V 4 + V 0) * (V 1 * V 3))) (by decide)
        (fun | 0 => sumd c R | 1 => Xi z inc F | 2 => Xi z inc B | 3 => Xi z inc (h :: B)
             | _ => c h)
    exact abs_cancel hB0 key

/-- Chain sum. -/
def CS (y : α) : Nat → α → Q'
  | 0, g => ε g * M g * m g * ((1 + ε y * M y) + (1 + ε y * M y))
  | d + 1, g => ε g * M g * m g * sumd (CS y d) (Γ.filter (inc g))

/-- `g` is at incompatibility distance `≥ d` from `y` through `Γ`. -/
def far (y : α) : Nat → α → Prop
  | 0, _ => True
  | d + 1, g => inc y g = false ∧ ∀ h, h ∈ Γ → inc g h = true → far y d h

include hε0 hM0 hm0 in
theorem CS_nonneg (y : α) : ∀ d g, (0 : Q') ≤ CS inc Γ ε M m y d g
  | 0, g => Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 g) (hM0 g)) (hm0 g))
      (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (by decide) (Q'.mul_nonneg _ _ (hε0 y) (hM0 y)))
        (Q'.zero_le_add _ _ (by decide) (Q'.mul_nonneg _ _ (hε0 y) (hM0 y))))
  | d + 1, g => Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 g) (hM0 g)) (hm0 g))
      (sumd_nonneg _ (CS_nonneg y d) _)

include hsym in
theorem U_eqv (y g : α) (l : List α) :
    (U z inc y g l).eqv (z g * (Xi z inc ((y :: l).filter (cpt inc g)) * Xi z inc l +
      -(Xi z inc (y :: l) * Xi z inc (l.filter (cpt inc g))))) := by
  unfold U
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _
    (Xi_swap z inc hsym y g l)) (Q'.eqv_refl _)) ?_
  rw [Xi_cons z inc g (y :: l), Xi_cons z inc g l]
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    ((V 0 + V 1 * V 2) * V 3 + -(V 0 * (V 3 + V 1 * V 4)))
    (V 1 * (V 2 * V 3 + -(V 0 * V 4))) (by decide)
    (fun | 0 => Xi z inc (y :: l) | 1 => z g | 2 => Xi z inc ((y :: l).filter (cpt inc g))
         | 3 => Xi z inc l | _ => Xi z inc (l.filter (cpt inc g)))

include hsym hpos hMb hmb hzb hε0 hM0 hm0 in
/-- **Chain bound (PROVED).** -/
theorem chain_bound [DecidableEq α] (y : α) : ∀ (d : Nat) (g : α) (l : List α), far inc Γ y d g →
    Good Γ (y :: g :: l) →
    Q'.abs (U z inc y g l) ≤ CS inc Γ ε M m y d g * (Xi z inc l * Xi z inc (g :: l))
  | d, g, l, hfar, hG => by
    have Gyl : Good Γ (y :: l) := good_sub (List.Sublist.cons₂ y (List.sublist_cons_self g l)) hG
    have Ggl : Good Γ (g :: l) := good_sub (List.sublist_cons_self y _) hG
    have Gl : Good Γ l := good_sub (List.sublist_cons_self g l) Ggl
    have GLg : Good Γ (l.filter (cpt inc g)) := good_sub List.filter_sublist Gl
    let L := Xi z inc l
    let G := Xi z inc (g :: l)
    let Y := Xi z inc (y :: l)
    let Lg := Xi z inc (l.filter (cpt inc g))
    let W := Xi z inc ((y :: l).filter (cpt inc g))
    have hL : (0 : Q') ≤ L := xi_nn z inc Γ Gl hpos
    have hG0 : (0 : Q') ≤ G := xi_nn z inc Γ Ggl hpos
    have hY : (0 : Q') ≤ Y := xi_nn z inc Γ Gyl hpos
    have hLg : (0 : Q') ≤ Lg := xi_nn z inc Γ GLg hpos
    have hlm : L ≤ m g * G := hmb g l Ggl
    have hLgM : Lg ≤ M g * L := hMb l g Gl
    let E := W * L + -(Y * Lg)
    have hU1 : Q'.abs (U z inc y g l) ≤ ε g * Q'.abs E :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (U_eqv z inc hsym y g l)))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (hzb g) (Q'.abs_nonneg _)))
    have hεg := hε0 g
    have hMg := hM0 g
    have hmg := hm0 g
    match d, hfar with
    | 0, _ =>
      have GW : Good Γ ((y :: l).filter (cpt inc g)) := good_sub List.filter_sublist Gyl
      have hW : (0 : Q') ≤ W := xi_nn z inc Γ GW hpos
      have hWM : W ≤ M g * Y := hMb (y :: l) g Gyl
      have hE : Q'.abs E ≤ (M g * Y) * L + Y * (M g * L) := by
        refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add ?_ ?_)
        · rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hW hL)]
          exact Q'.mul_le_mul_of_nonneg_right _ _ _ hWM hL
        · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) ?_
          rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hY hLg)]
          exact Q'.mul_le_mul_of_nonneg_left _ _ _ hLgM hY
      have GLy : Good Γ (l.filter (cpt inc y)) := good_sub List.filter_sublist Gl
      have hLy : (0 : Q') ≤ Xi z inc (l.filter (cpt inc y)) := xi_nn z inc Γ GLy hpos
      have hYb : Y ≤ L + ε y * (M y * L) := by
        show Xi z inc (y :: l) ≤ _
        rw [Xi_cons]
        refine Q'.add_le_add (Q'.le_refl' _) ?_
        refine Q'.le_trans' _ _ _ (Q'.le_abs_self _) (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) ?_)
        rw [ExpNeg.abs_of_nonneg hLy]
        refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (hzb y) hLy) ?_
        exact Q'.mul_le_mul_of_nonneg_left _ _ _ (hMb l y Gl) (hε0 y)
      have hE2 : (M g * Y) * L + Y * (M g * L) ≤
          (M g * ((1 + ε y * M y) + (1 + ε y * M y))) * (L * L) := by
        refine Q'.le_trans' _ _ _ (Q'.add_le_add
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hYb hMg) hL)
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hYb (Q'.mul_nonneg _ _ hMg hL))) (Q'.le_of_eqv ?_)
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq
          ((V 0 * (V 1 + V 2 * (V 3 * V 1))) * V 1 + (V 1 + V 2 * (V 3 * V 1)) * (V 0 * V 1))
          ((V 0 * ((PolyExpr.const 1 + V 2 * V 3) + (PolyExpr.const 1 + V 2 * V 3))) * (V 1 * V 1))
          (by decide) (fun | 0 => M g | 1 => L | 2 => ε y | _ => M y)
      have hK0 : (0 : Q') ≤ M g * ((1 + ε y * M y) + (1 + ε y * M y)) :=
        Q'.mul_nonneg _ _ hMg (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _ (by decide) (Q'.mul_nonneg _ _ (hε0 y) (hM0 y)))
          (Q'.zero_le_add _ _ (by decide) (Q'.mul_nonneg _ _ (hε0 y) (hM0 y))))
      have hE3 : Q'.abs E ≤ (M g * ((1 + ε y * M y) + (1 + ε y * M y))) * (L * (m g * G)) :=
        Q'.le_trans' _ _ _ hE (Q'.le_trans' _ _ _ hE2
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hlm hL) hK0))
      refine Q'.le_trans' _ _ _ hU1 (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hE3 hεg) (Q'.le_of_eqv ?_))
      show (ε g * ((M g * ((1 + ε y * M y) + (1 + ε y * M y))) * (L * (m g * G)))).eqv
        (ε g * M g * m g * ((1 + ε y * M y) + (1 + ε y * M y)) * (L * G))
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq
        (V 0 * ((V 1 * V 2) * (V 3 * (V 4 * V 5))))
        (V 0 * V 1 * V 4 * V 2 * (V 3 * V 5)) (by decide)
        (fun | 0 => ε g | 1 => M g | 2 => (1 + ε y * M y) + (1 + ε y * M y) | 3 => L
             | 4 => m g | _ => G)
    | d + 1, ⟨hyg, hfar'⟩ =>
      have hgy : cpt inc g y = true := by
        show (!inc g y) = true
        rw [hsym g y, hyg]; rfl
      have hfil : (y :: l).filter (cpt inc g) = y :: l.filter (cpt inc g) :=
        List.filter_cons_of_pos hgy
      let R := l.filter (inc g)
      let F := l.filter (cpt inc g)
      have hp : (R ++ F).Perm l := List.filter_append_perm (inc g) l
      have hG' : Good Γ (y :: (R ++ F)) := good_perm (hp.symm.cons y) Gyl
      have hT := telescope z inc Γ hpos y F (CS inc Γ ε M m y d) R (fun h hh X hX => by
        have hm := List.mem_filter.mp hh
        exact chain_bound y d h X (hfar' h (Gl.2 h hm.1) hm.2) hX) hG'
      have hRF : (Xi z inc (R ++ F)).eqv L := Xi_perm z inc hsym hp
      have hyRF : (Xi z inc (y :: (R ++ F))).eqv Y := Xi_perm z inc hsym (hp.cons y)
      have hED : (Q'.abs E).eqv (Q'.abs (D z inc y F (R ++ F))) := by
        refine Q'.abs_eqv_congr ?_
        show (Xi z inc ((y :: l).filter (cpt inc g)) * L + -(Y * Lg)).eqv
          (Xi z inc (y :: F) * Xi z inc (R ++ F) + -(Xi z inc (y :: (R ++ F)) * Xi z inc F))
        rw [hfil]
        exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hRF))
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hyRF)))
      let Sg := sumd (CS inc Γ ε M m y d) (Γ.filter (inc g))
      have hS : sumd (CS inc Γ ε M m y d) R ≤ Sg :=
        sumd_sub_le _ (CS_nonneg inc Γ ε M m hε0 hM0 hm0 y d) R _ (Gl.1.filter _)
          (fun h hh => List.mem_filter.mpr ⟨Gl.2 h (List.mem_filter.mp hh).1,
            (List.mem_filter.mp hh).2⟩)
      have hP : (0 : Q') ≤ Lg * L := Q'.mul_nonneg _ _ hLg hL
      have hE : Q'.abs E ≤ Sg * ((M g * L) * (m g * G)) := by
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hED) (Q'.le_trans' _ _ _ hT ?_)
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hRF))) ?_
        refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hS hP) ?_
        refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (sumd_nonneg _ (CS_nonneg inc Γ ε M m hε0 hM0 hm0 y d) _)
        exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hLgM hL)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hlm (Q'.mul_nonneg _ _ hMg hL))
      refine Q'.le_trans' _ _ _ hU1 (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hE hεg) (Q'.le_of_eqv ?_))
      show (ε g * (Sg * ((M g * L) * (m g * G)))).eqv (ε g * M g * m g * Sg * (L * G))
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq
        (V 0 * (V 1 * ((V 2 * V 3) * (V 4 * V 5))))
        (V 0 * V 2 * V 4 * V 1 * (V 3 * V 5)) (by decide)
        (fun | 0 => ε g | 1 => Sg | 2 => M g | 3 => L | 4 => m g | _ => G)

end env

end YMGap.Continuum.PolymerChainDecay

#print axioms YMGap.Continuum.PolymerChainDecay.Xi_perm
#print axioms YMGap.Continuum.PolymerChainDecay.sumd_sub_le
#print axioms YMGap.Continuum.PolymerChainDecay.telescope
#print axioms YMGap.Continuum.PolymerChainDecay.chain_bound
