/-
# R1 commit 14: the removal chain, which bounds T(y,g) without KP at the roots

ADDITIVE.  GENERIC (any gas list Γ, any symmetric `inc`).  The activity enters only through
`hzb : |z a| ≤ ε a` together with the KP-environment hypotheses on lists of Γ, as in
`chain_bound` / `link_decay`.

`T y g l = Ξ(l)·Ξ(l_{g,y}) − Ξ(l_y)·Ξ(l_g)`, with `l_y = l ∩ cpt y`.  The roots y and g are
arbitrary: they need not be in Γ, and no KP condition is imposed at them.

* `Vr_eqv`: if y and h are compatible, `Ξ((h::X)_y)Ξ(X) − Ξ(X_y)Ξ(h::X) ≈ z_h · T y h X`.
* `teleR`: D-telescoping for `Dr y A C = Ξ(A_y)Ξ(C) − Ξ(C_y)Ξ(A)`.
* `T_bound`: `farW y f r g → Good Γ l → |T y g l| ≤ M y · BW f r g · Ξ(l)²`.
  The chain sum is `BW f r g = 2M_g` at the base and `M_g Σ_{h∈Γ, inc g h} ε_h m_h BW f (r+1−w h) h`
  at a step.
* `BW_le`: `ε_g m_g BW f r g ≤ CSW f r g`, so the existing lattice-decay bounds on `CSW`
  (`CSWL_le`) apply.

Labels: strong coupling, heat-kernel (spin-truncated), not Wilson; also true for U(1), not gap
evidence.
-/

import YMGap.Continuum.PolymerLatticeDecay

namespace YMGap.Continuum.PolymerRemovalChain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.PolymerChainDecay
open YMGap.Continuum.PolymerLatticeDecay (CSW farW)
open YMGap.Continuum.PolymerDecayZ4 (sumd_mul sumd_mono)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

theorem filter_comm {β : Type} (p q : β → Bool) : ∀ l : List β,
    (l.filter p).filter q = (l.filter q).filter p
  | [] => rfl
  | a :: l => by
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq, filter_comm p q l]

variable {α : Type} (z : α → Q') (inc : α → α → Bool)

def T (y g : α) (l : List α) : Q' :=
  Xi z inc l * Xi z inc ((l.filter (cpt inc g)).filter (cpt inc y)) +
    -(Xi z inc (l.filter (cpt inc y)) * Xi z inc (l.filter (cpt inc g)))

def Dr (y : α) (A C : List α) : Q' :=
  Xi z inc (A.filter (cpt inc y)) * Xi z inc C + -(Xi z inc (C.filter (cpt inc y)) * Xi z inc A)

def Vr (y h : α) (X : List α) : Q' :=
  Xi z inc ((h :: X).filter (cpt inc y)) * Xi z inc X + -(Xi z inc (X.filter (cpt inc y)) * Xi z inc (h :: X))

theorem Vr_eqv (y h : α) (X : List α) (hyh : inc y h = false) :
    (Vr z inc y h X).eqv (z h * T z inc y h X) := by
  have hc : cpt inc y h = true := by show (!inc y h) = true; rw [hyh]; rfl
  unfold Vr T
  rw [List.filter_cons_of_pos hc, Xi_cons z inc h (X.filter (cpt inc y)), Xi_cons z inc h X,
    filter_comm (cpt inc y) (cpt inc h) X]
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq ((V 0 + V 1 * V 2) * V 3 + -(V 0 * (V 3 + V 1 * V 4)))
    (V 1 * (V 3 * V 2 + -(V 0 * V 4))) (by decide)
    (fun | 0 => Xi z inc (X.filter (cpt inc y)) | 1 => z h
         | 2 => Xi z inc ((X.filter (cpt inc h)).filter (cpt inc y)) | 3 => Xi z inc X
         | _ => Xi z inc (X.filter (cpt inc h)))

theorem Vr_inc (y h : α) (X : List α) (hyh : inc y h = true) :
    (Vr z inc y h X).eqv (-(z h * (Xi z inc (X.filter (cpt inc y)) * Xi z inc (X.filter (cpt inc h))))) := by
  have hc : cpt inc y h = false := by show (!inc y h) = false; rw [hyh]; rfl
  unfold Vr
  rw [List.filter_cons_of_neg (by rw [hc]; decide), Xi_cons z inc h X]
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 1 + -(V 0 * (V 1 + V 2 * V 3))) (-(V 2 * (V 0 * V 3)))
    (by decide)
    (fun | 0 => Xi z inc (X.filter (cpt inc y)) | 1 => Xi z inc X | 2 => z h
         | _ => Xi z inc (X.filter (cpt inc h)))

theorem teleR_id (y : α) (A B C : List α) :
    (Dr z inc y A C * Xi z inc B).eqv (Dr z inc y A B * Xi z inc C + Dr z inc y B C * Xi z inc A) := by
  unfold Dr
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq ((V 0 * V 5 + -(V 4 * V 1)) * V 3)
    ((V 0 * V 3 + -(V 2 * V 1)) * V 5 + (V 2 * V 5 + -(V 4 * V 3)) * V 1) (by decide)
    (fun | 0 => Xi z inc (A.filter (cpt inc y)) | 1 => Xi z inc A | 2 => Xi z inc (B.filter (cpt inc y))
         | 3 => Xi z inc B | 4 => Xi z inc (C.filter (cpt inc y)) | _ => Xi z inc C)

section env
variable (hsym : ∀ a b, inc a b = inc b a) (Γ : List α) (ε M m : α → Q')
variable (hpos : ∀ l, Good Γ l → (0 : Q') < Xi z inc l)
variable (hMb : ∀ (l : List α) (a : α), Good Γ l → Xi z inc (l.filter (cpt inc a)) ≤ M a * Xi z inc l)
variable (hmb : ∀ (x : α) (l : List α), Good Γ (x :: l) → Xi z inc l ≤ m x * Xi z inc (x :: l))
variable (hzb : ∀ a, Q'.abs (z a) ≤ ε a)
variable (hε0 : ∀ a, (0 : Q') ≤ ε a) (hM0 : ∀ a, (0 : Q') ≤ M a) (hm0 : ∀ a, (0 : Q') ≤ m a)
variable (w : α → Nat)

include hpos in
theorem teleR (y : α) (F : List α) (c : α → Q') :
    ∀ R : List α, (∀ h, h ∈ R → ∀ X, Good Γ (h :: X) →
        Q'.abs (Vr z inc y h X) ≤ c h * (Xi z inc X * Xi z inc (h :: X))) →
      Good Γ (R ++ F) →
      Q'.abs (Dr z inc y F (R ++ F)) ≤ sumd c R * (Xi z inc F * Xi z inc (R ++ F))
  | [], _, hG => by
    have hF : (0 : Q') ≤ Xi z inc F := Q'.le_of_lt (hpos _ hG)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (show (Dr z inc y F ([] ++ F)).eqv 0 from by
      unfold Dr
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 + -(V 0 * V 1)) (PolyExpr.const 0) (by decide)
        (fun | 0 => Xi z inc (F.filter (cpt inc y)) | _ => Xi z inc F)))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (show Q'.abs 0 = 0 by decide))) ?_
    exact Q'.mul_nonneg _ _ (Q'.le_refl' 0) (Q'.mul_nonneg _ _ hF hF)
  | h :: R, hc, hG => by
    let B := R ++ F
    have hGC : Good Γ (h :: B) := hG
    have hGB : Good Γ B := good_sub (List.sublist_cons_self h B) hGC
    have hGF : Good Γ F := good_sub (List.sublist_append_right R F) hGB
    have ih := teleR y F c R (fun h' hh' => hc h' (List.mem_cons_of_mem _ hh')) hGB
    have hV := hc h List.mem_cons_self B hGC
    have hF0 := Q'.le_of_lt (hpos F hGF)
    have hB0 := hpos B hGB
    have hC0 := Q'.le_of_lt (hpos _ hGC)
    have hDBC : Q'.abs (Dr z inc y B (h :: B)) ≤ c h * (Xi z inc B * Xi z inc (h :: B)) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr ?_)
        (Q'.abs_neg' (Vr z inc y h B)))) hV
      unfold Dr Vr
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 + -(V 2 * V 3)) (-(V 2 * V 3 + -(V 0 * V 1)))
        (by decide)
        (fun | 0 => Xi z inc (B.filter (cpt inc y)) | 1 => Xi z inc (h :: B)
             | 2 => Xi z inc ((h :: B).filter (cpt inc y)) | _ => Xi z inc B)
    have key : Q'.abs (Dr z inc y F (h :: B) * Xi z inc B) ≤
        Xi z inc B * ((c h + sumd c R) * (Xi z inc F * Xi z inc (h :: B))) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (teleR_id z inc y F B (h :: B)))) ?_
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

/-- The removal chain sum. -/
def BW (y : α) : Nat → Nat → α → Q'
  | 0, _, g => M g + M g
  | _ + 1, 0, g => M g + M g
  | f + 1, r + 1, g => M g * sumd (fun h => ε h * m h * BW y f (r + 1 - w h) h) (Γ.filter (inc g))

include hε0 hM0 hm0 in
theorem BW_nonneg (y : α) : ∀ f r g, (0 : Q') ≤ BW inc Γ ε M m w y f r g
  | 0, _, g => Q'.zero_le_add _ _ (hM0 g) (hM0 g)
  | _ + 1, 0, g => Q'.zero_le_add _ _ (hM0 g) (hM0 g)
  | f + 1, r + 1, g => Q'.mul_nonneg _ _ (hM0 g) (sumd_nonneg _ (fun h =>
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 h) (hm0 h)) (BW_nonneg y f (r + 1 - w h) h)) _)

include hpos hMb hM0 in
/-- Base bound: `|T y g l| ≤ M_y (M_g + M_g) Ξ(l)²`. -/
theorem T_base (y g : α) (l : List α) (hl : Good Γ l) :
    Q'.abs (T z inc y g l) ≤ M y * (M g + M g) * (Xi z inc l * Xi z inc l) := by
  have Gg : Good Γ (l.filter (cpt inc g)) := good_sub List.filter_sublist hl
  have Gy : Good Γ (l.filter (cpt inc y)) := good_sub List.filter_sublist hl
  have Ggy : Good Γ ((l.filter (cpt inc g)).filter (cpt inc y)) := good_sub List.filter_sublist Gg
  have hL := Q'.le_of_lt (hpos _ hl)
  have hLg := Q'.le_of_lt (hpos _ Gg)
  have hLy := Q'.le_of_lt (hpos _ Gy)
  have hLgy := Q'.le_of_lt (hpos _ Ggy)
  have a1 := hMb _ y Gg
  have a2 := hMb l g hl
  have a3 := hMb l y hl
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) ?_
  rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hL hLgy)]
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))) ?_
  rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hLy hLg)]
  have b1 : Xi z inc l * Xi z inc ((l.filter (cpt inc g)).filter (cpt inc y)) ≤
      Xi z inc l * (M y * (M g * Xi z inc l)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ a1
      (Q'.mul_le_mul_of_nonneg_left _ _ _ a2 (hM0 y))) hL
  have b2 : Xi z inc (l.filter (cpt inc y)) * Xi z inc (l.filter (cpt inc g)) ≤
      (M y * Xi z inc l) * (M g * Xi z inc l) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ a3 hLg)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ a2 (Q'.mul_nonneg _ _ (hM0 y) hL))
  refine Q'.le_trans' _ _ _ (Q'.add_le_add b1 b2) (Q'.le_of_eqv ?_)
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * (V 1 * (V 2 * V 0)) + V 1 * V 0 * (V 2 * V 0))
    (V 1 * (V 2 + V 2) * (V 0 * V 0)) (by decide)
    (fun | 0 => Xi z inc l | 1 => M y | _ => M g)

include hsym hpos hMb hmb hzb hε0 hM0 hm0 in
/-- **Removal-chain bound (PROVED).**  No KP condition at `y` or `g`. -/
theorem T_bound [DecidableEq α] (y : α) : ∀ (f r : Nat) (g : α) (l : List α),
    farW inc Γ w y f r g → Good Γ l →
    Q'.abs (T z inc y g l) ≤ M y * BW inc Γ ε M m w y f r g * (Xi z inc l * Xi z inc l)
  | 0, _, g, l, _, hl => T_base z inc Γ M hpos hMb hM0 y g l hl
  | _ + 1, 0, g, l, _, hl => T_base z inc Γ M hpos hMb hM0 y g l hl
  | f + 1, r + 1, g, l, ⟨hyg, hfar⟩, hl => by
    let R := l.filter (inc g)
    let F := l.filter (cpt inc g)
    have hp : (R ++ F).Perm l := List.filter_append_perm (inc g) l
    have hG' : Good Γ (R ++ F) := good_perm hp.symm hl
    let c := fun h => M y * (ε h * m h * BW inc Γ ε M m w y f (r + 1 - w h) h)
    have hVb : ∀ h, h ∈ R → ∀ X, Good Γ (h :: X) →
        Q'.abs (Vr z inc y h X) ≤ c h * (Xi z inc X * Xi z inc (h :: X)) := by
      intro h hh X hX
      have hm := List.mem_filter.mp hh
      have hfh := hfar h (hl.2 h hm.1) hm.2
      have GX : Good Γ X := good_sub (List.sublist_cons_self h X) hX
      have hX0 := Q'.le_of_lt (hpos X GX)
      have hhX := hmb h X hX
      have hBW := BW_nonneg inc Γ ε M m hε0 hM0 hm0 w y f (r + 1 - w h) h
      have core : Q'.abs (Vr z inc y h X) ≤ ε h * (M y * BW inc Γ ε M m w y f (r + 1 - w h) h *
          (Xi z inc X * Xi z inc X)) := by
        cases hyh : inc y h with
        | false =>
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Vr_eqv z inc y h X hyh))) ?_
          exact Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ _ (hzb h) (Q'.abs_nonneg _))
            (Q'.mul_le_mul_of_nonneg_left _ _ _ (T_bound y f (r + 1 - w h) h X hfh GX) (hε0 h)))
        | true =>
          -- incompatible: farW is trivial only at the base, where BW = M_h + M_h
          have hbase : M h ≤ BW inc Γ ε M m w y f (r + 1 - w h) h := by
            cases f with
            | zero => exact Q'.add_le_self_of_nonneg _ _ (hM0 h)
            | succ f' =>
              cases hr : r + 1 - w h with
              | zero => show M h ≤ M h + M h; exact Q'.add_le_self_of_nonneg _ _ (hM0 h)
              | succ r' => rw [hr] at hfh; rw [hfh.1] at hyh; exact absurd hyh (by decide)
          have Gy := good_sub (List.filter_sublist (p := cpt inc y)) GX
          have Gh := good_sub (List.filter_sublist (p := cpt inc h)) GX
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr
            (Vr_inc z inc y h X hyh)) (Q'.abs_neg' _))) ?_
          refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ _ (hzb h) (Q'.abs_nonneg _)) ?_)
          refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (hε0 h)
          rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ (Q'.le_of_lt (hpos _ Gy)) (Q'.le_of_lt (hpos _ Gh)))]
          refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (hMb X y GX)
            (Q'.le_of_lt (hpos _ Gh))) (Q'.mul_le_mul_of_nonneg_left _ _ _ (hMb X h GX)
              (Q'.mul_nonneg _ _ (hM0 y) hX0))) ?_
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show ((M y * Xi z inc X) * (M h * Xi z inc X)).eqv
            (M y * M h * (Xi z inc X * Xi z inc X)) from by
              let V := PolyExpr.var
              exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 1)) (V 0 * V 2 * (V 1 * V 1))
                (by decide) (fun | 0 => M y | 1 => Xi z inc X | _ => M h))) ?_
          exact Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hbase (hM0 y))
            (Q'.mul_nonneg _ _ hX0 hX0)
      refine Q'.le_trans' _ _ _ core ?_
      have hK0 : (0 : Q') ≤ M y * BW inc Γ ε M m w y f (r + 1 - w h) h := Q'.mul_nonneg _ _ (hM0 y) hBW
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hhX hX0) hK0) (hε0 h)) (Q'.le_of_eqv ?_)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2 * (V 3 * (V 4 * V 5))))
        (V 1 * (V 0 * V 4 * V 2) * (V 3 * V 5)) (by decide)
        (fun | 0 => ε h | 1 => M y | 2 => BW inc Γ ε M m w y f (r + 1 - w h) h | 3 => Xi z inc X
             | 4 => m h | _ => Xi z inc (h :: X))
    have hT := teleR z inc Γ hpos y F c R hVb hG'
    have hRF : (Xi z inc (R ++ F)).eqv (Xi z inc l) := Xi_perm z inc hsym hp
    have hRFy : (Xi z inc ((R ++ F).filter (cpt inc y))).eqv (Xi z inc (l.filter (cpt inc y))) :=
      Xi_perm z inc hsym (hp.filter _)
    have hTD : (T z inc y g l).eqv (Dr z inc y F (R ++ F)) := by
      unfold T Dr
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hRF))
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hRFy))))
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.add_eqv_congr' (Q'.mul_comm_eqv _ _) (Q'.eqv_refl _))
    have GF : Good Γ F := good_sub List.filter_sublist hl
    have hF0 := Q'.le_of_lt (hpos F GF)
    have hL0 := Q'.le_of_lt (hpos l hl)
    let Sg := sumd (fun h => ε h * m h * BW inc Γ ε M m w y f (r + 1 - w h) h) (Γ.filter (inc g))
    have hS : sumd (fun h => ε h * m h * BW inc Γ ε M m w y f (r + 1 - w h) h) R ≤ Sg :=
      sumd_sub_le _ (fun h => Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 h) (hm0 h))
        (BW_nonneg inc Γ ε M m hε0 hM0 hm0 w y f _ h)) R _ (hl.1.filter _)
        (fun h hh => List.mem_filter.mpr ⟨hl.2 h (List.mem_filter.mp hh).1, (List.mem_filter.mp hh).2⟩)
    have hcR : (sumd c R).eqv (M y * sumd (fun h => ε h * m h * BW inc Γ ε M m w y f (r + 1 - w h) h) R) :=
      sumd_mul _ _ R
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hTD)) (Q'.le_trans' _ _ _ hT ?_)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hcR)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hRF)))) ?_
    have hSg0 : (0 : Q') ≤ Sg := sumd_nonneg _ (fun h => Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 h) (hm0 h))
      (BW_nonneg inc Γ ε M m hε0 hM0 hm0 w y f _ h)) _
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hS (hM0 y)) (Q'.mul_nonneg _ _ hF0 hL0)) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hMb l g hl) hL0) (Q'.mul_nonneg _ _ (hM0 y) hSg0)) (Q'.le_of_eqv ?_)
    show (M y * Sg * (M g * Xi z inc l * Xi z inc l)).eqv (M y * (M g * Sg) * (Xi z inc l * Xi z inc l))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3 * V 3)) (V 0 * (V 2 * V 1) * (V 3 * V 3))
      (by decide) (fun | 0 => M y | 1 => Sg | 2 => M g | _ => Xi z inc l)

include hε0 hM0 hm0 in
/-- `ε_g m_g BW ≤ CSW`, transferring the lattice-decay bounds. -/
theorem BW_le (y : α) : ∀ f r g, ε g * m g * BW inc Γ ε M m w y f r g ≤ CSW inc Γ ε M m w y f r g
  | 0, _, g => base g
  | _ + 1, 0, g => base g
  | f + 1, r + 1, g => by
    show ε g * m g * (M g * sumd _ _) ≤ ε g * M g * m g * sumd _ _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.mul_le_mul_of_nonneg_left _ _ _
      (sumd_mono _ _ (fun h => BW_le y f (r + 1 - w h) h) _)
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 g) (hM0 g)) (hm0 g)))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3)) (V 0 * V 2 * V 1 * V 3) (by decide)
      (fun | 0 => ε g | 1 => m g | 2 => M g | _ => sumd _ (Γ.filter (inc g)))
where
  base (g : α) : ε g * m g * (M g + M g) ≤ CS inc Γ ε M m y 0 g := by
    show _ ≤ ε g * M g * m g * ((1 + ε y * M y) + (1 + ε y * M y))
    have h1 : (1 : Q') ≤ 1 + ε y * M y := Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 y) (hM0 y))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (ε g * m g * (M g + M g)).eqv (ε g * M g * m g * (1 + 1)) from by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 + V 2)) (V 0 * V 2 * V 1 * (PolyExpr.const 1 + PolyExpr.const 1))
        (by decide) (fun | 0 => ε g | 1 => m g | _ => M g))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add h1 h1)
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 g) (hM0 g)) (hm0 g))

end env

end YMGap.Continuum.PolymerRemovalChain
