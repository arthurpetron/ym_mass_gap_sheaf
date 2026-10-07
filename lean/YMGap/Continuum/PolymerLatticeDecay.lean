/-
# Lattice-distance decay for the degree-24 polymer gases (commit C of the d-decay)

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule).  Needs two-sided `|z X| ≤ ε^{|X|}`.

* `step_bound`, `CSW`, `farW`, `chainW_bound`: a size-weighted chain.  The lattice budget drops
  by `w h` when the chain steps to `h`.
* `CSW_le`: `CSW_r(g) ≤ λ^r (λη)^{|g|}` with λ = 6/7, ε = 1/10000, η = 1/2500.  Each `η^{|h|}`
  pays for that step's lattice length, so the rate does not depend on the max polymer size.
* `PlaqMetric`: a ℕ-valued plaquette distance with `ld p p = 0`, the triangle inequality, and
  `≤ 1` across a shared link.
* `diam_le`: a connected polymer has `ld p q + 1 ≤ |X|` (ball growth).
* `sepL y g R`: all plaquette pairs are at distance `≥ R`.
* `lattice_decay`: `|U| ≤ (6/7)^R (λη)^{|g|} Ξ(l)Ξ(g::l)`.  `zheat_lattice_decay` is the same
  at w = 1/40.
-/

import YMGap.Continuum.PolymerDecayZ4

namespace YMGap.Continuum.PolymerLatticeDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.BddLatticeAnimal (BddLattice)
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay
open YMGap.Continuum.PolymerDecayZ4

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## 1. Generic one-step bound and the weighted chain -/

section step
variable {α : Type} (z : α → Q') (inc : α → α → Bool)
variable (hsym : ∀ a b, inc a b = inc b a) (Γ : List α) (ε M m : α → Q')
variable (hpos : ∀ l, Good Γ l → (0 : Q') < Xi z inc l)
variable (hMb : ∀ (l : List α) (a : α), Good Γ l →
  Xi z inc (l.filter (cpt inc a)) ≤ M a * Xi z inc l)
variable (hmb : ∀ (x : α) (l : List α), Good Γ (x :: l) → Xi z inc l ≤ m x * Xi z inc (x :: l))
variable (hzb : ∀ a, Q'.abs (z a) ≤ ε a)
variable (hε0 : ∀ a, (0 : Q') ≤ ε a) (hM0 : ∀ a, (0 : Q') ≤ M a) (hm0 : ∀ a, (0 : Q') ≤ m a)

include hsym hpos hMb hmb hzb hε0 hM0 in
theorem step_bound [DecidableEq α] (y g : α) (l : List α) (c : α → Q') (hc0 : ∀ h, (0 : Q') ≤ c h)
    (hyg : inc y g = false)
    (hrec : ∀ h, h ∈ Γ → inc g h = true → ∀ X, Good Γ (y :: h :: X) →
      Q'.abs (U z inc y h X) ≤ c h * (Xi z inc X * Xi z inc (h :: X)))
    (hG : Good Γ (y :: g :: l)) :
    Q'.abs (U z inc y g l) ≤
      ε g * M g * m g * sumd c (Γ.filter (inc g)) * (Xi z inc l * Xi z inc (g :: l)) := by
  have Gyl : Good Γ (y :: l) := good_sub (List.Sublist.cons₂ y (List.sublist_cons_self g l)) hG
  have Ggl : Good Γ (g :: l) := good_sub (List.sublist_cons_self y _) hG
  have Gl : Good Γ l := good_sub (List.sublist_cons_self g l) Ggl
  have GLg : Good Γ (l.filter (cpt inc g)) := good_sub List.filter_sublist Gl
  let L := Xi z inc l
  let G := Xi z inc (g :: l)
  let Y := Xi z inc (y :: l)
  let Lg := Xi z inc (l.filter (cpt inc g))
  have hL : (0 : Q') ≤ L := xi_nn z inc Γ Gl hpos
  have hLg : (0 : Q') ≤ Lg := xi_nn z inc Γ GLg hpos
  have hlm : L ≤ m g * G := hmb g l Ggl
  have hLgM : Lg ≤ M g * L := hMb l g Gl
  let E := Xi z inc ((y :: l).filter (cpt inc g)) * L + -(Y * Lg)
  have hU1 : Q'.abs (U z inc y g l) ≤ ε g * Q'.abs E :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (U_eqv z inc hsym y g l)))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (hzb g) (Q'.abs_nonneg _)))
  have hgy : cpt inc g y = true := by
    show (!inc g y) = true
    rw [hsym g y, hyg]; rfl
  have hfil : (y :: l).filter (cpt inc g) = y :: l.filter (cpt inc g) :=
    List.filter_cons_of_pos hgy
  let R := l.filter (inc g)
  let F := l.filter (cpt inc g)
  have hp : (R ++ F).Perm l := List.filter_append_perm (inc g) l
  have hG' : Good Γ (y :: (R ++ F)) := good_perm (hp.symm.cons y) Gyl
  have hT := telescope z inc Γ hpos y F c R (fun h hh X hX => by
    have hm := List.mem_filter.mp hh
    exact hrec h (Gl.2 h hm.1) hm.2 X hX) hG'
  have hRF : (Xi z inc (R ++ F)).eqv L := Xi_perm z inc hsym hp
  have hyRF : (Xi z inc (y :: (R ++ F))).eqv Y := Xi_perm z inc hsym (hp.cons y)
  have hED : (Q'.abs E).eqv (Q'.abs (D z inc y F (R ++ F))) := by
    refine Q'.abs_eqv_congr ?_
    show (Xi z inc ((y :: l).filter (cpt inc g)) * L + -(Y * Lg)).eqv
      (Xi z inc (y :: F) * Xi z inc (R ++ F) + -(Xi z inc (y :: (R ++ F)) * Xi z inc F))
    rw [hfil]
    exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hRF))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hyRF)))
  let Sg := sumd c (Γ.filter (inc g))
  have hS : sumd c R ≤ Sg :=
    sumd_sub_le _ hc0 R _ (Gl.1.filter _)
      (fun h hh => List.mem_filter.mpr ⟨Gl.2 h (List.mem_filter.mp hh).1,
        (List.mem_filter.mp hh).2⟩)
  have hP : (0 : Q') ≤ Lg * L := Q'.mul_nonneg _ _ hLg hL
  have hE : Q'.abs E ≤ Sg * ((M g * L) * (m g * G)) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hED) (Q'.le_trans' _ _ _ hT ?_)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hRF))) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hS hP) ?_
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (sumd_nonneg _ hc0 _)
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hLgM hL)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hlm (Q'.mul_nonneg _ _ (hM0 g) hL))
  refine Q'.le_trans' _ _ _ hU1 (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hE (hε0 g)) (Q'.le_of_eqv ?_))
  show (ε g * (Sg * ((M g * L) * (m g * G)))).eqv (ε g * M g * m g * Sg * (L * G))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    (V 0 * (V 1 * ((V 2 * V 3) * (V 4 * V 5))))
    (V 0 * V 2 * V 4 * V 1 * (V 3 * V 5)) (by decide)
    (fun | 0 => ε g | 1 => Sg | 2 => M g | 3 => L | 4 => m g | _ => G)

variable (w : α → Nat)

def CSW (y : α) : Nat → Nat → α → Q'
  | 0, _, g => CS inc Γ ε M m y 0 g
  | _ + 1, 0, g => CS inc Γ ε M m y 0 g
  | f + 1, r + 1, g => ε g * M g * m g * sumd (fun h => CSW y f (r + 1 - w h) h) (Γ.filter (inc g))

def farW (y : α) : Nat → Nat → α → Prop
  | 0, _, _ => True
  | _ + 1, 0, _ => True
  | f + 1, r + 1, g => inc y g = false ∧ ∀ h, h ∈ Γ → inc g h = true → farW y f (r + 1 - w h) h

include hε0 hM0 hm0 in
theorem CSW_nonneg (y : α) : ∀ f r g, (0 : Q') ≤ CSW inc Γ ε M m w y f r g
  | 0, _, g => CS_nonneg inc Γ ε M m hε0 hM0 hm0 y 0 g
  | _ + 1, 0, g => CS_nonneg inc Γ ε M m hε0 hM0 hm0 y 0 g
  | f + 1, r + 1, g => Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hε0 g) (hM0 g)) (hm0 g))
      (sumd_nonneg _ (fun h => CSW_nonneg y f (r + 1 - w h) h) _)

include hsym hpos hMb hmb hzb hε0 hM0 hm0 in
theorem chainW_bound [DecidableEq α] (y : α) : ∀ (f r : Nat) (g : α) (l : List α),
    farW inc Γ w y f r g → Good Γ (y :: g :: l) →
    Q'.abs (U z inc y g l) ≤ CSW inc Γ ε M m w y f r g * (Xi z inc l * Xi z inc (g :: l))
  | 0, _, g, l, _, hG => chain_bound z inc hsym Γ ε M m hpos hMb hmb hzb hε0 hM0 hm0 y 0 g l trivial hG
  | _ + 1, 0, g, l, _, hG =>
      chain_bound z inc hsym Γ ε M m hpos hMb hmb hzb hε0 hM0 hm0 y 0 g l trivial hG
  | f + 1, r + 1, g, l, ⟨hyg, hfar⟩, hG =>
      step_bound z inc hsym Γ ε M m hpos hMb hmb hzb hε0 hM0 y g l _
        (fun h => CSW_nonneg inc Γ ε M m hε0 hM0 hm0 w y f (r + 1 - w h) h) hyg
        (fun h hh hi X hX => chainW_bound y f (r + 1 - w h) h X (hfar h hh hi) hX) hG

end step

/-! ## 2. Scalars: λ = 6/7, η_λ = λη -/

def lam : Q' := Q'.mkPos 6 7 (by decide)
abbrev etaL : Q' := lam * etaZ

theorem pow_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) : ∀ t : Nat, a ^ t ≤ b ^ t
  | 0 => Q'.le_refl' _
  | t + 1 => by
    show a * a ^ t ≤ b * b ^ t
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono ha hab t) ha)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hab (Q'.pow_nonneg _ (Q'.le_trans' _ _ _ ha hab) _))

theorem geo_le {a b K : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) (haK : a * K ≤ b) :
    ∀ s : Nat, 1 ≤ s → a ^ s * K ≤ b ^ s
  | 0, h => absurd h (by decide)
  | t + 1, _ => by
    show a * a ^ t * K ≤ b * b ^ t
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (a * a ^ t * K).eqv (a ^ t * (a * K)) from by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * V 2) (V 1 * (V 0 * V 2)) (by decide)
        (fun | 0 => a | 1 => a ^ t | _ => K))) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ haK (Q'.pow_nonneg _ ha _)) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (pow_mono ha hab t)
      (Q'.le_trans' _ _ _ ha hab)) (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

theorem fin_le (a K : Q') (s : Nat) (hs : 1 ≤ s) (ha : (0 : Q') ≤ a) (hK : (0 : Q') ≤ K)
    (hal : a ≤ lam) (haK : a * ((1 + etaZ) * K) ≤ lam) :
    a ^ s * etaZ ^ s * (1 + etaZ ^ s) * K ≤ etaL ^ s := by
  have hη := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) s hs
  have h0 : (0 : Q') ≤ a ^ s * etaZ ^ s := Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ha _) (Q'.pow_nonneg _ (by decide) _)
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add (Q'.le_refl' 1) hη) h0) hK) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (a ^ s * etaZ ^ s * (1 + etaZ) * K).eqv
      (a ^ s * ((1 + etaZ) * K) * etaZ ^ s) from by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 3) (V 0 * (V 2 * V 3) * V 1) (by decide)
      (fun | 0 => a ^ s | 1 => etaZ ^ s | 2 => 1 + etaZ | _ => K))) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (geo_le ha hal haK s hs) (Q'.pow_nonneg _ (by decide) _)) (Q'.le_of_eqv (mul_pow' _ _ s))

theorem stepW (s : Nat) (hs : 1 ≤ s) :
    epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) * five3 ^ s ≤ etaL ^ s := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (fin_le sigma 1 s hs (by decide) (by decide) (by decide) (by decide))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ (eps55_pow s)))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 1) (V 0 * V 1 * V 1 * V 2 * PolyExpr.const 1)
    (by decide) (fun | 0 => epsZ ^ s | 1 => five3 ^ s | _ => 1 + etaZ ^ s)

theorem baseW (s t : Nat) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) *
      ((1 + epsZ ^ t * five3 ^ t) + (1 + epsZ ^ t * five3 ^ t)) ≤ etaL ^ s := by
  have hρt := pow_le_self (by decide : (0 : Q') ≤ rho) (by decide) t ht
  have hηt := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) t ht
  have hpt : epsZ ^ t * five3 ^ t ≤ rho * etaZ :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (eps5_pow t)) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hρt (Q'.pow_nonneg _ (by decide) _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hηt (by decide)))
  have hK : (1 + epsZ ^ t * five3 ^ t) + (1 + epsZ ^ t * five3 ^ t) ≤
      (1 + rho * etaZ) + (1 + rho * etaZ) :=
    Q'.add_le_add (Q'.add_le_add (Q'.le_refl' 1) hpt) (Q'.add_le_add (Q'.le_refl' 1) hpt)
  have hA0 : (0 : Q') ≤ epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
      (Q'.pow_nonneg _ (by decide) _)) (Q'.zero_le_add _ _ (by decide) (Q'.pow_nonneg _ (by decide) _))
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hK hA0) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (eps5_pow s))))
    (fin_le rho _ s hs (by decide) (by decide) (by decide) (by decide))

/-! ## 3. The degree-24 weighted chain-sum bound -/

section Gas
variable {BL : BddLattice}

theorem lam_shift (a s r : Nat) (h : r ≤ a + s) :
    lam ^ a * etaL ^ s ≤ lam ^ r * etaZ ^ s := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have e : (lam ^ a * etaL ^ s).eqv (lam ^ (a + s) * etaZ ^ s) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (mul_pow' lam etaZ s))) ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (YMGap.Continuum.HeatKernelPolymerActivityR1.pow_add' lam a s)))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 0 * V 1 * V 2) (by decide)
      (fun | 0 => lam ^ a | 1 => lam ^ s | _ => etaZ ^ s)
  rw [hk] at e
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e) (Q'.mul_le_mul_of_nonneg_right _ _ _
    (YMGap.Continuum.HeatKernelPolymerActivityR1.pow_anti (by decide) (by decide) r k)
    (Q'.pow_nonneg _ (by decide) _))

theorem CSW_le (hD : BL.D = 24) (d0 : PL BL) (B : Z4BoxGas BL) (y : Poly BL) :
    ∀ (f r : Nat) (g : Poly BL), r ≤ f →
      CSW shareB B.polys eF MF mF sz y f r g ≤ lam ^ r * etaL ^ sz g
  | 0, 0, g, _ => Q'.le_trans' _ _ _ (baseW (sz g) (sz y) (sz_pos g) (sz_pos y))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
  | 0, _ + 1, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, 0, g, _ => Q'.le_trans' _ _ _ (baseW (sz g) (sz y) (sz_pos g) (sz_pos y))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
  | f + 1, r + 1, g, hr => by
    let L := B.polys.filter (shareB g)
    have ha : (0 : Q') ≤ eF g * MF g * mF g :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (eF_nn g) (MF_nn g)) (mF_nn g)
    have hl0 : (0 : Q') ≤ lam ^ (r + 1) := Q'.pow_nonneg _ (by decide) _
    have hS : sumd (fun h => CSW shareB B.polys eF MF mF sz y f (r + 1 - sz h) h) L ≤
        lam ^ (r + 1) * five3 ^ sz g := by
      refine Q'.le_trans' _ _ _ (sumd_mono _ (fun h => lam ^ (r + 1) * etaZ ^ sz h) (fun h =>
        Q'.le_trans' _ _ _ (CSW_le hD d0 B y f (r + 1 - sz h) h (by have := sz_pos h; omega))
          (lam_shift _ _ _ (by omega))) L) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumd_mul _ (fun h => etaZ ^ sz h) L)) ?_
      refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hl0
      exact Q'.le_trans' _ _ _ (sumd_le_prodm (fun h => etaZ ^ sz h)
        (fun h => Q'.pow_nonneg _ (by decide) _) L) (z4_hgroup hD d0 B g)
    show eF g * MF g * mF g * sumd _ L ≤ lam ^ (r + 1) * etaL ^ sz g
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hS ha) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (eF g * MF g * mF g * (lam ^ (r + 1) * five3 ^ sz g)).eqv
        (lam ^ (r + 1) * (epsZ ^ sz g * five3 ^ sz g * (1 + etaZ ^ sz g) * five3 ^ sz g)) from by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * (V 3 * V 1)) (V 3 * (V 0 * V 1 * V 2 * V 1))
        (by decide)
        (fun | 0 => epsZ ^ sz g | 1 => five3 ^ sz g | 2 => 1 + etaZ ^ sz g | _ => lam ^ (r + 1)))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (stepW (sz g) (sz_pos g)) hl0

/-! ## 4. Lattice distance and separation -/

structure PlaqMetric (BL : BddLattice) where
  ld : PL BL → PL BL → Nat
  self : ∀ p, ld p p = 0
  tri : ∀ p q r, ld p r ≤ ld p q + ld q r
  adj : ∀ p q, BL.toLattice.Adjacent p q → ld p q ≤ 1

variable (pm : PlaqMetric BL)

theorem filt_le {β : Type} (P Q : β → Bool) (h : ∀ x, P x = true → Q x = true) :
    ∀ l : List β, (l.filter P).length ≤ (l.filter Q).length
  | [] => Nat.le_refl 0
  | x :: l => by
    have ih := filt_le P Q h l
    cases hp : P x <;> cases hq : Q x <;> simp only [List.filter, hp, hq, List.length_cons]
    · exact ih
    · exact Nat.le_succ_of_le ih
    · exact absurd (h x hp) (by rw [hq]; decide)
    · exact Nat.succ_le_succ ih

theorem filt_lt {β : Type} (P Q : β → Bool) (h : ∀ x, P x = true → Q x = true) (b : β)
    (hQ : Q b = true) (hP : P b = false) :
    ∀ l : List β, b ∈ l → (l.filter P).length < (l.filter Q).length
  | [], hb => absurd hb List.not_mem_nil
  | x :: l, hb => by
    rcases List.mem_cons.mp hb with e | hb'
    · subst e
      have := filt_le P Q h l
      simp only [List.filter, hP, hQ, List.length_cons]
      exact Nat.lt_succ_of_le this
    · have ih := filt_lt P Q h b hQ hP l hb'
      cases hp : P x <;> cases hq : Q x <;> simp only [List.filter, hp, hq, List.length_cons]
      · exact ih
      · exact Nat.lt_succ_of_lt ih
      · exact absurd (h x hp) (by rw [hq]; decide)
      · exact Nat.succ_lt_succ ih

theorem ivt (X : Poly BL) (p : PL BL) : ∀ a q : PL BL,
    YMGap.Continuum.PolymerModel.ChainIn BL.toLattice X a q → a ∈ X →
    ∀ j, pm.ld p a ≤ j → j ≤ pm.ld p q → ∃ b, b ∈ X ∧ pm.ld p b = j
  | a, _, .refl _, ha, j, h1, h2 => ⟨a, ha, Nat.le_antisymm h1 h2⟩
  | a, q, .step (r := r) adj hr rest, ha, j, h1, h2 => by
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · exact ⟨a, ha, e⟩
    · have := pm.tri p a r; have := pm.adj _ _ adj
      exact ivt X p _ q rest hr j (by omega) h2

theorem diam_le (X : Poly BL) (p q : PL BL)
    (c : YMGap.Continuum.PolymerModel.ChainIn BL.toLattice X p q) (hp : p ∈ X) :
    pm.ld p q + 1 ≤ X.length := by
  let cnt := fun k => (X.filter (fun x => decide (pm.ld p x ≤ k))).length
  have grow : ∀ k, k ≤ pm.ld p q → k + 1 ≤ cnt k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hp, decide_eq_true (Nat.le_of_eq (pm.self p))⟩)
    | succ k ih =>
      intro hk
      obtain ⟨b, hb, hbk⟩ := ivt pm X p p q c hp (k + 1) (by rw [pm.self]; exact Nat.zero_le _) hk
      have h := filt_lt (fun x => decide (pm.ld p x ≤ k)) (fun x => decide (pm.ld p x ≤ k + 1))
        (fun x hx => decide_eq_true (Nat.le_succ_of_le (of_decide_eq_true hx))) b
        (decide_eq_true (Nat.le_of_eq hbk)) (decide_eq_false (by omega)) X hb
      exact Nat.le_trans (Nat.succ_le_succ (ih (by omega))) h
  exact Nat.le_trans (grow _ (Nat.le_refl _)) (List.length_filter_le _ _)

def sepL (y g : Poly BL) (R : Nat) : Prop := ∀ p, p ∈ y → ∀ q, q ∈ g → R ≤ pm.ld p q

theorem sep_incomp (y g : Poly BL) (R : Nat) (hs : sepL pm y g R) (hR : 1 ≤ R) :
    shareB y g = false := by
  cases hb : shareB y g with
  | false => rfl
  | true =>
    obtain ⟨c, hcy, hcg⟩ := (shareB_iff y g).mp hb
    have := hs c hcy c hcg
    rw [pm.self] at this
    exact absurd this (by omega)

theorem sep_step (B : Z4BoxGas BL) (y g h : Poly BL) (R : Nat) (hs : sepL pm y g R)
    (hh : h ∈ B.polys) (hgh : shareB g h = true) : sepL pm y h (R - sz h) := by
  obtain ⟨c, hcg, hch⟩ := (shareB_iff g h).mp hgh
  obtain ⟨cn⟩ := B.conn h hh
  intro p hp q hq
  have h1 := hs p hp c hcg
  have h2 := pm.tri p q c
  have h3 := diam_le pm h q c (cn q c hq hch) hq
  rw [← sz_of_ne h (B.size_ok h hh).1] at h3
  omega

theorem sep_far (B : Z4BoxGas BL) (y : Poly BL) : ∀ (f R : Nat) (g : Poly BL),
    sepL pm y g R → farW shareB B.polys sz y f R g
  | 0, _, _, _ => trivial
  | _ + 1, 0, _, _ => trivial
  | f + 1, r + 1, g, hs => ⟨sep_incomp pm y g (r + 1) hs (Nat.succ_le_succ (Nat.zero_le _)),
      fun h hh hi => sep_far B y f (r + 1 - sz h) h (sep_step pm B y g h (r + 1) hs hh hi)⟩

/-- **Lattice-distance decay (PROVED):** rate `(6/7)^R`, independent of the max polymer size. -/
theorem lattice_decay (hD : BL.D = 24) (d0 : PL BL) (B : Z4BoxGas BL) (z : Poly BL → Q')
    (hz1 : ∀ X, (0 : Q') ≤ z X + epsZ ^ sz X) (hz2 : ∀ X, z X ≤ epsZ ^ sz X)
    (y g : Poly BL) (l : List (Poly BL)) (R : Nat)
    (hsep : sepL pm y g R) (hG : Good B.polys (y :: g :: l)) :
    Q'.abs (U z shareB y g l) ≤ (lam ^ R * etaL ^ sz g) * (Xi z shareB l * Xi z shareB (g :: l)) := by
  have hcb := chainW_bound z shareB shareB_symm B.polys eF MF mF
    (env_pos hD d0 B z hz1) (env_M hD d0 B z hz1) (env_m hD d0 B z hz1) (env_z z hz1 hz2)
    eF_nn MF_nn mF_nn sz y R R g l (sep_far pm B y R R g hsep) hG
  have hP : (0 : Q') ≤ Xi z shareB l * Xi z shareB (g :: l) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (env_pos hD d0 B z hz1 l
      (good_sub (List.sublist_cons_self g l) (good_sub (List.sublist_cons_self y _) hG))))
      (Q'.le_of_lt (env_pos hD d0 B z hz1 (g :: l) (good_sub (List.sublist_cons_self y _) hG)))
  exact Q'.le_trans' _ _ _ hcb
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (CSW_le hD d0 B y R R g (Nat.le_refl R)) hP)

open YMGap.Continuum.HeatKernelPolymerActivityR1 in
/-- **Lattice-distance decay for the heat-kernel gas at w = 1/40 (PROVED).** -/
theorem zheat_lattice_decay (hD : BL.D = 24) (d0 : PL BL) (B : Z4BoxGas BL) (M : Nat)
    (y g : Poly BL) (l : List (Poly BL)) (R : Nat)
    (hsep : sepL pm y g R) (hG : Good B.polys (y :: g :: l)) :
    Q'.abs (U (zHeat M) shareB y g l) ≤
      (lam ^ R * etaL ^ sz g) * (Xi (zHeat M) shareB l * Xi (zHeat M) shareB (g :: l)) :=
  lattice_decay pm hD d0 B (zHeat M)
    (fun X => Q'.zero_le_add _ _ (zHeat_bounds M X).1 (Q'.pow_nonneg _ (by decide : (0 : Q') ≤ epsZ) _))
    (fun X => (zHeat_bounds M X).2) y g l R hsep hG

end Gas

end YMGap.Continuum.PolymerLatticeDecay
