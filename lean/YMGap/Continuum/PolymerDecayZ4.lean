/-
# Graph-distance decay for the degree-24 polymer gases, and for the zHeat gas at w = 1/40
(commit B of the d-decay)

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).  The decay needs
the two-sided activity bound `|z X| ≤ ε^{|X|}`; the KP bound alone needs only the lower bound.

For a `Z4BoxGas BL` with `BL.D = 24` (box `z4Chain` or torus `torusChain N`), take `Γ = polys`
and `Good` = duplicate-free inside `Γ`.

* `env_*`: the hypotheses of `PolymerChainDecay.chain_bound`, discharged:
  - positivity `0 < Ξ`;
  - `Ξ(l∖N a) ≤ (5/3)^{|a|} Ξ(l)`;
  - removal ratio `1+η^{|x|}`;
  - `|z| ≤ ε^{|X|}`.
* `CS_le`: `CS_d(g) ≤ (7/10)^d · η^{|g|}`, with ε = 1/10000 and η = 1/2500.  The constants are
  q = 7/10 and C = 1.  The step bounds `Σ_{h∈Γ, h∩g≠∅} η^{|h|}` by `Π(1+η^{|h|}) ≤ (5/3)^{|g|}`
  (`z4_hgroup`).  The scalar facts are `(1+η)·25/36 ≤ 7/10` and `(1+η)(5/12)·2(1+1/6000) ≤ 1`.
* `deg24_decay`: if g is at incompatibility distance ≥ d from y, then
  `|Ξ(y::g::l)Ξ(l) − Ξ(y::l)Ξ(g::l)| ≤ (7/10)^d η^{|g|} Ξ(l)Ξ(g::l)`.
* `zheat_decay`: the same statement for the explicit activity `zHeat` at w = 1/40.
-/

import YMGap.Continuum.PolymerChainDecay
import YMGap.Continuum.HeatKernelPolymerActivityR1

namespace YMGap.Continuum.PolymerDecayZ4

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.BddLatticeAnimal (BddLattice)
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## Generic helpers -/

theorem prodm_perm {α : Type} (f : α → Q') {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (prodm f l₁).eqv (prodm f l₂) := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons x _ ih => exact Q'.mul_eqv_congr_left _ _ _ ih
  | swap x y l =>
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * (V 0 * V 2)) (by decide)
      (fun | 0 => f y | 1 => f x | _ => prodm f l)
  | trans _ _ ih₁ ih₂ => exact Q'.eqv_trans _ _ _ ih₁ ih₂

theorem prodm_sub_le {α : Type} [DecidableEq α] (f : α → Q') (hf : ∀ x, (1 : Q') ≤ f x) :
    ∀ l₁ l₂ : List α, l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → prodm f l₁ ≤ prodm f l₂
  | [], l₂, _, _ => prodm_ge_one f hf l₂
  | x :: l₁, l₂, hnd, hs => by
    have hx : x ∈ l₂ := hs x List.mem_cons_self
    have hp := YMGap.Continuum.TorusWilsonAction.perm_cons_rem x hx
    have hnx : x ∉ l₁ := (List.nodup_cons.mp hnd).1
    have ih := prodm_sub_le f hf l₁ (YMGap.Continuum.TorusWilsonAction.rem x l₂)
      (List.nodup_cons.mp hnd).2 (fun y hy => by
        have hyx : y ≠ x := fun e => hnx (e ▸ hy)
        exact YMGap.Continuum.TorusWilsonAction.mem_rem_of_ne x y hyx
          (hs y (List.mem_cons_of_mem _ hy)))
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih (m_nonneg f hf x)) ?_
    exact Q'.le_of_eqv (prodm_perm f hp.symm)

theorem sumd_le_prodm {α : Type} (δ : α → Q') (hδ : ∀ x, (0 : Q') ≤ δ x) :
    ∀ L : List α, sumd δ L ≤ prodm (fun x => 1 + δ x) L
  | [] => (by decide : (0 : Q') ≤ 1)
  | x :: L => by
    have hP := prodm_ge_one (fun x => 1 + δ x) (fun x => Q'.add_le_self_of_nonneg _ _ (hδ x)) L
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_refl' (δ x)) (sumd_le_prodm δ hδ L)) ?_
    refine le_of_eqv_add (S := δ x * (prodm (fun x => 1 + δ x) L + -1)) ?_
      (Q'.mul_nonneg _ _ (hδ x) (Q'.sub_nonneg_of_le hP))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq ((PolyExpr.const 1 + V 0) * V 1)
      ((V 0 + V 1) + V 0 * (V 1 + -(PolyExpr.const 1))) (by decide)
      (fun | 0 => δ x | _ => prodm (fun x => 1 + δ x) L)

theorem sumd_mono {α : Type} (f g : α → Q') (h : ∀ x, f x ≤ g x) :
    ∀ L : List α, sumd f L ≤ sumd g L
  | [] => Q'.le_refl' _
  | x :: L => Q'.add_le_add (h x) (sumd_mono f g h L)

theorem sumd_mul {α : Type} (c : Q') (f : α → Q') :
    ∀ L : List α, (sumd (fun x => c * f x) L).eqv (c * sumd f L)
  | [] => by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (PolyExpr.const 0) (V 0 * PolyExpr.const 0) (by decide)
        (fun _ => c)
  | x :: L => by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (sumd_mul c f L)) ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 + V 0 * V 2) (V 0 * (V 1 + V 2)) (by decide)
      (fun | 0 => c | 1 => f x | _ => sumd f L)

theorem pos_of_one_le_mul {P X : Q'} (hX : (0 : Q') ≤ X) (h : (1 : Q') ≤ P * X) :
    (0 : Q') < X := by
  have hn : (0 : Int) ≤ X.num := (Q'.zero_le_iff_num_nonneg X).mp hX
  show (0 : Int) * (X.den : Int) < X.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  rcases Int.lt_or_eq_of_le hn with h1 | h1
  · exact h1
  · have h' : (1 : Int) * ((P * X).den : Int) ≤ (P.num * X.num) * (1 : Int) := h
    rw [← h1, Int.mul_zero, Int.zero_mul, Int.one_mul] at h'
    exact absurd h' (Int.not_le.mpr (Int.ofNat_lt.mpr (Q'.den_pos _)))

theorem pow_le_self {r : Q'} (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) (s : Nat) (hs : 1 ≤ s) :
    r ^ s ≤ r := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  rw [hk]
  exact Q'.le_trans' _ _ _ (YMGap.Continuum.HeatKernelPolymerActivityR1.pow_anti h0 h1 1 k)
    (Q'.le_of_eqv (Q'.mul_one_eqv r))

/-! ## Scalar facts -/

def theta : Q' := Q'.mkPos 7 10 (by decide)
def rho : Q' := Q'.mkPos 5 12 (by decide)
def sigma : Q' := Q'.mkPos 25 36 (by decide)

theorem eps5_pow (s : Nat) : (epsZ ^ s * five3 ^ s).eqv (rho ^ s * etaZ ^ s) :=
  Q'.eqv_trans _ _ _ (mul_pow' _ _ s) (Q'.eqv_trans _ _ _
    (pow_congr' (by decide : (epsZ * five3).eqv (rho * etaZ)) s) (Q'.eqv_symm (mul_pow' _ _ s)))

theorem eps55_pow (s : Nat) : (epsZ ^ s * five3 ^ s * five3 ^ s).eqv (sigma ^ s * etaZ ^ s) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (mul_pow' _ _ s)) ?_
  refine Q'.eqv_trans _ _ _ (mul_pow' _ _ s) ?_
  exact Q'.eqv_trans _ _ _ (pow_congr' (by decide : (epsZ * five3 * five3).eqv (sigma * etaZ)) s)
    (Q'.eqv_symm (mul_pow' _ _ s))

theorem scalar_step (s : Nat) (hs : 1 ≤ s) :
    epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) * five3 ^ s ≤ theta * etaZ ^ s := by
  have hη := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) s hs
  have hσ := pow_le_self (by decide : (0 : Q') ≤ sigma) (by decide) s hs
  have hη0 : (0 : Q') ≤ etaZ ^ s := Q'.pow_nonneg _ (by decide) _
  have hσ0 : (0 : Q') ≤ sigma ^ s := Q'.pow_nonneg _ (by decide) _
  have e : (epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) * five3 ^ s).eqv
      ((1 + etaZ ^ s) * sigma ^ s * etaZ ^ s) := by
    have h1 : (epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) * five3 ^ s).eqv
        ((1 + etaZ ^ s) * (epsZ ^ s * five3 ^ s * five3 ^ s)) := by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 1) (V 2 * (V 0 * V 1 * V 1)) (by decide)
        (fun | 0 => epsZ ^ s | 1 => five3 ^ s | _ => 1 + etaZ ^ s)
    have h2 : ((1 + etaZ ^ s) * (sigma ^ s * etaZ ^ s)).eqv ((1 + etaZ ^ s) * sigma ^ s * etaZ ^ s) := by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 0 * V 1 * V 2) (by decide)
        (fun | 0 => 1 + etaZ ^ s | 1 => sigma ^ s | _ => etaZ ^ s)
    exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (eps55_pow s)) h2)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  refine Q'.mul_le_mul_of_nonneg_right _ _ _ ?_ hη0
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.add_le_add (Q'.le_refl' 1) hη) hσ0) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hσ (by decide))
    (by decide : (1 + etaZ) * sigma ≤ theta)

theorem scalar_base (s t : Nat) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) *
      ((1 + epsZ ^ t * five3 ^ t) + (1 + epsZ ^ t * five3 ^ t)) ≤ etaZ ^ s := by
  have hη := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) s hs
  have hρ := pow_le_self (by decide : (0 : Q') ≤ rho) (by decide) s hs
  have hρt := pow_le_self (by decide : (0 : Q') ≤ rho) (by decide) t ht
  have hηt := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) t ht
  have hη0 : (0 : Q') ≤ etaZ ^ s := Q'.pow_nonneg _ (by decide) _
  have hρ0 : (0 : Q') ≤ rho ^ s := Q'.pow_nonneg _ (by decide) _
  have hρt0 : (0 : Q') ≤ rho ^ t := Q'.pow_nonneg _ (by decide) _
  have hηt0 : (0 : Q') ≤ etaZ ^ t := Q'.pow_nonneg _ (by decide) _
  -- p^t ≤ rho*eta
  have hpt : epsZ ^ t * five3 ^ t ≤ rho * etaZ :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (eps5_pow t)) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hρt hηt0)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hηt (by decide)))
  have hK : (1 + epsZ ^ t * five3 ^ t) + (1 + epsZ ^ t * five3 ^ t) ≤
      (1 + rho * etaZ) + (1 + rho * etaZ) :=
    Q'.add_le_add (Q'.add_le_add (Q'.le_refl' 1) hpt) (Q'.add_le_add (Q'.le_refl' 1) hpt)
  have hA : epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) ≤ (rho * (1 + etaZ)) * etaZ ^ s := by
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_eqv (eps5_pow s))
      (Q'.zero_le_add _ _ (by decide) hη0)) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add (Q'.le_refl' 1) hη) (Q'.mul_nonneg _ _ hρ0 hη0)) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hρ hη0) (by decide)) (Q'.le_of_eqv ?_)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * V 2) ((V 0 * V 2) * V 1) (by decide)
      (fun | 0 => rho | 1 => etaZ ^ s | _ => 1 + etaZ)
  have hA0 : (0 : Q') ≤ epsZ ^ s * five3 ^ s * (1 + etaZ ^ s) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
      (Q'.pow_nonneg _ (by decide) _)) (Q'.zero_le_add _ _ (by decide) hη0)
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hK hA0) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hA (by decide)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (((rho * (1 + etaZ)) * etaZ ^ s) *
      ((1 + rho * etaZ) + (1 + rho * etaZ))).eqv
      ((((1 + rho * etaZ) + (1 + rho * etaZ)) * (rho * (1 + etaZ))) * etaZ ^ s) from by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq ((V 0 * V 1) * V 2) ((V 2 * V 0) * V 1) (by decide)
      (fun | 0 => rho * (1 + etaZ) | 1 => etaZ ^ s | _ => (1 + rho * etaZ) + (1 + rho * etaZ)))) ?_
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (by decide : ((1 + rho * etaZ) + (1 + rho * etaZ)) * (rho * (1 + etaZ)) ≤ 1) hη0)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))


/-! ## The degree-24 gas: environment, chain-sum bound, decay -/

section Gas
variable {BL : BddLattice}

abbrev eF (a : Poly BL) : Q' := epsZ ^ sz a
abbrev MF (a : Poly BL) : Q' := five3 ^ sz a
abbrev mF (a : Poly BL) : Q' := 1 + etaZ ^ sz a

theorem mF_ge (x : Poly BL) : (1 : Q') ≤ mF x :=
  Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
theorem eF_nn (a : Poly BL) : (0 : Q') ≤ eF a := Q'.pow_nonneg _ (by decide) _
theorem MF_nn (a : Poly BL) : (0 : Q') ≤ MF a := Q'.pow_nonneg _ (by decide) _
theorem mF_nn (a : Poly BL) : (0 : Q') ≤ mF a := Q'.le_trans' _ _ _ (by decide) (mF_ge a)

theorem hgroupG (hD : BL.D = 24) (d0 : PL BL) (B : Z4BoxGas BL) (l : List (Poly BL))
    (hl : Good B.polys l) (a : Poly BL) :
    prodm (fun x => 1 + etaZ ^ sz x) (l.filter (shareB a)) ≤ five3 ^ sz a :=
  Q'.le_trans' _ _ _ (prodm_sub_le _ mF_ge _ _ (hl.1.sublist List.filter_sublist)
    (fun x hx => by
      have h := List.mem_filter.mp hx
      exact List.mem_filter.mpr ⟨hl.2 x h.1, h.2⟩)) (z4_hgroup hD d0 B a)

section Env
variable (hD : BL.D = 24) (d0 : PL BL) (B : Z4BoxGas BL) (z : Poly BL → Q')
variable (hz1 : ∀ X, (0 : Q') ≤ z X + epsZ ^ sz X) (hz2 : ∀ X, z X ≤ epsZ ^ sz X)

include hD d0 hz1 in
theorem env_pos (l : List (Poly BL)) (hl : Good B.polys l) : (0 : Q') < Xi z shareB l := by
  have hc := z4_cond shareB sz sz_pos l (hgroupG hD d0 B l hl)
  exact pos_of_one_le_mul (kpw_main z shareB _ _ shareB_symm mF_ge eF_nn hz1 l hc.1 hc.2).1
    (kpw_lower z shareB _ _ shareB_symm mF_ge eF_nn hz1 l hc.1 hc.2)

include hD d0 hz1 in
theorem env_M (l : List (Poly BL)) (a : Poly BL) (hl : Good B.polys l) :
    Xi z shareB (l.filter (cpt shareB a)) ≤ MF a * Xi z shareB l := by
  have hc := z4_cond shareB sz sz_pos l (hgroupG hD d0 B l hl)
  have h0 := (kpw_main z shareB _ _ shareB_symm mF_ge eF_nn hz1 l hc.1 hc.2).1
  have hf := kpw_filter z shareB _ _ shareB_symm mF_ge eF_nn hz1 l hc.1 hc.2 (cpt shareB a)
  have hfe : l.filter (fun x => !cpt shareB a x) = l.filter (shareB a) :=
    filter_congr' _ _ (fun x => by unfold cpt; cases shareB a x <;> rfl) l
  rw [hfe] at hf
  exact Q'.le_trans' _ _ _ hf
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (hgroupG hD d0 B l hl a) h0)

include hD d0 hz1 in
theorem env_m (x : Poly BL) (l : List (Poly BL)) (hl : Good B.polys (x :: l)) :
    Xi z shareB l ≤ mF x * Xi z shareB (x :: l) := by
  have hc := z4_cond shareB sz sz_pos (x :: l) (hgroupG hD d0 B (x :: l) hl)
  exact (kpw_main z shareB _ _ shareB_symm mF_ge eF_nn hz1 (x :: l) hc.1 hc.2).2 [] x l rfl

include hz1 hz2 in
theorem env_z (a : Poly BL) : Q'.abs (z a) ≤ eF a := by
  refine Q'.abs_le ?_ (hz2 a)
  refine le_of_eqv_add (S := z a + epsZ ^ sz a) ?_ (hz1 a)
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0) (-(V 1) + (V 0 + V 1)) (by decide)
    (fun | 0 => z a | _ => epsZ ^ sz a)

include hD d0 in
/-- **Chain-sum bound (PROVED):** `CS_d(g) ≤ (7/10)^d · η^{|g|}`  (q = 7/10, C = 1). -/
theorem CS_le (y : Poly BL) : ∀ (d : Nat) (g : Poly BL),
    CS shareB B.polys eF MF mF y d g ≤ theta ^ d * etaZ ^ sz g
  | 0, g => Q'.le_trans' _ _ _ (scalar_base (sz g) (sz y) (sz_pos g) (sz_pos y))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
  | d + 1, g => by
    let L := B.polys.filter (shareB g)
    have ha : (0 : Q') ≤ eF g * MF g * mF g :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (eF_nn g) (MF_nn g)) (mF_nn g)
    have hθ : (0 : Q') ≤ theta ^ d := Q'.pow_nonneg _ (by decide) _
    have hS : sumd (CS shareB B.polys eF MF mF y d) L ≤ theta ^ d * five3 ^ sz g := by
      refine Q'.le_trans' _ _ _ (sumd_mono _ _ (CS_le y d) L) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumd_mul (theta ^ d) (fun h => etaZ ^ sz h) L)) ?_
      refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hθ
      exact Q'.le_trans' _ _ _ (sumd_le_prodm (fun h => etaZ ^ sz h)
        (fun h => Q'.pow_nonneg _ (by decide) _) L) (z4_hgroup hD d0 B g)
    show eF g * MF g * mF g * sumd (CS shareB B.polys eF MF mF y d) L ≤ theta ^ (d + 1) * etaZ ^ sz g
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hS ha) ?_
    have hs := scalar_step (sz g) (sz_pos g)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (eF g * MF g * mF g * (theta ^ d * five3 ^ sz g)).eqv
        (theta ^ d * (epsZ ^ sz g * five3 ^ sz g * (1 + etaZ ^ sz g) * five3 ^ sz g)) from by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * (V 3 * V 1)) (V 3 * (V 0 * V 1 * V 2 * V 1))
        (by decide)
        (fun | 0 => epsZ ^ sz g | 1 => five3 ^ sz g | 2 => 1 + etaZ ^ sz g | _ => theta ^ d))) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hs hθ) (Q'.le_of_eqv ?_)
    show (theta ^ d * (theta * etaZ ^ sz g)).eqv (theta * theta ^ d * etaZ ^ sz g)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * V 0 * V 2) (by decide)
      (fun | 0 => theta ^ d | 1 => theta | _ => etaZ ^ sz g)

include hD d0 hz1 hz2 in
/-- **Graph-distance decay, degree-24 box or torus gas (PROVED).** -/
theorem deg24_decay (y g : Poly BL) (l : List (Poly BL)) (d : Nat)
    (hfar : far shareB B.polys y d g) (hG : Good B.polys (y :: g :: l)) :
    Q'.abs (U z shareB y g l) ≤ (theta ^ d * etaZ ^ sz g) * (Xi z shareB l * Xi z shareB (g :: l)) := by
  have hcb := chain_bound z shareB shareB_symm B.polys eF MF mF
    (env_pos hD d0 B z hz1) (env_M hD d0 B z hz1) (env_m hD d0 B z hz1) (env_z z hz1 hz2)
    eF_nn MF_nn mF_nn y d g l hfar hG
  have hP : (0 : Q') ≤ Xi z shareB l * Xi z shareB (g :: l) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (env_pos hD d0 B z hz1 l
      (good_sub (List.sublist_cons_self g l) (good_sub (List.sublist_cons_self y _) hG))))
      (Q'.le_of_lt (env_pos hD d0 B z hz1 (g :: l) (good_sub (List.sublist_cons_self y _) hG)))
  exact Q'.le_trans' _ _ _ hcb (Q'.mul_le_mul_of_nonneg_right _ _ _ (CS_le hD d0 B y d g) hP)

end Env

open YMGap.Continuum.HeatKernelPolymerActivityR1 in
/-- **Decay for the explicit heat-kernel gas at w = 1/40 (PROVED).** -/
theorem zheat_decay (hD : BL.D = 24) (d0 : PL BL) (B : Z4BoxGas BL) (M : Nat)
    (y g : Poly BL) (l : List (Poly BL)) (d : Nat)
    (hfar : far shareB B.polys y d g) (hG : Good B.polys (y :: g :: l)) :
    Q'.abs (U (zHeat M) shareB y g l) ≤
      (theta ^ d * etaZ ^ sz g) * (Xi (zHeat M) shareB l * Xi (zHeat M) shareB (g :: l)) :=
  deg24_decay hD d0 B (zHeat M)
    (fun X => Q'.zero_le_add _ _ (zHeat_bounds M X).1 (Q'.pow_nonneg _ (by decide : (0 : Q') ≤ epsZ) _))
    (fun X => (zHeat_bounds M X).2) y g l d hfar hG

end Gas

end YMGap.Continuum.PolymerDecayZ4

#print axioms YMGap.Continuum.PolymerDecayZ4.CS_le
#print axioms YMGap.Continuum.PolymerDecayZ4.deg24_decay
#print axioms YMGap.Continuum.PolymerDecayZ4.zheat_decay
