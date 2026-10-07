/-
# One-polymer ratio-Lipschitz bound for the degree-24 polymer gases (box and torus)

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).

For a polymer `y` and polymer lists `S₀, T₀`, the "insertion ratio"
`R(Λ) := Ξ(y :: Λ) / Ξ(Λ)` is compared in cross-multiplied form (no division):

  `D := Ξ(y::S₀)·Ξ(T₀) − Ξ(y::T₀)·Ξ(S₀)`.

* `cross_step`: the exact identity `D ≡ z_y · (Ξ(S₀∖N y)·Ξ(T₀) − Ξ(T₀∖N y)·Ξ(S₀))`.
* `cross_bound`: abstract two-sided bound `|D| ≤ ε(M+M)·Ξ(S₀)Ξ(T₀)`, given
  `|z_y| ≤ ε` and `0 ≤ Ξ(X∖N y) ≤ M Ξ(X)`.
* `deg24_ratio_lip`: for every `Z4BoxGas BL` with `BL.D = 24` (this covers both `z4Chain`
  and `torusChain N`), any `S₀, T₀ ⊆ polys`, and `|z X| ≤ (1/10000)^{|X|}`:
  `|D| ≤ 2·(1/10000)^{|y|}·(5/3)^{|y|} · Ξ(S₀)Ξ(T₀)`.
  That is, `|R(S₀) − R(T₀)| ≤ C·q^{|y|}` with `C = 2` and `q = 1/6000`.

**Not proved here:** decay in the graph distance d between `y` and the symmetric difference of
`S₀` and `T₀`.  `cross_step` is the one-step recursion that would be iterated; the d-step
telescoping with ratio control is open.
-/

import YMGap.Continuum.Z4PolymerKP

namespace YMGap.Continuum.PolymerRatioLipschitz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.BddLatticeAnimal (BddLattice)
open YMGap.Continuum.Z4PolymerKP

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

section Generic
variable {α : Type} (z : α → Q') (inc : α → α → Bool)

/-- **Exact one-step identity (PROVED).** -/
theorem cross_step (y : α) (S₀ T₀ : List α) :
    (Xi z inc (y :: S₀) * Xi z inc T₀ + -(Xi z inc (y :: T₀) * Xi z inc S₀)).eqv
      (z y * (Xi z inc (S₀.filter (cpt inc y)) * Xi z inc T₀ +
        -(Xi z inc (T₀.filter (cpt inc y)) * Xi z inc S₀))) := by
  rw [Xi_cons, Xi_cons z inc y T₀]
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    ((V 0 + V 1 * V 2) * V 3 + -((V 3 + V 1 * V 4) * V 0))
    (V 1 * (V 2 * V 3 + -(V 4 * V 0))) (by decide)
    (fun | 0 => Xi z inc S₀ | 1 => z y | 2 => Xi z inc (S₀.filter (cpt inc y))
         | 3 => Xi z inc T₀ | _ => Xi z inc (T₀.filter (cpt inc y)))

/-- **Abstract two-sided one-polymer bound (PROVED).** -/
theorem cross_bound (y : α) (S₀ T₀ : List α) (ε M : Q')
    (hzU : z y ≤ ε) (hzL : (0 : Q') ≤ z y + ε) (hε : (0 : Q') ≤ ε)
    (hS : (0 : Q') ≤ Xi z inc S₀) (hT : (0 : Q') ≤ Xi z inc T₀)
    (hSy : (0 : Q') ≤ Xi z inc (S₀.filter (cpt inc y)))
    (hTy : (0 : Q') ≤ Xi z inc (T₀.filter (cpt inc y)))
    (hSM : Xi z inc (S₀.filter (cpt inc y)) ≤ M * Xi z inc S₀)
    (hTM : Xi z inc (T₀.filter (cpt inc y)) ≤ M * Xi z inc T₀) :
    Xi z inc (y :: S₀) * Xi z inc T₀ + -(Xi z inc (y :: T₀) * Xi z inc S₀) ≤
        (ε * (M + M)) * (Xi z inc S₀ * Xi z inc T₀) ∧
      (0 : Q') ≤ Xi z inc (y :: S₀) * Xi z inc T₀ + -(Xi z inc (y :: T₀) * Xi z inc S₀) +
        (ε * (M + M)) * (Xi z inc S₀ * Xi z inc T₀) := by
  rw [Xi_cons, Xi_cons z inc y T₀]
  let s := Xi z inc S₀
  let t := Xi z inc T₀
  let sy := Xi z inc (S₀.filter (cpt inc y))
  let ty := Xi z inc (T₀.filter (cpt inc y))
  have hεz : (0 : Q') ≤ ε + -(z y) := Q'.sub_nonneg_of_le hzU
  have hMs : (0 : Q') ≤ M * s + -sy := Q'.sub_nonneg_of_le hSM
  have hMt : (0 : Q') ≤ M * t + -ty := Q'.sub_nonneg_of_le hTM
  have hA : (0 : Q') ≤ sy * t := Q'.mul_nonneg _ _ hSy hT
  have hB : (0 : Q') ≤ ty * s := Q'.mul_nonneg _ _ hTy hS
  have hC : (0 : Q') ≤ ε * ((M * s + -sy) * t) :=
    Q'.mul_nonneg _ _ hε (Q'.mul_nonneg _ _ hMs hT)
  have hE : (0 : Q') ≤ ε * ((M * t + -ty) * s) :=
    Q'.mul_nonneg _ _ hε (Q'.mul_nonneg _ _ hMt hS)
  let V := PolyExpr.var
  let ρ : Nat → Q' := fun | 0 => s | 1 => z y | 2 => sy | 3 => t | 4 => ty | 5 => ε | _ => M
  constructor
  · refine le_of_eqv_add (S := (ε + -(z y)) * (sy * t) + (z y + ε) * (ty * s) +
      ε * ((M * s + -sy) * t) + ε * ((M * t + -ty) * s)) ?_ ?_
    · exact poly_identity_of_normal_eq
        ((V 5 * (V 6 + V 6)) * (V 0 * V 3))
        (((V 0 + V 1 * V 2) * V 3 + -((V 3 + V 1 * V 4) * V 0)) +
          ((V 5 + -V 1) * (V 2 * V 3) + (V 1 + V 5) * (V 4 * V 0) +
            V 5 * ((V 6 * V 0 + -V 2) * V 3) + V 5 * ((V 6 * V 3 + -V 4) * V 0)))
        (by decide) ρ
    · exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ hεz hA) (Q'.mul_nonneg _ _ hzL hB)) hC) hE
  · refine Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ hzL hA) (Q'.mul_nonneg _ _ hεz hB)) hC) hE) (Q'.le_of_eqv ?_)
    exact poly_identity_of_normal_eq
      ((V 1 + V 5) * (V 2 * V 3) + (V 5 + -V 1) * (V 4 * V 0) +
        V 5 * ((V 6 * V 0 + -V 2) * V 3) + V 5 * ((V 6 * V 3 + -V 4) * V 0))
      (((V 0 + V 1 * V 2) * V 3 + -((V 3 + V 1 * V 4) * V 0)) +
        (V 5 * (V 6 + V 6)) * (V 0 * V 3))
      (by decide) ρ

end Generic

section Deg24
variable {BL : BddLattice}

theorem neighbour_mass (hD : BL.D = 24) (d : PL BL) (B : Z4BoxGas BL) (z : Poly BL → Q')
    (hz1 : ∀ X, (0 : Q') ≤ z X + epsZ ^ sz X) (y : Poly BL) (S₀ : List (Poly BL))
    (hS : S₀.Sublist B.polys) :
    (0 : Q') ≤ Xi z shareB S₀ ∧ (0 : Q') ≤ Xi z shareB (S₀.filter (cpt shareB y)) ∧
      Xi z shareB (S₀.filter (cpt shareB y)) ≤ five3 ^ sz y * Xi z shareB S₀ := by
  have hc := z4_cond shareB sz sz_pos B.polys (fun a => z4_hgroup hD d B a)
  have hm : ∀ x : Poly BL, (1 : Q') ≤ 1 + etaZ ^ sz x :=
    fun x => Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
  have he : ∀ a : Poly BL, (0 : Q') ≤ epsZ ^ sz a := fun a => Q'.pow_nonneg _ (by decide) _
  have hcS := cond_mono shareB _ _ hm he hS hc.1
  have hcS2 := cond2_mono shareB _ _ hm he hS hc.2
  have hy : (S₀.filter (cpt shareB y)).Sublist S₀ := sub_filter_self _ S₀
  have h0 := (kpw_main z shareB _ _ shareB_symm hm he hz1 S₀ hcS hcS2).1
  have h0y := (kpw_main z shareB _ _ shareB_symm hm he hz1 _
    (cond_mono shareB _ _ hm he hy hcS) (cond2_mono shareB _ _ hm he hy hcS2)).1
  have hf := kpw_filter z shareB _ _ shareB_symm hm he hz1 S₀ hcS hcS2 (cpt shareB y)
  have hfe : S₀.filter (fun x => !cpt shareB y x) = S₀.filter (shareB y) :=
    filter_congr' _ _ (fun x => by unfold cpt; cases shareB y x <;> rfl) S₀
  rw [hfe] at hf
  have hsub : (S₀.filter (shareB y)).Sublist (B.polys.filter (shareB y)) :=
    sub_filter _ hS
  have hpm : prodm (fun x => 1 + etaZ ^ sz x) (S₀.filter (shareB y)) ≤ five3 ^ sz y :=
    Q'.le_trans' _ _ _ (prodm_sub _ hm hsub) (z4_hgroup hD d B y)
  exact ⟨h0, h0y, Q'.le_trans' _ _ _ hf (Q'.mul_le_mul_of_nonneg_right _ _ _ hpm h0)⟩

/-- **One-polymer ratio-Lipschitz bound, degree-24 box or torus gas (PROVED).**
`|Ξ(y::S₀)Ξ(T₀) − Ξ(y::T₀)Ξ(S₀)| ≤ ε^{|y|}·2·(5/3)^{|y|} · Ξ(S₀)Ξ(T₀)`. -/
theorem deg24_ratio_lip (hD : BL.D = 24) (d : PL BL) (B : Z4BoxGas BL) (z : Poly BL → Q')
    (hz1 : ∀ X, (0 : Q') ≤ z X + epsZ ^ sz X) (hz2 : ∀ X, z X ≤ epsZ ^ sz X)
    (y : Poly BL) (S₀ T₀ : List (Poly BL))
    (hS : S₀.Sublist B.polys) (hT : T₀.Sublist B.polys) :
    Xi z shareB (y :: S₀) * Xi z shareB T₀ + -(Xi z shareB (y :: T₀) * Xi z shareB S₀) ≤
        (epsZ ^ sz y * (five3 ^ sz y + five3 ^ sz y)) * (Xi z shareB S₀ * Xi z shareB T₀) ∧
      (0 : Q') ≤ Xi z shareB (y :: S₀) * Xi z shareB T₀ +
        -(Xi z shareB (y :: T₀) * Xi z shareB S₀) +
        (epsZ ^ sz y * (five3 ^ sz y + five3 ^ sz y)) * (Xi z shareB S₀ * Xi z shareB T₀) := by
  have nS := neighbour_mass hD d B z hz1 y S₀ hS
  have nT := neighbour_mass hD d B z hz1 y T₀ hT
  exact cross_bound z shareB y S₀ T₀ _ _ (hz2 y) (hz1 y) (Q'.pow_nonneg _ (by decide) _)
    nS.1 nT.1 nS.2.1 nT.2.1 nS.2.2 nT.2.2

end Deg24

end YMGap.Continuum.PolymerRatioLipschitz

#print axioms YMGap.Continuum.PolymerRatioLipschitz.cross_step
#print axioms YMGap.Continuum.PolymerRatioLipschitz.cross_bound
#print axioms YMGap.Continuum.PolymerRatioLipschitz.deg24_ratio_lip
