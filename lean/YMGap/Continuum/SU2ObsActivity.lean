/-
# R1 commit 17: observable-activity bounds and rooted sums at w₀

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson; also true for
U(1), not gap evidence.

* `zObs_bound`: `|z^S γ| ≤ D^{|S|}·ε_L^{|γ|}` for a nodup γ, with D = 514·10¹⁵ (so D·ε_L = 514).
  This is the "514/ε_L per observable plaquette" input.
* `root_sum`: for 0 ≤ c ≤ η = 1/2500, `Σ_{a∈gas, p∈a} c^{|a|} ≤ (5/3)^{24}`.  This is `hgroupL`
  with a = [p].
* `lam_shift`: `λ^{d−s} ≤ λ^d μ^s` with λ = 6/7 and μ = 7/6.
* `env_w0`: positivity of Ξ and the ratio bound `Ξ(l_a) ≤ M_a Ξ(l)` for the w₀ activity.
-/

import YMGap.Continuum.SU2TwoRoot
import YMGap.Continuum.SU2RemovalDecay

namespace YMGap.Continuum.SU2ObsActivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.SignedPolymerKP (Xi cpt)
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay (Good)
open YMGap.Continuum.PolymerDecayZ4 (sumd_le_prodm sumd_mono)
open YMGap.Continuum.PolymerLatticeDecay (lam pow_mono)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarL1Activity (l1 l1_nonneg l1_mul haar_abs prodPoly fPoly w0 epsL fPoly_pass activity_bound)
open YMGap.Continuum.SU2ObsInsertion
open YMGap.Continuum.SU2ObsRoot (hasP inc_of_mem)
open YMGap.Continuum.SU2LinkKP

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

def Dc : Q' := Q'.ofNat 514000000000000000
def mu : Q' := Q'.mkPos 7 6 (by decide)

variable (M : Nat) (links : List Z4Link) (N : Nat)

theorem gObs_l1 (S : List Z4Plaq) (r : Z4Plaq) :
    l1 (gObs w0 M links N S r) ≤ (if r ∈ S then Dc * epsL else epsL) := by
  by_cases h : r ∈ S
  · rw [if_pos h]
    exact Q'.le_trans' _ _ _ (l1_gObs w0 M links N S r epsL (fPoly_pass links N r M)) (by decide)
  · rw [if_neg h]
    have e : gObs w0 M links N S r = fPoly w0 links N r M := by unfold gObs; rw [if_neg h]
    rw [e]
    exact fPoly_pass links N r M

/-- Number of observable plaquettes in γ. -/
def cnt (S : List Z4Plaq) : List Z4Plaq → Nat
  | [] => 0
  | r :: γ => cnt S γ + (if r ∈ S then 1 else 0)

theorem prod_obs (S : List Z4Plaq) : ∀ γ : List Z4Plaq,
    l1 (prodPoly (gObs w0 M links N S) γ) ≤ Dc ^ cnt S γ * epsL ^ γ.length
  | [] => by show Q'.abs 1 + 0 ≤ Dc ^ 0 * epsL ^ 0; decide
  | r :: γ => by
    have ih := prod_obs S γ
    have hD : (0 : Q') ≤ Dc ^ cnt S γ * epsL ^ γ.length :=
      Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _) (Q'.pow_nonneg _ (by decide) _)
    refine Q'.le_trans' _ _ _ (l1_mul _ _) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (gObs_l1 M links N S r) (l1_nonneg _)) ?_)
    have hc0 : (0 : Q') ≤ (if r ∈ S then Dc * epsL else epsL) := by
      split <;> decide
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih hc0) (Q'.le_of_eqv ?_)
    show Q'.eqv _ (Dc ^ (cnt S γ + (if r ∈ S then 1 else 0)) * (epsL * epsL ^ γ.length))
    by_cases h : r ∈ S
    · rw [if_pos h, if_pos h]
      show Q'.eqv _ (Dc * Dc ^ cnt S γ * _)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3)) (V 0 * V 2 * (V 1 * V 3)) (by decide)
        (fun | 0 => Dc | 1 => epsL | 2 => Dc ^ cnt S γ | _ => epsL ^ γ.length)
    · rw [if_neg h, if_neg h]
      show Q'.eqv _ (Dc ^ cnt S γ * _)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 1 * (V 2 * V 3)) (V 2 * (V 1 * V 3)) (by decide)
        (fun | 1 => epsL | 2 => Dc ^ cnt S γ | _ => epsL ^ γ.length)

theorem cnt_nil (s : Z4Plaq) : ∀ γ : List Z4Plaq, s ∉ γ → cnt [s] γ = 0
  | [], _ => rfl
  | r :: γ, h => by
    have hr : r ∉ [s] := fun h' => h (List.mem_singleton.mp h' ▸ List.mem_cons_self)
    show cnt [s] γ + _ = 0
    rw [if_neg hr, cnt_nil s γ (fun h' => h (List.mem_cons_of_mem _ h'))]

theorem cnt_single (s : Z4Plaq) : ∀ γ : List Z4Plaq, γ.Nodup → cnt [s] γ ≤ 1
  | [], _ => Nat.zero_le _
  | r :: γ, h => by
    have hn := List.nodup_cons.mp h
    show cnt [s] γ + _ ≤ 1
    by_cases hr : r = s
    · subst hr
      rw [if_pos (List.mem_singleton.mpr rfl), cnt_nil r γ hn.1]; omega
    · rw [if_neg (fun h' => hr (List.mem_singleton.mp h'))]; exact cnt_single s γ hn.2

theorem cnt_cons (s : Z4Plaq) (S : List Z4Plaq) : ∀ γ : List Z4Plaq, cnt (s :: S) γ ≤ cnt [s] γ + cnt S γ
  | [] => Nat.zero_le _
  | r :: γ => by
    have ih := cnt_cons s S γ
    show cnt (s :: S) γ + (if r ∈ s :: S then 1 else 0) ≤
      (cnt [s] γ + (if r ∈ [s] then 1 else 0)) + (cnt S γ + (if r ∈ S then 1 else 0))
    have e : r ∈ s :: S ↔ r ∈ [s] ∨ r ∈ S := by
      rw [List.mem_cons, List.mem_singleton]
    by_cases h1 : r ∈ [s]
    · rw [if_pos (e.mpr (Or.inl h1)), if_pos h1]; split <;> omega
    · by_cases h2 : r ∈ S
      · rw [if_pos (e.mpr (Or.inr h2)), if_neg h1, if_pos h2]; omega
      · rw [if_neg (fun h3 => (e.mp h3).elim h1 h2), if_neg h1, if_neg h2]; omega

theorem cnt_empty : ∀ γ : List Z4Plaq, cnt [] γ = 0
  | [] => rfl
  | r :: γ => by
    show cnt [] γ + _ = 0
    rw [if_neg List.not_mem_nil, cnt_empty γ]

theorem cnt_le : ∀ (S γ : List Z4Plaq), γ.Nodup → cnt S γ ≤ S.length
  | [], γ, _ => by rw [cnt_empty]; exact Nat.le_refl _
  | s :: S, γ, h => by
    have := cnt_cons s S γ
    have := cnt_single s γ h
    have := cnt_le S γ h
    simp only [List.length_cons]; omega

/-- **Observable activity bound (PROVED):** `|z^S γ| ≤ D^{|S|} ε_L^{|γ|}` for nodup γ. -/
theorem zObs_bound (S γ : List Z4Plaq) (h : γ.Nodup) :
    Q'.abs (zObs w0 M links N S γ) ≤ Dc ^ S.length * epsL ^ γ.length :=
  Q'.le_trans' _ _ _ (haar_abs _ _) (Q'.le_trans' _ _ _ (prod_obs M links N S γ)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (YMGap.Continuum.SU2LinkGasBox.pow_mono_exp (by decide) (cnt_le S γ h))
      (Q'.pow_nonneg _ (by decide) _)))

theorem zObs_nil_eq : zObs w0 M links N [] =
    fun γ => quaternionHaar links.length (prodPoly (fun p => fPoly w0 links N p M) γ) :=
  funext fun γ => by unfold zObs; rw [gObs_nil]

/-! ## Rooted sums -/

theorem sumd_filter_le {β : Type} (f : β → Q') (hf : ∀ x, (0 : Q') ≤ f x) (c1 c2 : β → Bool)
    (h : ∀ x, c1 x = true → c2 x = true) : ∀ l : List β, sumd f (l.filter c1) ≤ sumd f (l.filter c2)
  | [] => Q'.le_refl' _
  | x :: l => by
    have ih := sumd_filter_le f hf c1 c2 h l
    cases h1 : c1 x
    · rw [List.filter_cons_of_neg (by simp [h1])]
      cases h2 : c2 x
      · rw [List.filter_cons_of_neg (by simp [h2])]; exact ih
      · rw [List.filter_cons_of_pos h2]
        have hh := Q'.add_le_add (hf x) (Q'.le_refl' (sumd f (l.filter c2)))
        rw [Q'.zero_add'] at hh
        exact Q'.le_trans' _ _ _ ih hh
    · rw [List.filter_cons_of_pos h1, List.filter_cons_of_pos (h x h1)]
      exact Q'.add_le_add (Q'.le_refl' _) ih

variable (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)

include hP hbox in
/-- **Rooted sum (PROVED):** `Σ_{a∈gas, p∈a} c^{|a|} ≤ (5/3)^{24·|[p]|}` for 0 ≤ c ≤ η. -/
theorem root_sum (c : Q') (hc0 : (0 : Q') ≤ c) (hc : c ≤ etaZ) (p : Z4Plaq) :
    sumd (fun a => c ^ S N a) ((gas N P).filter (hasP p)) ≤ ML N [p] := by
  refine Q'.le_trans' _ _ _ (sumd_filter_le _ (fun _ => Q'.pow_nonneg _ hc0 _) _ (incL N [p])
    (fun x hx => inc_of_mem N List.mem_cons_self (of_decide_eq_true hx)) _) ?_
  refine Q'.le_trans' _ _ _ (sumd_mono _ (fun a => etaZ ^ S N a) (fun a => pow_mono hc0 hc _) _) ?_
  exact Q'.le_trans' _ _ _ (sumd_le_prodm _ (fun _ => Q'.pow_nonneg _ (by decide) _) _)
    (YMGap.Continuum.SU2LinkGasBox.hgroupL N P hP hbox d0 [p])

theorem ML_one (p : Z4Plaq) : ML N [p] = five3 ^ 24 := rfl

/-! ## λ shift -/

theorem lam_shift (d : Nat) : ∀ s : Nat, lam ^ (d - s) ≤ lam ^ d * mu ^ s
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))
  | s + 1 => by
    have ih := lam_shift d s
    have hl : (0 : Q') ≤ lam ^ d * mu ^ s := Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
      (Q'.pow_nonneg _ (by decide) _)
    have re : (mu * (lam ^ d * mu ^ s)).eqv (lam ^ d * mu ^ (s + 1)) := by
      show Q'.eqv _ (lam ^ d * (mu * mu ^ s))
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * (V 0 * V 2)) (by decide)
        (fun | 0 => mu | 1 => lam ^ d | _ => mu ^ s)
    have hm : lam ^ d * mu ^ s ≤ mu * (lam ^ d * mu ^ s) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hl)
    by_cases h : d - s = 0
    · rw [show d - (s + 1) = d - s by omega]
      exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv re))
    · obtain ⟨k, hk⟩ : ∃ k, d - s = k + 1 := ⟨d - s - 1, by omega⟩
      rw [show d - (s + 1) = k by omega]
      rw [hk] at ih
      have e2 : (lam ^ k).eqv (mu * lam ^ (k + 1)) := by
        show Q'.eqv _ (mu * (lam * lam ^ k))
        refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)) (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (by decide : (1 : Q').eqv (mu * lam))) ?_)
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq (V 0 * V 1 * V 2) (V 0 * (V 1 * V 2)) (by decide)
          (fun | 0 => mu | 1 => lam | _ => lam ^ k)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ih (by decide)) (Q'.le_of_eqv re))

theorem one_le_shift (d s : Nat) (h : d ≤ s) : (1 : Q') ≤ lam ^ d * mu ^ s := by
  have := lam_shift d s
  rw [show d - s = 0 by omega] at this
  exact this

/-! ## KP environment for the w₀ activity -/

include hP hbox in
theorem env_w0 (l : List (List Z4Plaq)) (hl : Good (gas N P) l) (a : List Z4Plaq) :
    (0 : Q') < Xi (zObs w0 M links N []) (incL N) l ∧
    Xi (zObs w0 M links N []) (incL N) (l.filter (cpt (incL N) a)) ≤
      ML N a * Xi (zObs w0 M links N []) (incL N) l := by
  rw [zObs_nil_eq]
  have hz : ∀ x, x ∈ gas N P → Q'.abs (quaternionHaar links.length
      (prodPoly (fun p => fPoly w0 links N p M) x)) ≤ epsL ^ S N x := fun x hx => by
    rw [show S N x = x.length from sz_of_ne (BL := torusChain N) x
      ((YMGap.Continuum.SU2LinkGasBox.linkBox N P hP hbox).size_ok x hx).1]
    exact activity_bound links.length links N M x
  have sub : ∀ x, x ∈ l → x ∈ gas N P := hl.2
  have h1 := envL_pos N P hP hbox epsL (by decide) kp_pass _ hz l hl
  have h2 := envL_M N P hP hbox epsL (by decide) kp_pass _ hz l a hl
  rw [Xi_zc N P _ l sub] at h1 h2
  rw [Xi_zc N P _ _ (fun x hx => sub x (List.mem_filter.mp hx).1)] at h2
  exact ⟨h1, h2⟩

end YMGap.Continuum.SU2ObsActivity
