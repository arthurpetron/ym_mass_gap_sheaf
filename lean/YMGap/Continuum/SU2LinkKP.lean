/-
# R1 commit 9: Kotecký–Preiss for the link-compatibility gas, with the activity as a hypothesis

ADDITIVE.  **GROUP-BLIND PLUMBING.**  The gas is `gas N P` with `incL`.  `P` is duplicate-free and
lies in the torus box.  The activity enters only through the hypothesis
`hz : ∀ γ ∈ gas N P, |z γ| ≤ ε^{|γ|}`.  Either the ℓ¹ bound (`activity_bound`, w₀ = 10⁻⁸) or
Realizer's `polymer_activity_abs_le` can supply it.

Constants: `η = 1/2500`, `K = (5/3)^24` per plaquette (`hgroupL`), `M_a = K^{|a|}`, `m_a = 1+η^{|a|}`.
* `kp_scalar`: `(1+η^s)(εK)^s ≤ η^s` whenever `εK(1+η) ≤ η`.
* `Xi_congr`: `Ξ` depends only on the activities of list members.
* `envL_pos`, `envL_M`, `envL_m`, `envL_z`: the `chain_bound` environment for the truncated
  activity `zc` (equal to `z` on `gas N P`, zero elsewhere).
-/

import YMGap.Continuum.SU2LinkGasBox

namespace YMGap.Continuum.SU2LinkKP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay
open YMGap.Continuum.PolymerDecayZ4 (prodm_sub_le pos_of_one_le_mul pow_le_self)
open YMGap.Continuum.PolymerLatticeDecay (geo_le)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkGasGeometry (incL_symm)
open YMGap.Continuum.SU2LinkGasBox

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-! ## Scalars -/

def Kc : Q' := five3 ^ 24

theorem pow_mul_eqv (c : Q') (k : Nat) : ∀ s : Nat, (c ^ (k * s)).eqv ((c ^ k) ^ s)
  | 0 => Q'.eqv_refl _
  | s + 1 => by
    rw [Nat.mul_succ]
    refine Q'.eqv_trans _ _ _ (YMGap.Continuum.HeatKernelPolymerActivityR1.pow_add' c _ _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (pow_mul_eqv c k s)) ?_
    exact Q'.mul_comm_eqv _ _

theorem kp_scalar {a : Q'} (ha : (0 : Q') ≤ a) (h : a * (1 + etaZ) ≤ etaZ) (s : Nat) (hs : 1 ≤ s) :
    (1 + etaZ ^ s) * a ^ s ≤ etaZ ^ s := by
  have hab : a ≤ etaZ := Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv a)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ _ (by decide)) ha)) h
  have hη := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) s hs
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.add_le_add (Q'.le_refl' 1) hη) (Q'.pow_nonneg _ ha _)) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) (geo_le ha hab h s hs)

/-! ## Ξ congruence -/

theorem Xi_congr {α : Type} (z z' : α → Q') (inc : α → α → Bool) : ∀ (n : Nat) (l : List α),
    l.length ≤ n → (∀ a, a ∈ l → z a = z' a) → Xi z inc l = Xi z' inc l
  | _, [], _, _ => by rw [Xi_nil, Xi_nil]
  | 0, _ :: _, h, _ => absurd h (by simp)
  | n + 1, a :: l, h, hz => by
    have hl : l.length ≤ n := by simp only [List.length_cons] at h; omega
    rw [Xi_cons, Xi_cons, hz a List.mem_cons_self,
      Xi_congr z z' inc n l hl (fun b hb => hz b (List.mem_cons_of_mem _ hb)),
      Xi_congr z z' inc n _ (Nat.le_trans (List.length_filter_le _ _) hl)
        (fun b hb => hz b (List.mem_cons_of_mem _ (List.mem_filter.mp hb).1))]

/-! ## The environment -/

section Env
variable (N : Nat) (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
variable (ε : Q') (hε0 : (0 : Q') ≤ ε) (hK : ε * Kc * (1 + etaZ) ≤ etaZ)

abbrev S (x : List Z4Plaq) : Nat := sz (BL := torusChain N) x
abbrev eL (x : List Z4Plaq) : Q' := ε ^ S N x
abbrev mL (x : List Z4Plaq) : Q' := 1 + etaZ ^ S N x
abbrev ML (x : List Z4Plaq) : Q' := five3 ^ (24 * S N x)

def d0 : Z4Plaq := ((0, 0, 0, 0), .p01)

theorem mL_ge (x : List Z4Plaq) : (1 : Q') ≤ mL N x :=
  Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
theorem mL_nn (x : List Z4Plaq) : (0 : Q') ≤ mL N x := Q'.le_trans' _ _ _ (by decide) (mL_ge N x)

include hP hbox in
theorem hgroupG' (l : List (List Z4Plaq)) (hl : Good (gas N P) l) (a : List Z4Plaq) :
    prodm (mL N) (l.filter (incL N a)) ≤ ML N a :=
  Q'.le_trans' _ _ _ (prodm_sub_le _ (mL_ge N) _ _ (hl.1.sublist List.filter_sublist)
    (fun x hx => by
      have h := List.mem_filter.mp hx
      exact List.mem_filter.mpr ⟨hl.2 x h.1, h.2⟩)) (hgroupL N P hP hbox d0 a)

include hP hbox hε0 hK in
theorem condL (l : List (List Z4Plaq)) (hl : Good (gas N P) l) :
    Cond (incL N) (eL N ε) (mL N) l ∧ Cond2 (incL N) (eL N ε) (mL N) l := by
  have hKc0 : (0 : Q') ≤ Kc := Q'.pow_nonneg _ (by decide) _
  have ha : (0 : Q') ≤ ε * Kc := Q'.mul_nonneg _ _ hε0 hKc0
  have core : ∀ a, eL N ε a * prodm (mL N) (l.filter (incL N a)) ≤ (ε * Kc) ^ S N a := fun a =>
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hgroupG' N P hP hbox l hl a)
      (Q'.pow_nonneg _ hε0 _)) (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (pow_mul_eqv five3 24 (S N a))) (mul_pow' _ _ _)))
  have hsc := fun a => kp_scalar ha hK (S N a) (sz_pos (BL := torusChain N) a)
  constructor
  · intro a
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (core a) (mL_nn N a)) ?_
    refine Q'.le_trans' _ _ _ (hsc a) (Q'.le_of_eqv ?_)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0) (PolyExpr.const 1 + V 0 + -PolyExpr.const 1)
      (by decide) (fun _ => etaZ ^ S N a)
  · intro a
    refine Q'.le_trans' _ _ _ (core a) ?_
    have hx : (0 : Q') ≤ (ε * Kc) ^ S N a := Q'.pow_nonneg _ ha _
    refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (mL_ge N a) hx)) (Q'.le_trans' _ _ _ (hsc a) ?_)
    exact Q'.le_trans' _ _ _ (pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) _ (sz_pos (BL := torusChain N) a))
      (by decide)

variable (z : List Z4Plaq → Q')
variable (hz : ∀ x, x ∈ gas N P → Q'.abs (z x) ≤ ε ^ S N x)

/-- The activity truncated to the gas (equal to `z` on every gas polymer). -/
def zc (x : List Z4Plaq) : Q' := if x ∈ gas N P then z x else 0

include hz hε0 in
theorem envL_z (a : List Z4Plaq) : Q'.abs (zc N P z a) ≤ eL N ε a := by
  unfold zc
  split
  · rename_i h; exact hz a h
  · exact Q'.le_trans' _ _ _ (show Q'.abs 0 ≤ 0 from by decide) (Q'.pow_nonneg _ hε0 _)

include hz hε0 in
theorem envL_z1 (a : List Z4Plaq) : (0 : Q') ≤ zc N P z a + eL N ε a := by
  have h := Q'.le_trans' _ _ _ (Q'.neg_le_abs _) (envL_z N P ε hε0 z hz a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.add_le_add_left _ _ _ h)
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (PolyExpr.const 0) (V 0 + -(V 0)) (by decide)
    (fun _ => zc N P z a)

theorem eL_nn (hε0 : (0 : Q') ≤ ε) (a : List Z4Plaq) : (0 : Q') ≤ eL N ε a := Q'.pow_nonneg _ hε0 _

include hP hbox hε0 hK hz in
theorem envL_pos (l : List (List Z4Plaq)) (hl : Good (gas N P) l) :
    (0 : Q') < Xi (zc N P z) (incL N) l := by
  have hc := condL N P hP hbox ε hε0 hK l hl
  exact pos_of_one_le_mul (kpw_main (zc N P z) (incL N) _ _ (incL_symm N) (mL_ge N)
      (eL_nn N ε hε0) (envL_z1 N P ε hε0 z hz) l hc.1 hc.2).1
    (kpw_lower (zc N P z) (incL N) _ _ (incL_symm N) (mL_ge N) (eL_nn N ε hε0)
      (envL_z1 N P ε hε0 z hz) l hc.1 hc.2)

include hP hbox hε0 hK hz in
theorem envL_M (l : List (List Z4Plaq)) (a : List Z4Plaq) (hl : Good (gas N P) l) :
    Xi (zc N P z) (incL N) (l.filter (cpt (incL N) a)) ≤ ML N a * Xi (zc N P z) (incL N) l := by
  have hc := condL N P hP hbox ε hε0 hK l hl
  have h0 := (kpw_main (zc N P z) (incL N) _ _ (incL_symm N) (mL_ge N) (eL_nn N ε hε0)
    (envL_z1 N P ε hε0 z hz) l hc.1 hc.2).1
  have hf := kpw_filter (zc N P z) (incL N) _ _ (incL_symm N) (mL_ge N) (eL_nn N ε hε0)
    (envL_z1 N P ε hε0 z hz) l hc.1 hc.2 (cpt (incL N) a)
  have hfe : l.filter (fun x => !cpt (incL N) a x) = l.filter (incL N a) :=
    filter_congr' _ _ (fun x => by unfold cpt; cases incL N a x <;> rfl) l
  rw [hfe] at hf
  exact Q'.le_trans' _ _ _ hf
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (hgroupG' N P hP hbox l hl a) h0)

include hP hbox hε0 hK hz in
theorem envL_m (x : List Z4Plaq) (l : List (List Z4Plaq)) (hl : Good (gas N P) (x :: l)) :
    Xi (zc N P z) (incL N) l ≤ mL N x * Xi (zc N P z) (incL N) (x :: l) := by
  have hc := condL N P hP hbox ε hε0 hK (x :: l) hl
  exact (kpw_main (zc N P z) (incL N) _ _ (incL_symm N) (mL_ge N) (eL_nn N ε hε0)
    (envL_z1 N P ε hε0 z hz) (x :: l) hc.1 hc.2).2 [] x l rfl

theorem Xi_zc (l : List (List Z4Plaq)) (hl : ∀ x, x ∈ l → x ∈ gas N P) :
    Xi (zc N P z) (incL N) l = Xi z (incL N) l :=
  Xi_congr _ _ _ l.length l (Nat.le_refl _) fun a ha => by
    unfold zc; rw [if_pos (hl a ha)]

end Env

/-! ## Pass at ε_L = 10⁻¹⁵ -/

theorem kp_pass : YMGap.Continuum.SU2HaarL1Activity.epsL * Kc * (1 + etaZ) ≤ etaZ := by decide

end YMGap.Continuum.SU2LinkKP
