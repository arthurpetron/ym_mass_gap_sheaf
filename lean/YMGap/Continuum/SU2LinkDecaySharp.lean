/-
# Parallel of the Prover's `SU2LinkDecay` with `Kc = (3/2)^24` (STRONG COUPLING ONLY)

ADDITIVE copy (no edits to `SU2LinkDecay`); it uses `SU2LinkKPSharp`. Here `link_decay` is the generic theorem
with the activity hypothesis `|z γ| ≤ ε^{|γ|}`. It is also true for U(1), so it is NOT gap evidence.
-/

import YMGap.Continuum.SU2LinkKPSharp
import YMGap.Continuum.Z4PlaqMetric

namespace YMGap.Continuum.SU2LinkDecaySharp

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
open YMGap.Continuum.PolymerDecayZ4 (pow_le_self sumd_le_prodm sumd_mono sumd_mul)
open YMGap.Continuum.PolymerLatticeDecay
open YMGap.Continuum.SU2PolymerIdentity (incL gas polyPartition_eq_Xi)
open YMGap.Continuum.SU2LinkGasGeometry (incL_symm incL_iff adjT adj_symm)
open YMGap.Continuum.SU2LinkGasBox
open YMGap.Continuum.SU2LinkKPSharp
open YMGap.Continuum.SU2LinkGroupSharp (three2 hgroupL_sharp)
open YMGap.Continuum.HeatKernelPolymerActivityR1 (pow_add' pow_anti)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly fPoly)
open YMGap.Continuum.SU2PlaqSupport
open YMGap.Continuum.Z4PlaqMetric (torusMetric)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

abbrev etaD : Q' := lam * lam * etaZ

theorem lam2_shift (a s r : Nat) (h : r ≤ a + s + s) :
    lam ^ a * etaD ^ s ≤ lam ^ r * etaZ ^ s := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have e : (lam ^ a * etaD ^ s).eqv (lam ^ (a + s + s) * etaZ ^ s) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (mul_pow' (lam * lam) etaZ s))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (mul_pow' lam lam s)))) ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (pow_add' lam (a + s) s)
        (Q'.mul_eqv_congr_right _ _ _ (pow_add' lam a s)))))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 1 * V 2)) (V 0 * V 1 * V 1 * V 2) (by decide)
      (fun | 0 => lam ^ a | 1 => lam ^ s | _ => etaZ ^ s)
  rw [hk] at e
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e) (Q'.mul_le_mul_of_nonneg_right _ _ _
    (pow_anti (by decide) (by decide) r k) (Q'.pow_nonneg _ (by decide) _))

theorem lin_le {a b : Q'} (h : a ≤ b) : a ≤ 1 * b :=
  Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))

section Decay
variable (N : Nat) (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
variable (ε : Q') (hε0 : (0 : Q') ≤ ε) (hε1 : ε * Kc ≤ 1)
variable (hS1 : ε * Kc * Kc * (1 + etaZ) ≤ etaD)
variable (hS2 : ε * Kc * ((1 + etaZ) * ((1 + ε * Kc) + (1 + ε * Kc))) ≤ etaD)

abbrev wL (x : List Z4Plaq) : Nat := 2 * S N x

theorem eM (x : List Z4Plaq) : (eL N ε x * ML N x).eqv ((ε * Kc) ^ S N x) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (pow_mul_eqv three2 24 (S N x))) (mul_pow' _ _ _)

include hε0 hε1 hS2 in
theorem baseL (y g : List Z4Plaq) :
    CS (incL N) (gas N P) (eL N ε) (ML N) (mL N) y 0 g ≤ etaD ^ S N g := by
  have ha : (0 : Q') ≤ ε * Kc := Q'.mul_nonneg _ _ hε0 (Q'.pow_nonneg _ (by decide) _)
  have hy : eL N ε y * ML N y ≤ ε * Kc := Q'.le_trans' _ _ _ (Q'.le_of_eqv (eM N ε y))
    (pow_le_self ha hε1 _ (sz_pos (BL := torusChain N) y))
  have hB : (1 + eL N ε y * ML N y) + (1 + eL N ε y * ML N y) ≤ (1 + ε * Kc) + (1 + ε * Kc) :=
    Q'.add_le_add (Q'.add_le_add (Q'.le_refl' 1) hy) (Q'.add_le_add (Q'.le_refl' 1) hy)
  have hs := sz_pos (BL := torusChain N) g
  have hη := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) _ hs
  have hB0 : (0 : Q') ≤ (1 + ε * Kc) + (1 + ε * Kc) :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (by decide) ha) (Q'.zero_le_add _ _ (by decide) ha)
  have hab : ε * Kc ≤ etaD := Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (1 + etaZ) * (1 + 1))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add (Q'.add_le_self_of_nonneg _ _ ha)
          (Q'.add_le_self_of_nonneg _ _ ha)) (by decide))) ha)) hS2
  show eL N ε g * ML N g * mL N g * _ ≤ _
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hB
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hε0 _) (Q'.pow_nonneg _ (by decide) _))
      (mL_nn N g))) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add (Q'.le_refl' 1) hη)
      (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hε0 _) (Q'.pow_nonneg _ (by decide) _))) hB0) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (geo_le ha hab hS2 _ hs)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ (eM N ε g))) ?_
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 1 * V 2) (V 0 * (V 1 * V 2)) (by decide)
    (fun | 0 => (ε * Kc) ^ S N g | 1 => 1 + etaZ | _ => (1 + ε * Kc) + (1 + ε * Kc))

include hP hbox hε0 hε1 hS1 hS2 in
theorem CSWL_le (y : List Z4Plaq) : ∀ (f r : Nat) (g : List Z4Plaq), r ≤ f →
    CSW (incL N) (gas N P) (eL N ε) (ML N) (mL N) (wL N) y f r g ≤ lam ^ r * etaD ^ S N g
  | 0, 0, g, _ => lin_le (baseL N P ε hε0 hε1 hS2 y g)
  | 0, _ + 1, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, 0, g, _ => lin_le (baseL N P ε hε0 hε1 hS2 y g)
  | f + 1, r + 1, g, hr => by
    let L := (gas N P).filter (incL N g)
    have ha : (0 : Q') ≤ eL N ε g * ML N g * mL N g :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hε0 _) (Q'.pow_nonneg _ (by decide) _)) (mL_nn N g)
    have hl0 : (0 : Q') ≤ lam ^ (r + 1) := Q'.pow_nonneg _ (by decide) _
    have hS : sumd (fun h => CSW (incL N) (gas N P) (eL N ε) (ML N) (mL N) (wL N) y f
        (r + 1 - wL N h) h) L ≤ lam ^ (r + 1) * ML N g := by
      refine Q'.le_trans' _ _ _ (sumd_mono _ (fun h => lam ^ (r + 1) * etaZ ^ S N h) (fun h =>
        Q'.le_trans' _ _ _ (CSWL_le y f (r + 1 - wL N h) h (by have : 1 ≤ S N h := sz_pos (BL := torusChain N) h; unfold wL; omega))
          (lam2_shift _ _ _ (by unfold wL; omega))) L) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumd_mul _ (fun h => etaZ ^ S N h) L)) ?_
      refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hl0
      exact Q'.le_trans' _ _ _ (sumd_le_prodm (fun h => etaZ ^ S N h)
        (fun h => Q'.pow_nonneg _ (by decide) _) L) (hgroupL_sharp N P hP hbox d0 g)
    show eL N ε g * ML N g * mL N g * sumd _ L ≤ lam ^ (r + 1) * etaD ^ S N g
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hS ha) ?_
    have hK0 : (0 : Q') ≤ ε * Kc * Kc := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hε0
      (Q'.pow_nonneg _ (by decide) _)) (Q'.pow_nonneg _ (by decide) _)
    have hab : ε * Kc * Kc ≤ etaD := Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ _ (by decide)) hK0)) hS1
    have hs := sz_pos (BL := torusChain N) g
    have hη := pow_le_self (by decide : (0 : Q') ≤ etaZ) (by decide) _ hs
    have e2 : (eL N ε g * ML N g * ML N g).eqv ((ε * Kc * Kc) ^ S N g) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (eM N ε g)) (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (pow_mul_eqv three2 24 (S N g))) (mul_pow' _ _ _))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show (eL N ε g * ML N g * mL N g * (lam ^ (r + 1) * ML N g)).eqv
        (lam ^ (r + 1) * ((eL N ε g * ML N g * ML N g) * mL N g)) from by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * (V 3 * V 1)) (V 3 * (V 0 * V 1 * V 1 * V 2))
        (by decide) (fun | 0 => eL N ε g | 1 => ML N g | 2 => mL N g | _ => lam ^ (r + 1)))) ?_
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hl0
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ e2)) ?_
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add (Q'.le_refl' 1) hη)
      (Q'.pow_nonneg _ hK0 _)) (geo_le hK0 hab hS1 _ hs)

/-! ## Separation -/

include hP hbox in
theorem in_box {x : List Z4Plaq} (hx : x ∈ gas N P) {p : Z4Plaq} (hp : p ∈ x) : p ∈ torusPlaquettes N :=
  hbox p ((gas_inv N P hP x hx).2.2 p hp)

include hP hbox in
theorem sep_incL (y g : List Z4Plaq) (hy : y ∈ gas N P) (hg : g ∈ gas N P) (R : Nat)
    (hs : sepL (torusMetric N) y g R) (hR : 2 ≤ R) : incL N y g = false := by
  cases hb : incL N y g with
  | false => rfl
  | true =>
    obtain ⟨p, hp, q, hq, hpq⟩ := (incL_iff N y g).mp hb
    obtain ⟨A⟩ := adjT N (in_box N P hP hbox hy hp) (in_box N P hP hbox hg hq) hpq
    have h1 := (torusMetric N).adj p q A
    have h2 := hs p hp q hq
    omega

include hP hbox in
theorem sep_stepL (y g h : List Z4Plaq) (hg : g ∈ gas N P) (R : Nat)
    (hs : sepL (torusMetric N) y g R) (hh : h ∈ gas N P) (hgh : incL N g h = true) :
    ∀ p, p ∈ y → ∀ q, q ∈ h → R ≤ (torusMetric N).ld p q + S N h := by
  obtain ⟨c, hc, c', hc', hcc⟩ := (incL_iff N g h).mp hgh
  obtain ⟨A⟩ := adjT N (in_box N P hP hbox hh hc') (in_box N P hP hbox hg hc)
    (by rw [adj_symm]; exact hcc)
  obtain ⟨cn⟩ := (linkBox N P hP hbox).conn h hh
  intro p hp q hq
  have h1 := hs p hp c hc
  have h2 := (torusMetric N).tri p q c
  have h3 := (torusMetric N).tri q c' c
  have h4 := (torusMetric N).adj c' c A
  have h5 := diam_le (torusMetric N) h q c' (cn q c' hq hc') hq
  have h7 : (torusMetric N).ld q c' + 1 ≤ S N h := by
    have e := sz_of_ne (BL := torusChain N) h ((linkBox N P hP hbox).size_ok h hh).1
    show _ ≤ sz (BL := torusChain N) h
    rw [e]; exact h5
  omega

include hP hbox in
theorem sepL_far (y : List Z4Plaq) (hy : y ∈ gas N P) : ∀ (f R : Nat) (g : List Z4Plaq),
    g ∈ gas N P → sepL (torusMetric N) y g (R + 1) → farW (incL N) (gas N P) (wL N) y f R g
  | 0, _, _, _, _ => trivial
  | _ + 1, 0, _, _, _ => trivial
  | f + 1, r + 1, g, hg, hs => ⟨sep_incL N P hP hbox y g hy hg _ hs (by omega), fun h hh hi => by
      have h' := sep_stepL N P hP hbox y g h hg _ hs hh hi
      have : 1 ≤ S N h := sz_pos (BL := torusChain N) h
      cases hR : r + 1 - wL N h with
      | zero => cases f <;> trivial
      | succ R' => exact sepL_far y hy f (R' + 1) h hh (fun p hp q hq => by
          have h2 := h' p hp q hq; unfold wL at hR; revert h2 hR; generalize S N h = s at *
          intro h2 hR; omega)⟩

/-! ## Decay -/

include hP hbox hε0 hε1 hS1 hS2 in
theorem link_decay (hK : ε * Kc * (1 + etaZ) ≤ etaZ) (z : List Z4Plaq → Q')
    (hz : ∀ x, x ∈ gas N P → Q'.abs (z x) ≤ ε ^ S N x)
    (y g : List Z4Plaq) (l : List (List Z4Plaq)) (R : Nat)
    (hsep : sepL (torusMetric N) y g (R + 1)) (hG : Good (gas N P) (y :: g :: l)) :
    Q'.abs (U z (incL N) y g l) ≤
      (lam ^ R * etaD ^ S N g) * (Xi z (incL N) l * Xi z (incL N) (g :: l)) := by
  let zz := zc N P z
  have hy := hG.2 y List.mem_cons_self
  have hg := hG.2 g (List.mem_cons_of_mem _ List.mem_cons_self)
  have hcb := chainW_bound zz (incL N) (incL_symm N) (gas N P) (eL N ε) (ML N) (mL N)
    (envL_pos N P hP hbox ε hε0 hK z hz) (fun l a hl => envL_M N P hP hbox ε hε0 hK z hz l a hl)
    (envL_m N P hP hbox ε hε0 hK z hz) (envL_z N P ε hε0 z hz)
    (eL_nn N ε hε0) (fun _ => Q'.pow_nonneg _ (by decide) _) (mL_nn N) (wL N) y R R g l
    (sepL_far N P hP hbox y hy R R g hg hsep) hG
  have sub : ∀ k : List (List Z4Plaq), (∀ x, x ∈ k → x ∈ y :: g :: l) → ∀ x, x ∈ k → x ∈ gas N P :=
    fun k hk x hx => hG.2 x (hk x hx)
  have hU : U zz (incL N) y g l = U z (incL N) y g l := by
    unfold U
    rw [Xi_zc N P z _ (sub _ (fun _ h => h)), Xi_zc N P z l (sub _ (fun _ h =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      Xi_zc N P z (y :: l) (sub _ (fun x h => by
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      Xi_zc N P z (g :: l) (sub _ (fun _ h => List.mem_cons_of_mem _ h))]
  have hl := good_sub (List.sublist_cons_self g l) (good_sub (List.sublist_cons_self y _) hG)
  have hgl := good_sub (List.sublist_cons_self y _) hG
  rw [hU, Xi_zc N P z l (fun x h => hl.2 x h), Xi_zc N P z (g :: l) (fun x h => hgl.2 x h)] at hcb
  have hP0 : (0 : Q') ≤ Xi z (incL N) l * Xi z (incL N) (g :: l) := by
    have a := envL_pos N P hP hbox ε hε0 hK z hz l hl
    have b := envL_pos N P hP hbox ε hε0 hK z hz (g :: l) hgl
    rw [Xi_zc N P z l (fun x h => hl.2 x h)] at a
    rw [Xi_zc N P z (g :: l) (fun x h => hgl.2 x h)] at b
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt a) (Q'.le_of_lt b)
  exact Q'.le_trans' _ _ _ hcb (Q'.mul_le_mul_of_nonneg_right _ _ _
    (CSWL_le N P hP hbox ε hε0 hε1 hS1 hS2 y R R g (Nat.le_refl R)) hP0)

end Decay

end YMGap.Continuum.SU2LinkDecaySharp

#print axioms YMGap.Continuum.SU2LinkDecaySharp.link_decay
