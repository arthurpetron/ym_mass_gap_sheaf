/-
# R1 commit 19: truncated χ₁ correlator decay at w₀ (torus, uniform in N and M)

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson; also true for
U(1), not gap evidence.  The Wilson counterpart of the polymer decay is Realizer's
`SU2WilsonLinkDecay`; torus RP is Realizer's (`SU2TorusRPWilson`).

* `boundA` and `boundB`: the double-root sum (via `kernel_bound` and `root_sum`) and the
  both-point polymers (each has size ≥ d+1).
* `trunc_decay`: `|Zpq·Z − Zp·Zq| ≤ λ^d · (C · Z²)`, with λ = 6/7 and d = ld(q,p) (the torus ℓ∞
  plaquette distance).  The constant C = `Ctr` (≈ 2.4·10⁴⁶) is explicit and uniform in N, M and P.
-/

import YMGap.Continuum.SU2PairKernel

namespace YMGap.Continuum.SU2TruncDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.SignedPolymerKP (Xi cpt)
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay (Good good_sub)
open YMGap.Continuum.PolymerLatticeDecay (lam sepL diam_le)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkGasGeometry (incL_symm)
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.SU2HaarL1Activity (w0 epsL)
open YMGap.Continuum.SU2ObsInsertion
open YMGap.Continuum.SU2ObsRoot (hasP inc_of_mem)
open YMGap.Continuum.SU2TwoRoot (K sumd_mulL zObs_agree two_root_obs)
open YMGap.Continuum.PolymerRemovalChain (T)
open YMGap.Continuum.SU2LinkKP (S ML Xi_congr)
open YMGap.Continuum.SU2ObsActivity
open YMGap.Continuum.SU2PairKernel

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable (M : Nat) (links : List Z4Link) (N : Nat) (P : List Z4Plaq) (hP : P.Nodup)
  (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)

local notation "zz" => zObs w0 M links N []
local notation "XX" => Xi (zObs w0 M links N []) (incL N) (gas N P)

/-! ## Constants and sums -/

def D1 : Q' := Dc ^ 1 + Dc ^ 0
def D2 : Q' := Dc ^ 2 + Dc ^ 1 + (Dc ^ 1 + Dc ^ 0)
def K5 : Q' := five3 ^ 24
/-- The correlator constant `C = 2·D1²·K² + D2·K` with K = (5/3)^24 (≈ 2.4·10⁴⁶). -/
def Ctr : Q' := (D1 * D1 * K5 + D1 * D1 * K5) * K5 + D2 * K5

theorem abs_sumd_mem {β : Type} (f g : β → Q') : ∀ l : List β, (∀ x, x ∈ l → Q'.abs (f x) ≤ g x) →
    Q'.abs (sumd f l) ≤ sumd g l
  | [], _ => by show Q'.abs 0 ≤ 0; decide
  | x :: l, h => Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add (h x List.mem_cons_self)
      (abs_sumd_mem f g l fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pw1 (s : Nat) : (epsL ^ s * mu ^ s * five3 ^ (24 * s)).eqv ((epsL * mu * five3 ^ 24) ^ s) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (YMGap.Continuum.SU2LinkKP.pow_mul_eqv five3 24 s))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (mul_pow' _ _ s)) (mul_pow' _ _ s))

theorem pw2 (s : Nat) : (epsL ^ s * mu ^ s * five3 ^ (24 * s) * five3 ^ (24 * s)).eqv
    ((epsL * mu * five3 ^ 24 * five3 ^ 24) ^ s) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (YMGap.Continuum.SU2LinkKP.pow_mul_eqv five3 24 s))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (pw1 s)) (mul_pow' _ _ s))

include hP hbox in
theorem RS1 (p : Z4Plaq) :
    sumd (fun a => epsL ^ S N a * mu ^ S N a * ML N a) ((gas N P).filter (hasP p)) ≤ ML N [p] :=
  Q'.le_trans' _ _ _ (YMGap.Continuum.PolymerDecayZ4.sumd_mono _ _ (fun a => Q'.le_of_eqv (pw1 (S N a))) _)
    (root_sum N P hP hbox _ (by decide) (by decide) p)

include hP hbox in
theorem RS2 (p : Z4Plaq) :
    sumd (fun a => epsL ^ S N a * mu ^ S N a * ML N a * ML N a) ((gas N P).filter (hasP p)) ≤ ML N [p] :=
  Q'.le_trans' _ _ _ (YMGap.Continuum.PolymerDecayZ4.sumd_mono _ _ (fun a => Q'.le_of_eqv (pw2 (S N a))) _)
    (root_sum N P hP hbox _ (by decide) (by decide) p)

include hP hbox in
theorem dif (S1 S2 : List Z4Plaq) (a : List Z4Plaq) (ha : a ∈ gas N P) :
    Q'.abs (zObs w0 M links N S1 a + -zObs w0 M links N S2 a) ≤
      (Dc ^ S1.length + Dc ^ S2.length) * epsL ^ S N a := by
  have nd := (YMGap.Continuum.SU2LinkGasBox.gas_inv N P hP a ha).2.1
  rw [hlen N P hP hbox a ha]
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.le_trans' _ _ _ (Q'.add_le_add
    (zObs_bound M links N S1 a nd) (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
      (zObs_bound M links N S2 a nd))) (Q'.le_of_eqv ?_))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * V 2 + V 1 * V 2) ((V 0 + V 1) * V 2) (by decide)
    (fun | 0 => Dc ^ S1.length | 1 => Dc ^ S2.length | _ => epsL ^ a.length)

/-! ## The two pieces -/

include hP hbox in
theorem boundA (p q : Z4Plaq) :
    Q'.abs (sumd (fun a => (zObs w0 M links N [p] a + -zz a) *
        sumd (fun b => (zObs w0 M links N [q] b + -zz b) * K N zz (gas N P) a b) ((gas N P).filter (hasP q)))
        ((gas N P).filter (hasP p))) ≤
      lam ^ (torusMetric N).ld q p * (XX * XX) * ((D1 * D1 * ML N [q] + D1 * D1 * ML N [q]) * ML N [p]) := by
  let Ld := lam ^ (torusMetric N).ld q p
  let X2 := XX * XX
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have hX0 : (0 : Q') ≤ XX := Q'.le_of_lt (env_w0 M links N P hP hbox (gas N P) hG [p]).1
  have hX2 : (0 : Q') ≤ X2 := Q'.mul_nonneg _ _ hX0 hX0
  have hLd : (0 : Q') ≤ Ld := Q'.pow_nonneg _ (by decide) _
  have hM0 : ∀ x, (0 : Q') ≤ ML N x := fun x => Q'.le_trans' _ _ _ (by decide) (ML_ge N x)
  have hD1 : (0 : Q') ≤ D1 := by decide
  have hE : ∀ s, (0 : Q') ≤ epsL ^ s := fun _ => Q'.pow_nonneg _ (by decide) _
  have hMu : ∀ s, (0 : Q') ≤ mu ^ s := fun _ => Q'.pow_nonneg _ (by decide) _
  let F := fun a : List Z4Plaq => Ld * X2 * (mu ^ S N a * ML N a * ML N a)
  let g := fun b : List Z4Plaq => D1 * (epsL ^ S N b * mu ^ S N b * ML N b)
  have hF0 : ∀ a, (0 : Q') ≤ F a + F a := fun a => Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hMu _) (hM0 a)) (hM0 a)))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hMu _) (hM0 a)) (hM0 a)))
  have inner : ∀ a, a ∈ (gas N P).filter (hasP p) →
      Q'.abs (sumd (fun b => (zObs w0 M links N [q] b + -zz b) * K N zz (gas N P) a b)
        ((gas N P).filter (hasP q))) ≤ (F a + F a) * (D1 * ML N [q]) := by
    intro a ha
    have ham := List.mem_filter.mp ha
    refine Q'.le_trans' _ _ _ (abs_sumd_mem _ (fun b => (F a + F a) * g b) _ fun b hb => ?_) ?_
    · have hbm := List.mem_filter.mp hb
      have hk := kernel_bound M links N P hP hbox p q a b ham.1 hbm.1 (of_decide_eq_true ham.2)
        (of_decide_eq_true hbm.2)
      refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
        (YMGap.Constructive.Q'.mul_le_mul_of_nonneg (dif M links N P hP hbox [q] [] b hbm.1) hk
          (Q'.mul_nonneg _ _ hD1 (hE _)) (Q'.abs_nonneg _)) (Q'.le_of_eqv ?_))
      show Q'.eqv _ ((Ld * X2 * (mu ^ S N a * ML N a * ML N a) + Ld * X2 * (mu ^ S N a * ML N a * ML N a)) *
        (D1 * (epsL ^ S N b * mu ^ S N b * ML N b)))
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq
        (V 0 * V 1 * ((V 2 * V 3 * V 4) * (V 5 * V 6 * V 6) * V 7 + (V 2 * V 3 * V 4) * (V 5 * V 6 * V 6) * V 7))
        ((V 2 * V 7 * (V 3 * V 6 * V 6) + V 2 * V 7 * (V 3 * V 6 * V 6)) * (V 0 * (V 1 * V 4 * V 5)))
        (by decide)
        (fun | 0 => D1 | 1 => epsL ^ S N b | 2 => Ld | 3 => mu ^ S N a | 4 => mu ^ S N b
             | 5 => ML N b | 6 => ML N a | _ => X2)
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL g (F a + F a) _))) ?_
      refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (hF0 a)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL _ D1 _)))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (RS1 N P hP hbox q) hD1)
  let CA := Ld * X2 * (D1 * D1 * ML N [q] + D1 * D1 * ML N [q])
  have hCA : (0 : Q') ≤ CA := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (by
    have := hM0 [q]
    exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hD1 hD1) this)
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hD1 hD1) this))
  refine Q'.le_trans' _ _ _ (abs_sumd_mem _ (fun a => CA * (epsL ^ S N a * mu ^ S N a * ML N a * ML N a)) _
    fun a ha => ?_) ?_
  · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
      (YMGap.Constructive.Q'.mul_le_mul_of_nonneg (dif M links N P hP hbox [p] [] a (List.mem_filter.mp ha).1)
        (inner a ha) (Q'.mul_nonneg _ _ hD1 (hE _)) (Q'.abs_nonneg _)) (Q'.le_of_eqv ?_))
    show Q'.eqv _ (Ld * X2 * (D1 * D1 * ML N [q] + D1 * D1 * ML N [q]) *
      (epsL ^ S N a * mu ^ S N a * ML N a * ML N a))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq
      (V 0 * V 1 * ((V 2 * V 3 * (V 4 * V 5 * V 5) + V 2 * V 3 * (V 4 * V 5 * V 5)) * (V 0 * V 6)))
      (V 2 * V 3 * (V 0 * V 0 * V 6 + V 0 * V 0 * V 6) * (V 1 * V 4 * V 5 * V 5)) (by decide)
      (fun | 0 => D1 | 1 => epsL ^ S N a | 2 => Ld | 3 => X2 | 4 => mu ^ S N a | 5 => ML N a
           | _ => ML N [q])
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL _ CA _)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (RS2 N P hP hbox p) hCA) (Q'.le_of_eqv ?_))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 4)
      (V 0 * V 1 * ((V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 4)) (by decide)
      (fun | 0 => Ld | 1 => X2 | 2 => D1 | 3 => ML N [q] | _ => ML N [p])

include hP hbox in
theorem boundB (p q : Z4Plaq) :
    Q'.abs (sumd (fun a => (zObs w0 M links N [p, q] a + -zObs w0 M links N [q] a +
          -(zObs w0 M links N [p] a + -zz a)) *
        Xi (zObs w0 M links N [q]) (incL N) ((gas N P).filter (cpt (incL N) a)) * XX)
        ((gas N P).filter (hasP p))) ≤
      lam ^ (torusMetric N).ld q p * (XX * XX) * (D2 * ML N [p]) := by
  let Ld := lam ^ (torusMetric N).ld q p
  let X2 := XX * XX
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have hX0 : (0 : Q') ≤ XX := Q'.le_of_lt (env_w0 M links N P hP hbox (gas N P) hG [p]).1
  have hX2 : (0 : Q') ≤ X2 := Q'.mul_nonneg _ _ hX0 hX0
  have hLd : (0 : Q') ≤ Ld := Q'.pow_nonneg _ (by decide) _
  have hM0 : ∀ x, (0 : Q') ≤ ML N x := fun x => Q'.le_trans' _ _ _ (by decide) (ML_ge N x)
  have hC : (0 : Q') ≤ Ld * X2 * D2 := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (by decide)
  refine Q'.le_trans' _ _ _ (abs_sumd_mem _ (fun a => Ld * X2 * D2 * (epsL ^ S N a * mu ^ S N a * ML N a)) _
    fun a ha => ?_) ?_
  · have ham := List.mem_filter.mp ha
    have hpa : p ∈ a := of_decide_eq_true ham.2
    have hw0 : (0 : Q') ≤ Ld * X2 * D2 * (epsL ^ S N a * mu ^ S N a * ML N a) :=
      Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
        (Q'.pow_nonneg _ (by decide) _)) (hM0 a))
    by_cases hqa : q ∈ a
    · have hcg : Xi (zObs w0 M links N [q]) (incL N) ((gas N P).filter (cpt (incL N) a)) =
          Xi zz (incL N) ((gas N P).filter (cpt (incL N) a)) :=
        Xi_congr _ _ _ _ _ (Nat.le_refl _) fun x hx => zObs_off w0 M links N [q] x fun r hr hrq => by
          rw [List.mem_singleton.mp hrq] at hr
          have h1 := (List.mem_filter.mp hx).2
          unfold cpt at h1
          rw [inc_of_mem N hqa hr] at h1
          exact absurd h1 (by decide)
      rw [hcg]
      have eA := env_w0 M links N P hP hbox (gas N P) hG a
      have hXa0 : (0 : Q') ≤ Xi zz (incL N) ((gas N P).filter (cpt (incL N) a)) :=
        Q'.le_of_lt (env_w0 M links N P hP hbox _ (good_sub List.filter_sublist hG) a).1
      have he : Q'.abs (zObs w0 M links N [p, q] a + -zObs w0 M links N [q] a +
          -(zObs w0 M links N [p] a + -zz a)) ≤ D2 * epsL ^ S N a := by
        refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.le_trans' _ _ _ (Q'.add_le_add
          (dif M links N P hP hbox [p, q] [q] a ham.1) (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
            (dif M links N P hP hbox [p] [] a ham.1))) (Q'.le_of_eqv ?_))
        show Q'.eqv _ ((Dc ^ 2 + Dc ^ 1 + (Dc ^ 1 + Dc ^ 0)) * _)
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq ((V 0 + V 1) * V 4 + (V 2 + V 3) * V 4)
          ((V 0 + V 1 + (V 2 + V 3)) * V 4) (by decide)
          (fun | 0 => Dc ^ 2 | 1 => Dc ^ 1 | 2 => Dc ^ 1 | 3 => Dc ^ 0 | _ => epsL ^ S N a)
      have hsh := one_le_shift ((torusMetric N).ld q p) (S N a)
        (by have := diam N P hP hbox a ham.1 q p hqa hpa; omega)
      refine Q'.le_trans' _ _ _ (YMGap.Continuum.PolymerChainDecay.abs_mul_nonneg_le hX0) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
        (YMGap.Continuum.PolymerChainDecay.abs_mul_nonneg_le hXa0) hX0) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
        (YMGap.Constructive.Q'.mul_le_mul_of_nonneg he eA.2 (Q'.mul_nonneg _ _ (by decide)
          (Q'.pow_nonneg _ (by decide) _)) hXa0) hX0) ?_
      let Y := D2 * X2 * (epsL ^ S N a * ML N a)
      have hY : (0 : Q') ≤ Y := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hX2)
        (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _) (hM0 a))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show Q'.eqv _ (1 * Y) from ?_)) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsh hY) (Q'.le_of_eqv ?_))
      · refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.one_mul_eqv _))
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3) * V 3) (V 0 * (V 3 * V 3) * (V 1 * V 2))
          (by decide) (fun | 0 => D2 | 1 => epsL ^ S N a | 2 => ML N a | _ => XX)
      · let V := PolyExpr.var
        exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3 * (V 4 * V 5)))
          (V 0 * V 3 * V 2 * (V 4 * V 1 * V 5)) (by decide)
          (fun | 0 => Ld | 1 => mu ^ S N a | 2 => D2 | 3 => X2 | 4 => epsL ^ S N a | _ => ML N a)
    · have e1 : zObs w0 M links N [p, q] a = zObs w0 M links N [p] a :=
        zObs_agree N w0 M links _ _ a fun r hr => by
          have hrq : r ≠ q := fun e => hqa (e ▸ hr)
          simp [hrq]
      have e2 : zObs w0 M links N [q] a = zz a :=
        zObs_off w0 M links N [q] a fun r hr hrq => hqa (List.mem_singleton.mp hrq ▸ hr)
      rw [e1, e2]
      let Xq := Xi (zObs w0 M links N [q]) (incL N) ((gas N P).filter (cpt (incL N) a))
      have h0 : ((zObs w0 M links N [p] a + -zz a + -(zObs w0 M links N [p] a + -zz a)) * Xq * XX).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.add_neg_self_eqv _))) (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
            (Q'.zero_mul_eqv _))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr h0)) ?_
      rw [ExpNeg.abs_of_nonneg (Q'.le_refl' 0)]
      exact hw0
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL _ _ _)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (RS1 N P hP hbox p) hC) (Q'.le_of_eqv ?_))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 3) (V 0 * V 1 * (V 2 * V 3)) (by decide)
      (fun | 0 => Ld | 1 => X2 | 2 => D2 | _ => ML N [p])

/-! ## The correlator theorem -/

include hP hbox in
/-- **Truncated χ₁ correlator decay at w₀ = 10⁻⁸ (PROVED).**  Uniform in N, M and P:
`|Zpq·Z − Zp·Zq| ≤ λ^{d} · (C · Z²)`, where λ = 6/7, d = ld(q,p) is the torus ℓ∞ plaquette
distance and `C = Ctr = 2·D1²·K² + D2·K`.  Here K = (5/3)^24, D1 = D + 1 and D2 = D² + 2D + 1
with D = 514·10¹⁵.  Z is the heat-kernel partition function `ZObs []`. -/
theorem trunc_decay (hL : ∀ r ∈ P, YMGap.Continuum.SU2ClusterExplore.Lk links N r) (p q : Z4Plaq) :
    let Z := ZObs w0 M links N P []
    let Zp := ZObs w0 M links N P [p] + -Z
    let Zq := ZObs w0 M links N P [q] + -Z
    let Zpq := ZObs w0 M links N P [p, q] + -ZObs w0 M links N P [p] + -ZObs w0 M links N P [q] + Z
    Q'.abs (Zpq * Z + -(Zp * Zq)) ≤ lam ^ (torusMetric N).ld q p * (Ctr * (Z * Z)) := by
  intro Z Zp Zq Zpq
  have e := two_root_obs N w0 M links P hL p q
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr e)) ?_
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.le_trans' _ _ _
    (Q'.add_le_add (boundA M links N P hP hbox p q) (boundB M links N P hP hbox p q)) (Q'.le_of_eqv ?_))
  have eZ : Z.eqv XX := ZObs_eq_Xi w0 M links N P [] hL
  refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm eZ))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm eZ)))))
  show Q'.eqv _ (lam ^ (torusMetric N).ld q p * (((D1 * D1 * K5 + D1 * D1 * K5) * K5 + D2 * K5) * (XX * XX)))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    (V 0 * V 1 * ((V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 3) + V 0 * V 1 * (V 4 * V 3))
    (V 0 * (((V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 3 + V 4 * V 3) * V 1)) (by decide)
    (fun | 0 => lam ^ (torusMetric N).ld q p | 1 => XX * XX | 2 => D1 | 3 => K5 | _ => D2)

end YMGap.Continuum.SU2TruncDecay
