/-
# R1 commit 21: the truncated-correlator decay, generic in the plaquette weight

ADDITIVE.  **Labels:** strong coupling; this file is generic (heat kernel or Wilson); also true
for U(1), not gap evidence.

This abstracts `SU2PairKernel`/`SU2TruncDecay` once over the activity package, so that heat
kernel and Wilson are both instances.  The data are:
* activities `z, z^p, z^q, z^{pq}` on gas polymers, which agree off p (resp. q) as in
  `SU2TwoRoot.two_root`;
* activity bounds `|z^p − z|, |z^q − z| ≤ D1 ε^{|a|}` and `|ε_a| ≤ D2 ε^{|a|}`;
* a link-KP package `M`, with `1 ≤ M`, the environment (`0 < Ξ`, `Ξ(l_a) ≤ M_a Ξ(l)`), the
  removal-chain bound `|T(y,g)| ≤ λ^{R+1} M_y M_g² Ξ²` at separation R+2, and the rooted sums
  `Σ_{a∋s} ε^{|a|} μ^{|a|} M_a (M_a) ≤ K1`.

* `trunc_gen`: `|Ξ(z^{pq})Ξ(z) − Ξ(z^p)Ξ(z^q)| ≤ λ^{ld(q,p)} · (Cg · Ξ(z)²)`, with
  `Cg = 2·D1²·K1² + D2·K1`.
-/

import YMGap.Continuum.SU2TruncRatio

namespace YMGap.Continuum.SU2TruncGeneric

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
open YMGap.Continuum.SU2ObsRoot (hasP inc_of_mem)
open YMGap.Continuum.SU2TwoRoot (K sumd_mulL two_root hasP_false)
open YMGap.Continuum.PolymerRemovalChain (T)
open YMGap.Continuum.SU2LinkKP (S Xi_congr)
open YMGap.Continuum.SU2ObsActivity (mu lam_shift one_le_shift)
open YMGap.Continuum.SU2PairKernel (diam dist_pair le_bump)
open YMGap.Continuum.SU2TruncDecay (abs_sumd_mem)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable (N : Nat) (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
variable (z zp zq zpq : List Z4Plaq → Q') (p q : Z4Plaq)
variable (Mf : List Z4Plaq → Q') (hM1 : ∀ x, (1 : Q') ≤ Mf x)
variable (henv : ∀ l, Good (gas N P) l → ∀ a, (0 : Q') < Xi z (incL N) l ∧
  Xi z (incL N) (l.filter (cpt (incL N) a)) ≤ Mf a * Xi z (incL N) l)
variable (hT : ∀ y g, y ∈ gas N P → g ∈ gas N P → ∀ R, sepL (torusMetric N) y g (R + 2) →
  Q'.abs (T z (incL N) y g (gas N P)) ≤ lam ^ (R + 1) * (Mf y * Mf g * Mf g) *
    (Xi z (incL N) (gas N P) * Xi z (incL N) (gas N P)))
variable (ε D1 D2 K1 : Q') (hε0 : (0 : Q') ≤ ε) (hD1 : (0 : Q') ≤ D1) (hD2 : (0 : Q') ≤ D2)
variable (hd0 : ∀ a, a ∈ gas N P → Q'.abs (zp a + -z a) ≤ D1 * ε ^ S N a)
variable (hη : ∀ b, b ∈ gas N P → Q'.abs (zq b + -z b) ≤ D1 * ε ^ S N b)
variable (hε2 : ∀ a, a ∈ gas N P → Q'.abs (zpq a + -zq a + -(zp a + -z a)) ≤ D2 * ε ^ S N a)
variable (h2 : ∀ x, x ∈ gas N P → q ∉ x → zq x = z x)
variable (h3 : ∀ x, x ∈ gas N P → q ∉ x → zpq x = zp x)
variable (hroot1 : ∀ s : Z4Plaq, sumd (fun a => ε ^ S N a * mu ^ S N a * Mf a) ((gas N P).filter (hasP s)) ≤ K1)
variable (hroot2 : ∀ s : Z4Plaq,
  sumd (fun a => ε ^ S N a * mu ^ S N a * Mf a * Mf a) ((gas N P).filter (hasP s)) ≤ K1)

local notation "XX" => Xi z (incL N) (gas N P)

include hP hbox hM1 henv hT in
/-- **Pair-kernel bound (PROVED).** -/
theorem kernel_bound (a b : List Z4Plaq) (ha : a ∈ gas N P) (hb : b ∈ gas N P)
    (hpa : p ∈ a) (hqb : q ∈ b) :
    Q'.abs (K N z (gas N P) a b) ≤
      (lam ^ (torusMetric N).ld q p * mu ^ S N a * mu ^ S N b) * (Mf b * Mf a * Mf a) * (XX * XX) +
      (lam ^ (torusMetric N).ld q p * mu ^ S N a * mu ^ S N b) * (Mf b * Mf a * Mf a) * (XX * XX) := by
  let d := (torusMetric N).ld q p
  let L := lam ^ d * mu ^ S N a * mu ^ S N b
  let W := Mf b * Mf a * Mf a
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have eA := henv (gas N P) hG a
  have eB := henv (gas N P) hG b
  have eAB := henv ((gas N P).filter (cpt (incL N) a)) (good_sub List.filter_sublist hG) b
  have eBA := henv ((gas N P).filter (cpt (incL N) b)) (good_sub List.filter_sublist hG) a
  have hX0 : (0 : Q') ≤ XX := Q'.le_of_lt eA.1
  have hX2 : (0 : Q') ≤ XX * XX := Q'.mul_nonneg _ _ hX0 hX0
  have hM0 : ∀ x, (0 : Q') ≤ Mf x := fun x => Q'.le_trans' _ _ _ (by decide) (hM1 x)
  have hW0 : (0 : Q') ≤ W := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hM0 b) (hM0 a)) (hM0 a)
  have hL0 : (0 : Q') ≤ L := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
    (Q'.pow_nonneg _ (by decide) _)) (Q'.pow_nonneg _ (by decide) _)
  have hB0 : (0 : Q') ≤ L * W * (XX * XX) := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hL0 hW0) hX2
  have hsh : lam ^ (d - (S N a + S N b)) ≤ L := Q'.le_trans' _ _ _ (lam_shift d _) (Q'.le_of_eqv (by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (YMGap.Continuum.HeatKernelPolymerActivityR1.pow_add' mu _ _)) ?_
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 0 * V 1 * V 2) (by decide)
      (fun | 0 => lam ^ d | 1 => mu ^ S N a | _ => mu ^ S N b)))
  show Q'.abs _ ≤ L * W * (XX * XX) + L * W * (XX * XX)
  by_cases hd : S N a + S N b ≤ d
  · have hsep : sepL (torusMetric N) b a (d - (S N a + S N b) + 2) := fun x hx y hy => by
      have := dist_pair N P hP hbox a b ha hb p q hpa hqb x y hx hy
      omega
    have hinc : incL N a b = false := by
      rw [incL_symm]
      exact YMGap.Continuum.SU2LinkDecay.sep_incL N P hP hbox b a hb ha _ hsep (by omega)
    have hc : cpt (incL N) a b = true := by unfold cpt; rw [hinc]; rfl
    unfold K; rw [if_pos hc]
    have ht : Q'.abs (T z (incL N) b a (gas N P)) ≤
        lam ^ (d - (S N a + S N b) + 1) * W * (XX * XX) := by
      exact hT b a hb ha _ hsep
    refine Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ ?_ (Q'.add_le_self_of_nonneg _ _ hB0))
    refine Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ?_ hW0) hX2
    refine Q'.le_trans' _ _ _ ?_ hsh
    show lam * lam ^ (d - (S N a + S N b)) ≤ _
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : lam ≤ 1)
      (Q'.pow_nonneg _ (by decide) _)) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  · have hL1 : (1 : Q') ≤ L := by
      rw [show d - (S N a + S N b) = 0 by omega] at hsh; exact hsh
    let Xa := Xi z (incL N) ((gas N P).filter (cpt (incL N) a))
    let Xb := Xi z (incL N) ((gas N P).filter (cpt (incL N) b))
    have hXa0 : (0 : Q') ≤ Xa := Q'.le_of_lt eAB.1
    have hXb0 : (0 : Q') ≤ Xb := Q'.le_of_lt eBA.1
    have hbump := le_bump hL1 (hM1 a) (Q'.mul_nonneg _ _ (hM0 b) (hM0 a)) hX2
    have hprod : Xb * Xa ≤ Mf b * Mf a * (XX * XX) :=
      Q'.le_trans' _ _ _ (YMGap.Constructive.Q'.mul_le_mul_of_nonneg eB.2 eA.2
        (Q'.mul_nonneg _ _ (hM0 b) hX0) hXa0) (Q'.le_of_eqv (by
          let V := PolyExpr.var
          exact poly_identity_of_normal_eq (V 0 * V 2 * (V 1 * V 2)) (V 0 * V 1 * (V 2 * V 2)) (by decide)
            (fun | 0 => Mf b | 1 => Mf a | _ => XX)))
    have hneg : Q'.abs (-(Xb * Xa)) ≤ L * W * (XX * XX) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) ?_
      rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hXb0 hXa0)]
      exact Q'.le_trans' _ _ _ hprod hbump
    unfold K
    split
    · refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add ?_ hneg)
      have hXab0 : (0 : Q') ≤ Xi z (incL N) (((gas N P).filter (cpt (incL N) a)).filter (cpt (incL N) b)) :=
        Q'.le_of_lt (henv _ (good_sub List.filter_sublist
          (good_sub List.filter_sublist hG)) a).1
      rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hX0 hXab0)]
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ eAB.2
        (Q'.mul_le_mul_of_nonneg_left _ _ _ eA.2 (hM0 b))) hX0) (Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hbump)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 2 * (V 0 * (V 1 * V 2))) (V 0 * V 1 * (V 2 * V 2)) (by decide)
        (fun | 0 => Mf b | 1 => Mf a | _ => XX)
    · exact Q'.le_trans' _ _ _ hneg (Q'.add_le_self_of_nonneg _ _ hB0)

include hP hbox hM1 henv hT hε0 hD1 hd0 hη hroot1 hroot2 in
theorem boundA :
    Q'.abs (sumd (fun a => (zp a + -z a) *
        sumd (fun b => (zq b + -z b) * K N z (gas N P) a b) ((gas N P).filter (hasP q)))
        ((gas N P).filter (hasP p))) ≤
      lam ^ (torusMetric N).ld q p * (XX * XX) * ((D1 * D1 * K1 + D1 * D1 * K1) * K1) := by
  let Ld := lam ^ (torusMetric N).ld q p
  let X2 := XX * XX
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have hX0 : (0 : Q') ≤ XX := Q'.le_of_lt (henv (gas N P) hG [p]).1
  have hX2 : (0 : Q') ≤ X2 := Q'.mul_nonneg _ _ hX0 hX0
  have hLd : (0 : Q') ≤ Ld := Q'.pow_nonneg _ (by decide) _
  have hM0 : ∀ x, (0 : Q') ≤ Mf x := fun x => Q'.le_trans' _ _ _ (by decide) (hM1 x)
  have hE : ∀ s, (0 : Q') ≤ ε ^ s := fun _ => Q'.pow_nonneg _ hε0 _
  have hMu : ∀ s, (0 : Q') ≤ mu ^ s := fun _ => Q'.pow_nonneg _ (by decide) _
  let F := fun a : List Z4Plaq => Ld * X2 * (mu ^ S N a * Mf a * Mf a)
  let g := fun b : List Z4Plaq => D1 * (ε ^ S N b * mu ^ S N b * Mf b)
  have hF0 : ∀ a, (0 : Q') ≤ F a + F a := fun a => Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hMu _) (hM0 a)) (hM0 a)))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hMu _) (hM0 a)) (hM0 a)))
  have inner : ∀ a, a ∈ (gas N P).filter (hasP p) →
      Q'.abs (sumd (fun b => (zq b + -z b) * K N z (gas N P) a b)
        ((gas N P).filter (hasP q))) ≤ (F a + F a) * (D1 * K1) := by
    intro a ha
    have ham := List.mem_filter.mp ha
    refine Q'.le_trans' _ _ _ (abs_sumd_mem _ (fun b => (F a + F a) * g b) _ fun b hb => ?_) ?_
    · have hbm := List.mem_filter.mp hb
      have hk := kernel_bound N P hP hbox z p q Mf hM1 henv hT a b ham.1 hbm.1 (of_decide_eq_true ham.2)
        (of_decide_eq_true hbm.2)
      refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
        (YMGap.Constructive.Q'.mul_le_mul_of_nonneg (hη b hbm.1) hk
          (Q'.mul_nonneg _ _ hD1 (hE _)) (Q'.abs_nonneg _)) (Q'.le_of_eqv ?_))
      show Q'.eqv _ ((Ld * X2 * (mu ^ S N a * Mf a * Mf a) + Ld * X2 * (mu ^ S N a * Mf a * Mf a)) *
        (D1 * (ε ^ S N b * mu ^ S N b * Mf b)))
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq
        (V 0 * V 1 * ((V 2 * V 3 * V 4) * (V 5 * V 6 * V 6) * V 7 + (V 2 * V 3 * V 4) * (V 5 * V 6 * V 6) * V 7))
        ((V 2 * V 7 * (V 3 * V 6 * V 6) + V 2 * V 7 * (V 3 * V 6 * V 6)) * (V 0 * (V 1 * V 4 * V 5)))
        (by decide)
        (fun | 0 => D1 | 1 => ε ^ S N b | 2 => Ld | 3 => mu ^ S N a | 4 => mu ^ S N b
             | 5 => Mf b | 6 => Mf a | _ => X2)
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL g (F a + F a) _))) ?_
      refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (hF0 a)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL _ D1 _)))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (hroot1 q) hD1)
  let CA := Ld * X2 * (D1 * D1 * K1 + D1 * D1 * K1)
  have hCA : (0 : Q') ≤ CA := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) (by
    have : (0 : Q') ≤ K1 := Q'.le_trans' _ _ _ (sumd_nonneg _ (fun a => Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hε0 _) (Q'.pow_nonneg _ (by decide) _)) (hM0 a)) _) (hroot1 q)
    exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hD1 hD1) this)
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hD1 hD1) this))
  refine Q'.le_trans' _ _ _ (abs_sumd_mem _ (fun a => CA * (ε ^ S N a * mu ^ S N a * Mf a * Mf a)) _
    fun a ha => ?_) ?_
  · refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
      (YMGap.Constructive.Q'.mul_le_mul_of_nonneg (hd0 a (List.mem_filter.mp ha).1)
        (inner a ha) (Q'.mul_nonneg _ _ hD1 (hE _)) (Q'.abs_nonneg _)) (Q'.le_of_eqv ?_))
    show Q'.eqv _ (Ld * X2 * (D1 * D1 * K1 + D1 * D1 * K1) *
      (ε ^ S N a * mu ^ S N a * Mf a * Mf a))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq
      (V 0 * V 1 * ((V 2 * V 3 * (V 4 * V 5 * V 5) + V 2 * V 3 * (V 4 * V 5 * V 5)) * (V 0 * V 6)))
      (V 2 * V 3 * (V 0 * V 0 * V 6 + V 0 * V 0 * V 6) * (V 1 * V 4 * V 5 * V 5)) (by decide)
      (fun | 0 => D1 | 1 => ε ^ S N a | 2 => Ld | 3 => X2 | 4 => mu ^ S N a | 5 => Mf a
           | _ => K1)
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL _ CA _)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hroot2 p) hCA) (Q'.le_of_eqv ?_))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 4)
      (V 0 * V 1 * ((V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 4)) (by decide)
      (fun | 0 => Ld | 1 => X2 | 2 => D1 | 3 => K1 | _ => K1)

include hP hbox hM1 henv hε0 hD2 hε2 h2 h3 hroot1 in
theorem boundB :
    Q'.abs (sumd (fun a => (zpq a + -zq a +
          -(zp a + -z a)) *
        Xi (zq) (incL N) ((gas N P).filter (cpt (incL N) a)) * XX)
        ((gas N P).filter (hasP p))) ≤
      lam ^ (torusMetric N).ld q p * (XX * XX) * (D2 * K1) := by
  let Ld := lam ^ (torusMetric N).ld q p
  let X2 := XX * XX
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have hX0 : (0 : Q') ≤ XX := Q'.le_of_lt (henv (gas N P) hG [p]).1
  have hX2 : (0 : Q') ≤ X2 := Q'.mul_nonneg _ _ hX0 hX0
  have hLd : (0 : Q') ≤ Ld := Q'.pow_nonneg _ (by decide) _
  have hM0 : ∀ x, (0 : Q') ≤ Mf x := fun x => Q'.le_trans' _ _ _ (by decide) (hM1 x)
  have hC : (0 : Q') ≤ Ld * X2 * D2 := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hLd hX2) hD2
  refine Q'.le_trans' _ _ _ (abs_sumd_mem _ (fun a => Ld * X2 * D2 * (ε ^ S N a * mu ^ S N a * Mf a)) _
    fun a ha => ?_) ?_
  · have ham := List.mem_filter.mp ha
    have hpa : p ∈ a := of_decide_eq_true ham.2
    have hw0 : (0 : Q') ≤ Ld * X2 * D2 * (ε ^ S N a * mu ^ S N a * Mf a) :=
      Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hε0 _)
        (Q'.pow_nonneg _ (by decide) _)) (hM0 a))
    by_cases hqa : q ∈ a
    · have hcg : Xi (zq) (incL N) ((gas N P).filter (cpt (incL N) a)) =
          Xi z (incL N) ((gas N P).filter (cpt (incL N) a)) :=
        Xi_congr _ _ _ _ _ (Nat.le_refl _) fun x hx => h2 x (List.mem_filter.mp hx).1 fun hr => by
          have h1 := (List.mem_filter.mp hx).2
          unfold cpt at h1
          rw [inc_of_mem N hqa hr] at h1
          exact absurd h1 (by decide)
      rw [hcg]
      have eA := henv (gas N P) hG a
      have hXa0 : (0 : Q') ≤ Xi z (incL N) ((gas N P).filter (cpt (incL N) a)) :=
        Q'.le_of_lt (henv _ (good_sub List.filter_sublist hG) a).1
      have he := hε2 a ham.1
      have hsh := one_le_shift ((torusMetric N).ld q p) (S N a)
        (by have := diam N P hP hbox a ham.1 q p hqa hpa; omega)
      refine Q'.le_trans' _ _ _ (YMGap.Continuum.PolymerChainDecay.abs_mul_nonneg_le hX0) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
        (YMGap.Continuum.PolymerChainDecay.abs_mul_nonneg_le hXa0) hX0) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
        (YMGap.Constructive.Q'.mul_le_mul_of_nonneg he eA.2 (Q'.mul_nonneg _ _ hD2
          (Q'.pow_nonneg _ hε0 _)) hXa0) hX0) ?_
      let Y := D2 * X2 * (ε ^ S N a * Mf a)
      have hY : (0 : Q') ≤ Y := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hD2 hX2)
        (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hε0 _) (hM0 a))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (show Q'.eqv _ (1 * Y) from ?_)) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsh hY) (Q'.le_of_eqv ?_))
      · refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.one_mul_eqv _))
        let V := PolyExpr.var
        exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3) * V 3) (V 0 * (V 3 * V 3) * (V 1 * V 2))
          (by decide) (fun | 0 => D2 | 1 => ε ^ S N a | 2 => Mf a | _ => XX)
      · let V := PolyExpr.var
        exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3 * (V 4 * V 5)))
          (V 0 * V 3 * V 2 * (V 4 * V 1 * V 5)) (by decide)
          (fun | 0 => Ld | 1 => mu ^ S N a | 2 => D2 | 3 => X2 | 4 => ε ^ S N a | _ => Mf a)
    · have e1 : zpq a = zp a := h3 a ham.1 hqa
      have e2 : zq a = z a := h2 a ham.1 hqa
      rw [e1, e2]
      let Xq := Xi (zq) (incL N) ((gas N P).filter (cpt (incL N) a))
      have h0 : ((zp a + -z a + -(zp a + -z a)) * Xq * XX).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.add_neg_self_eqv _))) (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
            (Q'.zero_mul_eqv _))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr h0)) ?_
      rw [ExpNeg.abs_of_nonneg (Q'.le_refl' 0)]
      exact hw0
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sumd_mulL _ _ _)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hroot1 p) hC) (Q'.le_of_eqv ?_))
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 3) (V 0 * V 1 * (V 2 * V 3)) (by decide)
      (fun | 0 => Ld | 1 => X2 | 2 => D2 | _ => K1)


/-- `Cg = 2·D1²·K1² + D2·K1`. -/
def Cg (D1 D2 K1 : Q') : Q' := (D1 * D1 * K1 + D1 * D1 * K1) * K1 + D2 * K1

include hP hbox hM1 henv hT hε0 hD1 hD2 hd0 hη hε2 h2 h3 hroot1 hroot2 in
/-- **Generic truncated-correlator decay (PROVED).** -/
theorem trunc_gen (h1 : ∀ x, x ∈ gas N P → p ∉ x → zp x = z x ∧ zpq x = zq x) :
    Q'.abs (Xi zpq (incL N) (gas N P) * XX + -(Xi zp (incL N) (gas N P) * Xi zq (incL N) (gas N P))) ≤
      lam ^ (torusMetric N).ld q p * (Cg D1 D2 K1 * (XX * XX)) := by
  have hB : ∀ s : Z4Plaq, ∀ a, a ∈ gas N P → hasP s a = true → ∀ b, b ∈ gas N P → hasP s b = true →
      incL N a b = true :=
    fun _ a _ ha b _ hb => inc_of_mem N (of_decide_eq_true ha) (of_decide_eq_true hb)
  have e := two_root N z zp zq zpq (hasP p) (hasP q) (gas N P) (hB p) (hB q)
    (fun x hx hpx => h1 x hx (hasP_false hpx)) (fun x hx hqx => h2 x hx (hasP_false hqx))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr e)) ?_
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.le_trans' _ _ _
    (Q'.add_le_add (boundA N P hP hbox z zp zq p q Mf hM1 henv hT ε D1 K1 hε0 hD1 hd0 hη hroot1 hroot2)
      (boundB N P hP hbox z zp zq zpq p q Mf hM1 henv ε D2 K1 hε0 hD2 hε2 h2 h3 hroot1)) (Q'.le_of_eqv ?_))
  show Q'.eqv _ (lam ^ (torusMetric N).ld q p * (((D1 * D1 * K1 + D1 * D1 * K1) * K1 + D2 * K1) * (XX * XX)))
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    (V 0 * V 1 * ((V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 3) + V 0 * V 1 * (V 4 * V 3))
    (V 0 * (((V 2 * V 2 * V 3 + V 2 * V 2 * V 3) * V 3 + V 4 * V 3) * V 1)) (by decide)
    (fun | 0 => lam ^ (torusMetric N).ld q p | 1 => XX * XX | 2 => D1 | 3 => K1 | _ => D2)

end YMGap.Continuum.SU2TruncGeneric
