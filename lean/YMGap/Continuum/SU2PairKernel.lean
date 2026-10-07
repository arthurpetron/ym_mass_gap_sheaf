/-
# R1 commit 18: the pair-kernel bound for the two-root formula at w₀

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson; also true for
U(1), not gap evidence.  The Wilson counterpart of the polymer decay is Realizer's
`SU2WilsonLinkDecay`; torus RP is Realizer's (`SU2TorusRPWilson`).

* `kernel_bound`: let a ∋ p and b ∋ q be gas polymers, d = ld(q,p) and L = λ^d μ^{|a|} μ^{|b|}.
  Then `|K(a,b)| ≤ 2·L·M_b M_a²·Ξ²`, where Ξ = Ξ(z;gas).
  - In the far case (|a|+|b| ≤ d) this comes from `T_su2_w0`.
  - In the near case it comes from the KP ratio bounds.
* The truncated-correlator theorem that uses this is `SU2TruncDecay.trunc_decay`.
-/

import YMGap.Continuum.SU2ObsActivity

namespace YMGap.Continuum.SU2PairKernel

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

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable (M : Nat) (links : List Z4Link) (N : Nat) (P : List Z4Plaq) (hP : P.Nodup)
  (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)

local notation "zz" => zObs w0 M links N []
local notation "XX" => Xi (zObs w0 M links N []) (incL N) (gas N P)

include hP hbox in
theorem hlen (a : List Z4Plaq) (ha : a ∈ gas N P) : S N a = a.length :=
  sz_of_ne (BL := torusChain N) a ((YMGap.Continuum.SU2LinkGasBox.linkBox N P hP hbox).size_ok a ha).1

include hP hbox in
theorem diam (a : List Z4Plaq) (ha : a ∈ gas N P) (x y : Z4Plaq) (hx : x ∈ a) (hy : y ∈ a) :
    (torusMetric N).ld x y + 1 ≤ S N a := by
  obtain ⟨cn⟩ := (YMGap.Continuum.SU2LinkGasBox.linkBox N P hP hbox).conn a ha
  rw [hlen N P hP hbox a ha]
  exact diam_le (torusMetric N) a x y (cn x y hx hy) hx

include hP hbox in
theorem dist_pair (a b : List Z4Plaq) (ha : a ∈ gas N P) (hb : b ∈ gas N P) (p q : Z4Plaq)
    (hpa : p ∈ a) (hqb : q ∈ b) (x y : Z4Plaq) (hx : x ∈ b) (hy : y ∈ a) :
    (torusMetric N).ld q p + 2 ≤ (torusMetric N).ld x y + (S N a + S N b) := by
  have h1 := (torusMetric N).tri q x p
  have h2 := (torusMetric N).tri x y p
  have h3 := diam N P hP hbox b hb q x hqb hx
  have h4 := diam N P hP hbox a ha y p hy hpa
  omega

theorem ML_ge (x : List Z4Plaq) : (1 : Q') ≤ ML N x :=
  YMGap.Continuum.SU2LinkGasBox.pow_mono_exp (by decide) (Nat.zero_le _)

theorem le_bump {L A B Y : Q'} (hL : (1 : Q') ≤ L) (hA : (1 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (hY : (0 : Q') ≤ Y) : B * Y ≤ L * (B * A) * Y := by
  refine Q'.mul_le_mul_of_nonneg_right _ _ _ ?_ hY
  have h1 : B ≤ B * A := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv B)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hA hB)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hL (Q'.le_trans' _ _ _ hB h1)))

include hP hbox in
/-- **Pair-kernel bound (PROVED).** -/
theorem kernel_bound (p q : Z4Plaq) (a b : List Z4Plaq) (ha : a ∈ gas N P) (hb : b ∈ gas N P)
    (hpa : p ∈ a) (hqb : q ∈ b) :
    Q'.abs (K N zz (gas N P) a b) ≤
      (lam ^ (torusMetric N).ld q p * mu ^ S N a * mu ^ S N b) * (ML N b * ML N a * ML N a) * (XX * XX) +
      (lam ^ (torusMetric N).ld q p * mu ^ S N a * mu ^ S N b) * (ML N b * ML N a * ML N a) * (XX * XX) := by
  let d := (torusMetric N).ld q p
  let L := lam ^ d * mu ^ S N a * mu ^ S N b
  let W := ML N b * ML N a * ML N a
  have hG : Good (gas N P) (gas N P) := ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup N P hP, fun _ h => h⟩
  have eA := env_w0 M links N P hP hbox (gas N P) hG a
  have eB := env_w0 M links N P hP hbox (gas N P) hG b
  have eAB := env_w0 M links N P hP hbox ((gas N P).filter (cpt (incL N) a)) (good_sub List.filter_sublist hG) b
  have eBA := env_w0 M links N P hP hbox ((gas N P).filter (cpt (incL N) b)) (good_sub List.filter_sublist hG) a
  have hX0 : (0 : Q') ≤ XX := Q'.le_of_lt eA.1
  have hX2 : (0 : Q') ≤ XX * XX := Q'.mul_nonneg _ _ hX0 hX0
  have hM0 : ∀ x, (0 : Q') ≤ ML N x := fun x => Q'.le_trans' _ _ _ (by decide) (ML_ge N x)
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
    have ht : Q'.abs (T zz (incL N) b a (gas N P)) ≤
        lam ^ (d - (S N a + S N b) + 1) * W * (XX * XX) := by
      have h := YMGap.Continuum.SU2RemovalDecay.T_su2_w0 N P hP hbox M links b a hb ha (gas N P) _ hsep hG
      rw [zObs_nil_eq]; exact h
    refine Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ ?_ (Q'.add_le_self_of_nonneg _ _ hB0))
    refine Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ?_ hW0) hX2
    refine Q'.le_trans' _ _ _ ?_ hsh
    show lam * lam ^ (d - (S N a + S N b)) ≤ _
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : lam ≤ 1)
      (Q'.pow_nonneg _ (by decide) _)) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  · have hL1 : (1 : Q') ≤ L := by
      rw [show d - (S N a + S N b) = 0 by omega] at hsh; exact hsh
    let Xa := Xi zz (incL N) ((gas N P).filter (cpt (incL N) a))
    let Xb := Xi zz (incL N) ((gas N P).filter (cpt (incL N) b))
    have hXa0 : (0 : Q') ≤ Xa := Q'.le_of_lt eAB.1
    have hXb0 : (0 : Q') ≤ Xb := Q'.le_of_lt eBA.1
    have hbump := le_bump hL1 (ML_ge N a) (Q'.mul_nonneg _ _ (hM0 b) (hM0 a)) hX2
    have hprod : Xb * Xa ≤ ML N b * ML N a * (XX * XX) :=
      Q'.le_trans' _ _ _ (YMGap.Constructive.Q'.mul_le_mul_of_nonneg eB.2 eA.2
        (Q'.mul_nonneg _ _ (hM0 b) hX0) hXa0) (Q'.le_of_eqv (by
          let V := PolyExpr.var
          exact poly_identity_of_normal_eq (V 0 * V 2 * (V 1 * V 2)) (V 0 * V 1 * (V 2 * V 2)) (by decide)
            (fun | 0 => ML N b | 1 => ML N a | _ => XX)))
    have hneg : Q'.abs (-(Xb * Xa)) ≤ L * W * (XX * XX) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) ?_
      rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hXb0 hXa0)]
      exact Q'.le_trans' _ _ _ hprod hbump
    unfold K
    split
    · refine Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add ?_ hneg)
      have hXab0 : (0 : Q') ≤ Xi zz (incL N) (((gas N P).filter (cpt (incL N) a)).filter (cpt (incL N) b)) :=
        Q'.le_of_lt (env_w0 M links N P hP hbox _ (good_sub List.filter_sublist
          (good_sub List.filter_sublist hG)) a).1
      rw [ExpNeg.abs_of_nonneg (Q'.mul_nonneg _ _ hX0 hXab0)]
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ eAB.2
        (Q'.mul_le_mul_of_nonneg_left _ _ _ eA.2 (hM0 b))) hX0) (Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hbump)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 2 * (V 0 * (V 1 * V 2))) (V 0 * V 1 * (V 2 * V 2)) (by decide)
        (fun | 0 => ML N b | 1 => ML N a | _ => XX)
    · exact Q'.le_trans' _ _ _ hneg (Q'.add_le_self_of_nonneg _ _ hB0)

end YMGap.Continuum.SU2PairKernel
