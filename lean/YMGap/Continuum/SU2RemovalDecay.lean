/-
# R1 commit 15: removal-chain decay instances, with the old constants and the sharp K

ADDITIVE.  **Labels:** strong coupling, heat-kernel (spin-truncated), not Wilson; also true for
U(1), not gap evidence.  The Wilson polymer decay is Realizer's `SU2WilsonLinkDecay`.

`T_link_decay` uses K = (5/3)^24 (`SU2LinkDecay`); `T_link_decay_sharp` uses K = (3/2)^24
(Realizer's `SU2LinkDecaySharp`).  In both, the activity is a hypothesis `|z γ| ≤ ε^{|γ|}` on gas
polymers, with the same scalar hypotheses as the corresponding `link_decay`.
`T_su2_w0` is the SU(2) heat instance at w₀ = 10⁻⁸ (ε_L = 10⁻¹⁵), uniform in M.
-/

import YMGap.Continuum.PolymerRemovalChain
import YMGap.Continuum.SU2LinkDecay
import YMGap.Continuum.SU2LinkDecaySharp

namespace YMGap.Continuum.SU2RemovalDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.SignedPolymerKP (Xi)
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerChainDecay (Good)
open YMGap.Continuum.PolymerDecayZ4 (sumd_le_prodm sumd_mono sumd_mul)
open YMGap.Continuum.PolymerLatticeDecay (lam sepL)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkGasGeometry (incL_symm)
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.PolymerRemovalChain

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

variable (N : Nat) (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
variable (ε : Q') (hε0 : (0 : Q') ≤ ε)

section OldV
open YMGap.Continuum.SU2LinkKP
open YMGap.Continuum.SU2LinkDecay
variable (hε1 : ε * Kc ≤ 1) (hS1 : ε * Kc * Kc * (1 + etaZ) ≤ etaD)
  (hS2 : ε * Kc * ((1 + etaZ) * ((1 + ε * Kc) + (1 + ε * Kc))) ≤ etaD) (hK : ε * Kc * (1 + etaZ) ≤ etaZ)
  (z : List Z4Plaq → Q') (hz : ∀ x, x ∈ gas N P → Q'.abs (z x) ≤ ε ^ S N x)

open YMGap.Continuum.SU2LinkKP
open YMGap.Continuum.SU2LinkDecay

include hP hbox hε0 hε1 hS1 hS2 hK hz in
/-- **Removal-chain lattice decay (PROVED; strong coupling, heat-kernel, not Wilson, U(1)-true).**
`|Ξ(l)Ξ(l_{g,y}) − Ξ(l_y)Ξ(l_g)| ≤ λ^{R+1}·M_y M_g²·Ξ(l)²`, where `M_x = K^{24|x|}` (per plaquette)
and y, g are at torus ℓ∞ distance ≥ R+2.  The activity enters only through `hz`. -/
theorem T_link_decay (y g : List Z4Plaq) (hy : y ∈ gas N P) (hg : g ∈ gas N P) (l : List (List Z4Plaq))
    (R : Nat) (hsep : sepL (torusMetric N) y g (R + 2)) (hl : Good (gas N P) l) :
    Q'.abs (T z (incL N) y g l) ≤
      lam ^ (R + 1) * (ML N y * ML N g * ML N g) * (Xi z (incL N) l * Xi z (incL N) l) := by
  have sub : ∀ x, x ∈ l → x ∈ gas N P := hl.2
  have hTz : T (zc N P z) (incL N) y g l = T z (incL N) y g l := by
    unfold T
    rw [Xi_zc N P z l sub, Xi_zc N P z _ (fun x hx => sub x (List.mem_filter.mp (List.mem_filter.mp hx).1).1),
      Xi_zc N P z _ (fun x hx => sub x (List.mem_filter.mp hx).1),
      Xi_zc N P z (l.filter _) (fun x hx => sub x (List.mem_filter.mp hx).1)]
  have hM0 : ∀ x, (0 : Q') ≤ ML N x := fun _ => Q'.pow_nonneg _ (by decide) _
  have hb := T_bound (zc N P z) (incL N) (incL_symm N) (gas N P) (eL N ε) (ML N) (mL N)
    (envL_pos N P hP hbox ε hε0 hK z hz) (fun l a hl => envL_M N P hP hbox ε hε0 hK z hz l a hl)
    (envL_m N P hP hbox ε hε0 hK z hz) (envL_z N P ε hε0 z hz) (eL_nn N ε hε0) hM0 (mL_nn N) (wL N) y
    (R + 1) (R + 1) g l (sepL_far N P hP hbox y hy (R + 1) (R + 1) g hg hsep) hl
  rw [hTz, Xi_zc N P z l sub] at hb
  have hl0 : (0 : Q') ≤ lam ^ (R + 1) := Q'.pow_nonneg _ (by decide) _
  have hS : sumd (fun h => eL N ε h * mL N h * BW (incL N) (gas N P) (eL N ε) (ML N) (mL N) (wL N) y R
      (R + 1 - wL N h) h) ((gas N P).filter (incL N g)) ≤ lam ^ (R + 1) * ML N g := by
    refine Q'.le_trans' _ _ _ (sumd_mono _ (fun h => lam ^ (R + 1) * etaZ ^ S N h) (fun h =>
      Q'.le_trans' _ _ _ (BW_le (incL N) (gas N P) (eL N ε) (ML N) (mL N) (eL_nn N ε hε0) hM0 (mL_nn N)
        (wL N) y R _ h) (Q'.le_trans' _ _ _ (CSWL_le N P hP hbox ε hε0 hε1 hS1 hS2 y R _ h
          (by have : 1 ≤ S N h := sz_pos (BL := torusChain N) h; unfold wL; omega))
          (lam2_shift _ _ _ (by unfold wL; omega)))) _) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumd_mul _ (fun h => etaZ ^ S N h) _)) ?_
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hl0
    exact Q'.le_trans' _ _ _ (sumd_le_prodm (fun h => etaZ ^ S N h)
      (fun h => Q'.pow_nonneg _ (by decide) _) _) (YMGap.Continuum.SU2LinkGasBox.hgroupL N P hP hbox d0 g)
  have hX0 : (0 : Q') ≤ Xi z (incL N) l * Xi z (incL N) l := by
    have a := envL_pos N P hP hbox ε hε0 hK z hz l hl
    rw [Xi_zc N P z l sub] at a
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt a) (Q'.le_of_lt a)
  refine Q'.le_trans' _ _ _ hb ?_
  show ML N y * (ML N g * sumd _ _) * _ ≤ _
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hS (hM0 g)) (hM0 y)) hX0) (Q'.le_of_eqv ?_)
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * (V 1 * (V 2 * V 1)) * V 3) (V 2 * (V 0 * V 1 * V 1) * V 3)
    (by decide) (fun | 0 => ML N y | 1 => ML N g | 2 => lam ^ (R + 1) | _ => Xi z (incL N) l * Xi z (incL N) l)


end OldV

section SharpV
open YMGap.Continuum.SU2LinkKPSharp
open YMGap.Continuum.SU2LinkDecaySharp
variable (hε1 : ε * Kc ≤ 1) (hS1 : ε * Kc * Kc * (1 + etaZ) ≤ etaD)
  (hS2 : ε * Kc * ((1 + etaZ) * ((1 + ε * Kc) + (1 + ε * Kc))) ≤ etaD) (hK : ε * Kc * (1 + etaZ) ≤ etaZ)
  (z : List Z4Plaq → Q') (hz : ∀ x, x ∈ gas N P → Q'.abs (z x) ≤ ε ^ S N x)

open YMGap.Continuum.SU2LinkKPSharp
open YMGap.Continuum.SU2LinkDecaySharp

include hP hbox hε0 hε1 hS1 hS2 hK hz in
/-- **Removal-chain lattice decay (PROVED; strong coupling, heat-kernel, not Wilson, U(1)-true).**
`|Ξ(l)Ξ(l_{g,y}) − Ξ(l_y)Ξ(l_g)| ≤ λ^{R+1}·M_y M_g²·Ξ(l)²`, where `M_x = K^{24|x|}` (per plaquette)
and y, g are at torus ℓ∞ distance ≥ R+2.  The activity enters only through `hz`. -/
theorem T_link_decay_sharp (y g : List Z4Plaq) (hy : y ∈ gas N P) (hg : g ∈ gas N P) (l : List (List Z4Plaq))
    (R : Nat) (hsep : sepL (torusMetric N) y g (R + 2)) (hl : Good (gas N P) l) :
    Q'.abs (T z (incL N) y g l) ≤
      lam ^ (R + 1) * (ML N y * ML N g * ML N g) * (Xi z (incL N) l * Xi z (incL N) l) := by
  have sub : ∀ x, x ∈ l → x ∈ gas N P := hl.2
  have hTz : T (zc N P z) (incL N) y g l = T z (incL N) y g l := by
    unfold T
    rw [Xi_zc N P z l sub, Xi_zc N P z _ (fun x hx => sub x (List.mem_filter.mp (List.mem_filter.mp hx).1).1),
      Xi_zc N P z _ (fun x hx => sub x (List.mem_filter.mp hx).1),
      Xi_zc N P z (l.filter _) (fun x hx => sub x (List.mem_filter.mp hx).1)]
  have hM0 : ∀ x, (0 : Q') ≤ ML N x := fun _ => Q'.pow_nonneg _ (by decide) _
  have hb := T_bound (zc N P z) (incL N) (incL_symm N) (gas N P) (eL N ε) (ML N) (mL N)
    (envL_pos N P hP hbox ε hε0 hK z hz) (fun l a hl => envL_M N P hP hbox ε hε0 hK z hz l a hl)
    (envL_m N P hP hbox ε hε0 hK z hz) (envL_z N P ε hε0 z hz) (eL_nn N ε hε0) hM0 (mL_nn N) (wL N) y
    (R + 1) (R + 1) g l (sepL_far N P hP hbox y hy (R + 1) (R + 1) g hg hsep) hl
  rw [hTz, Xi_zc N P z l sub] at hb
  have hl0 : (0 : Q') ≤ lam ^ (R + 1) := Q'.pow_nonneg _ (by decide) _
  have hS : sumd (fun h => eL N ε h * mL N h * BW (incL N) (gas N P) (eL N ε) (ML N) (mL N) (wL N) y R
      (R + 1 - wL N h) h) ((gas N P).filter (incL N g)) ≤ lam ^ (R + 1) * ML N g := by
    refine Q'.le_trans' _ _ _ (sumd_mono _ (fun h => lam ^ (R + 1) * etaZ ^ S N h) (fun h =>
      Q'.le_trans' _ _ _ (BW_le (incL N) (gas N P) (eL N ε) (ML N) (mL N) (eL_nn N ε hε0) hM0 (mL_nn N)
        (wL N) y R _ h) (Q'.le_trans' _ _ _ (CSWL_le N P hP hbox ε hε0 hε1 hS1 hS2 y R _ h
          (by have : 1 ≤ S N h := sz_pos (BL := torusChain N) h; unfold wL; omega))
          (lam2_shift _ _ _ (by unfold wL; omega)))) _) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumd_mul _ (fun h => etaZ ^ S N h) _)) ?_
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hl0
    exact Q'.le_trans' _ _ _ (sumd_le_prodm (fun h => etaZ ^ S N h)
      (fun h => Q'.pow_nonneg _ (by decide) _) _) (YMGap.Continuum.SU2LinkGroupSharp.hgroupL_sharp N P hP hbox d0 g)
  have hX0 : (0 : Q') ≤ Xi z (incL N) l * Xi z (incL N) l := by
    have a := envL_pos N P hP hbox ε hε0 hK z hz l hl
    rw [Xi_zc N P z l sub] at a
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt a) (Q'.le_of_lt a)
  refine Q'.le_trans' _ _ _ hb ?_
  show ML N y * (ML N g * sumd _ _) * _ ≤ _
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hS (hM0 g)) (hM0 y)) hX0) (Q'.le_of_eqv ?_)
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0 * (V 1 * (V 2 * V 1)) * V 3) (V 2 * (V 0 * V 1 * V 1) * V 3)
    (by decide) (fun | 0 => ML N y | 1 => ML N g | 2 => lam ^ (R + 1) | _ => Xi z (incL N) l * Xi z (incL N) l)


end SharpV

open YMGap.Continuum.SU2LinkKP in
open YMGap.Continuum.SU2LinkDecay in
open YMGap.Continuum.SU2HaarL1Activity (epsL w0 activity_bound prodPoly fPoly) in
open YMGap.Continuum.BF4GeometricHaarMehlerProjection in
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier in
include hP hbox in
/-- **SU(2) heat instance at w₀ = 10⁻⁸ (PROVED; uniform in M).** -/
theorem T_su2_w0 (M : Nat) (links : List Z4Link) (y g : List Z4Plaq) (hy : y ∈ gas N P)
    (hg : g ∈ gas N P) (l : List (List Z4Plaq)) (R : Nat) (hsep : sepL (torusMetric N) y g (R + 2))
    (hl : Good (gas N P) l) :
    let z := fun γ => quaternionHaar links.length (prodPoly (fun p => fPoly w0 links N p M) γ)
    Q'.abs (T z (incL N) y g l) ≤
      lam ^ (R + 1) * (ML N y * ML N g * ML N g) * (Xi z (incL N) l * Xi z (incL N) l) :=
  T_link_decay N P hP hbox epsL (by decide) decay_pass.1 decay_pass.2.1 decay_pass.2.2 kp_pass _
    (fun x hx => by
      rw [show S N x = x.length from sz_of_ne (BL := torusChain N) x
        ((YMGap.Continuum.SU2LinkGasBox.linkBox N P hP hbox).size_ok x hx).1]
      exact activity_bound links.length links N M x) y g hy hg l R hsep hl

end YMGap.Continuum.SU2RemovalDecay
