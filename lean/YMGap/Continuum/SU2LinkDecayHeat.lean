/-
# R1 commit 11: lattice decay for the SU(2) polyPartition using the character envelope

ADDITIVE.  **Regime:** strong coupling, heat-kernel (spin-truncated), not Wilson.  The bound is
also true for U(1), so it is not gap evidence.

This swaps the ℓ¹ activity bound (w₀ = 10⁻⁸) for Realizer's sharper
`SU2PolymerActivityHeat.z_abs_le` (|z γ| ≤ charEnv(w,M)^{|γ|}, for 0 < w).

* `lk_cover`: `Lk links N p → LinksCover links N p` (the same four links).
* `S_len`: `sz γ = γ.length` for nonempty γ (every gas polymer is nonempty).
* `charEnv_zero`: `charEnv 0 M ≤ 0`.  `z_abs_zero`: the w = 0 case, via the ℓ¹ route.
* `charEnv_wH`: at `w_H = 1/100000`, `charEnv w_H M ≤ ε_H = 5·10⁻¹⁵` for every M (uniform).
* `heat_pass`: the KP and decay scalar conditions at ε_H, proved by `decide`.
* `su2_link_decay_heat`: for w ∈ {0, 1/100000}, `polyPartition ≈ Ξ(gas)` and
  `|U| ≤ (6/7)^R (λ²η)^{|g|} Ξ(l)Ξ(g::l)`, uniform in M.
The observable is the polymer insertion/removal correlation U.  No Wilson loop is involved.
-/

import YMGap.Continuum.SU2LinkDecay
import YMGap.Continuum.SU2PolymerActivityHeat

namespace YMGap.Continuum.SU2LinkDecayHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.PolymerChainDecay
open YMGap.Continuum.SignedPolymerKP (Xi le_of_eqv_add)
open YMGap.Continuum.PolymerLatticeDecay (lam sepL pow_mono)
open YMGap.Continuum.SU2PolymerIdentity (incL gas polyPartition_eq_Xi)
open YMGap.Continuum.SU2LinkGasBox
open YMGap.Continuum.SU2LinkKP
open YMGap.Continuum.SU2LinkDecay
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.HeatKernelPolymerActivityR1 (charEnv charEnv_inv charEnv_nonneg)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly fPoly haar_abs prod_l1 fPoly_l1 B513)
open YMGap.Continuum.SU2PlaqSupport

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

theorem lk_cover (links : List Z4Link) (N : Nat) (p : Z4Plaq)
    (h : YMGap.Continuum.SU2ClusterExplore.Lk links N p) :
    YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p :=
  ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self),
   h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
   h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem S_len (N : Nat) (x : List Z4Plaq) (h : 1 ≤ x.length) : S N x = x.length :=
  sz_of_ne (BL := torusChain N) x h

theorem charEnv_le_of {w c : Q'} (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1)
    (hr : Q'.ofNat 4 * w ^ 3 * (1 + c) ≤ c) (hc : (0 : Q') ≤ c) (M : Nat) : charEnv w M ≤ c := by
  refine Q'.le_trans' _ _ _ (charEnv_inv h0 h1 hr M) ?_
  have hr0 : (0 : Q') ≤ c * (Q'.ofNat 4 * w ^ 3) ^ M :=
    Q'.mul_nonneg _ _ hc (Q'.pow_nonneg _ (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ h0 _)) _)
  refine le_of_eqv_add (S := c * (Q'.ofNat 4 * w ^ 3) ^ M) ?_ hr0
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0) ((V 0 + -(V 1)) + V 1) (by decide)
    (fun | 0 => c | _ => c * (Q'.ofNat 4 * w ^ 3) ^ M)

def wH : Q' := Q'.mkPos 1 100000 (by decide)
def epsH : Q' := Q'.mkPos 5 1000000000000000 (by decide)

theorem charEnv_wH (M : Nat) : charEnv wH M ≤ epsH :=
  charEnv_le_of (by decide) (by decide) (by decide) (by decide) M

theorem charEnv_zero (M : Nat) : charEnv (B513 * 0) M ≤ 0 :=
  charEnv_le_of (by decide) (by decide) (by decide) (by decide) M

/-- The `w = 0` case: for nonempty γ the true activity is bounded by `c^{|γ|}` for every `c ≥ 0`. -/
theorem z_abs_zero (links : List Z4Link) (N M : Nat) (γ : List Z4Plaq) (c : Q') (hc : (0 : Q') ≤ c) :
    Q'.abs (quaternionHaar links.length (prodPoly (fun p => fPoly 0 links N p M) γ)) ≤ c ^ γ.length :=
  Q'.le_trans' _ _ _ (haar_abs _ _) (Q'.le_trans' _ _ _
    (prod_l1 _ (charEnv (B513 * 0) M) (charEnv_nonneg (by decide) M)
      (fun p => fPoly_l1 (by decide) links N p M) γ)
    (pow_mono (charEnv_nonneg (by decide) M) (Q'.le_trans' _ _ _ (charEnv_zero M) hc) _))

theorem z_abs_wH (links : List Z4Link) (N M : Nat) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    Q'.abs (quaternionHaar links.length (prodPoly (fun p => fPoly wH links N p M) γ)) ≤ epsH ^ γ.length := by
  have h := YMGap.Continuum.SU2PolymerActivityHeat.z_abs_le (w := wH) (by decide) M links N γ hc
  have hp := pow_mono (charEnv_nonneg (by decide) M) (charEnv_wH M) γ.length
  exact Q'.abs_le_of_bounds (Q'.le_trans' _ _ _ (Q'.neg_le_neg hp) h.1) (Q'.le_trans' _ _ _ h.2 hp)

theorem heat_pass :
    epsH * Kc * (1 + etaZ) ≤ etaZ ∧ epsH * Kc ≤ 1 ∧ epsH * Kc * Kc * (1 + etaZ) ≤ etaD ∧
      epsH * Kc * ((1 + etaZ) * ((1 + epsH * Kc) + (1 + epsH * Kc))) ≤ etaD := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **SU(2) lattice decay with the character envelope (PROVED; strong coupling, heat-kernel action
spin-truncated at M, not Wilson; also true for U(1), so not gap evidence).**  At `w = 1/100000`
(and at `w = 0`), `polyPartition ≈ Ξ(gas)` and the insertion/removal correlation `U` decays like
`(6/7)^R`, uniformly in `M`. -/
theorem su2_link_decay_heat (w : Q') (hw : w = 0 ∨ w = wH) (N M : Nat) (links : List Z4Link)
    (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
    (hL : ∀ p ∈ P, YMGap.Continuum.SU2ClusterExplore.Lk links N p)
    (y g : List Z4Plaq) (l : List (List Z4Plaq)) (R : Nat)
    (hsep : sepL (torusMetric N) y g (R + 1)) (hG : Good (gas N P) (y :: g :: l)) :
    let z := fun γ => quaternionHaar links.length (prodPoly (fun p => fPoly w links N p M) γ)
    (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.polyPartition w M links N P).eqv
      (Xi z (incL N) (gas N P)) ∧
    Q'.abs (U z (incL N) y g l) ≤
      (lam ^ R * etaD ^ S N g) * (Xi z (incL N) l * Xi z (incL N) (g :: l)) :=
  ⟨polyPartition_eq_Xi N w M links P hL,
   link_decay N P hP hbox epsH (by decide) heat_pass.2.1 heat_pass.2.2.1 heat_pass.2.2.2 heat_pass.1 _
    (fun x hx => by
      rw [S_len N x ((linkBox N P hP hbox).size_ok x hx).1]
      rcases hw with hw | hw
      · subst hw; exact z_abs_zero links N M x epsH (by decide)
      · subst hw
        exact z_abs_wH links N M x (fun p hp =>
          lk_cover links N p (hL p ((gas_inv N P hP x hx).2.2 p hp)))) y g l R hsep hG⟩

end YMGap.Continuum.SU2LinkDecayHeat
