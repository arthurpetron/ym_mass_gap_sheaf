/-
# Wilson action, commit 5: link-KP lattice decay for the (Taylor-truncated) Wilson gas

**STRONG COUPLING ONLY (β ≲ 1e-4; here β₀ = 1/(4·10¹⁴)).** This is a volume-uniform strong-coupling
cluster expansion for the actual Wilson action, uniform in the Taylor order `K`. It is equally true for U(1).
It is NOT mass-gap or continuum evidence. The observable is the polymer insertion/removal correlation `U`,
not a Wilson loop.

Mirrors the Prover's `SU2LinkDecayHeat.su2_link_decay_heat`, reusing `lk_cover`, `S_len`, `heat_pass`,
`epsH = 5·10⁻¹⁵` and `link_decay` (no edits). The heat-kernel activity is replaced by the normalised
Wilson activity `z_norm γ = ∫ Π_{p∈γ} recip(c_0) g_p` (`SU2WilsonPolymerIdentity.zn_abs_le`).
* `wilson_pass_H` : `β₀ = 1/(4·10¹⁴)` has `0 < β₀`, `2β₀ ≤ 1` and `2β₀ ≤ epsH`.
* `zn_abs_H` : `|z_norm γ| ≤ epsH^{|γ|}` at β₀.
* `su2_link_decay_wilson` : `Z_W ≈ c_0^{|P|} Ξ(gas)` and `|U| ≤ (6/7)^R (λ²η)^{|g|} Ξ(l) Ξ(g::l)`.
-/

import YMGap.Continuum.SU2LinkDecayHeat
import YMGap.Continuum.SU2WilsonPolymerIdentity

namespace YMGap.Continuum.SU2WilsonLinkDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.PolymerChainDecay
open YMGap.Continuum.SignedPolymerKP (Xi)
open YMGap.Continuum.PolymerLatticeDecay (lam sepL pow_mono)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkGasBox
open YMGap.Continuum.SU2LinkKP
open YMGap.Continuum.SU2LinkDecay
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2LinkDecayHeat (lk_cover S_len epsH heat_pass)
open YMGap.Continuum.SU2WilsonPolymerIdentity (TK FW c0 zn_abs_le wilson_polyPartition_eq_Xi)

/-- `β₀ = 1/(4·10¹⁴)`, so `2β₀ = 5·10⁻¹⁵ = epsH`. -/
def betaH : Q' := Q'.mkPos 1 400000000000000 (by decide)

theorem wilson_pass_H : (0 : Q') < betaH ∧ 2 * betaH ≤ 1 ∧ 2 * betaH ≤ epsH := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- STRONG COUPLING ONLY. `|z_norm γ| ≤ epsH^{|γ|}` at `β₀`, uniform in `K`. -/
theorem zn_abs_H (links : List Z4Link) (N K : Nat) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    Q'.abs (quaternionHaar links.length (prodPoly (FW links N betaH K) γ)) ≤ epsH ^ γ.length := by
  have h := zn_abs_le links N betaH K wilson_pass_H.1 wilson_pass_H.2.1 γ hc
  have hp := pow_mono (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt wilson_pass_H.1)) wilson_pass_H.2.2 γ.length
  exact Q'.abs_le_of_bounds (Q'.le_trans' _ _ _ (Q'.neg_le_neg hp) h.1) (Q'.le_trans' _ _ _ h.2 hp)

/-- **SU(2) Wilson lattice decay (STRONG COUPLING ONLY: β₀ = 1/(4·10¹⁴); Wilson action truncated at
Taylor order K, uniform in K and in the volume; also true for U(1), so NOT gap or continuum evidence).**
`Z_W = ∫ Π_{p∈P} T_K(U_p) ≈ c_0^{|P|} · Ξ(gas)` with normalised activities `z_norm`, and the
insertion/removal correlation `U` decays like `(6/7)^R`. -/
theorem su2_link_decay_wilson (N K : Nat) (links : List Z4Link)
    (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
    (hL : ∀ p ∈ P, YMGap.Continuum.SU2ClusterExplore.Lk links N p)
    (y g : List Z4Plaq) (l : List (List Z4Plaq)) (R : Nat)
    (hsep : sepL (torusMetric N) y g (R + 1)) (hG : Good (gas N P) (y :: g :: l)) :
    let z := fun γ => quaternionHaar links.length (prodPoly (FW links N betaH K) γ)
    (quaternionHaar links.length (prodPoly (TK links N betaH K) P)).eqv
      (c0 betaH K ^ P.length * Xi z (incL N) (gas N P)) ∧
    Q'.abs (U z (incL N) y g l) ≤
      (lam ^ R * etaD ^ S N g) * (Xi z (incL N) l * Xi z (incL N) (g :: l)) :=
  ⟨wilson_polyPartition_eq_Xi links N betaH K (Q'.le_of_lt wilson_pass_H.1) P hL,
   link_decay N P hP hbox epsH (by decide) heat_pass.2.1 heat_pass.2.2.1 heat_pass.2.2.2 heat_pass.1 _
    (fun x hx => by
      rw [S_len N x ((linkBox N P hP hbox).size_ok x hx).1]
      exact zn_abs_H links N K x (fun p hp =>
        lk_cover links N p (hL p ((gas_inv N P hP x hx).2.2 p hp)))) y g l R hsep hG⟩

end YMGap.Continuum.SU2WilsonLinkDecay

#print axioms YMGap.Continuum.SU2WilsonLinkDecay.wilson_pass_H
#print axioms YMGap.Continuum.SU2WilsonLinkDecay.zn_abs_H
#print axioms YMGap.Continuum.SU2WilsonLinkDecay.su2_link_decay_wilson
