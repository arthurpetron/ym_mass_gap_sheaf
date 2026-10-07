/-
# Sharp link-KP instances: heat kernel and Wilson at `ε_S = 10⁻¹²` (was `5·10⁻¹⁵`)

**STRONG COUPLING ONLY.** This is a volume-uniform strong-coupling cluster expansion. It is equally true for U(1)
and is NOT mass-gap or continuum evidence. The observable is the insertion/removal correlation `U`.

The grouping constant is `Kc = (3/2)^24 ≈ 1.68·10⁴` (`SU2LinkGroupSharp`). The binding scalar condition is the
decay margin `ε K²(1+η) ≤ λ²η`, which gives the ceiling `ε ≲ 1.04·10⁻¹²`. We use `ε_S = 10⁻¹²`.
* heat kernel: `w_S = 1/20000` (`charEnv ≤ 4w³(1+ε)… ≤ 10⁻¹²`), up from `w_H = 10⁻⁵`;
* Wilson: `β_S = 1/(2·10¹²)` (`2β_S = ε_S`), up from `1/(4·10¹⁴)`.
-/

import YMGap.Continuum.SU2LinkDecaySharp
import YMGap.Continuum.SU2LinkDecayHeat
import YMGap.Continuum.SU2WilsonLinkDecay

namespace YMGap.Continuum.SU2LinkDecaySharpInst

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
open YMGap.Continuum.SU2PolymerIdentity (incL gas polyPartition_eq_Xi)
open YMGap.Continuum.SU2LinkGasBox
open YMGap.Continuum.SU2LinkKPSharp
open YMGap.Continuum.SU2LinkDecaySharp
open YMGap.Continuum.Z4PlaqMetric (torusMetric)
open YMGap.Continuum.HeatKernelPolymerActivityR1 (charEnv charEnv_nonneg)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly fPoly)
open YMGap.Continuum.SU2LinkDecayHeat (lk_cover S_len charEnv_le_of z_abs_zero)
open YMGap.Continuum.SU2WilsonPolymerIdentity (TK FW c0 zn_abs_le wilson_polyPartition_eq_Xi)

def epsS : Q' := Q'.mkPos 1 1000000000000 (by decide)
def wS : Q' := Q'.mkPos 1 20000 (by decide)
def betaS : Q' := Q'.mkPos 1 2000000000000 (by decide)

/-- KP and decay scalar conditions at `ε_S = 10⁻¹²` with `Kc = (3/2)^24`. -/
theorem sharp_pass :
    epsS * Kc * (1 + etaZ) ≤ etaZ ∧ epsS * Kc ≤ 1 ∧ epsS * Kc * Kc * (1 + etaZ) ≤ etaD ∧
      epsS * Kc * ((1 + etaZ) * ((1 + epsS * Kc) + (1 + epsS * Kc))) ≤ etaD := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem charEnv_wS (M : Nat) : charEnv wS M ≤ epsS :=
  charEnv_le_of (by decide) (by decide) (by decide) (by decide) M

theorem z_abs_wS (links : List Z4Link) (N M : Nat) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    Q'.abs (quaternionHaar links.length (prodPoly (fun p => fPoly wS links N p M) γ)) ≤ epsS ^ γ.length := by
  have h := YMGap.Continuum.SU2PolymerActivityHeat.z_abs_le (w := wS) (by decide) M links N γ hc
  have hp := pow_mono (charEnv_nonneg (by decide) M) (charEnv_wS M) γ.length
  exact Q'.abs_le_of_bounds (Q'.le_trans' _ _ _ (Q'.neg_le_neg hp) h.1) (Q'.le_trans' _ _ _ h.2 hp)

/-- **Sharp heat-kernel lattice decay** (STRONG COUPLING ONLY; heat-kernel action spin-truncated at M;
also true for U(1), NOT gap evidence). For `w = 0` or `w = 1/20000`, uniform in M. -/
theorem su2_link_decay_heat_sharp (w : Q') (hw : w = 0 ∨ w = wS) (N M : Nat) (links : List Z4Link)
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
   link_decay N P hP hbox epsS (by decide) sharp_pass.2.1 sharp_pass.2.2.1 sharp_pass.2.2.2 sharp_pass.1 _
    (fun x hx => by
      rw [show S N x = x.length from S_len N x ((linkBox N P hP hbox).size_ok x hx).1]
      rcases hw with hw | hw
      · subst hw; exact z_abs_zero links N M x epsS (by decide)
      · subst hw
        exact z_abs_wS links N M x (fun p hp =>
          lk_cover links N p (hL p ((gas_inv N P hP x hx).2.2 p hp)))) y g l R hsep hG⟩

theorem zn_abs_S (links : List Z4Link) (N K : Nat) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    Q'.abs (quaternionHaar links.length (prodPoly (FW links N betaS K) γ)) ≤ epsS ^ γ.length := by
  have h := zn_abs_le links N betaS K (by decide) (by decide) γ hc
  have hp := pow_mono (Q'.mul_nonneg _ _ (by decide) (by decide)) (by decide : 2 * betaS ≤ epsS) γ.length
  exact Q'.abs_le_of_bounds (Q'.le_trans' _ _ _ (Q'.neg_le_neg hp) h.1) (Q'.le_trans' _ _ _ h.2 hp)

/-- **Sharp Wilson lattice decay** (STRONG COUPLING ONLY: `β_S = 1/(2·10¹²)`; Wilson action truncated at
Taylor order K, uniform in K and the volume; also true for U(1), NOT gap evidence). -/
theorem su2_link_decay_wilson_sharp (N K : Nat) (links : List Z4Link)
    (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)
    (hL : ∀ p ∈ P, YMGap.Continuum.SU2ClusterExplore.Lk links N p)
    (y g : List Z4Plaq) (l : List (List Z4Plaq)) (R : Nat)
    (hsep : sepL (torusMetric N) y g (R + 1)) (hG : Good (gas N P) (y :: g :: l)) :
    let z := fun γ => quaternionHaar links.length (prodPoly (FW links N betaS K) γ)
    (quaternionHaar links.length (prodPoly (TK links N betaS K) P)).eqv
      (c0 betaS K ^ P.length * Xi z (incL N) (gas N P)) ∧
    Q'.abs (U z (incL N) y g l) ≤
      (lam ^ R * etaD ^ S N g) * (Xi z (incL N) l * Xi z (incL N) (g :: l)) :=
  ⟨wilson_polyPartition_eq_Xi links N betaS K (by decide) P hL,
   link_decay N P hP hbox epsS (by decide) sharp_pass.2.1 sharp_pass.2.2.1 sharp_pass.2.2.2 sharp_pass.1 _
    (fun x hx => by
      rw [show S N x = x.length from S_len N x ((linkBox N P hP hbox).size_ok x hx).1]
      exact zn_abs_S links N K x (fun p hp =>
        lk_cover links N p (hL p ((gas_inv N P hP x hx).2.2 p hp)))) y g l R hsep hG⟩

end YMGap.Continuum.SU2LinkDecaySharpInst

#print axioms YMGap.Continuum.SU2LinkDecaySharpInst.sharp_pass
#print axioms YMGap.Continuum.SU2LinkDecaySharpInst.su2_link_decay_heat_sharp
#print axioms YMGap.Continuum.SU2LinkDecaySharpInst.su2_link_decay_wilson_sharp
