/-
# R1 wall, activity side: an explicit heat-kernel polymer activity obeying `|z| ≤ ε^{|γ|}`

ADDITIVE.  **GROUP-BLIND PLUMBING** for the KP use (U(1) rule).  The activity
envelope is SU(2) heat-kernel arithmetic.

* `wR1 = 1/40`, so `4·w³ = 1/16000 ≤ ε = 1/10000`.
* `plaqEnv M := PlaquetteActivity.plaqActivity wR1 M = Σ_{s=1}^{M} coeffW wR1 s`, where
  `coeffW w s = (s+1)·w^{s(s+2)}` (`BondMovingStep.coeffW`).  This is the excited-character
  mass of one plaquette.  `plaqEnv_le` shows `0 ≤ plaqEnv M ≤ 1/10000` for every truncation M.
* `zHeat M γ := (plaqEnv M)^{|γ|}`: the product over the plaquettes of `γ` of the
  per-plaquette excited mass.  `zHeat_bounds` gives `0 ≤ zHeat ≤ ε^{|γ|}`.
* `heat_kp`: the unconditional degree-24 KP bound (`deg24_kp`) and the one-polymer
  ratio-Lipschitz bound (`deg24_ratio_lip`) for this activity, on any degree-24 gas
  (box `z4Chain` or torus `torusChain N`).

**OPEN (the actual R1 wall):** this does not prove that the Wilson heat-kernel partition
function equals `Ξ` of a gas with activity `zHeat`, or one bounded by it.  The minimal missing
identity is:

  `∫ Π_p (Σ_{s≤M} coeffW w s · χ_s(U_p)) dU  =  Σ_{compatible families}  Π_γ z_true(γ)`,

where `z_true(γ)` is the Haar integral of the connected character products over `γ`.  It
must come with the bound `|z_true(γ)| ≤ zHeat M γ` (characters bounded by dimension, which
is already absorbed in `coeffW`).  No file proves the Haar/character expansion to a polymer
gas.  HKPS was not imported.
-/

import YMGap.Continuum.PolymerRatioLipschitz
import YMGap.Continuum.PlaquetteActivity

namespace YMGap.Continuum.HeatKernelPolymerActivityR1

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.BddLatticeAnimal (BddLattice)
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerRatioLipschitz

def wR1 : Q' := Q'.mkPos 1 40 (by decide)

def plaqEnv (M : Nat) : Q' := plaqActivity wR1 M

theorem wR1_nonneg : (0 : Q') ≤ wR1 := by decide

theorem plaqEnv_le (M : Nat) : (0 : Q') ≤ plaqEnv M ∧ plaqEnv M ≤ epsZ :=
  ⟨plaqActivity_nonneg wR1_nonneg M,
    Q'.le_trans' _ _ _ (plaqActivity_le wR1_nonneg (by decide) M)
      (by decide : Q'.ofNat 4 * HeatKernelGap.heatKernelSep wR1 ≤ epsZ)⟩

variable {BL : BddLattice}

def zHeat (M : Nat) (γ : Poly BL) : Q' := plaqEnv M ^ sz γ

theorem zHeat_bounds (M : Nat) (γ : Poly BL) :
    (0 : Q') ≤ zHeat M γ ∧ zHeat M γ ≤ epsZ ^ sz γ :=
  ⟨Q'.pow_nonneg _ (plaqEnv_le M).1 _,
    pow_le_pow_base' (plaqEnv_le M).1 (plaqEnv_le M).2 _⟩

/-- **KP and ratio-Lipschitz for the explicit heat-kernel activity (PROVED).** -/
theorem heat_kp (hD : BL.D = 24) (d : PL BL) (B : Z4BoxGas BL) (M : Nat) :
    (((0 : Q') ≤ Xi (zHeat M) shareB B.polys ∧
      ∀ p b r, B.polys = p ++ b :: r →
        Xi (zHeat M) shareB (p ++ r) ≤ (1 + etaZ ^ sz b) * Xi (zHeat M) shareB B.polys) ∧
      (1 : Q') ≤ prodm (fun x => 1 + etaZ ^ sz x) B.polys * Xi (zHeat M) shareB B.polys) ∧
    ∀ (y : Poly BL) (S₀ T₀ : List (Poly BL)), S₀.Sublist B.polys → T₀.Sublist B.polys →
      Xi (zHeat M) shareB (y :: S₀) * Xi (zHeat M) shareB T₀ +
          -(Xi (zHeat M) shareB (y :: T₀) * Xi (zHeat M) shareB S₀) ≤
        (epsZ ^ sz y * (five3 ^ sz y + five3 ^ sz y)) *
          (Xi (zHeat M) shareB S₀ * Xi (zHeat M) shareB T₀) ∧
      (0 : Q') ≤ Xi (zHeat M) shareB (y :: S₀) * Xi (zHeat M) shareB T₀ +
          -(Xi (zHeat M) shareB (y :: T₀) * Xi (zHeat M) shareB S₀) +
        (epsZ ^ sz y * (five3 ^ sz y + five3 ^ sz y)) *
          (Xi (zHeat M) shareB S₀ * Xi (zHeat M) shareB T₀) := by
  have hz1 : ∀ X : Poly BL, (0 : Q') ≤ zHeat M X + epsZ ^ sz X :=
    fun X => Q'.zero_le_add _ _ (zHeat_bounds M X).1 (Q'.pow_nonneg _ (by decide) _)
  have hz2 : ∀ X : Poly BL, zHeat M X ≤ epsZ ^ sz X := fun X => (zHeat_bounds M X).2
  exact ⟨deg24_kp hD d B (zHeat M) hz1,
    fun y S₀ T₀ hS hT => deg24_ratio_lip hD d B (zHeat M) hz1 hz2 y S₀ T₀ hS hT⟩

end YMGap.Continuum.HeatKernelPolymerActivityR1

#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.plaqEnv_le
#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.zHeat_bounds
#print axioms YMGap.Continuum.HeatKernelPolymerActivityR1.heat_kp
