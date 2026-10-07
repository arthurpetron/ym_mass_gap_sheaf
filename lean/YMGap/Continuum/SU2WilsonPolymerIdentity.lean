/-
# Wilson action, commit 4: Wilson partition function = `c_0^{|P|} · Ξ(normalised link gas)`

**STRONG COUPLING ONLY (β ≲ 1e-4).** This is a volume-uniform strong-coupling cluster expansion for the
actual (Taylor-truncated, uniform in `K`) Wilson action. It is equally true for U(1). It is NOT mass-gap or
continuum evidence.

* `T_split` : `T_K(p) ≅ c_0 · (1 + F_p)` with `F_p = recip(c_0) · g_p` and `g_p = Σ_{s=1}^{K} c_s χ_s(U_p)`.
  This is the ONLY place a reciprocal appears.
* `wilson_polyPartition_eq_Xi` : `quaternionHaar(Π_{p∈P} T_K(p)) ≈ c_0^{|P|} · Ξ(gas P, incL, z_norm)`,
  obtained by reusing the Prover's `SU2PolymerIdentity.polymer_identity` with `c = 1` (no edits to it).
* `zn_abs_le` : `−(2β)^{|γ|} ≤ z_norm γ ≤ (2β)^{|γ|}`.
-/

import YMGap.Continuum.SU2WilsonActivity
import YMGap.Continuum.SU2PolymerIdentity

namespace YMGap.Continuum.SU2WilsonPolymerIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterHaarBound (H haar_coeff)
open YMGap.Continuum.SU2WilsonCharacterPower (cc wCoeff wilsonPoly wilsonPoly_expand)
open YMGap.Continuum.SU2WilsonCoeffBounds (wList dQ)
open YMGap.Continuum.SU2WilsonActivity
open YMGap.Continuum.SU2PolymerActivityBound
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2HaarDisjointSupport (FreeOff)
open YMGap.Continuum.SU2PlaqSupport (idxB free_add free_map plaq_free)
open YMGap.Continuum.SU2ClusterExplore (W Lk)
open YMGap.Continuum.SU2PolymerIdentity (incL gas polymer_identity)
open YMGap.Continuum.SignedPolymerKP (Xi)

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≅ " => RatPolyCoeffEqv

variable (links : List Z4Link) (N : Nat) (β : Q') (K : Nat)

/-- `c_0^{(K)}(β)`. -/
abbrev c0 : Q' := wCoeff (wilsonA β) K 0

/-- STRONG COUPLING ONLY. Truncated Wilson plaquette weight `T_K(U_p) = Σ_{k≤K} (β/2)^k/k! (tr U_p)^k`. -/
def TK (p : Z4Plaq) : RatPoly :=
  wilsonPoly (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord links N p).scalar (wilsonA β) K

/-- Unnormalised centred factor `g_p = Σ_{s=1}^{K} c_s χ_s(U_p)`. -/
abbrev gW (p : Z4Plaq) : RatPoly := charSum links N p (wilsonList β K)

/-- Normalised centred factor `F_p = recip(c_0) · g_p` (the single reciprocal). -/
def FW (p : Z4Plaq) : RatPoly := polySmul (Q'.recip (c0 β K)) (gW links N β K p)

theorem cc_split (p : Z4Plaq) (c : Nat → Q') : ∀ j,
    cc (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord links N p).scalar c j ≅
      polyAdd (polySmul (c 0) polyOne) (charSum links N p (wList c j))
  | 0 => (RatPolyCoeffEqv.add_zero _).symm
  | j + 1 => (RatPolyCoeffEqv.add (cc_split p c j) (RatPolyCoeffEqv.refl _)).trans
      ((RatPolyCoeffEqv.add_assoc _ _ _).trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) (RatPolyCoeffEqv.add_comm _ _)))

variable {β}

theorem c0_ge {hβ : (0 : Q') ≤ β} : (1 : Q') ≤ c0 β K := by
  have h := c0_ge_one hβ K
  have hd : dQ 0 = 1 := rfl
  rw [hd] at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv _))

theorem c0_pos (hβ : (0 : Q') ≤ β) : (0 : Q') < c0 β K :=
  pos_of_pos_le (by decide) (c0_ge K (hβ := hβ))

/-- **Plaquette split** (STRONG COUPLING ONLY): `T_K(p) ≅ c_0 · W F 1 p = c_0 · (1 + F_p)`. -/
theorem T_split (hβ : (0 : Q') ≤ β) (p : Z4Plaq) :
    TK links N β K p ≅ polySmul (c0 β K) (W (FW links N β K) 1 p) := by
  have hr : polySmul (c0 β K) (FW links N β K p) ≅ gW links N β K p :=
    (RatPolyCoeffEqv.smul_assoc _ _ _).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_recip_eqv _ (c0_pos K hβ)) _).trans
        (RatPolyCoeffEqv.one_smul _))
  exact ((wilsonPoly_expand _ _ K).trans (cc_split links N p _ K)).trans
    ((RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) hr.symm).trans (RatPolyCoeffEqv.smul_add _ _ _).symm)

theorem prod_split (hβ : (0 : Q') ≤ β) : ∀ P : List Z4Plaq,
    prodPoly (TK links N β K) P ≅ polySmul (c0 β K ^ P.length) (prodPoly (W (FW links N β K) 1) P)
  | [] => (RatPolyCoeffEqv.one_smul _).symm
  | p :: ps => (RatPolyCoeffEqv.mul (T_split links N K hβ p) (prod_split hβ ps)).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
        ((RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.polyMul_smul_right _ _ _)).trans
          (RatPolyCoeffEqv.smul_assoc _ _ _)))

variable (β)

theorem free_charSum (p : Z4Plaq) : ∀ L : List (Q' × Nat),
    FreeOff (idxB links N p) false (charSum links N p L)
  | [] => fun _ hs => nomatch hs
  | t :: ts => free_add _ _ (free_map _ _ _ (plaq_free links N p t.2)) (free_charSum p ts)

theorem FW_free (p : Z4Plaq) : FreeOff (idxB links N p) false (FW links N β K p) :=
  free_map _ _ _ (free_charSum links N p _)

/-- **Wilson analogue of `polyPartition_eq_Xi`** (STRONG COUPLING ONLY, β ≲ 1e-4; also true for U(1);
NOT mass-gap evidence): `Z_W := ∫ Π_{p∈P} T_K(U_p) ≈ c_0^{|P|} · Ξ(gas P)`, with link-incompatibility and
normalised true activities `z_norm γ = ∫ Π_{p∈γ} F_p`. -/
theorem wilson_polyPartition_eq_Xi (hβ : (0 : Q') ≤ β) (P : List Z4Plaq) (hL : ∀ p ∈ P, Lk links N p) :
    (quaternionHaar links.length (prodPoly (TK links N β K) P)).eqv
      (c0 β K ^ P.length *
        Xi (fun γ => quaternionHaar links.length (prodPoly (FW links N β K) γ)) (incL N) (gas N P)) :=
  Q'.eqv_trans _ _ _ (haar_coeff (prod_split links N K hβ P) _)
    (Q'.eqv_trans _ _ _ (haar_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _
      (polymer_identity N links.length links (FW links N β K) 1 (Q'.eqv_refl 1)
        (fun p => FW_free links N β K p) P.length P (Nat.le_refl _) hL)))

/-! ## Normalised activity bound -/

theorem prodFW (γ : List Z4Plaq) : prodPoly (FW links N β K) γ ≅
    polySmul (Q'.recip (c0 β K) ^ γ.length) (polyProd links N (wilsonPolymer β K γ)) := by
  induction γ with
  | nil => exact (RatPolyCoeffEqv.one_smul _).symm
  | cons p ps ih =>
    exact (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) ih).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
        ((RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.polyMul_smul_right _ _ _)).trans
          (RatPolyCoeffEqv.smul_assoc _ _ _)))

theorem recip_le_one (hβ : (0 : Q') ≤ β) : Q'.recip (c0 β K) ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (c0_ge K (hβ := hβ)) (Q'.le_of_lt (Q'.recip_pos _)))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recip_eqv _ (c0_pos K hβ)))))

theorem pow_le_one {r : Q'} (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) : ∀ n : Nat, r ^ n ≤ 1
  | 0 => Q'.le_refl' _
  | n + 1 => Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg h1 (pow_le_one h0 h1 n) (by decide)
      (Q'.pow_nonneg r h0 n)) (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-- **Normalised Wilson activity bound** (STRONG COUPLING ONLY): `−(2β)^{|γ|} ≤ z_norm γ ≤ (2β)^{|γ|}`,
uniform in `K` and in the volume. This is the input for the link-KP environment. -/
theorem zn_abs_le (hβ : (0 : Q') < β) (h2 : 2 * β ≤ 1) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    let zn := quaternionHaar links.length (prodPoly (FW links N β K) γ)
    (-((2 * β) ^ γ.length)) ≤ zn ∧ zn ≤ (2 * β) ^ γ.length := by
  intro zn
  have hz := wilson_z_abs_le hβ h2 K links N γ hc
  let z := quaternionHaar links.length (polyProd links N (wilsonPolymer β K γ))
  let B := (2 * β) ^ γ.length
  let ρ := Q'.recip (c0 β K) ^ γ.length
  have hB : (0 : Q') ≤ B := Q'.pow_nonneg _ (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt hβ)) _
  have hρ0 : (0 : Q') ≤ ρ := Q'.pow_nonneg _ (Q'.le_of_lt (Q'.recip_pos _)) _
  have hρ1 : ρ ≤ 1 := pow_le_one (Q'.le_of_lt (Q'.recip_pos _)) (recip_le_one β K (Q'.le_of_lt hβ)) _
  have he : zn ≈ ρ * z := Q'.eqv_trans _ _ _ (haar_coeff (prodFW links N β K γ) _) (haar_smul _ _ _)
  have hρB : ρ * B ≤ B := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hρ1 hB)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  refine ⟨?_, Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hz.2 hρ0) hρB)⟩
  refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hρB) (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_neg_eqv ρ B))) ?_)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hz.1 hρ0) (Q'.le_of_eqv (Q'.eqv_symm he))

end YMGap.Continuum.SU2WilsonPolymerIdentity

#print axioms YMGap.Continuum.SU2WilsonPolymerIdentity.T_split
#print axioms YMGap.Continuum.SU2WilsonPolymerIdentity.wilson_polyPartition_eq_Xi
#print axioms YMGap.Continuum.SU2WilsonPolymerIdentity.zn_abs_le
