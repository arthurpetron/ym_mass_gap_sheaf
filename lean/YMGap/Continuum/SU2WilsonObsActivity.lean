/-
# R1 commit 22: observable-modified Wilson activities and their bound (uniform in K)

ADDITIVE.  **Labels:** strong coupling; Wilson action (Taylor-truncated at K, uniform in K); also
true for U(1), not gap evidence.  Realizer's files are imported, not edited.

* `gWo S r`: the observable factor `F_r` (r ∉ S) or `(F_r + χ_r) + χ_r F_r` (r ∈ S), with
  `F = FW` the normalised Wilson factor of `SU2WilsonPolymerIdentity`.
* `gWo_cs`: `gWo S r ≅ charSum r (oL S r)` for an explicit list (scaled Wilson list, then
  `(1,1)`, then the χ₁-shifted list via `chi1_mul_succ`).
* `bSum_oL`: `bSum(oL S r) ≤ ε` (r ∉ S) or `≤ ε + (2 + (ε + ε))` (r ∈ S) when `2β ≤ ε`.
* `zW_bound`: `|zW S γ| ≤ Dw^{|S|} ε^{|γ|}` for nodup γ, when `ε + (2+(ε+ε)) ≤ Dw·ε` and `1 ≤ Dw`.
-/

import YMGap.Continuum.SU2LinkDecaySharpInst
import YMGap.Continuum.SU2ObsActivity

namespace YMGap.Continuum.SU2WilsonObsActivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterHaarBound (haar_coeff)
open YMGap.Continuum.SU2WilsonActivity
open YMGap.Continuum.SU2PolymerActivityBound
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2HaarDisjointSupport
open YMGap.Continuum.SU2PlaqSupport
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (plaqCharacter)
open YMGap.Continuum.SU2WilsonPolymerIdentity (FW FW_free c0 c0_pos recip_le_one)
open YMGap.Continuum.SU2ObsActivity (cnt cnt_le)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

local infix:50 " ≅ " => RatPolyCoeffEqv

variable (links : List Z4Link) (N : Nat)

/-! ## Coefficient lists -/

def scaleL (ρ : Q') : List (Q' × Nat) → List (Q' × Nat)
  | [] => []
  | t :: ts => (ρ * t.1, t.2) :: scaleL ρ ts

/-- χ₁-shift: `χ₁ χ₀ = χ₁`, `χ₁ χ_{n+1} = χ_{n+2} + χ_n`. -/
def shiftL : List (Q' × Nat) → List (Q' × Nat)
  | [] => []
  | (c, 0) :: ts => (c, 1) :: shiftL ts
  | (c, n + 1) :: ts => (c, n + 2) :: (c, n) :: shiftL ts

def oL (L : List (Q' × Nat)) (S : List Z4Plaq) (r : Z4Plaq) : List (Q' × Nat) :=
  if r ∈ S then L ++ ((1, 1) :: shiftL L) else L

theorem cs_append (p : Z4Plaq) : ∀ A B : List (Q' × Nat),
    charSum links N p (A ++ B) ≅ polyAdd (charSum links N p A) (charSum links N p B)
  | [], _ => (RatPolyCoeffEqv.zero_add _).symm
  | _ :: A, B => (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) (cs_append p A B)).trans
      (RatPolyCoeffEqv.add_assoc _ _ _).symm

theorem cs_scale (ρ : Q') (p : Z4Plaq) : ∀ L : List (Q' × Nat),
    charSum links N p (scaleL ρ L) ≅ polySmul ρ (charSum links N p L)
  | [] => (RatPolyCoeffEqv.smul_zero ρ).symm
  | _ :: L => (RatPolyCoeffEqv.add (RatPolyCoeffEqv.smul_assoc _ _ _).symm (cs_scale ρ p L)).trans
      (RatPolyCoeffEqv.smul_add _ _ _).symm

theorem chi_cs (p : Z4Plaq) : ∀ L : List (Q' × Nat),
    polyMul (plaqCharacter links N p 1) (charSum links N p L) ≅ charSum links N p (shiftL L)
  | [] => RatPolyCoeffEqv.mul_zero_right _
  | (c, 0) :: L => (RatPolyCoeffEqv.mul_add_right _ _ _).trans (RatPolyCoeffEqv.add
      ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
        (RatPolyCoeffEqv.smul c (RatPolyCoeffEqv.mul_one _))) (chi_cs p L))
  | (c, n + 1) :: L => (RatPolyCoeffEqv.mul_add_right _ _ _).trans ((RatPolyCoeffEqv.add
      ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans ((RatPolyCoeffEqv.smul c
        (YMGap.Continuum.SU2WilsonCharacterPower.chi1_mul_succ _ n)).trans (RatPolyCoeffEqv.smul_add _ _ _)))
      (chi_cs p L)).trans (RatPolyCoeffEqv.add_assoc _ _ _))

/-! ## Observable factors -/

variable (β : Q') (K : Nat)

abbrev chi (r : Z4Plaq) : RatPoly := plaqCharacter links N r 1

def gWo (S : List Z4Plaq) (r : Z4Plaq) : RatPoly :=
  if r ∈ S then polyAdd (polyAdd (FW links N β K r) (chi links N r)) (polyMul (chi links N r) (FW links N β K r))
  else FW links N β K r

/-- `zW S γ = ∫ Π_{r∈γ} gWo S r`. -/
def zW (S γ : List Z4Plaq) : Q' := quaternionHaar links.length (prodPoly (gWo links N β K S) γ)

abbrev rL : List (Q' × Nat) := scaleL (Q'.recip (c0 β K)) (wilsonList β K)

theorem gWo_free (S : List Z4Plaq) (r : Z4Plaq) : FreeOff (idxB links N r) false (gWo links N β K S r) := by
  unfold gWo
  split
  · exact free_add _ _ (free_add _ _ (FW_free links N β K r) (plaq_free links N r 1))
      (free_mul _ _ (plaq_free links N r 1) (FW_free links N β K r))
  · exact FW_free links N β K r

theorem gWo_cs (S : List Z4Plaq) (r : Z4Plaq) :
    gWo links N β K S r ≅ charSum links N r (oL (rL β K) S r) := by
  have hF : FW links N β K r ≅ charSum links N r (rL β K) := (cs_scale links N _ r _).symm
  unfold gWo oL
  split
  · refine (RatPolyCoeffEqv.add_assoc _ _ _).trans (RatPolyCoeffEqv.trans ?_ (cs_append links N r _ _).symm)
    exact RatPolyCoeffEqv.add hF (RatPolyCoeffEqv.add (RatPolyCoeffEqv.one_smul _).symm
      ((RatPolyCoeffEqv.mul_left _ hF).trans (chi_cs links N r _)))
  · exact hF

def obsPoly (S : List Z4Plaq) : List Z4Plaq → List (Z4Plaq × List (Q' × Nat))
  | [] => []
  | r :: γ => (r, oL (rL β K) S r) :: obsPoly S γ

theorem prod_cs (S : List Z4Plaq) : ∀ γ : List Z4Plaq,
    prodPoly (gWo links N β K S) γ ≅ polyProd links N (obsPoly β K S γ)
  | [] => RatPolyCoeffEqv.refl _
  | r :: γ => RatPolyCoeffEqv.mul (gWo_cs links N β K S r) (prod_cs S γ)

/-! ## Envelope -/

theorem ofInt_nn (s : Nat) : (0 : Q') ≤ Q'.ofInt ((s : Int) + 1) := by
  show (0 : Int) * ((0 + 1 : Nat) : Int) ≤ ((s : Int) + 1) * ((0 + 1 : Nat) : Int)
  omega

theorem bs_append : ∀ A B : List (Q' × Nat), bSum (A ++ B) ≤ bSum A + bSum B
  | [], B => Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
  | t :: A, B => by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (bs_append A B)) (Q'.le_of_eqv ?_)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + (V 1 + V 2)) (V 0 + V 1 + V 2) (by decide)
      (fun | 0 => Q'.abs t.1 * Q'.ofInt ((t.2 : Int) + 1) | 1 => bSum A | _ => bSum B)

theorem bs_scale {ρ : Q'} (h0 : (0 : Q') ≤ ρ) (h1 : ρ ≤ 1) : ∀ L : List (Q' × Nat), bSum (scaleL ρ L) ≤ bSum L
  | [] => Q'.le_refl' _
  | t :: L => Q'.add_le_add (Q'.mul_le_mul_of_nonneg_right _ _ _
      (YMGap.Constructive.TrigBound.abs_mul_le_of_abs_le_one (by rw [ExpNeg.abs_of_nonneg h0]; exact h1))
      (ofInt_nn _)) (bs_scale h0 h1 L)

theorem comb (x a b d e R L : Q') (h : (a + b).eqv (d + e)) (hR : R ≤ L + L) :
    x * a + (x * b + R) ≤ (x * d + L) + (x * e + L) := by
  let V := PolyExpr.var
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq (V 0 * V 1 + (V 0 * V 2 + V 3))
    (V 0 * (V 1 + V 2) + V 3) (by decide) (fun | 0 => x | 1 => a | 2 => b | _ => R)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ h)) hR) (Q'.le_of_eqv ?_))
  exact poly_identity_of_normal_eq (V 0 * (V 1 + V 2) + (V 3 + V 3)) ((V 0 * V 1 + V 3) + (V 0 * V 2 + V 3))
    (by decide) (fun | 0 => x | 1 => d | 2 => e | _ => L)

theorem comb0 (x a d R L : Q') (h : a.eqv (d + d)) (hR : R ≤ L + L) :
    x * a + R ≤ (x * d + L) + (x * d + L) := by
  let V := PolyExpr.var
  refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ h)) hR) (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq (V 0 * (V 1 + V 1) + (V 3 + V 3)) ((V 0 * V 1 + V 3) + (V 0 * V 1 + V 3))
    (by decide) (fun | 0 => x | 1 => d | _ => L)

theorem bs_shift : ∀ L : List (Q' × Nat), bSum (shiftL L) ≤ bSum L + bSum L
  | [] => by decide
  | (c, 0) :: L => comb0 _ _ _ _ _ (show (Q'.ofInt (((1 : Nat) : Int) + 1)).eqv
      (Q'.ofInt (((0 : Nat) : Int) + 1) + Q'.ofInt (((0 : Nat) : Int) + 1)) by decide) (bs_shift L)
  | (c, n + 1) :: L => comb _ _ _ _ _ _ _ (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (YMGap.Continuum.RingNormaliser.ofInt_add _ _))
      (Q'.eqv_trans _ _ _ (by rw [show ((n + 2 : Nat) : Int) + 1 + ((n : Int) + 1) =
        ((n + 1 : Nat) : Int) + 1 + (((n + 1 : Nat) : Int) + 1) by omega]; exact Q'.eqv_refl _)
        (YMGap.Continuum.RingNormaliser.ofInt_add _ _))) (bs_shift L)

theorem bSum_oL {ε : Q'} (hβ : (0 : Q') < β) (h2 : 2 * β ≤ 1) (hε : 2 * β ≤ ε) (S : List Z4Plaq) (r : Z4Plaq) :
    bSum (oL (rL β K) S r) ≤ (if r ∈ S then ε + (2 + (ε + ε)) else ε) := by
  have hA : bSum (rL β K) ≤ ε := Q'.le_trans' _ _ _ (bs_scale (Q'.le_of_lt (Q'.recip_pos _))
    (recip_le_one β K (Q'.le_of_lt hβ)) _) (Q'.le_trans' _ _ _ (envelope_le (Q'.le_of_lt hβ) h2 K) hε)
  unfold oL
  split
  · refine Q'.le_trans' _ _ _ (bs_append _ _) (Q'.add_le_add hA (Q'.add_le_add (by decide) ?_))
    exact Q'.le_trans' _ _ _ (bs_shift _) (Q'.add_le_add hA hA)
  · exact hA

/-! ## Positivity of coefficients and the polymer bound -/

theorem scale_pos {ρ c : Q'} (hρ : (0 : Q') < ρ) (hc : (0 : Q') < Q'.abs c) : (0 : Q') < Q'.abs (ρ * c) :=
  if h : (0 : Q') < Q'.abs (ρ * c) then h else by
    have hle : Q'.abs (ρ * c) ≤ 0 := Int.not_lt.mp h
    let r := Q'.recip ρ
    have he : c.eqv (r * (ρ * c)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv c)) (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_recip_eqv ρ hρ))) ?_)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 * V 2) (V 1 * (V 0 * V 2)) (by decide)
        (fun | 0 => ρ | 1 => r | _ => c)
    have h3 : Q'.abs c ≤ 0 := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hle (Q'.abs_nonneg _))
        (Q'.le_of_eqv (YMGap.Constructive.Q'.mul_zero_eqv _))))
    have h4 : Q'.abs c < Q'.abs c := Q'.lt_of_le_of_lt h3 hc
    exact absurd h4 (Int.lt_irrefl _)

theorem scaleL_pos {ρ : Q'} (hρ : (0 : Q') < ρ) : ∀ L : List (Q' × Nat), (∀ t ∈ L, (0 : Q') < Q'.abs t.1) →
    ∀ t ∈ scaleL ρ L, (0 : Q') < Q'.abs t.1
  | [], _, _, ht => nomatch ht
  | u :: L, h, t, ht => by
    cases ht with
    | head => exact scale_pos hρ (h u List.mem_cons_self)
    | tail _ ht => exact scaleL_pos hρ L (fun v hv => h v (List.mem_cons_of_mem _ hv)) t ht

theorem shiftL_pos : ∀ L : List (Q' × Nat), (∀ t ∈ L, (0 : Q') < Q'.abs t.1) →
    ∀ t ∈ shiftL L, (0 : Q') < Q'.abs t.1
  | [], _, _, ht => nomatch ht
  | (c, 0) :: L, h, t, ht => by
    cases ht with
    | head => exact h (c, 0) List.mem_cons_self
    | tail _ ht => exact shiftL_pos L (fun v hv => h v (List.mem_cons_of_mem _ hv)) t ht
  | (c, n + 1) :: L, h, t, ht => by
    cases ht with
    | head => exact h (c, n + 1) List.mem_cons_self
    | tail _ ht =>
      cases ht with
      | head => exact h (c, n + 1) List.mem_cons_self
      | tail _ ht => exact shiftL_pos L (fun v hv => h v (List.mem_cons_of_mem _ hv)) t ht

theorem obsPoly_ok (hβ : (0 : Q') < β) (S : List Z4Plaq) : ∀ γ : List Z4Plaq,
    (∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) → PolymerOK links N (obsPoly β K S γ)
  | [], _ => fun _ hq => nomatch hq
  | p :: ps, hc => fun q hq => by
    cases hq with
    | head =>
      refine ⟨hc p List.mem_cons_self, ?_⟩
      have hA := scaleL_pos (Q'.recip_pos (c0 β K)) _ (wilsonList_pos hβ K K (Nat.le_refl _))
      show ∀ t ∈ oL (rL β K) S p, _
      unfold oL
      split
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hA t ht
        · cases ht with
          | head => decide
          | tail _ ht => exact shiftL_pos _ hA t ht
      · exact hA
    | tail _ h => exact obsPoly_ok hβ S ps (fun r hr => hc r (List.mem_cons_of_mem _ hr)) q h

variable {Dw ε : Q'} (hε0 : (0 : Q') ≤ ε) (hD1 : (1 : Q') ≤ Dw) (hDε : ε + (2 + (ε + ε)) ≤ Dw * ε)

include hε0 hD1 hDε in
theorem bProd_obs (hβ : (0 : Q') < β) (h2 : 2 * β ≤ 1) (hε : 2 * β ≤ ε) (S : List Z4Plaq) :
    ∀ γ : List Z4Plaq, bProd (obsPoly β K S γ) ≤ Dw ^ cnt S γ * ε ^ γ.length
  | [] => by show (1 : Q') ≤ 1 * 1; decide
  | r :: γ => by
    have hDw0 : (0 : Q') ≤ Dw := Q'.le_trans' _ _ _ (by decide) hD1
    have hc : bSum (oL (rL β K) S r) ≤ (if r ∈ S then Dw * ε else ε) := by
      have := bSum_oL β K hβ h2 hε S r
      split
      · rw [if_pos ‹_›] at this; exact Q'.le_trans' _ _ _ this hDε
      · rw [if_neg ‹_›] at this; exact this
    have hc0 : (0 : Q') ≤ (if r ∈ S then Dw * ε else ε) := by
      split
      · exact Q'.mul_nonneg _ _ hDw0 hε0
      · exact hε0
    refine Q'.le_trans' _ _ _ (YMGap.Constructive.Q'.mul_le_mul_of_nonneg hc
      (bProd_obs hβ h2 hε S γ) hc0 (bProd_nonneg _)) (Q'.le_of_eqv ?_)
    show Q'.eqv _ (Dw ^ (cnt S γ + (if r ∈ S then 1 else 0)) * (ε * ε ^ γ.length))
    let V := PolyExpr.var
    by_cases h : r ∈ S
    · rw [if_pos h, if_pos h]
      show Q'.eqv _ (Dw * Dw ^ cnt S γ * _)
      exact poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3)) (V 0 * V 2 * (V 1 * V 3)) (by decide)
        (fun | 0 => Dw | 1 => ε | 2 => Dw ^ cnt S γ | _ => ε ^ γ.length)
    · rw [if_neg h, if_neg h]
      show Q'.eqv _ (Dw ^ cnt S γ * _)
      exact poly_identity_of_normal_eq (V 1 * (V 2 * V 3)) (V 2 * (V 1 * V 3)) (by decide)
        (fun | 1 => ε | 2 => Dw ^ cnt S γ | _ => ε ^ γ.length)

include hε0 hD1 hDε in
/-- **Observable Wilson activity bound (PROVED; uniform in K).** -/
theorem zW_bound (hβ : (0 : Q') < β) (h2 : 2 * β ≤ 1) (hε : 2 * β ≤ ε) (S γ : List Z4Plaq) (hn : γ.Nodup)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    Q'.abs (zW links N β K S γ) ≤ Dw ^ S.length * ε ^ γ.length := by
  have he := haar_coeff (prod_cs links N β K S γ) links.length
  have hab := polymer_activity_abs_le (obsPoly β K S γ) (obsPoly_ok links N β K hβ S γ hc)
  have hB := Q'.le_trans' _ _ _ (bProd_obs β K hε0 hD1 hDε hβ h2 hε S γ)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (YMGap.Continuum.SU2LinkGasBox.pow_mono_exp hD1 (cnt_le S γ hn))
      (Q'.pow_nonneg _ hε0 _))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he)) (Q'.abs_le_of_bounds ?_ ?_)
  · exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hB) hab.1
  · exact Q'.le_trans' _ _ _ hab.2 hB

theorem gWo_nil : gWo links N β K [] = FW links N β K :=
  funext fun r => by unfold gWo; rw [if_neg List.not_mem_nil]

end YMGap.Continuum.SU2WilsonObsActivity
