/-
# Wilson action, commit 3: Wilson Taylor weights, envelope `B_K ≤ 2β`, and the polymer activity bound

**STRONG COUPLING ONLY (β ≲ 1e-4).** This is a volume-uniform strong-coupling cluster expansion for the
actual Wilson action `exp((β/2) tr U)`, truncated at Taylor order `K` and uniform in `K`. It is equally
true for U(1). It is NOT mass-gap or continuum evidence.

* `wilsonA β k = (β/2)^k / k!`, built from the rational literals `1/2` and `1/(k+1)`. No reciprocal
  operation is used.
* `envelope_le` : for a free rational `0 ≤ β ≤ 1/2`, `B_K := bSum (centred list) ≤ 2β` and `1 ≤ c_0`.
  This is the cross-multiplied form: the normalised envelope satisfies `B_K / c_0 ≤ B_K ≤ 2β`.
* `wilson_z_abs_le` : the unnormalised centred Wilson activity
  `z γ = h(Π_{p∈γ} Σ_{s=1}^{K} c_s χ_s(U_p))` obeys `−(2β)^{|γ|} ≤ z γ ≤ (2β)^{|γ|}`.
* `wilson_pass` : at `β₀ = 1/20000`, `2β₀ ≤ ε = 1/10000`.
-/

import YMGap.Continuum.SU2WilsonCoeffBounds
import YMGap.Continuum.SizeWeightedPolymerKP

namespace YMGap.Continuum.SU2WilsonActivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2WilsonCharacterPower (wCoeff mult)
open YMGap.Continuum.SU2WilsonCoeffBounds
open YMGap.Continuum.SU2PolymerActivityBound
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv
local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

/-- `1/(k+1)` as a literal. -/
def invS (k : Nat) : Q' := ⟨1, k⟩
def half : Q' := ⟨1, 1⟩

theorem invS_pos (k : Nat) : (0 : Q') < invS k := by
  show (0 : Int) * ((k + 1 : Nat) : Int) < 1 * ((0 + 1 : Nat) : Int); omega
theorem invS_le_one (k : Nat) : invS k ≤ 1 := by
  show (1 : Int) * ((0 + 1 : Nat) : Int) ≤ 1 * ((k + 1 : Nat) : Int); omega

/-- STRONG COUPLING ONLY. Wilson Taylor weight `a_k = (β/2)^k / k!`. -/
def wilsonA (β : Q') : Nat → Q'
  | 0 => 1
  | k + 1 => wilsonA β k * β * half * invS k

theorem wilsonA_pos {β : Q'} (hβ : (0 : Q') < β) : ∀ k, (0 : Q') < wilsonA β k
  | 0 => show (0 : Q') < 1 by decide
  | k + 1 => Q'.mul_pos (Q'.mul_pos (Q'.mul_pos (wilsonA_pos hβ k) hβ) (by decide)) (invS_pos k)

theorem wilsonA_nonneg {β : Q'} (hβ : (0 : Q') ≤ β) : ∀ k, (0 : Q') ≤ wilsonA β k
  | 0 => show (0 : Q') ≤ 1 by decide
  | k + 1 => Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (wilsonA_nonneg hβ k) hβ)
      (by decide)) (Q'.le_of_lt (invS_pos k))

/-- `a_k 2^k ≤ β^k`. -/
theorem wilsonA_pow2_le {β : Q'} (hβ : (0 : Q') ≤ β) : ∀ k, wilsonA β k * pow2 k ≤ β ^ k
  | 0 => show (1 : Q') * 1 ≤ 1 by decide
  | k + 1 => by
    let V := PolyExpr.var
    have e : wilsonA β (k + 1) * pow2 (k + 1) ≈ (wilsonA β k * pow2 k) * (β * invS k) * (2 * half) :=
      poly_identity_of_normal_eq (V 0 * V 1 * V 2 * V 3 * (V 4 * V 5))
        (V 0 * V 5 * (V 1 * V 3) * (V 4 * V 2)) (by decide)
        (fun | 0 => wilsonA β k | 1 => β | 2 => half | 3 => invS k | 4 => 2 | _ => pow2 k)
    have h2 : (2 : Q') * half ≈ 1 := by decide
    have hi : β * invS k ≤ β :=
      Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (invS_le_one k) hβ)
        (Q'.le_of_eqv (Q'.mul_one_eqv _))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.mul_one_eqv _))) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg (wilsonA_pow2_le hβ k) hi
      (Q'.pow_nonneg β hβ k) (Q'.mul_nonneg _ _ hβ (Q'.le_of_lt (invS_pos k)))) ?_
    exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)

/-- `Σ_{k≤K} r^k`. -/
def gsum (r : Q') : Nat → Q'
  | 0 => 1
  | K + 1 => gsum r K + r ^ (K + 1)

theorem wsum_le {β : Q'} (hβ : (0 : Q') ≤ β) : ∀ K, wsum (wilsonA β) K ≤ gsum β K
  | 0 => wilsonA_pow2_le hβ 0
  | K + 1 => Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (wsum_le hβ K))
      (Q'.add_le_add_left _ _ _ (wilsonA_pow2_le hβ (K + 1)))

/-- Geometric bound `Σ_{k≤K} r^k + 2 r^{K+1} ≤ 1 + 2r` for `0 ≤ r`, `2r ≤ 1`. -/
theorem geo {r : Q'} (hr : (0 : Q') ≤ r) (h2 : 2 * r ≤ 1) :
    ∀ K, gsum r K + 2 * r ^ (K + 1) ≤ 1 + 2 * r
  | 0 => Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv r)))
  | K + 1 => by
    let V := PolyExpr.var
    let t := r ^ (K + 1)
    have ht : (0 : Q') ≤ t := Q'.pow_nonneg r hr (K + 1)
    have e1 : gsum r (K + 1) + 2 * r ^ (K + 2) ≈ gsum r K + (t + (2 * r) * t) :=
      poly_identity_of_normal_eq (V 0 + V 1 + V 3 * (V 2 * V 1)) (V 0 + (V 1 + V 3 * V 2 * V 1)) (by decide)
        (fun | 0 => gsum r K | 1 => t | 2 => r | _ => 2)
    have e2 : gsum r K + (t + 1 * t) ≈ gsum r K + 2 * t :=
      poly_identity_of_normal_eq (V 0 + (V 1 + .const 1 * V 1)) (V 0 + .const 2 * V 1) (by decide)
        (fun | 0 => gsum r K | _ => t)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h2 ht))) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (geo hr h2 K)

theorem gsum_le {r : Q'} (hr : (0 : Q') ≤ r) (h2 : 2 * r ≤ 1) (K : Nat) : gsum r K ≤ 1 + 2 * r :=
  Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (YMGap.Constructive.QPoly.q_add_zero_eqv _)))
    (Q'.add_le_add_left _ _ _ (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg r hr _)))) (geo hr h2 K)

/-- The centred Wilson list `[(c_s, s) | s = 1..K]`. -/
abbrev wilsonList (β : Q') (K : Nat) : List (Q' × Nat) := wList (wCoeff (wilsonA β) K) K

theorem c0_ge_one {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) : (1 : Q') ≤ wCoeff (wilsonA β) K 0 * dQ 0 :=
  Q'.le_trans' _ _ _ (wCoeff_ge_diag _ (wilsonA_nonneg hβ) 0 K (Nat.zero_le _))
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _)))

/-- **Envelope** (STRONG COUPLING ONLY): for free rational `0 ≤ β`, `2β ≤ 1`,
`bSum (wilsonList β K) ≤ 2β`, uniformly in `K`. Since `c_0 ≥ 1`, the normalised envelope is also `≤ 2β`. -/
theorem envelope_le {β : Q'} (hβ : (0 : Q') ≤ β) (h2 : 2 * β ≤ 1) (K : Nat) :
    bSum (wilsonList β K) ≤ 2 * β := by
  have hE := centred_envelope (wilsonA β) (wilsonA_nonneg hβ) K
  have h1 : bSum (wilsonList β K) + 1 ≤ 1 + 2 * β :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (c0_ge_one hβ K))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hE) (Q'.le_trans' _ _ _ (wsum_le hβ K) (gsum_le hβ h2 K)))
  have h3 := Q'.add_le_add_right _ _ (-1) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (add_neg_cancel_q _ _)))
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (add_neg_cancel_q _ _)))

theorem wilsonList_pos {β : Q'} (hβ : (0 : Q') < β) (K : Nat) :
    ∀ j, j ≤ K → ∀ t ∈ wList (wCoeff (wilsonA β) K) j, (0 : Q') < Q'.abs t.1
  | 0, _, _, ht => nomatch ht
  | j + 1, hj, t, ht => by
    cases ht with
    | head =>
      have hc : (0 : Q') < wCoeff (wilsonA β) K (j + 1) := pos_of_pos_le (wilsonA_pos hβ (j + 1))
        (wCoeff_ge_diag _ (wilsonA_nonneg (Q'.le_of_lt hβ)) (j + 1) K hj)
      show (0 : Q') < Q'.abs (wCoeff (wilsonA β) K (j + 1))
      rw [show Q'.abs (wCoeff (wilsonA β) K (j + 1)) = _ from if_pos (Q'.le_of_lt hc)]; exact hc
    | tail _ h => exact wilsonList_pos hβ K j (by omega) t h

/-- Polymer input list for γ. -/
def wilsonPolymer (β : Q') (K : Nat) : List Z4Plaq → List (Z4Plaq × List (Q' × Nat))
  | [] => []
  | p :: ps => (p, wilsonList β K) :: wilsonPolymer β K ps

theorem wilsonPolymer_ok {β : Q'} (hβ : (0 : Q') < β) (K : Nat) (links : List Z4Link) (N : Nat) :
    ∀ γ : List Z4Plaq, (∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) →
      PolymerOK links N (wilsonPolymer β K γ)
  | [], _ => fun _ hq => nomatch hq
  | p :: ps, hc => fun q hq => by
    cases hq with
    | head => exact ⟨hc p (.head _), wilsonList_pos hβ K K (Nat.le_refl _)⟩
    | tail _ h => exact wilsonPolymer_ok hβ K links N ps (fun r hr => hc r (.tail _ hr)) q h

theorem bProd_wilson_le {β : Q'} (hβ : (0 : Q') ≤ β) (h2 : 2 * β ≤ 1) (K : Nat) :
    ∀ γ : List Z4Plaq, bProd (wilsonPolymer β K γ) ≤ (2 * β) ^ γ.length
  | [] => Q'.le_refl' _
  | _ :: ps => Q'.mul_le_mul_of_nonneg (envelope_le hβ h2 K) (bProd_wilson_le hβ h2 K ps)
      (Q'.mul_nonneg _ _ (by decide) hβ) (bProd_nonneg _)

/-- **Wilson activity bound** (STRONG COUPLING ONLY, β ≲ 1e-4; also true for U(1); NOT mass-gap
evidence). For the unnormalised centred Wilson factor `g_p = Σ_{s=1}^{K} c_s^{(K)} χ_s(U_p)`,
`z γ = quaternionHaar n (Π_{p∈γ} g_p)` satisfies `−(2β)^{|γ|} ≤ z γ ≤ (2β)^{|γ|}`, uniformly in `K`
and in the volume. Shared links are allowed. Cross-multiplied form: `c_0 ≥ 1` (`c0_ge_one`), so the
normalised activity `z γ / c_0^{|γ|}` obeys the same bound. -/
theorem wilson_z_abs_le {β : Q'} (hβ : (0 : Q') < β) (h2 : 2 * β ≤ 1) (K : Nat)
    (links : List Z4Link) (N : Nat) (γ : List Z4Plaq)
    (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    let z := quaternionHaar links.length (polyProd links N (wilsonPolymer β K γ))
    (-((2 * β) ^ γ.length)) ≤ z ∧ z ≤ (2 * β) ^ γ.length := by
  intro z
  have hab := polymer_activity_abs_le (wilsonPolymer β K γ) (wilsonPolymer_ok hβ K links N γ hc)
  have hB := bProd_wilson_le (Q'.le_of_lt hβ) h2 K γ
  exact ⟨Q'.le_trans' _ _ _ (Q'.neg_le_neg hB) hab.1, Q'.le_trans' _ _ _ hab.2 hB⟩

def beta0 : Q' := ⟨1, 19999⟩

/-- Concrete pass: at `β₀ = 1/20000`, `2β₀ ≤ ε = 1/10000` (the KP threshold `epsZ`). -/
theorem wilson_pass : (0 : Q') < beta0 ∧ 2 * beta0 ≤ 1 ∧
    2 * beta0 ≤ YMGap.Continuum.SizeWeightedPolymerKP.epsZ := by decide

end YMGap.Continuum.SU2WilsonActivity

#print axioms YMGap.Continuum.SU2WilsonActivity.envelope_le
#print axioms YMGap.Continuum.SU2WilsonActivity.wilson_z_abs_le
#print axioms YMGap.Continuum.SU2WilsonActivity.wilson_pass
