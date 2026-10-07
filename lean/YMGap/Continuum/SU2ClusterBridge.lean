/-
# Clustering bridge for the single-plaquette observable (partial): geometry, Z > 0, explicit distance

ADDITIVE.  **Labels:** STRONG COUPLING β_S = 1/(2·10¹²); Wilson `T_K` at fixed K (the clustering constant
`Cw` and rate `λ = 6/7` are uniform in K, but `Z` is not); also true for U(1), not gap evidence.

**Geometry check.** `SU2WilsonTrunc.wilson_trunc_ratio` is stated for an arbitrary link list, side `N` and
plaquette list `P ⊆ torusPlaquettes N` (nodup, links covered).  Instantiated at `links = torusLinks (2M)`,
`N = 2M`, `P = torusPlaquettes (2M)`, `β = β_S`, it is the same torus, plaquette set and `T_K` weight as
`rpB hM β_S K` (`ZW … []` is literally `∫ Π T_K`).  No mismatch.  The distance is the torus ℓ∞ metric on base
vertices (`torusMetric`, with wrap-around).

Proved:
* `lk_torus`: every torus plaquette has its links in `torusLinks`.
* `Z_pos`: `0 < Z` with `Z = ZW (torusLinks 2M) (2M) K (torusPlaquettes 2M) []`, constructively in Q′.
* `dist_mir_shift`: for a spatial plaquette `p` based at time 1, and `n + 1 ≤ M`,
  `ld (τ_n p) (mir p) = n + 1`.  The mirror is at time 0, `τ_n p` is at time `1+n`, and there is no wrap since
  `1+n ≤ M`.
* `cov_decay`: `|Z_{ab}/Z − (Z_a/Z)(Z_b/Z)| ≤ Cw · λ^(n+1)` for `a = mir p`, `b = τ_n p`.
* **`torus_gap_bridge`**: `torus_gap_cond` with `hcl` discharged from `cov_decay`, given the identification
  `hcov` below.  Constants: `C = Z·(Cw·λ)`, `q = λ = 6/7`, so the ratio bound is per two steps in `λ² = (6/7)²`.

**Carried (OPEN):**
* `hcov`: `G n ≈ Z · (Z_{ab}/Z − (Z_a/Z)(Z_b/Z))` for `n ≤ 2X`.  This identifies the RP correlator
  `rpB F̃ (τ_n F̃)`, with `F̃ = χ_p − ⟨χ_p⟩`, as `Z` times the covariance.  It needs `Θχ_p ≡ χ_{mir p}` (from
  the `theta_TK` pattern), the bilinear expansion of `rpB` against `ZW`, and equal one-point means
  `⟨χ_{mir p}⟩ = ⟨χ_{τ_n p}⟩ = ⟨χ_p⟩` (time-shift and reflection invariance).
* `hsup`, `hshift`: Realizer's (as in commit 35).
* Range: `2X + 1 ≤ M`, i.e. `X ≲ N_t/4`.
-/

import YMGap.Continuum.SU2TorusGapCond
import YMGap.Continuum.SU2WilsonTrunc
import YMGap.Continuum.SU2TimeShift
import YMGap.Continuum.SU2TorusRPTorusZ

namespace YMGap.Continuum.SU2ClusterBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2WilsonTrunc (ZW ZW_eq Cw hz)
open YMGap.Continuum.PolymerLatticeDecay (lam)
open YMGap.Continuum.Z4PlaqMetric (torusMetric ld4 tw tw_self)
open YMGap.Continuum.SU2TimeShift (shv vs)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPCSShape (rpB PtSup)
open YMGap.Continuum.SU2LogConvexGap (le_e e_le)
open YMGap.Continuum.SU2TorusGapCond (E torus_gap_cond)

variable {M : Nat} (hM : 1 ≤ M) (K : Nat)

local notation "Ls" => torusLinks (2 * M)
local notation "Ps" => torusPlaquettes (2 * M)

include hM in
theorem lk_torus : ∀ r ∈ Ps, YMGap.Continuum.SU2ClusterExplore.Lk Ls (2 * M) r := fun r hr ℓ h =>
  YMGap.Continuum.SU2TorusRPTorusZ.plaqL_mem hM r hr ℓ h

theorem pow_pos' {a : Q'} (ha : (0 : Q') < a) : ∀ n : Nat, (0 : Q') < a ^ n
  | 0 => by show (0 : Int) * 1 < 1 * 1; decide
  | n + 1 => Q'.mul_pos ha (pow_pos' ha n)

/-- `Z := ∫ Π_{torus} T_K` at `β_S`. -/
abbrev Z : Q' := ZW Ls (2 * M) K Ps []

include hM in
/-- **`Z > 0` (PROVED, constructive in Q′).** -/
theorem Z_pos : (0 : Q') < Z K (M := M) := by
  have hP := torusPlaquettes_nodup (2 * M)
  have hbox : ∀ p, p ∈ Ps → p ∈ Ps := fun _ h => h
  have hz' := hz Ls (2 * M) K Ps hP hbox (lk_torus hM)
  have hG : YMGap.Continuum.PolymerChainDecay.Good (YMGap.Continuum.SU2PolymerIdentity.gas (2 * M) Ps)
      (YMGap.Continuum.SU2PolymerIdentity.gas (2 * M) Ps) :=
    ⟨YMGap.Continuum.SU2LinkGasBox.gas_nodup (2 * M) Ps hP, fun _ h => h⟩
  have h0 := YMGap.Continuum.SU2LinkKPSharp.envL_pos (2 * M) Ps hP hbox
    YMGap.Continuum.SU2LinkDecaySharpInst.epsS (by decide) YMGap.Continuum.SU2LinkDecaySharpInst.sharp_pass.1 _ hz' _ hG
  rw [YMGap.Continuum.SU2LinkKPSharp.Xi_zc (2 * M) Ps _ _ hG.2] at h0
  have hc := pow_pos' (YMGap.Continuum.SU2WilsonPolymerIdentity.c0_pos
    (β := YMGap.Continuum.SU2LinkDecaySharpInst.betaS) K (by decide)) (torusPlaquettes (2 * M)).length
  exact Q'.pos_of_lt_of_le (Q'.mul_pos hc h0) (Q'.ge_of_eqv (ZW_eq Ls (2 * M) K Ps [] (lk_torus hM)))

include hM in
/-- **Explicit torus distance (PROVED).** -/
theorem dist_mir_shift (b c d : Nat) (P : Z4Plane)
    (hP : YMGap.Continuum.SU2TorusRPThetaTK.isT (dirsOf P).1 = false) (n : Nat) (hn : n + 1 ≤ M) :
    (torusMetric (2 * M)).ld (shv (2 * M) n ((1, b, c, d), P)) (mir M ((1, b, c, d), P)) = n + 1 := by
  have hm : mir M ((1, b, c, d), P) = ((0, b, c, d), P) := by
    unfold mir; rw [hP]; rfl
  rw [hm]
  show ld4 (tw (2 * M)) ((1 + n) % (2 * M), b, c, d) (0, b, c, d) = n + 1
  rw [Nat.mod_eq_of_lt (by omega)]
  unfold ld4
  show max (max (tw (2 * M) (1 + n) 0) (tw (2 * M) b b)) (max (tw (2 * M) c c) (tw (2 * M) d d)) = n + 1
  rw [tw_self, tw_self, tw_self]
  unfold tw YMGap.Continuum.Z4PlaqMetric.dn
  rw [Nat.mod_eq_of_lt (show 1 + n < 2 * M by omega), Nat.zero_mod]
  omega

variable (b c d : Nat) (P : Z4Plane)

/-- The pair `a = mir p`, `b = τ_n p` for `p = ((1,b,c,d),P)`. -/
abbrev pA : Z4Plaq := mir M ((1, b, c, d), P)
abbrev pB (n : Nat) : Z4Plaq := shv (2 * M) n ((1, b, c, d), P)

/-- The normalised covariance of `χ_a` and `χ_b`, in `wilson_trunc_ratio`'s form. -/
abbrev cov (n : Nat) : Q' :=
  ZW Ls (2 * M) K Ps [pA (M := M) b c d P, pB (M := M) b c d P n] * Q'.recip (Z K (M := M)) +
    -((ZW Ls (2 * M) K Ps [pA (M := M) b c d P] * Q'.recip (Z K (M := M))) *
      (ZW Ls (2 * M) K Ps [pB (M := M) b c d P n] * Q'.recip (Z K (M := M))))

include hM in
/-- **Covariance decay at explicit distance (PROVED).** -/
theorem cov_decay (hP : YMGap.Continuum.SU2TorusRPThetaTK.isT (dirsOf P).1 = false) (n : Nat) (hn : n + 1 ≤ M) :
    Q'.abs (cov K b c d P n (M := M)) ≤ Cw * lam ^ (n + 1) := by
  have h := YMGap.Continuum.SU2WilsonTrunc.wilson_trunc_ratio Ls (2 * M) K Ps (torusPlaquettes_nodup _)
    (fun _ h => h) (lk_torus hM) (pA (M := M) b c d P) (pB (M := M) b c d P n)
  rw [dist_mir_shift hM b c d P hP n hn] at h
  exact h

include hM in
/-- **Conditional finite-volume ratio bound with explicit constants (PROVED, conditional).**
STRONG COUPLING β_S = 1/(2·10¹²); Wilson `T_K` at fixed K; also true for U(1), not gap evidence.
`E m = G(2m)`, `C = Z·(Cw·λ)`, `λ = 6/7`. -/
theorem torus_gap_bridge (hP : YMGap.Continuum.SU2TorusRPThetaTK.isT (dirsOf P).1 = false)
    (τ : Nat → RatPoly) (G : Nat → Q') (X : Nat) (hX : 2 * X + 1 ≤ M)
    (hsup : ∀ x, x ≤ X → PtSup (M := M) (τ x))
    (hshift : ∀ x y, x ≤ X → y ≤ X →
      (rpB hM YMGap.Continuum.SU2LinkDecaySharpInst.betaS K (τ x) (τ y)).eqv (G (x + y)))
    (hcov : ∀ n, n ≤ 2 * X → (G n).eqv (Z K (M := M) * cov K b c d P n (M := M)))
    (k e : Nat) (h : k + e ≤ X) :
    E G (k + 1) ^ e * E G k ≤ Z K (M := M) * (Cw * lam) * (lam * lam) ^ (k + e) * E G k ^ e := by
  have hZ := Q'.le_of_lt (Z_pos hM K)
  have hCl : (0 : Q') ≤ Cw * lam :=
    le_e (Q'.le_trans' _ _ _ (Q'.abs_nonneg _) (cov_decay hM K b c d P hP 0 (by omega)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))
  have hl : (0 : Q') ≤ lam := by decide
  refine torus_gap_cond hM (by decide) K τ G X hsup hshift (Q'.mul_nonneg _ _ hZ hCl) hl (fun n hn => ?_) k e h
  refine e_le (hcov n hn) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_abs_self _) hZ) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (cov_decay hM K b c d P hP n (by omega)) hZ) ?_
  refine Q'.le_of_eqv ?_
  show (Z K (M := M) * (Cw * (lam * lam ^ n))).eqv (Z K (M := M) * (Cw * lam) * lam ^ n)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

end YMGap.Continuum.SU2ClusterBridge
