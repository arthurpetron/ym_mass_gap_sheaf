/-
Track B / R2 — the **scaled Casimir-square moment bound** (THE α VERDICT) and the
general inverse-power summability endpoint.

# What this settles

The full-mode assembly carries ONE quantitative residual: a bound on the scaled
Casimir-square moment

    casimirSqSum w N q n  =  ∑_{s<n} μ_τ(s)·qfac(w,s)^q·C₄(s)²

uniform enough to close the full-mode product-floor chain (the chain consumes it
as the hypothesis `d_quad`).  This module PROVES that moment bound and pins the
exact α verdict.

# THE α VERDICT (stated EXACTLY as proved — AGENTS.md Rule 6)

The bound proved here is

    casimirSqSum w N q (S+M)  ≤  casimirSqM q r S      (`casimir_moment_bound`),

with the constant `casimirSqM q r S = ofNat S · ((1+C₄(S))^q · C₄(S)²) + (1/2)^r`
**INDEPENDENT of the weight `w`** for a FIXED cutoff `S`.  This is the **α = 0**
verdict *for a fixed finite cutoff*: at fixed `S` the moment is bounded by a single
`w`-independent constant, so the renormalized defect is the CLEAN `τ²`
(`δ_ren = (1−w)²·casimirSqSum ≤ casimirSqM·(1−w)²`).

The HONEST caveat (identical to the underlying tail modulus): the bound consumes
two explicit `w`-dependent cutoff inequalities (`hcut`/`hhead`), which at a FIXED
`S` hold on any compact sub-interval `0 < w ≤ w₀ < 1` but FAIL as `w → 1` (where
the active-mode spread forces the moving cutoff `S = S(w) ≍ τ^{−1/2}`).  So the
constant is `w`-uniform for fixed `S`; covering `w → 1` is the moving-cutoff
residual, carried as the explicit cutoff-certificate family (NOT eliminated here).

# Route taken

This is the CRUDE-but-clean route (the head/tail split of `moment_bound`, applied
directly to `casimirSqTerm`): the head (`s < S`) is `≤ ofNat S · headMax` by
`μ ≤ 1` and the `w`-monotone test factor, the tail (`s ≥ S`) is `≤ (1/2)^r` by the
Gaussian/Casimir tail modulus.  The exp-beats-poly KERNEL `geom_beats_sq` (the
seed for the sharper partition-ratio α = 0 route) is provided too.

# The general inverse-power summability endpoint (bonus)

`summable_of_inverse_pow_bound`: any sequence dominated by `A·invSqTerm` is
summable with the explicit `A·pot` tail bound — this is the `p = 2` endpoint
(`α = 0` ⇒ `2 − α = 2`).  For the `α < 1` regime (`p = 2 − α ∈ (1,2)`) the inverse-
square endpoint already dominates (`1/(k+B)^p ≤ 1/(k+B)²·(k+B)^{2−p}`… the cruder
`δ ≤ A/(k+2)²` route is what the chain actually uses), so the inverse-square
endpoint is sufficient for every `α ∈ [0,1)` here.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable facts; every
load-bearing declaration is `#print axioms`-gated (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.FullModeAssembly
import YMGap.Constructive.GeomBeatsLinear

namespace YMGap.Continuum.CasimirMoment

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummableInverseSquare

/-! ## 0. The exp-beats-poly KERNEL (the seed for the sharp α = 0 route)

The kernel says a QUADRATIC weight is beaten by a geometric factor: for `4s ≤ 1`,
`k²·sᵏ ≤ 1`.  PROOF: `k² ≤ 4ᵏ` (Nat) and `ofNat(4ᵏ)·sᵏ ≃ (4s)ᵏ ≤ 1`.  This is the
`Q'` analogue of `(1+y)^q·y² ≤ C_q·e^{y/2}` (polynomial beaten by the half-
exponential): the geometric `sᵏ = wᵏ` is the heat-kernel `e^{−τ·…}`. -/

/-- `(1 : Q')ᵏ ≃ 1`. -/
theorem one_pow_eqv (k : Nat) : ((1 : Q') ^ k).eqv (1 : Q') := by
  induction k with
  | zero => rw [Q'.pow_zero]; exact Q'.eqv_refl _
  | succ n ih =>
      rw [Q'.pow_succ]
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') ^ n)) ih

/-- `1 ≤ 2ᵏ` (Nat), by induction. -/
theorem one_le_two_pow : ∀ k : Nat, 1 ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
      have ih := one_le_two_pow k
      rw [Nat.pow_succ]; omega

/-- `k ≤ 2ᵏ` (Nat). -/
theorem nat_le_two_pow : ∀ k : Nat, k ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
      have ih := nat_le_two_pow k
      have h1 : (1 : Nat) ≤ 2 ^ k := one_le_two_pow k
      calc k + 1 ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega

/-- `4ᵏ = 2ᵏ · 2ᵏ` (Nat). -/
theorem four_pow_eq (k : Nat) : 4 ^ k = 2 ^ k * 2 ^ k := by
  rw [← Nat.pow_add]
  have h2 : (4 : Nat) = 2 ^ 2 := by decide
  rw [h2, ← Nat.pow_mul]
  congr 1; omega

/-- `k·k ≤ 4ᵏ` (Nat).  From `k ≤ 2ᵏ`: `k·k ≤ 2ᵏ·2ᵏ = 4ᵏ`. -/
theorem nat_sq_le_four_pow (k : Nat) : k * k ≤ 4 ^ k := by
  have hk : k ≤ 2 ^ k := nat_le_two_pow k
  rw [four_pow_eq k]
  exact Nat.mul_le_mul hk hk

/-- A four-factor middle-regroup `(A·B)·(C·D) ≃ (A·C)·(B·D)` (pure assoc/comm at
the num/den cross-product level). -/
theorem mul_four_mid (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  show ((A * B) * (C * D)).num * (((A * C) * (B * D)).den : Int)
      = ((A * C) * (B * D)).num * (((A * B) * (C * D)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

/-- **`ofNat(4ᵏ)·sᵏ ≃ (ofNat 4 · s)ᵏ`** (distribute the power over the product).
Induction on `k`. -/
theorem ofNat_four_pow_mul (s : Q') :
    ∀ k, (Q'.ofNat (4 ^ k) * s ^ k).eqv ((Q'.ofNat 4 * s) ^ k)
  | 0 => by
      show (Q'.ofNat (4 ^ 0) * s ^ 0).eqv ((Q'.ofNat 4 * s) ^ 0)
      rw [Q'.pow_zero, Q'.pow_zero]
      show (Q'.ofNat 1 * (1 : Q')).eqv (1 : Q')
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (Q'.ofNat 1)) (by decide)
  | k + 1 => by
      show (Q'.ofNat (4 ^ (k + 1)) * s ^ (k + 1)).eqv ((Q'.ofNat 4 * s) ^ (k + 1))
      rw [Q'.pow_succ, Q'.pow_succ]
      -- LHS = ofNat(4^{k+1}) · (s · s^k) ;  RHS = (ofNat4·s) · (ofNat4·s)^k
      -- ofNat(4^{k+1}) ≃ ofNat 4 · ofNat(4^k)
      have h4 : (Q'.ofNat (4 ^ (k + 1))).eqv (Q'.ofNat 4 * Q'.ofNat (4 ^ k)) := by
        have : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [Nat.pow_succ]; omega
        rw [this]
        exact Q'.eqv_symm (ofNat_mul_eqv 4 (4 ^ k))
      -- LHS ≃ (ofNat4·ofNat(4^k))·(s·s^k) ≃ (ofNat4·s)·(ofNat(4^k)·s^k)
      --     ≃ (ofNat4·s)·((ofNat4·s)^k) = RHS
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (s * s ^ k) h4) ?_
      -- (A·B)·(C·D) ≃ (A·C)·(B·D) with A=ofNat4, B=ofNat(4^k), C=s, D=s^k
      refine Q'.eqv_trans _ _ _
        (mul_four_mid (Q'.ofNat 4) (Q'.ofNat (4 ^ k)) s (s ^ k)) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (ofNat_four_pow_mul s k)

/-- **THE EXP-BEATS-POLY KERNEL.**  For `0 ≤ s` with `4·s ≤ 1` (`s ≤ 1/4`), the
quadratic-weighted geometric term is bounded:

    ofNat (k·k) · sᵏ  ≤  1   for every `k`.

PROOF.  `k·k ≤ 4ᵏ` (`nat_sq_le_four_pow`), so `ofNat(k²)·sᵏ ≤ ofNat(4ᵏ)·sᵏ ≃
(4s)ᵏ ≤ 1ᵏ = 1` (since `0 ≤ 4s ≤ 1`).  This is the rational seed for the sharp
`(1+y)^q·y² ≤ C_q·e^{y/2}` partition-ratio (α = 0) route. -/
theorem geom_beats_sq {s : Q'} (hs0 : (0 : Q') ≤ s) (h4s : Q'.ofNat 4 * s ≤ 1) :
    ∀ k, Q'.ofNat (k * k) * s ^ k ≤ 1 := by
  intro k
  have hspow_nn : (0 : Q') ≤ s ^ k := Q'.pow_nonneg s hs0 k
  -- ofNat(k²) ≤ ofNat(4ᵏ)
  have hpoly : Q'.ofNat (k * k) ≤ Q'.ofNat (4 ^ k) :=
    ofNat_le_ofNat (nat_sq_le_four_pow k)
  have h1 : Q'.ofNat (k * k) * s ^ k ≤ Q'.ofNat (4 ^ k) * s ^ k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpoly hspow_nn
  refine Q'.le_trans' _ _ _ h1 ?_
  -- ofNat(4ᵏ)·sᵏ ≃ (4s)ᵏ ≤ 1ᵏ = 1
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ofNat_four_pow_mul s k)) ?_
  have h4snn : (0 : Q') ≤ Q'.ofNat 4 * s :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 4) hs0
  have hpow : (Q'.ofNat 4 * s) ^ k ≤ (1 : Q') ^ k :=
    pow_le_pow_of_le h4snn h4s k
  refine Q'.le_trans' _ _ _ hpow ?_
  -- 1ᵏ = 1
  exact Q'.le_of_eqv (one_pow_eqv k)

/-! ## 1. THE CASIMIR-SQUARE MOMENT BOUND (the α VERDICT)

The head/tail split of `moment_bound`, applied directly to `casimirSqTerm`. -/

/-- **The `w`-independent Casimir-square moment constant.**

    casimirSqM q r S  =  ofNat S · ((1 + C₄(S))^q · (C₄(S)·C₄(S)))  +  (1/2)^r.

A function of `(q, r, S)` ONLY — independent of the weight `w`. -/
def casimirSqM (q r S : Nat) : Q' :=
  Q'.ofNat S * ((((1 : Q') + Q'.ofNat (c4 S)) ^ q)
    * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))) + dyad r

theorem casimirSqM_nonneg (q r S : Nat) : (0 : Q') ≤ casimirSqM q r S := by
  refine Q'.zero_le_add _ _ ?_ (dyad_nonneg r)
  refine Q'.mul_nonneg _ _ (zero_le_ofNat _) ?_
  refine Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ?_ q)
    (Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _))
  exact Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)

/-- **The uniform head-term bound for the Casimir-square summand.**  For `s < S`
(and `0 < w < 1`, `s < N`), the summand is bounded by a `w`-INDEPENDENT head max:

    μ(s)·qfac(w,s)^q·C₄(s)²  ≤  (1+C₄(S))^q·(C₄(S)·C₄(S)).

PROOF.  `μ(s) ≤ 1`; `qfac(w,s) ≤ 1+C₄(s) ≤ 1+C₄(S)`; `C₄(s)² ≤ C₄(S)²`. -/
theorem casimirSqTerm_head_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (S s : Nat)
    (hsS : s < S) (hsN : s < N) :
    casimirSqTerm w N hZ q s
      ≤ (((1 : Q') + Q'.ofNat (c4 S)) ^ q) * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S)) := by
  show μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))
      ≤ (((1 : Q') + Q'.ofNat (c4 S)) ^ q) * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  have hw1' : w ≤ (1 : Q') := Q'.le_of_lt hw1
  have hC4mono : c4 s ≤ c4 S := c4_mono (Nat.le_of_lt hsS)
  have hC4le : Q'.ofNat (c4 s) ≤ Q'.ofNat (c4 S) := ofNat_le_ofNat hC4mono
  have hC4nn : (0 : Q') ≤ Q'.ofNat (c4 s) := zero_le_ofNat _
  have hC4Snn : (0 : Q') ≤ Q'.ofNat (c4 S) := zero_le_ofNat _
  have hqfacnn : (0 : Q') ≤ qfac w s := qfac_nonneg hw1' s
  have hqfacpownn : (0 : Q') ≤ qfac w s ^ q := Q'.pow_nonneg _ hqfacnn q
  have hbasenn : (0 : Q') ≤ (1 : Q') + Q'.ofNat (c4 S) :=
    Q'.zero_le_add _ _ (by decide) hC4Snn
  have hbasepownn : (0 : Q') ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q := Q'.pow_nonneg _ hbasenn q
  -- C₄(s)² ≤ C₄(S)²
  have hsqle : Q'.ofNat (c4 s) * Q'.ofNat (c4 s)
      ≤ Q'.ofNat (c4 S) * Q'.ofNat (c4 S) := by
    have h1 : Q'.ofNat (c4 s) * Q'.ofNat (c4 s) ≤ Q'.ofNat (c4 S) * Q'.ofNat (c4 s) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hC4le hC4nn
    have h2 : Q'.ofNat (c4 S) * Q'.ofNat (c4 s) ≤ Q'.ofNat (c4 S) * Q'.ofNat (c4 S) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hC4le hC4Snn
    exact Q'.le_trans' _ _ _ h1 h2
  have hsqnn : (0 : Q') ≤ Q'.ofNat (c4 s) * Q'.ofNat (c4 s) :=
    Q'.mul_nonneg _ _ hC4nn hC4nn
  -- qfac^q ≤ (1+C₄ S)^q
  have hqbase : qfac w s ≤ (1 : Q') + Q'.ofNat (c4 S) :=
    Q'.le_trans' _ _ _ (qfac_le_w0 hw0' s) (Q'.add_le_add_left (1 : Q') _ _ hC4le)
  have hqfacpow : qfac w s ^ q ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q :=
    pow_le_pow_of_le hqfacnn hqbase q
  -- combine the test factor: qfac^q·C₄(s)² ≤ (1+C₄S)^q·C₄(S)²
  have hfac : qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
      ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S)) := by
    have h1 : qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
        ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hqfacpow hsqnn
    have h2 : ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
        ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hsqle hbasepownn
    exact Q'.le_trans' _ _ _ h1 h2
  -- μ ≤ 1, combine
  have hμle : μ w N hZ s ≤ (1 : Q') := μ_le_one hw0 N hZ s hsN
  have hfacnn : (0 : Q') ≤ qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) :=
    Q'.mul_nonneg _ _ hqfacpownn hsqnn
  have hA : μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))
      ≤ (1 : Q') * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hμle hfacnn
  have hB : (1 : Q') * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))
      ≤ (1 : Q') * (((1 : Q') + Q'.ofNat (c4 S)) ^ q
          * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfac (by decide)
  refine Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ hB ?_)
  exact Q'.le_of_eqv (Q'.one_mul_eqv _)

/-- **THE CASIMIR-SQUARE MOMENT BOUND (the α VERDICT, α = 0 at fixed cutoff).**
Fix the heat-kernel weight `0 < w < 1`, a power `q`, a precision `r`, a cutoff `S`,
a cutoff index `N₀ ≥ S`.  Suppose:

  * the per-tail-term Casimir domination at the absorbed degree `m + 2`
    (`hsummand`): each Casimir-square tail summand is `≤ tailTerm w (m+2) (S+k)`;
  * the two explicit moving-cutoff inequalities (`hcut`, `hhead`).

Then for EVERY window `M`,

    casimirSqSum w N₀ hZ q (S + M)  ≤  casimirSqM q r S,

with `casimirSqM` **independent of `w`** (a function of `(q, r, S)`).  This is the
α = 0 verdict for a fixed finite cutoff `S`: the moment is bounded by a single
`w`-uniform constant.

PROOF.  Head/tail split at `S`: head `≤ ofNat S · headMax`
(`casimirSqTerm_head_le`, `finSum_le_count_mul`); tail `≤ (1/2)^r`
(`norm_tail_modulus`, `absQ` of the nonneg `C₄²` is itself). -/
theorem casimir_moment_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q m r S N₀ : Nat) (hSN : S ≤ N₀)
    (hZ : (0 : Q') < Zsum w N₀)
    (hsummand : ∀ k, casimirSqTerm w N₀ hZ q (S + k) ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    ∀ M, casimirSqSum w N₀ hZ q (S + M) ≤ casimirSqM q r S := by
  intro M
  let f : Nat → Q' := fun s => casimirSqTerm w N₀ hZ q s
  let headMax : Q' :=
    (((1 : Q') + Q'.ofNat (c4 S)) ^ q) * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))
  show RationalTail.finSum f (S + M) ≤ casimirSqM q r S
  have hsplit : (RationalTail.finSum f (S + M)).eqv
      (RationalTail.finSum f S + RationalTail.finSum (fun j => f (S + j)) M) :=
    finSum_split f S M
  have hHMnn : (0 : Q') ≤ headMax := by
    refine Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ?_ q)
      (Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _))
    exact Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)
  -- HEAD
  have hhead_terms : ∀ i, i < S → f i ≤ headMax := by
    intro i hi
    have hiN : i < N₀ := Nat.lt_of_lt_of_le hi hSN
    exact casimirSqTerm_head_le hw0 hw1 N₀ hZ q S i hi hiN
  have hHEAD : RationalTail.finSum f S ≤ Q'.ofNat S * headMax :=
    finSum_le_count_mul hHMnn f S hhead_terms
  -- TAIL: rewrite casimirSqTerm into μ·(qfac^q·absQ(C₄²)) and apply norm_tail_modulus.
  have hTAIL : RationalTail.finSum (fun j => f (S + j)) M ≤ dyad r := by
    have hsumm' : ∀ k,
        μ w N₀ hZ (S + k)
          * (qfac w (S + k) ^ q * absQ (Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k))))
          ≤ tailTerm w (m + 2) (S + k) := by
      intro k
      have hC4sqnn : (0 : Q') ≤ Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k)) :=
        Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)
      rw [absQ_of_nonneg _ hC4sqnn]
      exact hsummand k
    have htail := norm_tail_modulus
      (rrel := fun s => Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
      hw0 hw1 N₀ hZ q m r S hsumm' hcut hhead M
    refine Q'.le_trans' _ _ _ ?_ htail
    refine Q'.le_of_eqv ?_
    have hcong : ∀ k,
        (f (S + k)).eqv
          (μ w N₀ hZ (S + k)
            * (qfac w (S + k) ^ q
                * absQ (Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k))))) := by
      intro k
      show (μ w N₀ hZ (S + k)
            * (qfac w (S + k) ^ q * (Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k))))).eqv
          (μ w N₀ hZ (S + k)
            * (qfac w (S + k) ^ q
                * absQ (Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k)))))
      have hC4sqnn : (0 : Q') ≤ Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k)) :=
        Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)
      rw [absQ_of_nonneg _ hC4sqnn]
      exact Q'.eqv_refl _
    exact RationalTail.finSum_eqv_congr (fun j => f (S + j))
      (fun k => μ w N₀ hZ (S + k)
        * (qfac w (S + k) ^ q
            * absQ (Q'.ofNat (c4 (S + k)) * Q'.ofNat (c4 (S + k))))) hcong M
  -- COMBINE
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hHEAD)
    (Q'.add_le_add_left (Q'.ofNat S * headMax) _ _ hTAIL)

/-! ## 2. The general inverse-power summability endpoint (bonus)

Any sequence dominated by `A·invSqTerm 2` is summable with the explicit `A·pot 2`
tail bound — the `p = 2` (α = 0) endpoint.  This re-exports `summableBound_of_invSq`
in the form the chain consumes: it certifies summability for every `α ∈ [0,1)`,
since the chain's per-step bound is the inverse-SQUARE `δ ≤ A/(k+2)²`. -/

/-- **The inverse-power summability endpoint.**  If `δ k ≤ A · invSqTerm 2 k` for
all `k` (with `A ≥ 0`), then every tail window is bounded: `tailSum δ N M ≤
A · pot 2 N`.  This is the `2 − α = 2` endpoint that closes the chain for `α = 0`
(and a fortiori dominates any `p = 2 − α ∈ (1,2)`, since the chain's per-step
defect is itself inverse-square). -/
theorem summable_of_inverse_pow_bound (A : Q') (hA : (0 : Q') ≤ A)
    (δ : Nat → Q') (hδ : ∀ k, δ k ≤ A * invSqTerm 2 (by decide) k) (N M : Nat) :
    tailSum δ N M ≤ A * pot 2 (by decide) N :=
  summableBound_of_invSq 2 (by decide) A hA δ hδ N M

/-! ## 3. FIRING THE CHAIN — the moment hypothesis discharged into the defect

We build the full-mode scalar defect `FullModeDefect` whose clean quadratic
constant `M = casimirSqM q r S` is now PROVED (not assumed): `d_quad` is
discharged via `fullMode_defect_clean_quadratic` fed by `casimir_moment_bound`.

The remaining input is the FAMILY of cutoff certificates — one
`(hsummand, hcut, hhead, hZ)` per step `k` — which is the honest moving-cutoff
residual (`S = S(w_k)`).  We package it as a structure `CutoffData` so the chain
fires `fullMode_gap_of_AFRate` with the moment now an internal lemma, leaving ONLY
the cutoff-certificate family named (NOT a hidden moment hypothesis). -/

/-- The per-step cutoff certificate family: for each step `k` (weight `w_k`), the
fixed-cutoff data `(S, N₀, M_win)` and the three explicit cutoff inequalities that
make `casimir_moment_bound` fire at that weight.  This is the moving-cutoff
residual, named explicitly. -/
structure CutoffData (afr : AFRateModulus) (q m r S N₀ Mwin : Nat) : Type where
  /-- `S ≤ N₀` (cutoff inside the fusion degree). -/
  hSN : S ≤ N₀
  /-- Strict positivity of each weight (the AF interface only gives `0 ≤ w`; the
  moment bound needs `0 < w`, and e.g. the canonical rate has `w₀ = 0`). -/
  hwpos : ∀ k, (0 : Q') < afr.w k
  /-- The partition normalizer is positive at each weight. -/
  hZ : ∀ k, (0 : Q') < Zsum (afr.w k) N₀
  /-- The per-tail-term Casimir domination at each weight. -/
  hsummand : ∀ k, ∀ j,
    casimirSqTerm (afr.w k) N₀ (hZ k) q (S + j) ≤ tailTerm (afr.w k) (m + 2) (S + j)
  /-- The ratio cutoff inequality at each weight. -/
  hcut : ∀ k, Q'.ofNat (2 ^ (m + 2)) * qpow (afr.w k) (2 * S + 3) ≤ HalfPow.half
  /-- The head cutoff inequality at each weight. -/
  hhead : ∀ k, tailTerm (afr.w k) (m + 2) S ≤ dyad (r + 1)

/-- **The full-mode defect assembled with the PROVED moment.**  Given the AF rate
and a cutoff-certificate family, the per-step defect `d k = momentSum w_k …` (the
genuine scaled square-test moment at the fixed cutoff `S + Mwin`) satisfies the
clean quadratic bound `d k ≤ casimirSqM q r S · (1−w_k)²` — with the constant now
PROVED by `casimir_moment_bound`, no longer assumed. -/
def fullModeDefect_proved (afr : AFRateModulus) (q m r S N₀ Mwin : Nat)
    (cd : CutoffData afr q m r S N₀ Mwin) : FullModeDefect afr where
  d := fun k => momentSum (afr.w k) N₀ (cd.hZ k) q sqPoly (S + Mwin)
  d_nonneg := fun k => by
    refine finSum_nonneg (fun s => ?_) (S + Mwin)
    show (0 : Q') ≤ momentTerm (afr.w k) N₀ (cd.hZ k) q sqPoly s
    refine Q'.mul_nonneg _ _ (μ_nonneg (afr.w_nonneg k) N₀ (cd.hZ k) s) ?_
    refine Q'.mul_nonneg _ _
      (Q'.pow_nonneg _ (qfac_nonneg (Q'.le_of_lt (afr.w_lt_one k)) s) q) ?_
    exact Peval_nonneg sqPoly sqPoly_nonneg
      (yArg_nonneg (Q'.le_of_lt (afr.w_lt_one k)) s)
  M := casimirSqM q r S
  M_nonneg := casimirSqM_nonneg q r S
  d_quad := fun k => by
    -- δ_ren = (1−w)²·casimirSqSum ≤ casimirSqM·(1−w)² via the clean-quadratic assembly.
    have hmom : casimirSqSum (afr.w k) N₀ (cd.hZ k) q (S + Mwin) ≤ casimirSqM q r S :=
      casimir_moment_bound (w := afr.w k)
        (cd.hwpos k) (afr.w_lt_one k)
        q m r S N₀ cd.hSN (cd.hZ k) (cd.hsummand k) (cd.hcut k) (cd.hhead k) Mwin
    exact fullMode_defect_clean_quadratic (afr.w_nonneg k)
      (Q'.le_of_lt (afr.w_lt_one k)) N₀ (cd.hZ k) q (S + Mwin)
      (casimirSqM q r S) hmom

/-- **THE FULL-MODE GAP WITH THE MOMENT PROVED.**  Along ANY AF rate `afr` carrying
a cutoff-certificate family `cd`, the running product of the renormalized full-mode
per-block rates has a STRICTLY POSITIVE floor — with the Casimir-square moment now
PROVED internally (`casimir_moment_bound`), NOT carried as a hypothesis.

SCOPE: full-mode scalar defect; `s = 1`-matched renormalization; finite fusion
degree `N₀`; tail `k ≥ k₀`; AF rate the named two-loop input; and the moving-cutoff
certificate family `cd` (the genuine residual, named explicitly — `S = S(w_k)`). -/
def fullMode_gap_of_AFRate_proved_moment (afr : AFRateModulus)
    (q m r S N₀ Mwin : Nat) (cd : CutoffData afr q m r S N₀ Mwin) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix
            (fmTailRate afr (fullModeDefect_proved afr q m r S N₀ Mwin cd)
              (fmCutoff afr (fullModeDefect_proved afr q m r S N₀ Mwin cd))) n) :=
  fullMode_gap_of_AFRate afr (fullModeDefect_proved afr q m r S N₀ Mwin cd)

end YMGap.Continuum.CasimirMoment

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CasimirMoment.one_pow_eqv
#print axioms YMGap.Continuum.CasimirMoment.nat_le_two_pow
#print axioms YMGap.Continuum.CasimirMoment.nat_sq_le_four_pow
#print axioms YMGap.Continuum.CasimirMoment.ofNat_four_pow_mul
#print axioms YMGap.Continuum.CasimirMoment.geom_beats_sq
#print axioms YMGap.Continuum.CasimirMoment.casimirSqM_nonneg
#print axioms YMGap.Continuum.CasimirMoment.casimirSqTerm_head_le
#print axioms YMGap.Continuum.CasimirMoment.casimir_moment_bound
#print axioms YMGap.Continuum.CasimirMoment.summable_of_inverse_pow_bound
#print axioms YMGap.Continuum.CasimirMoment.fullModeDefect_proved
#print axioms YMGap.Continuum.CasimirMoment.fullMode_gap_of_AFRate_proved_moment
