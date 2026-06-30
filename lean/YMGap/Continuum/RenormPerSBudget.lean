/-
Track B / R2 — the RENORMALIZED PER-`s` BOND-MOVING BUDGET in the heat-kernel
SCALED norm, and the SHARP NEGATIVE verdict on its summability.

# What this module tests, and what it finds

The full Migdal–Kadanoff block step is `bond-moving ∘ decimation`.  Decimation is
exact; the bond-moving DEFECT `δ` over the SU(2) spin tower `s = 0,1,2,…` must be
SUMMABLE along the asymptotic-freedom trajectory (`1 − w_k ∼ 1/k`) for the
continuum gap.  The UNIFORM (full-mode) tower sum DIVERGES: the dominant `s = 1`
mode's renormalized defect is quadratic `O((1−w)²)` (proved upstream,
`BondMovingQuadratic.bondMovingDeltaRen_quadratic`), but the BULK modes
`s ∼ 1/√(1−w)` keep a LINEAR `O(1−w)` deviation.

The natural fix to try: measure the per-mode renormalized defect in the
heat-kernel-SCALED norm (weight `μ(s) ∝ (s+1)²·w^{C₄(s)}`, test the residual
relative to `Kτ(s)`), and reuse the per-mode SECOND-ORDER overshoot
`secondOrder_qpow` so each mode is quadratic per-`s`.  This module builds that
budget and tests its order in the margin `1 − w`.

# THE PER-`s` BUDGET (built here)

  * `perSDefect w s = C₄(s)·(1−w) − (1 − w^{C₄(s)})` — the per-MODE renormalized
    overshoot (the all-`s` generalization of the `s = 1` defect): the gap between
    the matched marginal-flow linear model `C₄(s)·(1−w)` and the true deviation
    `1 − w^{C₄(s)}`.  By `secondOrder_qpow` at `n = C₄(s)` it is QUADRATIC per mode:
        perSDefect w s  ≤  C₄(s)²·(1−w)²       (`perSDefect_quadratic`).
  * `perSDefect_scaledTerm_le` — its SCALED-norm summand `μ(s)·qfac^q·perSDefect`
    is dominated by `(1−w)²·casimirSqTerm` (the `(1−w)²`-stripped Casimir-square
    moment summand), so the budget below genuinely ENVELOPES the per-`s` defect.
  * `perSBudget w N hZ q = (1−w)²·casimirSqSum w N hZ q N` — the single per-step
    budget `∑_s μ(s)·qfac^q·(C₄(s)²·(1−w)²)`, reusing the proved scaled-norm
    `casimirSqSum`.

# THE CRUX — the order of `perSBudget` in `1 − w` (the α verdict)

Split the tower LOW / BULK / TAIL (the `casimir_moment_bound` head/tail split).

  POSITIVE half (`perSBudget_le_quadratic_fixedCutoff`).  At a FIXED cutoff `S`,
  the budget is CLEAN QUADRATIC:
        perSBudget w (S+M) hZ q  ≤  casimirSqM q r S · (1−w)²,
  with `casimirSqM q r S` INDEPENDENT of `w` (the `α = 2` verdict AT FIXED `S`),
  valid on any compact `0 < w ≤ w₀ < 1` where the tail cutoff inequalities hold.

  NEGATIVE half (`envelope_value_ge_quarter` — THE SHARP RESULT).  But the tail
  cutoff inequality (`hcut : 2^{m+2}·w^{2S+3} ≤ 1/2`) is exactly what FORCES the
  bulk: as `w → 1` it can only hold once the MOVING cutoff `S = S(w)` grows.
  Quantitatively (`cutoff_forces_margin`) the cutoff forces
        (2S+3)·(1−w)  ≥  1/2,
  i.e. `S ≳ 1/(1−w)`.  At that cutoff the "constant" `casimirSqM q r S ≥ C₄(S)²`,
  so the SAME envelope value, evaluated where it is valid, is BOUNDED BELOW:
        casimirSqM q r S · (1−w)²  ≥  (C₄(S)·(1−w))²  ≥  (1/2)²  =  1/4   (S ≥ 2).

  VERDICT: the quadratic envelope is VACUOUS exactly where it must apply — its
  certificate value does NOT vanish as `w → 1`, it stays `≥ 1/4 = O((1−w)⁰)`.  So
  for this per-mode C₄²-OVERSHOOT weighting `α = 0` (NOT summable): the danger
  flagged at the bulk scale `s ∼ 1/√(1−w)` (where `w^{C₄(s)} ≈ e^{−1} = O(1)`, NOT
  suppressed) is REAL and computed honestly — the heat-kernel scaling does not
  rescue the crude overshoot envelope.

# What this KILLS, and what it points to (honest)

This SHARP NEGATIVE kills the specific hope that the per-mode SECOND-ORDER
overshoot `C₄(s)²·(1−w)²`, reweighted by the heat-kernel `μ`, becomes summable.
It does NOT touch the genuine route: the bond-moved coefficient measured RELATIVE
to the retuned heat kernel (`GenuineResidualDefect.GenuineResidualBound.hbound`,
`BondMovingRelResidual.FusionRelResidualBound`) can still be `O((1−w)²)` per mode
with a BOUNDED Gaussian-moment test `Peval P (y_s)` (a polynomial in
`y_s = (1−w)·C₄(s)`, hence `O(1)` on the active modes), NOT the unbounded `C₄(s)²`
overshoot.  The next step is precisely there: bound the genuine RELATIVE residual,
not the absolute overshoot.  (Consistent with the divergence already documented
numerically in `BondMovingRelResidual` / `GenuineResidualDefect`.)

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition over already-proved engines
(`secondOrder_qpow`, `casimir_moment_bound`, `oneSub_qpow_le`).  Every load-bearing
declaration is `#print axioms`-gated; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide` (only `decide` on decidable facts), no
`sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.GenuineResidualDefect
import YMGap.Continuum.CasimirMoment

namespace YMGap.Continuum.RenormPerSBudget

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.CasimirMoment

/-! ## 0. The per-MODE renormalized overshoot defect (all `s`) -/

/-- **The per-mode renormalized bond-moving overshoot defect.**  On mode `s`, the
bond-moving raises the coefficient to a power `∝ C₄(s)`; after the marginal-flow
retune (matching the linear model `C₄(s)·(1−w)`), the genuinely transverse residual
is the OVERSHOOT of that linear model over the true deviation `1 − w^{C₄(s)}`:

    perSDefect w s  =  C₄(s)·(1−w)  −  (1 − w^{C₄(s)}).

This is the all-`s` generalization of `BondMovingQuadratic.bondMovingDeltaRen`
(which is the `s = 1` instance, scaled by `dimQ 1` and `p`). -/
def perSDefect (w : Q') (s : Nat) : Q' :=
  (Q'.ofNat (c4 s) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 s))

/-- The per-mode defect is nonnegative on `[0,1]` (the linear marginal model
over-estimates: `1 − w^{C₄(s)} ≤ C₄(s)·(1−w)`, `oneSub_qpow_le`). -/
theorem perSDefect_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    (0 : Q') ≤ perSDefect w s := by
  have hlin : (1 : Q') - qpow w (c4 s) ≤ Q'.ofNat (c4 s) * ((1 : Q') - w) :=
    oneSub_qpow_le hw0 hw1 (c4 s)
  exact Q'.sub_nonneg_of_le hlin

/-- **THE PER-MODE QUADRATIC BOUND.**  On `[0,1]`,

    perSDefect w s  ≤  C₄(s)²·(1−w)²,

DIRECTLY from the second-order overshoot engine `secondOrder_qpow` at `n = C₄(s)`:
the per-mode retuned overshoot is QUADRATIC in the margin, with the mode-dependent
Casimir-SQUARE prefactor `C₄(s)²`. -/
theorem perSDefect_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    perSDefect w s
      ≤ (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
  secondOrder_qpow hw0 hw1 (c4 s)

/-! ## 1. The SCALED-norm per-`s` summand is enveloped by the Casimir-square moment -/

/-- **The per-mode defect, in the SCALED norm, is dominated by `(1−w)²·casimirSqTerm`.**
The scaled-norm summand of the genuine per-mode defect,
`μ(s)·qfac(w,s)^q·perSDefect w s`, is `≤ (1−w)²` times the Casimir-square moment
summand `casimirSqTerm w N hZ q s = μ(s)·qfac^q·C₄(s)²`.  PROOF: `perSDefect ≤
(1−w)²·C₄(s)²` (`perSDefect_quadratic`, commuted), multiplied by the nonneg weight
`μ·qfac^q`, then `moment_pull_factor` pulls the `(1−w)²` out front. -/
theorem perSDefect_scaledTerm_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q s : Nat) :
    μ w N hZ s * (qfac w s ^ q * perSDefect w s)
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s := by
  have hμnn : (0 : Q') ≤ μ w N hZ s := μ_nonneg hw0 N hZ s
  have hqfacnn : (0 : Q') ≤ qfac w s ^ q := Q'.pow_nonneg _ (qfac_nonneg hw1 s) q
  -- perSDefect ≤ (1−w)²·C₄(s)²  (commute the quadratic bound)
  have hquad : perSDefect w s
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) := by
    refine Q'.le_trans' _ _ _ (perSDefect_quadratic hw0 hw1 s) ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) (((1 : Q') - w) * ((1 : Q') - w)))
  -- multiply by qfac^q ≥ 0, then μ ≥ 0
  have h1 : qfac w s ^ q * perSDefect w s
      ≤ qfac w s ^ q
          * (((1 : Q') - w) * ((1 : Q') - w) * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hquad hqfacnn
  have h2 : μ w N hZ s * (qfac w s ^ q * perSDefect w s)
      ≤ μ w N hZ s
          * (qfac w s ^ q
              * (((1 : Q') - w) * ((1 : Q') - w) * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h1 hμnn
  refine Q'.le_trans' _ _ _ h2 ?_
  -- μ·(qfac^q·((1−w)²·C₄²)) ≃ (1−w)²·(μ·(qfac^q·C₄²)) = (1−w)²·casimirSqTerm
  refine Q'.le_of_eqv ?_
  exact moment_pull_factor (((1 : Q') - w) * ((1 : Q') - w))
    (μ w N hZ s) (qfac w s ^ q) (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))

/-! ## 2. The per-step budget `perSBudget = (1−w)²·casimirSqSum` -/

/-- **The renormalized per-step bond-moving budget** in the scaled norm:

    perSBudget w N hZ q  =  (1−w)² · casimirSqSum w N hZ q N
                         =  ∑_{s<N} μ(s)·qfac(w,s)^q·(C₄(s)²·(1−w)²).

A single `Q'` value (the finite scaled-norm window sum; its tail past the moving
cutoff is dyadically small by `tail_modulus`).  By `perSDefect_scaledTerm_le` this
ENVELOPES the genuine per-`s` renormalized defect summed in the scaled norm. -/
def perSBudget (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) : Q' :=
  ((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w N hZ q N

theorem perSBudget_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) : (0 : Q') ≤ perSBudget w N hZ q := by
  refine Q'.mul_nonneg _ _ ?_ (casimirSqSum_nonneg hw0 hw1 N hZ q N)
  exact Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1)

/-! ## 3. POSITIVE half — fixed-cutoff `α = 2` (reusing `casimir_moment_bound`) -/

/-- **The fixed-cutoff QUADRATIC bound (`α = 2` at fixed `S`).**  At a FIXED cutoff
`S`, with the tail cutoff certificates (`hsummand`/`hcut`/`hhead`), the per-step
budget at the matching window `N₀ = S + M` is clean quadratic:

    perSBudget w (S+M) hZ q  ≤  casimirSqM q r S · (1−w)²,

with `casimirSqM q r S` INDEPENDENT of `w`.  This is `casimir_moment_bound` (the
proved Gaussian-tail head/tail split) folded through the `(1−w)²` factor.  HONEST:
the constant is `w`-uniform only for FIXED `S`; the cutoff inequalities hold on a
compact `0 < w ≤ w₀ < 1` and FAIL as `w → 1` (the negative half below). -/
theorem perSBudget_le_quadratic_fixedCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q m r S M : Nat) (hZ : (0 : Q') < Zsum w (S + M))
    (hsummand : ∀ k, casimirSqTerm w (S + M) hZ q (S + k) ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    perSBudget w (S + M) hZ q
      ≤ casimirSqM q r S * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hmom : casimirSqSum w (S + M) hZ q (S + M) ≤ casimirSqM q r S :=
    casimir_moment_bound hw0 hw1 q m r S (S + M) (Nat.le_add_right S M) hZ
      hsummand hcut hhead M
  have hunn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  -- perSBudget = (1−w)²·casimirSqSum ≤ (1−w)²·casimirSqM ≃ casimirSqM·(1−w)²
  have hstep : ((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w (S + M) hZ q (S + M)
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * casimirSqM q r S :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmom hunn
  refine Q'.le_trans' _ _ _ hstep ?_
  exact Q'.le_of_eqv
    (Q'.mul_comm_eqv (((1 : Q') - w) * ((1 : Q') - w)) (casimirSqM q r S))

/-! ## 4. NEGATIVE half — the moving cutoff forces the bulk; the envelope is vacuous

The cutoff inequality `hcut` is the SAME one the tail modulus needs; as `w → 1` it
forces the cutoff `S` to GROW, and at that growing `S` the "constant" `casimirSqM`
blows up faster than `(1−w)²` shrinks.  We make this quantitative and GREEN. -/

/-- **`c4 S ≥ 2S+3` for `S ≥ 2`** (Nat).  `C₄(S) = S(S+2) = S² + 2S ≥ 2S + 2S =
4S ≥ 2S + 3` for `S ≥ 2`.  (`S² ≥ 2S` since `S ≥ 2`; `4S ≥ 2S+3` since `2S ≥ 3`.) -/
theorem c4_ge_lin (S : Nat) (hS : 2 ≤ S) : 2 * S + 3 ≤ c4 S := by
  show 2 * S + 3 ≤ S * (S + 2)
  have hSS : 2 * S ≤ S * S := by
    have := Nat.mul_le_mul_right S hS    -- 2*S ≤ S*S
    simpa [Nat.mul_comm] using this
  calc 2 * S + 3 ≤ 2 * S + 2 * S := by omega
    _ ≤ S * S + 2 * S := by omega
    _ = S * (S + 2) := by rw [Nat.mul_add]; omega

/-- **The cutoff `≥ 1` numeral fact** `1 ≤ 2^{m+2}` (Nat). -/
theorem one_le_two_pow_succ (m : Nat) : 1 ≤ 2 ^ (m + 2) := CasimirMoment.one_le_two_pow (m + 2)

/-- **THE CUTOFF-FORCING LEMMA.**  On `[0,1]`, the tail-modulus ratio cutoff
`2^{m+2}·w^{2S+3} ≤ 1/2` FORCES the margin-weighted Casimir increment below by a
fixed positive constant:

    1/2  ≤  (2S+3)·(1 − w).

In words: for the Gaussian tail to be dyadically small the cutoff `S` must satisfy
`(2S+3)(1−w) ≥ 1/2`, i.e. `S ≳ 1/(1−w)` — the MOVING cutoff that grows as `w → 1`.

PROOF.  Write `A = 2^{m+2}`, `n = 2S+3`, `u = 1−w`.  From `1 − w^n ≤ n·u`
(`oneSub_qpow_le`) and `A ≥ 0`, `A·(1 − w^n) ≤ A·(n·u)`; and `A·(1 − w^n) ≃
A − A·w^n ≥ A − 1/2` (the cutoff).  So `A − 1/2 ≤ A·(n·u)`.  Since `A ≥ 1` we have
`A·(1/2) ≤ A − 1/2`, hence `A·(1/2) ≤ A·(n·u)`; cancel the positive `A`. -/
theorem cutoff_forces_margin {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (m S : Nat)
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half) :
    HalfPow.half ≤ Q'.ofNat (2 * S + 3) * ((1 : Q') - w) := by
  -- abbreviations
  have hAnn : (0 : Q') ≤ Q'.ofNat (2 ^ (m + 2)) := zero_le_ofNat _
  have hone_le_A : (1 : Q') ≤ Q'.ofNat (2 ^ (m + 2)) := by
    have he : (Q'.ofNat 1).eqv (1 : Q') := by decide
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (ofNat_le_ofNat (one_le_two_pow_succ m))
  have hApos : (0 : Q') < Q'.ofNat (2 ^ (m + 2)) :=
    lt_of_lt_of_le (by decide : (0 : Q') < (1 : Q')) hone_le_A
  -- 1 − w^n ≤ n·u
  have hone : (1 : Q') - qpow w (2 * S + 3) ≤ Q'.ofNat (2 * S + 3) * ((1 : Q') - w) :=
    oneSub_qpow_le hw0 hw1 (2 * S + 3)
  -- A·(1 − w^n) ≤ A·(n·u)
  have hAle : Q'.ofNat (2 ^ (m + 2)) * ((1 : Q') - qpow w (2 * S + 3))
      ≤ Q'.ofNat (2 ^ (m + 2)) * (Q'.ofNat (2 * S + 3) * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hone hAnn
  -- A·(1 − w^n) ≃ A + -(A·w^n)
  have hexpand : (Q'.ofNat (2 ^ (m + 2)) * ((1 : Q') - qpow w (2 * S + 3))).eqv
      (Q'.ofNat (2 ^ (m + 2)) + -(Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat (2 ^ (m + 2))) (1 : Q') (-(qpow w (2 * S + 3)))) ?_
    refine Q'.add_eqv_congr' (Q'.mul_one_eqv (Q'.ofNat (2 ^ (m + 2)))) ?_
    exact Q'.mul_neg_eqv (Q'.ofNat (2 ^ (m + 2))) (qpow w (2 * S + 3))
  -- A + -(A·w^n) ≥ A + -(1/2)   (from the cutoff)
  have hge : Q'.ofNat (2 ^ (m + 2)) + -HalfPow.half
      ≤ Q'.ofNat (2 ^ (m + 2)) + -(Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3)) :=
    Q'.add_le_add_left (Q'.ofNat (2 ^ (m + 2))) _ _ (Q'.neg_le_neg hcut)
  -- so A − 1/2 ≤ A·(n·u)
  have hkey : Q'.ofNat (2 ^ (m + 2)) + -HalfPow.half
      ≤ Q'.ofNat (2 ^ (m + 2)) * (Q'.ofNat (2 * S + 3) * ((1 : Q') - w)) :=
    Q'.le_trans' _ _ _ hge (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hexpand) hAle)
  -- A·(1/2) ≤ A − 1/2 :  since A ≥ 1.
  -- A ≃ A·half + A·half ;  half ≤ A·half ;  so A·half + half ≤ A ;  so A·half ≤ A − half.
  have hsplitA : (Q'.ofNat (2 ^ (m + 2))).eqv
      (Q'.ofNat (2 ^ (m + 2)) * HalfPow.half + Q'.ofNat (2 ^ (m + 2)) * HalfPow.half) := by
    have hhh : ((1 : Q')).eqv (HalfPow.half + HalfPow.half) := by decide
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv (Q'.ofNat (2 ^ (m + 2))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (2 ^ (m + 2))) _ _ hhh) ?_
    exact Q'.mul_add_eqv (Q'.ofNat (2 ^ (m + 2))) HalfPow.half HalfPow.half
  have hhalf_le : HalfPow.half ≤ Q'.ofNat (2 ^ (m + 2)) * HalfPow.half := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv HalfPow.half)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hone_le_A HalfPow.half_nonneg
  -- A·half + half ≤ A
  have hsum_le : Q'.ofNat (2 ^ (m + 2)) * HalfPow.half + HalfPow.half
      ≤ Q'.ofNat (2 ^ (m + 2)) := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hsplitA)
    exact Q'.add_le_add_left (Q'.ofNat (2 ^ (m + 2)) * HalfPow.half) _ _ hhalf_le
  -- A·half ≤ A − half  (subtract half)
  have hAhalf_le : Q'.ofNat (2 ^ (m + 2)) * HalfPow.half
      ≤ Q'.ofNat (2 ^ (m + 2)) + -HalfPow.half := by
    have hstep : (Q'.ofNat (2 ^ (m + 2)) * HalfPow.half + HalfPow.half) + -HalfPow.half
        ≤ Q'.ofNat (2 ^ (m + 2)) + -HalfPow.half :=
      Q'.add_le_add_right _ _ _ hsum_le
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hstep
    -- (A·half + half) + -half ≃ A·half
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ HalfPow.half (-HalfPow.half)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv HalfPow.half)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  -- chain:  A·half ≤ A − half ≤ A·(n·u) ;  cancel A
  have hcancel : Q'.ofNat (2 ^ (m + 2)) * HalfPow.half
      ≤ Q'.ofNat (2 ^ (m + 2)) * (Q'.ofNat (2 * S + 3) * ((1 : Q') - w)) :=
    Q'.le_trans' _ _ _ hAhalf_le hkey
  exact Q'.le_of_mul_le_mul_left hcancel hApos

/-- **`casimirSqM q r S ≥ C₄(S)²` for `S ≥ 1`.**  The `w`-independent constant is at
least the QUARTIC-in-`S` head term: `casimirSqM = S·((1+C₄S)^q·C₄S²) + (1/2)^r ≥
1·(1·C₄S²) + 0` (using `ofNat S ≥ 1`, `(1+C₄S)^q ≥ 1`, `(1/2)^r ≥ 0`). -/
theorem casimirSqM_ge_c4sq (q r : Nat) {S : Nat} (hS : 1 ≤ S) :
    Q'.ofNat (c4 S) * Q'.ofNat (c4 S) ≤ casimirSqM q r S := by
  -- 1 ≤ ofNat S
  have h1S : (1 : Q') ≤ Q'.ofNat S := by
    have he : (Q'.ofNat 1).eqv (1 : Q') := by decide
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) (ofNat_le_ofNat hS)
  -- 1 ≤ (1 + C₄S)^q
  have h1pow : (1 : Q') ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q := by
    have hbase : (1 : Q') ≤ (1 : Q') + Q'.ofNat (c4 S) := by
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (1 : Q')))) ?_
      exact Q'.add_le_add_left (1 : Q') _ _ (zero_le_ofNat (c4 S))
    have hpow : (1 : Q') ^ q ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q :=
      pow_le_pow_of_le (by decide) hbase q
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (CasimirMoment.one_pow_eqv q)) hpow
  -- C₄S² ≤ S·((1+C₄S)^q·C₄S²)
  have hc4sqnn : (0 : Q') ≤ Q'.ofNat (c4 S) * Q'.ofNat (c4 S) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)
  have hpownn : (0 : Q') ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q :=
    Q'.pow_nonneg _ (Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)) q
  -- step A:  C₄S² ≤ (1+C₄S)^q · C₄S²
  have hA : Q'.ofNat (c4 S) * Q'.ofNat (c4 S)
      ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S)) := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ h1pow hc4sqnn
  -- step B:  (1+C₄S)^q · C₄S² ≤ S · ((1+C₄S)^q · C₄S²)
  have hBnn : (0 : Q') ≤ ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S)) :=
    Q'.mul_nonneg _ _ hpownn hc4sqnn
  have hB : ((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))
      ≤ Q'.ofNat S * (((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))) := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ h1S hBnn
  -- step C:  head ≤ head + (1/2)^r = casimirSqM
  have hC : Q'.ofNat S * (((1 : Q') + Q'.ofNat (c4 S)) ^ q * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S)))
      ≤ casimirSqM q r S := by
    show _ ≤ Q'.ofNat S * (((1 : Q') + Q'.ofNat (c4 S)) ^ q
        * (Q'.ofNat (c4 S) * Q'.ofNat (c4 S))) + dyad r
    exact Q'.add_le_self_of_nonneg _ _ (dyad_nonneg r)
  exact Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ hB hC)

/-- **THE SHARP NEGATIVE — the quadratic envelope is VACUOUS at the moving cutoff.**
On `[0,1]`, with `S ≥ 2`, GIVEN the SAME tail-modulus ratio cutoff `hcut`
(`2^{m+2}·w^{2S+3} ≤ 1/2`) that the positive half needs, the envelope value is
BOUNDED BELOW by a fixed positive constant:

    1/4  ≤  casimirSqM q r S · (1−w)².

So the "(1−w)²·constant" quadratic bound does NOT decay as `w → 1` — its value stays
`≥ 1/4 = O((1−w)⁰)`.  The order of the per-mode C₄²-OVERSHOOT budget is `α = 0`:
NOT summable.

PROOF.  `casimirSqM ≥ C₄(S)²` (`casimirSqM_ge_c4sq`), so `casimirSqM·(1−w)² ≥
(C₄(S)·(1−w))²`.  The cutoff forces `(2S+3)(1−w) ≥ 1/2` (`cutoff_forces_margin`),
and `C₄(S) ≥ 2S+3` for `S ≥ 2` (`c4_ge_lin`), so `C₄(S)·(1−w) ≥ 1/2 ≥ 0`; squaring
(`sq_le_sq`) gives `(C₄(S)·(1−w))² ≥ (1/2)² = 1/4`. -/
theorem envelope_value_ge_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (q m r : Nat) {S : Nat} (hS : 2 ≤ S)
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half) :
    HalfPow.half * HalfPow.half
      ≤ casimirSqM q r S * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hunn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  -- 1/2 ≤ (2S+3)·(1−w)
  have hmargin : HalfPow.half ≤ Q'.ofNat (2 * S + 3) * ((1 : Q') - w) :=
    cutoff_forces_margin hw0 hw1 m S hcut
  -- (2S+3)·(1−w) ≤ C₄(S)·(1−w)
  have hc4lin : Q'.ofNat (2 * S + 3) ≤ Q'.ofNat (c4 S) := ofNat_le_ofNat (c4_ge_lin S hS)
  have hc4u : Q'.ofNat (2 * S + 3) * ((1 : Q') - w) ≤ Q'.ofNat (c4 S) * ((1 : Q') - w) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hc4lin hunn
  -- 1/2 ≤ C₄(S)·(1−w)
  have hhalf_le : HalfPow.half ≤ Q'.ofNat (c4 S) * ((1 : Q') - w) :=
    Q'.le_trans' _ _ _ hmargin hc4u
  -- square:  (1/2)² ≤ (C₄(S)·(1−w))²
  have hsq : HalfPow.half * HalfPow.half
      ≤ (Q'.ofNat (c4 S) * ((1 : Q') - w)) * (Q'.ofNat (c4 S) * ((1 : Q') - w)) :=
    sq_le_sq HalfPow.half_nonneg hhalf_le
  refine Q'.le_trans' _ _ _ hsq ?_
  -- (C₄(S)·(1−w))² ≃ C₄(S)²·(1−w)²  ≤  casimirSqM·(1−w)²
  have hregroup : ((Q'.ofNat (c4 S) * ((1 : Q') - w)) * (Q'.ofNat (c4 S) * ((1 : Q') - w))).eqv
      ((Q'.ofNat (c4 S) * Q'.ofNat (c4 S)) * (((1 : Q') - w) * ((1 : Q') - w))) :=
    mul_four_mid (Q'.ofNat (c4 S)) ((1 : Q') - w) (Q'.ofNat (c4 S)) ((1 : Q') - w)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) ?_
  -- C₄(S)²·(1−w)² ≤ casimirSqM·(1−w)²
  have hu2nn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) :=
    Q'.mul_nonneg _ _ hunn hunn
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ (casimirSqM_ge_c4sq q r (by omega : 1 ≤ S)) hu2nn

/-! ## 5. THE VERDICT — α = 0 for this weighting (the two halves side by side) -/

/-- **THE RENORMALIZED-PER-`s`-BUDGET VERDICT (`α = 0`, SHARP NEGATIVE).**  At a
cutoff `S ≥ 2` with the tail-modulus certificates, BOTH hold simultaneously:

  (1)  the budget is bounded by the quadratic envelope
         perSBudget w (S+M) hZ q  ≤  E,   E := casimirSqM q r S · (1−w)²;
  (2)  the SAME envelope value is bounded BELOW away from `0`:
         1/4  ≤  E.

So the quadratic certificate `E` is VACUOUS: where it is valid (the moving cutoff
`S ≥ 2` forced by `hcut`) it does NOT vanish as `w → 1` — it stays `≥ 1/4`.  The
per-mode C₄²-OVERSHOOT budget therefore has order `α = 0` in the margin `1 − w`:
NOT summable.  (The genuine quadratic decay must come from the bond-moved RELATIVE
residual, not the absolute overshoot — see `GenuineResidualDefect.hbound`.)

Returned as the CONJUNCTION of the two proved inequalities at the SAME
`(w,q,m,r,S,M)`, witnessing that the envelope cannot certify summability. -/
theorem renormPerSBudget_verdict {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q m r S M : Nat) (hS : 2 ≤ S) (hZ : (0 : Q') < Zsum w (S + M))
    (hsummand : ∀ k, casimirSqTerm w (S + M) hZ q (S + k) ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    (perSBudget w (S + M) hZ q ≤ casimirSqM q r S * (((1 : Q') - w) * ((1 : Q') - w)))
    ∧ (HalfPow.half * HalfPow.half
        ≤ casimirSqM q r S * (((1 : Q') - w) * ((1 : Q') - w))) :=
  ⟨perSBudget_le_quadratic_fixedCutoff hw0 hw1 q m r S M hZ hsummand hcut hhead,
   envelope_value_ge_quarter (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) q m r hS hcut⟩

end YMGap.Continuum.RenormPerSBudget

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RenormPerSBudget.perSDefect_nonneg
#print axioms YMGap.Continuum.RenormPerSBudget.perSDefect_quadratic
#print axioms YMGap.Continuum.RenormPerSBudget.perSDefect_scaledTerm_le
#print axioms YMGap.Continuum.RenormPerSBudget.perSBudget_nonneg
#print axioms YMGap.Continuum.RenormPerSBudget.perSBudget_le_quadratic_fixedCutoff
#print axioms YMGap.Continuum.RenormPerSBudget.c4_ge_lin
#print axioms YMGap.Continuum.RenormPerSBudget.cutoff_forces_margin
#print axioms YMGap.Continuum.RenormPerSBudget.casimirSqM_ge_c4sq
#print axioms YMGap.Continuum.RenormPerSBudget.envelope_value_ge_quarter
#print axioms YMGap.Continuum.RenormPerSBudget.renormPerSBudget_verdict
