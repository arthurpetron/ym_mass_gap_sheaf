/-
Track B / local-CLT — PROVED anchor lemmas for the position-variance curvature floor
`Δ²_t ⟨D²⟩_t ≥ −2` (R1 = `CircleFourierPowerModel.SaddleVarianceFloor`).

# Why this file exists (read first — load-bearing honesty)

R1 is the `−2` floor on the FULL-range (Fourier-square) moments: `∀ s, FullRangeFloor w s`,
equivalently `Δ²V(s) ≥ −2` where `V(t) = dmomNfull w t / acNfull w t = ⟨D²⟩_t` is the theta-tilted
variance of `D = t − 2p` under `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`.  The windows `s = 0..6` are
proved in `CircleFourierPowerModel` by per-window Pólya/Bernstein certificates; the uniform-in-`s`
closure is the standing residual (relocated onto `PolyaCertifiedFloor` and `ContinuumFloor`).

The numerical analysis (`computations/direct_r1_closure_memo.md`) splits R1 by parity of the centre
window `s`:

  * ODD `s`  — comfortably above the floor: `Δ²V(s)+2 ≥ 12/7`, worst case `s = 1`.  The structural
    anchor is the EXACT two-point tie `V(odd t) ≥ 1` (every antidiagonal square `D² ≥ 1` on the odd
    lattice `D ∈ {±1, ±3, …}`).
  * EVEN `s` — binding only near `w → 0`, with the sharp minorant `Δ²V(s)+2 ≥ (144/25) w²(1−w²)`.

# What this file PROVES (axiom-clean, `Type`-level, NO `sorry`)

  * `one_le_dsq_of_odd` — the per-term arithmetic fact `1 ≤ dsq p t` for ODD `t` (the odd lattice has
    no `D = 0` point, so every `D² = (t−2p)² ≥ 1`).
  * `fsum_le_fsum` — termwise monotonicity of the finite partial sum `fsum`.
  * **`dmomNfull_ge_acNfull_odd`** — the EXACT two-point tie `V(odd t) ≥ 1`, in cleared form
    `acNfull w t ≤ dmomNfull w t` for odd `t` and `0 ≤ w`.  Termwise: `coeffW·coeffW ≤ dsq·(coeffW·
    coeffW)` since `dsq ≥ 1` on the odd lattice.  This is the anchor of the odd-`s` family of R1.
  * `covBridge` — `4·xmomNfull w t + dmomNfull w t ≃ (t²)·acNfull w t` (the FULL-range specialization
    of the covariance identity `4⟨x⟩ + ⟨D²⟩ = t²`, `x_p = p(t−p)`).  It yields the reformulation
    `Δ²V(s) + 2 = 4·(1 − Δ²⟨x⟩(s))`, i.e. `R1 ⟺ Δ²⟨x⟩ ≤ 1` (documented; the cleared three-window
    equivalence is not carried as a Lean field — it reintroduces subtractions).

# HONEST VERDICT

This file does NOT close R1.  It contributes the PROVED analytic anchor `V(odd t) ≥ 1` (the exact
two-point tie underlying the odd family, and the `−2` corner: `Δ²V → 0 + 0 − 2·1 = −2` at even `s`,
`w → 0`) together with the covariance bridge `covBridge`.  `V(odd) ≥ 1` lower-bounds the two odd
neighbours `V(s), V(s+2)` of an odd-centre second difference, but does NOT by itself discharge the
odd floor `2V(s+1) ≤ V(s)+V(s+2)+2` — that additionally needs an UPPER bound on the even-centre
variance `V(s+1)` (unbounded as `w → 1`), which is the coupled-two-chain obstruction identified in
the memo.  So the uniform-in-`s` closure of R1 remains OPEN; the existing relocations
(`PolyaCertifiedFloor`, `ContinuumFloor` + `FiniteCorrectionBound`) stand as the smallest named
residuals.  The Clay Yang–Mills mass gap remains OPEN.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

`#print axioms` at file end.  All load-bearing lemmas use only the reused `Q'` `≈`/`≤` machinery
(`propext`/`Quot.sound` at most).  No `Classical.*`, no `native_decide`, no `sorry`, no custom
`axiom`.
-/

import YMGap.Continuum.ContinuumShadowFloor

namespace YMGap.Continuum.EnvelopeClosure

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.CircleFourierPowerModel

/-! ## 1. The per-term arithmetic anchor: `dsq ≥ 1` on the odd lattice. -/

/-- **`one_le_dsq_of_odd`** — for ODD `t`, every antidiagonal square is `≥ 1`.  On the odd lattice the
centre `t/2` is not an integer, so `D = t − 2p` is odd (hence nonzero) for every `p`, giving `dsq p t
= (t−2p)² ≥ 1`.  (Nat-truncation-safe: `dsq p t = (t−2p)² + (2p−t)²`, exactly one summand nonzero.) -/
theorem one_le_dsq_of_odd {t : Nat} (ht : t % 2 = 1) (p : Nat) : 1 ≤ dsq p t := by
  show 1 ≤ (t - 2 * p) * (t - 2 * p) + (2 * p - t) * (2 * p - t)
  rcases Nat.lt_trichotomy (2 * p) t with h | h | h
  · -- 2p < t : the first summand `(t−2p)² ≥ 1`
    have ha : 1 ≤ (t - 2 * p) := by omega
    have hsq := Nat.mul_le_mul ha ha
    omega
  · -- 2p = t : impossible for odd t
    omega
  · -- t < 2p : the second summand `(2p−t)² ≥ 1`
    have hb : 1 ≤ (2 * p - t) := by omega
    have hsq := Nat.mul_le_mul hb hb
    omega

/-! ## 2. Termwise monotonicity of the finite partial sum. -/

/-- **`fsum_le_fsum`** — if `f i ≤ g i` termwise then `fsum f n ≤ fsum g n`. -/
theorem fsum_le_fsum {f g : Nat → Q'} (h : ∀ i, f i ≤ g i) :
    ∀ n, fsum f n ≤ fsum g n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show fsum f n + f n ≤ fsum g n + g n
      exact Q'.add_le_add (fsum_le_fsum h n) (h n)

/-! ## 3. THE ANCHOR — the exact two-point tie `V(odd t) ≥ 1` (cleared). -/

/-- **`dmomNfull_ge_acNfull_odd` — the exact two-point tie `V(odd t) ≥ 1`.**  For ODD `t` and `0 ≤ w`,
the tilted second moment dominates the mass: `acNfull w t ≤ dmomNfull w t`, i.e. `⟨D²⟩_t ≥ 1`.  Proof
is TERMWISE: every summand of `acNfull` is `coeffW w p · coeffW w (t−p) ≥ 0`, and the matching summand
of `dmomNfull` is `dsq p t` times it, with `dsq p t ≥ 1` on the odd lattice (`one_le_dsq_of_odd`).
This is the analytic anchor of the odd-`s` family of R1 and pins the `−2` corner (`Δ²V → −2·1` at even
`s`, `w → 0`). -/
theorem dmomNfull_ge_acNfull_odd {w : Q'} (hw : (0 : Q') ≤ w) {t : Nat} (ht : t % 2 = 1) :
    acNfull w t ≤ dmomNfull w t := by
  show fsum (fun p => coeffW w p * coeffW w (t - p)) (t + 1)
      ≤ fsum (fun p => Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))) (t + 1)
  refine fsum_le_fsum (fun p => ?_) (t + 1)
  -- termwise: `X ≤ dsq · X`, `X = coeffW w p · coeffW w (t−p) ≥ 0`, `dsq ≥ 1`.
  have hXnn : (0 : Q') ≤ coeffW w p * coeffW w (t - p) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw p) (coeffW_nonneg hw (t - p))
  have h1 : Q'.ofNat 1 ≤ Q'.ofNat (dsq p t) :=
    CReal.ofNat_le_ofNat (one_le_dsq_of_odd ht p)
  have hmul : Q'.ofNat 1 * (coeffW w p * coeffW w (t - p))
      ≤ Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p)) :=
    Q'.mul_le_mul_of_nonneg_right (Q'.ofNat 1) (Q'.ofNat (dsq p t))
      (coeffW w p * coeffW w (t - p)) h1 hXnn
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w p * coeffW w (t - p)))) hmul

/-! ## 4. The full-range covariance bridge `4⟨x⟩ + ⟨D²⟩ = t²`. -/

/-- **`xmomNfull w t`** — the FULL-range tilted first moment of `x_p = p(t−p)`:
`Σ_{p=0}^{t} p(t−p)·coeffW w p · coeffW w (t−p)` (the `⟨x⟩_t` numerator, cleared of the mass). -/
def xmomNfull (w : Q') (t : Nat) : Q' := xmomN w (t + 1) t

/-- **`covBridge`** — `4·xmomNfull w t + dmomNfull w t ≃ (t²)·acNfull w t`, the FULL-range
specialization (`s = t`) of the covariance identity `4⟨x⟩ + ⟨D²⟩ = t²`.  Consequence (documented,
not a Lean field): with `V(t) = t² − 4⟨x⟩_t` one gets `Δ²V(s) + 2 = 4·(1 − Δ²⟨x⟩(s))`, so
`R1 ⟺ Δ²⟨x⟩(s) ≤ 1` for all `s` — the cleaner mean-form of the floor. -/
theorem covBridge (w : Q') (t : Nat) :
    (Q'.ofNat 4 * xmomNfull w t + dmomNfull w t).eqv
      (Q'.ofNat (t * t) * acNfull w t) :=
  dsq_moment_eq w t t (Nat.le_refl t)

/-! ## 5. Doc-section — PROVED vs. OPEN (CRITICAL honesty)

PROVED (axiom-clean):
  * `one_le_dsq_of_odd` — `1 ≤ dsq p t` for odd `t` (odd lattice has no `D = 0`).
  * `fsum_le_fsum` — termwise monotonicity of `fsum`.
  * `dmomNfull_ge_acNfull_odd` — the EXACT two-point tie `V(odd t) ≥ 1`
    (`acNfull w t ≤ dmomNfull w t` for odd `t`, `0 ≤ w`).  The odd-family anchor and the `−2` corner.
  * `covBridge` — the full-range covariance bridge `4·xmomNfull + dmomNfull ≃ t²·acNfull`.

OPEN (unchanged — R1's uniform-in-`s` closure):
  * `CircleFourierPowerModel.SaddleVarianceFloor` (= R1), relocated onto
    `PolyaCertifiedFloor` (uniform Pólya positivity) and `ContinuumShadowFloor.ContinuumFloor`
    + `FiniteCorrectionBound` (elliptic modulus).  This file supplies the odd-family anchor
    `V(odd) ≥ 1` and the covariance reformulation, but does NOT discharge either residual: the odd
    floor still needs an upper bound on the even-centre variance `V(s+1)` (the coupled-two-chain
    obstruction), and the even floor still needs the sharp `(144/25) w²(1−w²)` envelope uniformly
    in `s`.  The Clay Yang–Mills mass gap remains OPEN.
-/

end YMGap.Continuum.EnvelopeClosure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EnvelopeClosure.one_le_dsq_of_odd
#print axioms YMGap.Continuum.EnvelopeClosure.fsum_le_fsum
#print axioms YMGap.Continuum.EnvelopeClosure.dmomNfull_ge_acNfull_odd
#print axioms YMGap.Continuum.EnvelopeClosure.covBridge
