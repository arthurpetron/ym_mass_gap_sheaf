# Audit: window survival from a step-ratio bound (2026-10-06 PT)

Module: `lean/YMGap/Continuum/BF4WilsonAllNomeExprStepRatioWindowSurvival.lean` (new leaf, additive).
Imports: `BF4WilsonAllNomeExprWindowGapCompatibility`, `BF4WilsonAllNomeDyadicFilteredGeometricSurvival`
and `BondMovingRetuneFix`. All three were already built.

## 1. Existing results (question 1)

There is no prior "ray floor ⇒ window survival" theorem. A grep found no producer of
`PathShiftedWindowSurvival` or `ExprShiftedWindowSurvival` other than
`pathShiftedWindowSurvival_of_lagSurvival`, which assumes the stronger lag survival.

These existing pieces are reused here, not reproved:

- `BF4WilsonAllNomeResponseLower.response_step_lower` (needs `0 ≤ ρ`):
  `ρ R(0) ≤ R(1)` ⇒ `ρ R(n) ≤ R(n+1)` for all `n`.
  `response_geometric_lower` gives `ρ^n R(0) ≤ R(n)`.
- `BF4WilsonAllNomeDyadicFilteredGeometricSurvival.response_shifted_step_lower` and
  `response_shifted_geometric_lower`, the start-lag-`k` versions:
  `ρ R(k) ≤ R(k+1)` ⇒ `ρ R(k+l) ≤ R(k+l+1)` and `ρ^l R(k) ≤ R(k+l)`.
  These are division-free. Each step uses `R(n+2) − 2ρR(n+1) + ρ²R(n) = B(x, T^n (T−ρ)² x) ≥ 0`
  (`response_second_difference`), so the case `R(n−1) = 0` never arises and no positivity of R is needed.
- `BondMovingRetuneFix.bernoulli_oneSub`: `1 − p t ≤ (1−t)^p` for `0 ≤ t ≤ 1`, constructive over `Q'`.
- Related, but about the MACRO ratio rather than the window:
  - `OddResponseJensen.macro_ratio_of_oneStep_floor`: `ρ^s R(s) ≤ R(2s)`, needs a norm floor.
  - `macro_ratio_of_oneStep_block`: `(1−δ)^k R(s) ≤ R(2s)` for `s = Lk`, `Lt ≤ δ < 1`.

## 2. New theorems (exact statements)

`tr : ExprAnchorTrajectory`. `R_j(n) = tr.response j n = B(Y_j, T^n Y_j)`, where `Y_j = tr.state j`.

- `bernoulli_pow ρ (0 ≤ ρ) (ρ ≤ 1) n : 1 − ofNat n · (1 − ρ) ≤ ρ^n`.
- `theta_le_window_pow ρ c s (2 ≤ s) (0 ≤ ρ) (ρ ≤ 1) (ofNat s · (1−ρ) ≤ c) : 1 − c ≤ ρ^(s/2+1)`.
- `def ExprStepRatio tr ρ k := ∀ j ≥ 1, ρ_j · R_j(k_j) ≤ R_j(k_j+1)`.
- `expr_window_pow_of_stepRatio`: from `0 ≤ ρ_j`, `k_j ≤ side_j/2` and `ExprStepRatio`, for `j ≥ 1`:
  `ρ_j^(side_j/2+1) · R_j(side_j/2) ≤ R_j(side_j+1)`.
- **`expr_windowSurvival_of_stepRatio tr ρ k c`**: hypotheses `0 ≤ ρ_j ≤ 1`, `k_j ≤ side_j/2` and
  `ofNat side_j · (1 − ρ_j) ≤ c` for all `j ≥ 1`, plus `ExprStepRatio tr ρ k`. Conclusion:
  `ExprShiftedWindowSurvival tr (1 − c)`, i.e. `(1 − c) R_j(side_j/2) ≤ R_j(side_j+1)` for `j ≥ 1`.
  - **θ = 1 − c**. It uses `side_j/2 + 1 ≤ side_j` for `j ≥ 1`.
  - `theta_pos : c < 1 → 0 < 1 − c`.
  - The sharper per-scale form `θ_j = 1 − (side_j/2+1)(1−ρ_j) = 1 − c(1/2 + 1/side_j)` is
    `bernoulli_pow` + `expr_window_pow_of_stepRatio`.
  - `ρ_j ≤ 1` costs nothing: since `R ≥ 0`, a ratio with `ρ > 1` implies the ratio with `ρ = 1`.

Math check: the product of ratios from `n = side/2` to `side` has `side/2 + 1` factors, so the
exponent is right. Bernoulli gives `≥ 1 − (side/2+1)(1−ρ) ≥ 1 − side(1−ρ) ≥ 1 − c`.

## 3. Which object the ratio lives on

`ExprStepRatio` is stated on the window response `R_j` of the SMOOTHED state `Y_j`, the
same object as in `ExprShiftedWindowSurvival` (`tr.response`). Data on the CENTERED vector
`x_j` transfers to it:

- `exprResponse_step_of_lagRatio`: `ρ R_x(k) ≤ R_x(k+1)` ⇒ `ρ R_Y(n) ≤ R_Y(n+1)` for every `n ≥ k`.
  - `R_Y(n) = Σ_m Σ_i a_m a_i R_x(m+i+n)` with box weights `a ≥ 0`, and `m+i+n ≥ k`.
  - Weight nonnegativity is `timeKernel_nonneg`; the monotone sum is `responseSum_ratio_mono`.
- `exprResponse_step_of_ray`: the same with the H-ray form `ρ B(x,x) ≤ B(x,Tx)`, at every `n`.
- `expr_stepRatio_of_hray : ExprHRay tr ρ → ExprStepRatio tr ρ (fun _ => 0)`.
- `expr_windowSurvival_of_hray`: `ExprHRay tr ρ`, `ρ_j ≤ 1` and `side_j(1−ρ_j) ≤ c` ⇒
  `ExprShiftedWindowSurvival tr (1 − c)`.

So `k = 0` data on `x_j` transfers through smoothing. The `T^(side/2)` shift needs no
transfer, because the window is stated through lags `side/2` and `side+1` of `R_Y`.

## 4. Compatibility with the gap side

- `expr_stepRatio_forces_rate_c0`: the hypotheses of §2 with `c < 1`, plus
  `ExprShiftedNondegenerate tr fl` (`fl > 0`) and `ExprPathOrbitContraction tr r` (`0 ≤ r ≤ 1`),
  give `ofNat side_j · (1 − r_j) ≤ c0` for `j ≥ 2` whenever `2(1−θ) ≤ θ c0` with θ = 1 − c.
  This is the composition with `expr_windowSurvival_forces_rate_c0`.
- `expr_stepRatio_zero_contraction`: a lag-0 ratio plus the contraction give
  `ρ_j² R_j(0) ≤ r_j² R_j(0)`.
  - With `R_j(0) > 0` this means `ρ_j ≤ r_j`, hence `side_j(1−r_j) ≤ side_j(1−ρ_j) ≤ c`, consistent with `≤ c0`.
  - The cancellation of `R_j(0)` is NOT formalized; it is stated here only.

## 5. Scope (honest)

- This is a SUFFICIENT condition only.
- It moves the open input from a lag-`side_j` correlator lower bound (window survival) to a
  one-step, or lag-`k_j`, ratio bound `side_j (1 − ρ_j) ≤ c < 1`.
- That ratio bound is still the nontriviality core. It is not proved for any YM trajectory,
  and `ExprHRay` with this rate is OPEN.

## 6. Build record

- Built on the box under the caps: `safe_lean_build.py --jobs 1`, `LEAN_NUM_THREADS=1`, `nice -n 10`,
  worker cap 3 GiB, reserve 1.5 GiB, 1800 s process-group timeout, 10 s sampler with abort below 1.5 GiB.
- One module was rebuilt; the imports were already up to date. Wall time ~10 s.
- `#print axioms`: every theorem is within `{propext, Quot.sound}`. `theta_pos` and `boxKernel_nonneg` use `[propext]` only.
- No warnings. `lean_forbidden_token_scan.py` reports `executable_forbidden_hits 0`.
