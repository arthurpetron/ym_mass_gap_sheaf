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
  one-step, or lag-`k_j`, ratio bound with `side_j (1 − ρ_j)` BOUNDED (any constant; see §7).
  The `c < 1` of §2 is an artifact of a single Bernoulli step.
- That ratio bound is still the nontriviality core. It is not proved for any YM trajectory,
  and `ExprHRay` with this rate is OPEN.

## 6. Build record

- Built on the box under the caps: `safe_lean_build.py --jobs 1`, `LEAN_NUM_THREADS=1`, `nice -n 10`,
  worker cap 3 GiB, reserve 1.5 GiB, 1800 s process-group timeout, 10 s sampler with abort below 1.5 GiB.
- One module was rebuilt; the imports were already up to date. Wall time ~10 s.
- `#print axioms`: every theorem is within `{propext, Quot.sound}`. `theta_pos` and `boxKernel_nonneg` use `[propext]` only.
- No warnings. `lean_forbidden_token_scan.py` reports `executable_forbidden_hits 0`.

## 7. Any bounded rate: block Bernoulli (follow-up, same day)

Module: `lean/YMGap/Continuum/BF4WilsonAllNomeExprStepRatioAnyC.lean` (new leaf). The `c < 1`
theorems above are kept, and they are still true.

- `thetaC C := (1/2)^(2C+2)`, with `thetaC_pos` and `thetaC_le_one`.
- **`block_pow_floor ρ c C s`**: hypotheses `1 ≤ C`, `2C ≤ s`, `0 ≤ ρ ≤ 1`, `c ≤ ofNat C` and
  `ofNat s · (1 − ρ) ≤ c`. Conclusion: `(1/2)^(2C+2) ≤ ρ^(s/2+1)`.
  - Blocks: `q = ⌊s/(2C)⌋ ≥ 1`, with `s = 2Cq + r` and `r < 2C`.
  - Per block: `2Cq(1−ρ) ≤ s(1−ρ) ≤ C`, so `q(1−ρ) ≤ 1/2`. Bernoulli then gives `ρ^q ≥ 1 − q(1−ρ) ≥ 1/2`.
  - Count: `s/2 + 1 ≤ Cq + C ≤ (2C+2)q`, using `Cq ≥ C`. So `ρ^(s/2+1) ≥ ρ^((2C+2)q) = (ρ^q)^(2C+2) ≥ (1/2)^(2C+2)`.
  - `C = 0` is excluded (`1 ≤ C`). For `0 ≤ c ≤ 1`, take `C = 1`, giving θ = 1/16.
- `thetaC_c0`: `c0 = 2^(2C+3)` satisfies `2(1−θ_C) ≤ θ_C c0`, since `θ_C · 2^(2C+3) = 2`.
- **`expr_windowSurvivalFrom_of_stepRatio_anyC tr ρ k c C j0`**:
  - Hypotheses: `1 ≤ C`, `c ≤ C` and `2C ≤ side_{j0}`; for `j ≥ 1`, `0 ≤ ρ_j` and `k_j ≤ side_j/2`;
    for `j ≥ j0`, `ρ_j ≤ 1` and `side_j(1−ρ_j) ≤ c`; and `ExprStepRatio tr ρ k`.
  - Conclusion: `ExprShiftedWindowSurvivalFrom tr j0 θ_C`, i.e. `θ_C R_j(side_j/2) ≤ R_j(side_j+1)` for `j ≥ max(1, j0)`.
- `expr_windowSurvivalFrom_of_hray_anyC`: the same from `ExprHRay` on `x_j`, with `k = 0`.

## 8. Small scales (`j < j0`): choice and reason

With only `0 ≤ ρ_j ≤ 1`, a scale with `side_j < 2C` can have `ρ_j` near 0, so
`s(1−ρ) ≤ c` alone gives no uniform θ there. I did not weaken anything silently:

- **(a), used for the package.** `ExprShiftedWindowSurvivalFrom tr j0 θ` (`∀ j ≥ j0, j ≥ 1`).
  - The A03 package only reads scales `j ≥ a`. Its input `ExprShiftedEpsBound tr c0` is over ALL `j`.
  - But at any scale with `side_j ≤ c0` that bound holds TRIVIALLY, for any vector:
    `oneStepEpsBound_le` gives `side_j (R(0) − R(1)) ≤ side_j R(0) ≤ c0 R(0)`.
  - So `exprShiftedEpsBound_of_windowSurvivalFrom` needs survival only for `j ≥ j0`, plus
    `side_j ≤ c0` for `j < j0`. These small scales are proved, not assumed.
  - `expr_normalized_anchor_of_windowSurvivalFrom` is the package from the From-version.
  - `windowSurvivalFrom_zero_iff` shows the From-version is the original Prop at `j0 = 0`.
- **(b), also provided.** `expr_windowSurvival_of_stepRatio_anyC_small`: an explicit small-scale
  constant `θ_s` for `1 ≤ j < j0`, and any `θ ≤ θ_C`, `θ ≤ θ_s`, give the FULL `ExprShiftedWindowSurvival tr θ`.
- (c) `side_j = 2^j`, so `2C ≤ side_{j0}` holds as soon as `j0 ≥ log₂(2C)`.

## 9. Combined A03 one-liner and how the constants scale with C

**`expr_normalized_anchor_of_hvar_hray_anyC tr c δ C j0 a`** has these hypotheses:
- `1 ≤ a`, `1 ≤ C`, `c ≤ C`;
- `2C ≤ side_{j0}` and `j0 ≤ 2C+4`;
- `0 ≤ δ < 1` and `2^(2C+3) ≤ side_a · δ`;
- `ExprHVar tr v` and `ExprHRay tr ρ`;
- for `j ≥ j0`, `ρ_j ≤ 1` and `side_j(1−ρ_j) ≤ c`.

Conclusion: `ExprShiftedAnchorPackage tr δ _ a (exprNondegFloor tr v ρ) _`.

Constants: θ = θ_C = 2^−(2C+2) and c0 = 2^(2C+3). The small scales `j < j0 ≤ 2C+4` have
`side_j ≤ 2^(2C+3) = c0`, so they are trivial.

HONEST FLAG: `side_a ≥ 2^(2C+3)/δ`, which is exponential in C. So the anchor scale `a` grows
linearly in C, roughly `a ≈ 2C + 3 + log₂(1/δ)`. For the measured `ε·side ≈ 2.4` (C = 3):
θ = 1/256, c0 = 512, `side_a ≥ 512/δ`.

## 10. Gap side with θ_C, and the sharpness remark

- `expr_windowSurvivalFrom_forces_rate_c0`: the pointwise From-version of the gap-side result.
- **`expr_stepRatio_forces_rate_anyC`**: the hypotheses of §7, plus `ExprShiftedNondegenerate` and
  `ExprPathOrbitContraction r` with `0 ≤ r ≤ 1`, give `side_j (1 − r_j) ≤ 2^(2C+3)` for `j ≥ max(2, j0)`.
  - This is `side_j(1−r_j) ≤ 2/θ_C`, which is at least `2(1−θ_C)/θ_C`.
  - It is consistent with the numerics `ε·side ≈ 2.4`: there is no contradiction, and a bounded `side_j(1−r_j)` is allowed.
- Sharpness: the true bound is `ρ^(s/2+1) ≥ (1−c/s)^(s/2+1) ≈ e^(−c/2)`, about 0.3 at `c ≈ 2.4`.
  That would need constructive exp/log lower bounds, which are not used here. The block
  constant `2^−(2C+2)` is far from sharp.
  - Finer blocks (`q(1−ρ) ≤ 1/m`) would approach `e^(−c/2)` as `m → ∞`. This is not done.

## 11. Build record (follow-up)

- Both `ExprStepRatioWindowSurvival` (docstring wording only) and `ExprStepRatioAnyC` were rebuilt
  on the box under the same caps, about 20 s wall.
- The first anyC build compiled but had one unused-variable warning. I removed that parameter;
  the final build has no warnings.
- `#print axioms`: every declaration is within `{propext, Quot.sound}`.
- `lean_forbidden_token_scan.py` reports `executable_forbidden_hits 0`.

## 12. Roles separated: the realistic frontier (follow-up)

- **Vacuity caveat.** The `k = 0` H-ray survival corollaries (`expr_windowSurvival_of_hray`,
  `expr_windowSurvivalFrom_of_hray_anyC`, `expr_normalized_anchor_of_hvar_hray_anyC`) are
  likely vacuous on raw slab vectors. UV contamination keeps the one-step ratio of a raw slab
  vector far from 1, so `side_j(1−ρ_j)` is not bounded there.
- **Realistic frontier.** The intermediate-lag step-ratio version on the smoothed state is
  the realistic frontier. That is what YM Numerics is measuring: `side·(1 − R(k+1)/R(k))` at
  `k = 0, 1, 2, side/4`.
- **New theorem `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC`.** It separates the two
  jobs of `ρ`:
  - H-var + H-ray (any `ρ_j > 0`) are used only for nondegeneracy.
  - `ExprStepRatio tr ρ' k` gives survival, at lag `k_j ≤ side_j/2` on the smoothed window
    response `R_j`, with its own rate `side_j(1−ρ'_j) ≤ c ≤ C` for `j ≥ j0`.
  - The constants are the same as in §9.
- The two earlier theorems got docstring caveats only; their statements are unchanged.
- Build: rebuilt the anyC module only, ~10 s wall. Axioms are within `{propext, Quot.sound}`; no warnings.

## 13. Even-lag step ratio = propagated lag-0 energy (REFORMULATION ONLY)

Module: `lean/YMGap/Continuum/BF4WilsonAllNomeExprPropagatedEnergy.lean` (new leaf).

This is a reformulation only. It makes NO progress on the open input, which is a bounded
intermediate-lag step-ratio rate. It restates that input equivalently.

Generic carrier results:
- `propagated_response x m n : B(T^m x, T^n T^m x) = B(x, T^(2m+n) x)`. This comes from
  self-adjointness via the existing `shift_response_pin`.
- `propagated_norm`: `B(φ,φ) = R(2m)`.
- `stepRatio_of_energy x L (0 < L) c`: `OneStepEpsBound x L c` gives
  `(1 − c·L⁻¹) B(x,x) ≤ B(x,Tx)`. `OneStepEpsBound` is the multiplied-out
  `L(B(x,x) − B(x,Tx)) ≤ c B(x,x)`. `energy_rate_side` gives `L(1 − ρ') ≤ c`, and in fact `= c`.
- `energy_of_stepRatio`: `ρ B(x,x) ≤ B(x,Tx)` with `L(1−ρ) ≤ c` gives `OneStepEpsBound x L c`.
  So the two forms are equivalent.

Expr layer results:
- `ExprPropagatedEnergy tr m c j0`: for `j ≥ j0`, `j ≥ 1`,
  `OneStepEpsBound (T^(m_j) Y_j) side_j c`, on the smoothed state.
- `stepRatio_of_propagatedEnergy`: it gives
  `ExprStepRatio tr (propagatedRate c j0) (fun j => 2 m_j)`.
  - The rate is `1 − c/side_j` for `j ≥ j0`.
  - It is `0` for `j < j0`, which is trivial since `R ≥ 0`.
- `propagatedEnergy_of_stepRatio`: the converse, given `side_j(1−ρ'_j) ≤ c`.
- `expr_normalized_anchor_of_hvar_hray_propagatedEnergy_anyC`: the A03 package from
  H-var + H-ray (nondegeneracy only), plus `ExprPropagatedEnergy tr m c j0`.
  - It requires `m_j ≤ side_j/4` and `0 ≤ c ≤ C`.
  - The constants and side conditions are those of §9/§12.

Index and sign details:
- `m_j ≤ side_j/4` gives `2m_j ≤ side_j/2` with Nat division, so no adjustment is needed.
- `0 ≤ c` is needed for `ρ' ≤ 1`.
- `ρ' ≥ 0` uses `c ≤ C ≤ side_j`, which holds for `j ≥ j0`.

Build: 1 module, ~10 s wall, on the box under the usual caps. All 12 declarations are
`[propext, Quot.sound]`. No warnings. `executable_forbidden_hits 0`.

## 14. Convexity sandwich: early window ⇔ late step ratio (REFORMULATION ONLY)

Module: `lean/YMGap/Continuum/BF4WilsonAllNomeExprConvexitySandwich.lean` (new leaf).

This is a reformulation only. It makes NO progress on the open input, which is a bounded
intermediate-lag step-ratio rate, or equivalently a window bound. It shows the window and
step-ratio forms are equivalent up to a factor-2 lag shift AND A LOSS OF CONSTANTS.
The equivalence is not exact.

Generic carrier results, with `R(n) = B(x, T^n x)` and `D(n) = R(n) − R(n+1)`:
- `response_diff_antitone`: `D(n+1) ≤ D(n)`. It comes from `∇²R(n) = mixedMoment x n 2 ≥ 0`,
  via `mixedMoment_eq_hausdorffDiff` and `mixedMoment_nonnegative_via_hankel`.
- `diff_sandwich` (`m ≤ k`): `(k−m+1) D(k) ≤ R(m) − R(k+1)`, by telescoping.
- `diff_sandwich_le`: `… ≤ R(m)`, since `R ≥ 0`.
- `side_le_four_window`: `s ≤ 4(s/2 − s/4 + 1)` for every Nat `s` (omega).
  So `s/((s/2 − s/4 + 1)θ) ≤ 4/θ`, with no Nat-division adjustment.
- `lagEnergy_of_window`: `θ R(s/4) ≤ R(s/2)`, `0 ≤ c` and `4 ≤ cθ` give
  `s (R(s/2) − R(s/2+1)) ≤ c R(s/2)`. No sign condition on `θ` is needed.
  `four_div_spec` shows `c = 4/θ` is admissible when `θ > 0`.
- `lagRatio_of_lagEnergy`: the energy form gives the ratio `1 − c/L` (pure algebra).

Expr layer results:
- `ExprEarlyWindow tr θ j0`: `θ R_j(side_j/4) ≤ R_j(side_j/2)` for `j ≥ j0`, `j ≥ 1`.
- `stepRatio_of_earlyWindow` gives `ExprStepRatio tr (propagatedRate c j0) (side/2)`.
  The rate is `1 − c/side_j` for `j ≥ j0`, so `side_j(1−ρ_j) = c`, and `0` below `j0`.
- Converse: `expr_earlyWindow_of_stepRatio_anyC`. A step ratio at `k_j ≤ side_j/4` with
  `side_j(1−ρ_j) ≤ c ≤ C` gives `ExprEarlyWindow tr θ_C j0`, with `θ_C = (1/2)^(2C+2)`,
  by block Bernoulli.
- Package: `expr_normalized_anchor_of_hvar_hray_earlyWindow_anyC`. It applies
  `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC` at `k_j = side_j/2`.

Clamping: NOT used, and no extra hypothesis is added.
- The rate is `1 − c/side_j`, not the sharp `1 − 1/((s/2−s/4+1)θ)`, which can be negative.
- `ρ_j ≥ 0` follows from the package's existing `c ≤ C ≤ side_j` for `j ≥ j0`.
- Below `j0` the rate is `0`, which is trivial since `R ≥ 0`.

Requirements:
- Lag `side_j/2` meets the package's `k_j ≤ side_j/2` with equality.
- The window hypothesis is used for `j ≥ j0`, `j ≥ 1`, matching the package.

Constants (honest):
- The input window `θ` and the package's output `θ_C = (1/2)^(2C+2)` are DIFFERENT numbers.
- The survival constant is `c ≥ 4/θ`, and it must satisfy `c ≤ C`. So `C ≳ 4/θ`, and then
  `θ_C ≪ θ`.
- The chain is: step ratio at lag ≤ s/4 ⇒ window [s/4,s/2] ⇒ step ratio at s/2 ⇒
  window [s/2,s+1]. Each arrow loses constants.

Build: 1 module, ~10 s wall, on the box under the usual caps. All 11 declarations are
`[propext, Quot.sound]`. No warnings. `executable_forbidden_hits 0`.

## 15. Two-sided band: step ratio + lower contraction ⇒ A03 + B04-shaped band (PACKAGING ONLY)

Module: `lean/YMGap/Continuum/BF4WilsonAllNomeExprTwoSidedBand.lean` (new leaf).

This is reformulation/packaging only. It makes NO progress on the nontriviality input (the
bounded step ratio) or on the gap input (the centered contraction with a lower margin).
Both stay OPEN.

**B04 shape found.** B04l consumes
`DynamicVacuumSectorPhysicalRateBand (trajectoryDynamicFamily ns gap)`. Its fields are
`floor, ceiling > 0` and `floor·2^-j ≤ 1 − (gap j).rate ≤ ceiling·2^-j`, where:
- `gap j : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData` is an
  ALL-VECTOR contraction on the SU(2) extent-one CUBE carrier;
- the open Prop `PathPhysicalContractionBand` is equivalent to this band.

**Expr-layer statements:**
- `ExprCenteredContractionLower tr r m` (OPEN):
  - `ExprPathOrbitContraction tr r`, an orbit contraction of the centered anchor;
  - `0 ≤ r_j ≤ 1`;
  - `0 < m` and `m·spacing_j ≤ 1 − r_j`.
- `lower_side_form` / `upper_spacing_form` convert between the spacing and side forms;
  `small_scale_upper` covers small scales.
- `ExprPhysicalRateBand r` is field-for-field B04l's band, with rate `r_j` and spacing `2^-j`.
- `expr_twoSidedBand_package`. Hypotheses: those of
  `expr_normalized_anchor_of_hvar_hray_stepRatio_anyC` (a step ratio with
  `side_j(1−ρ'_j) ≤ c ≤ C` at `k_j ≤ side_j/2`, including `k_j = side_j/2`) plus
  `ExprCenteredContractionLower tr r m`. Conclusions:
  - A03;
  - the two-sided bound `m ≤ side_j(1−r_j) ≤ 2^(2C+3)` for `j ≥ max(2,j0)`. The upper half
    comes from the compatibility theorem `expr_stepRatio_forces_rate_anyC`;
  - the NECESSARY consistency condition `m ≤ 2^(2C+3)`;
  - the band `exprTwoSidedBand`, with floor `m` and ceiling `2^(2C+3) + 2^(j0+2)`, at ALL
    scales.
- `b04Band_of_exprBand`: B04l's exact input, given ANY cube gap family with
  `(gap j).rate = r_j`. This is rational bookkeeping, NOT a bridge.

**Gap to B04, precisely:**
- (i) a cube contraction at every `w_j` (`PathCubeContraction`; the producer covers only
  `w ≤ 1/2`);
- (ii) the cube↔Wilson bridge identifying the transfers (see
  `audits/SCOPE-CUBE-WILSON-CARRIER-BRIDGE-2026-10-06.md`; verdict: needs analytic input);
- (iii) the Expr input is an orbit contraction, which is weaker than B04's all-vector one.

Build: ~12 s wall, under a 4.5 GiB MemAvailable reserve. All 9 declarations are
`[propext, Quot.sound]` (`ExprPhysicalRateBand` uses no axioms). No warnings.
