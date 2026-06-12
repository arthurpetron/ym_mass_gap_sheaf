# JTP closure progress — Wall 2 (differentiated Jacobi-triple-product residual)

Companion to `docs/jtp-convergence-notes.md`.  Records what the Lean module
`lean/YMGap/Continuum/JTPIdentity.lean` closed, the explicit modulus used, and
the honest residual.

## What closed (new, axiom-clean Lean content)

1. **The quadratic–geometric majorant for the `K_t` series.**  The heat-kernel
   Chebyshev series `K_t(x) = a^{-1} Σ_{n≥1} n·a^{n²}·U_{n-1}(x)` has term
   magnitude `|(n+1)·a^{(n+1)²}·U_n(x)| ≤ (n+1)²·a^{(n+1)²}` (via the closed
   Chebyshev bound `|U_n|≤n+1`, `ChebU.absU_le`).  The polynomial factor
   `(n+1)²` is absorbed into the super-geometric Gaussian decay `a^{(n+1)²}` by
   **squaring** the existing multiplicative Bernoulli bound
   `HKConvGen.bernoulli_pow`:

   - `n_pow_le_invG` : `ofNat n · aⁿ ≤ 1/(1−a)`  (linear Bernoulli, divided by `1−a`).
   - `nsq_aa_pow_le` : `(ofNat n · ofNat n)·(a·a)ⁿ ≤ (1/(1−a))²`  (square of the above).
   - `gauss_le_geo`  : `a^{(n+1)²} ≤ a^{(n+1)}·(a·a)ⁿ`  (exponent split
     `(n+1)² = (n+1) + (n+1)·n`, with `(n+1)·n ≥ 2n` ⟹ `a^{(n+1)·n} ≤ (a·a)ⁿ`).
   - `dTermMaj_le`   : the assembled geometric majorant
     **`(ofNat(n+1)·ofNat(n+1))·a^{(n+1)²} ≤ Cmaj a · aⁿ`** at base `a < 1`,
     constant `Cmaj a = (a·(1/(1−a))²)·(1/(a·a))`.

   This is the genuine new mathematics: the repo previously had only the
   *linear* Bernoulli cancellation (`bernoulli_pow`); the squaring gives the
   `n²·rⁿ` polynomial×geometric summability the Gaussian-weight `K_t` series
   needs, with no new quadratic-Bernoulli engine.

2. **`K_t`-side partial sums as a convergent `CReal`** for ALL `a ∈ (0,1)`,
   `−1 ≤ x ≤ 1`:

   - `dTerm a x n = ofNat(n+1)·a^{(n+1)²}·U_n(x)`, `dPartial = finSum (dTerm …)`.
   - `dTerm_le` / `neg_dTerm_le` : the two-sided single-step increment bound
     `|dTerm l| ≤ Cmaj a · aˡ` (via `Q'.mul_le_of_bounds` + `ChebU.absU_le`).
   - `dSeriesCReal` : the partial sums fed to the general-base geometric engine
     `HKConvGen.crealOfGeoIncrementBase` at base `r = a`, constant `Cmaj a`.
     This is the genuine constructive realisation of `K_t·a` (the heat-kernel
     series, modulo the rational prefactor `a^{-1}`), `approx N = dPartial a x N`.

3. **The conditional closure `DiffJTP → K_t ≥ 0`** (`Kt_geRat_zero_of_diff`):
   given the residual identity `(DIFF)`, `K_t = dSeriesCReal ≥ 0` follows by
   feeding `dSeriesCReal`, the product object `R = ϑ₃·S`
   (`Rproduct`, with `R_geRat_zero_gen`-style approximation nonnegativity from
   `Rproduct_approx_nonneg`), and the residual into
   `UTelescope.Kt_nonneg_of_residual`.

## The explicit modulus used

- **`K_t`-side (closed here).**  Geometric base `r = a`, constant `Cmaj a`.
  Cauchy modulus `N(ε) = powBaseCutoff a δ(ε)` with
  `δ(ε) = ε / (Cmaj a · 1/(1−a))`, inherited from `crealOfGeoIncrementBase` /
  `HKConvGen.pow_base_le`.  (The Gaussian decay `a^{(n+1)²}` is *faster* than
  this geometric rate; the geometric rate is what the engine discharges and it
  suffices.)
- **Residual log-derivative modulus (NOT discharged).**  A constructive proof of
  `DiffJTP` would carry the `O((a·a)ᵏ)` log-derivative modulus of
  `jtp-convergence-notes.md §2.3`.

## The honest residual

`DiffJTP` (`= CReal.Equiv (dSeriesCReal …) (Rproduct …)`) is the single
remaining analytic obligation — the differentiated Jacobi-triple-product
identity `Σ n a^{n²} sin nθ = (sin θ/2)·ϑ₃·S`, equivalently `Rtrunc M ≈ R` of
`UTelescope.Kt_nonneg_of_residual`.  It is **NOT** discharged and is **NOT** a
`sorry`: it is exposed as a named `Prop` hypothesis, and only the conditional
`DiffJTP → K_t ≥ 0` is proved.

It is genuinely hard: a term-by-term differentiation of a convergent product (a
double-limit interchange `lim_h lim_L = lim_L lim_h`), NOT a finite identity (at
every truncation the two sides live in different gradings — linear-Gaussian
`n a^{n²}` partial sums vs a product of two geometric truncations).  It
introduces **no new positivity content** (positivity is already closed in
`ThetaConvGen.R_geRat_zero_gen`); it is purely an analysis engine (commuting
`d/dθ` with the limit).  The repo does not contain a constructive
`HasDerivAt`-of-`tsum` engine with explicit modulus, and that — specialised to
the geometric log-derivative modulus — is the sole outstanding Wall-2 lemma.

## Axiom status

All load-bearing declarations report `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`.

## Build / wiring

- Module: `lean/YMGap/Continuum/JTPIdentity.lean`; builds green standalone via
  `cd lean && lake build YMGap.Continuum.JTPIdentity`.
- To include in the default build, add to `lean/YMGap.lean` (after the
  `UTelescope` / `ThetaConvGen` imports):
  `import YMGap.Continuum.JTPIdentity`.
