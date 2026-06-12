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

## NEW: the finite-difference Leibniz engine (`DiffProduct.lean`)

A new module `lean/YMGap/Continuum/DiffProduct.lean` closes the **finite
algebraic skeleton** of the differentiation — the genuine pure-`Q'` core that any
constructive product-differentiation engine must rest on:

- `pre f L = ∏_{k<L} f k`, `sufLen g m d = ∏_{m≤k<m+d} g k` — general (no
  positivity) finite products over arbitrary `Q'`-factor sequences.
- `sufLen_append`, `pre_split` — the prefix/suffix split identities.
- `split_core` — the pure ring identity `Pf − Qg ≈ (P−Q)g + P(f−g)`.
- `leib_sum_extend` — appending a factor `g L` extends every suffix product;
  `finSum (leibTerm f g (L+1)) L ≈ (finSum (leibTerm f g L) L)·g L`.
- **`leibniz` (CLOSED, all `L`)** — the discrete product rule / finite-difference
  Leibniz identity:
  `∏_{k<L} f k − ∏_{k<L} g k ≈ Σ_{j<L} (∏_{k<j} f k)·(f j − g j)·(∏_{j<k<L} g k)`,
  by induction on `L`, pure `Q'.eqv` algebra, NO smallness/positivity hypotheses.

With `f k = factor(c_k)(θ+h)`, `g k = factor(c_k)(θ)`, dividing `leibniz` by `h`
is exactly the finite-difference Leibniz expansion of `(∏(θ+h) − ∏(θ))/h` — the
term-by-term product derivative whose `L→∞` then `h→0` limit is the log-derivative
series.  `leibniz` is that interchange's *finite skeleton*; it introduces no new
positivity content.  The remaining analytic step (the uniform double-limit) is
exposed as the named `Prop` `DiffProduct.ProductDerivativeLimit`, and
`JTPIdentity.DiffJTP` is identified with it definitionally
(`DiffJTP_eq_productDerivativeLimit`), with the conditional closure re-exposed as
`Kt_geRat_zero_of_productDerivativeLimit`.

All of `DiffProduct.lean` and the new `JTPIdentity` bridges are axiom-clean
(`[propext]` / `[propext, Quot.sound]`; no `Classical.*`, no `native_decide`, no
`sorry`).

## FACTOR-`1/2` CORRECTION (soundness fix, 2026-06-12)

The residual was previously stated as `DiffJTP = CReal.Equiv (dSeriesCReal) (Rproduct)`
with `Rproduct = ϑ₃·S` (NO `1/2`).  **That statement is numerically false.**
At every `a ∈ (0,1)`, `θ ∈ (0,π)`, the bare product equals TWICE the series:

    ϑ₃(θ)·S(cos θ)  =  2 · dSeriesCReal      (ratio = 2.0, verified to 40 digits
                                              at a = 0.2, 0.3, 0.5, 0.8).

The correct differentiated-JTP identity is `§2.1(C)` of the convergence notes,
`K_t = ϑ₃·S/(2a)`, i.e. in the `U`-grading carried by `dSeriesCReal`
(`= Σ_{n≥1} n a^{n²} U_{n−1}(x) = D(θ)/sin θ`):

    dSeriesCReal  ≈  (1/2)·(ϑ₃·S)  =  Rhalf.                                  (DIFF)

The previous round dropped the `1/2`.  Closing the un-halved version would have
closed a FALSE `CReal.Equiv`; since the obligation was never discharged this did
not propagate (the conditional `K_t ≥ 0` never fired), but the *named obligation
itself was wrong*.  Fixed in `JTPIdentity.lean`:

- new `Rhalf := CReal.mul (ofQ' half) Rproduct` and `Rhalf_approx_nonneg`,
- `DiffJTP` now `:= CReal.Equiv (dSeriesCReal) (Rhalf)` (the TRUE identity),
- `Kt_geRat_zero_of_diff` / `Kt_geRat_zero_of_productDerivativeLimit` /
  `DiffJTP_eq_productDerivativeLimit` all re-oriented through `Rhalf`.

All axiom-clean (`[propext]`/`[propext, Quot.sound]`); build green.

## The honest residual

`DiffJTP` (`= CReal.Equiv (dSeriesCReal …) (Rhalf …)`, with the corrected `1/2`)
is the single remaining analytic obligation — the differentiated
Jacobi-triple-product identity `Σ n a^{n²} sin nθ = (sin θ/2)·ϑ₃·S`, equivalently
`Rtrunc M ≈ R` of `UTelescope.Kt_nonneg_of_residual`.  It is **NOT** discharged
and is **NOT** a `sorry`: it is exposed as a named `Prop` hypothesis, and only the
conditional `DiffJTP → K_t ≥ 0` is proved.

### Why the matched-truncation strategy does NOT close it (sharp finding, 2026-06-12)

The proposed closure route — find finite truncations `seriesTrunc M ≈ productTrunc M`
matched at each level `M` — **cannot succeed**, and the obstruction is now pinned
down exactly.  Reindex `dSeriesCReal`'s partial sum as `dPartial M`.  Then
(verified to 40 digits):

1. `dPartial M = D_M/sin θ` **exactly**, where `D_M = −½·d/dθ(th3series_M)` and
   `th3series_M(θ) = 1 + 2Σ_{n≤M} a^{n²} cos nθ` is the finite theta-**series**
   truncation.  (So the series side IS the differentiated finite theta-series.)
2. The finite log-derivative `d/dθ(th3prod_M) = −sin θ·th3prod_M·Spart_M` holds
   **exactly** (pure product rule — this is what `DiffProduct.leibniz` captures).
   So `(1/2)·Ppart_M·Spart_M` is the differentiated finite theta-**product**.
3. BUT `th3series_M ≠ th3prod_M` at every finite `M`: the finite Gauss identity
   `gauss_qbinom_all` (`qProd = gaussSum`) equates the product and the Gaussian
   sum only for the FULL coefficient sum / `N → ∞`; truncating the series at `M`
   terms and truncating the product at `M` factors give **different** finite
   numbers (differences `~ (a·a)^M`, e.g. `0.18, 0.028, 0.0059, 0.0015, …` at
   `a = 0.5`).
4. Consequently `dPartial M` (super-geometric, `~ a^{(M+1)²}`: at `a=0.5` already
   `10^{−11}` from its limit by `M=5`) and `(1/2)·Ppart_M·Spart_M` (geometric,
   `~ (a·a)^M`: only `10^{−3}` by `M=5`) converge to the SAME limit at
   **different rates**.  There is **no** finite `M` at which they are equal, so
   no finite equal-at-each-level identity exists.

The two truncation families are genuinely distinct finite objects coinciding
only in the limit; `CReal.Equiv` between them therefore reduces to *the two
limits being equal*, which is precisely the differentiation–limit interchange
and is NOT a finite algebraic identity.  `DiffProduct.leibniz` supplies the
finite product rule (step 2) but cannot bridge the series↔product truncation gap
(step 3) — that bridge is the `M → ∞` limit of Gauss's identity differentiated,
i.e. the missing engine.

It is genuinely hard: a term-by-term differentiation of a convergent product (a
double-limit interchange `lim_h lim_L = lim_L lim_h`), NOT a finite identity.  It
introduces **no new positivity content** (positivity is already closed in
`ThetaConvGen.R_geRat_zero_gen`); it is purely an analysis engine (commuting
`d/dθ` with the limit).  The repo does not contain a constructive
`HasDerivAt`-of-`tsum` engine with explicit modulus, and that — specialised to
the geometric log-derivative modulus — is the sole outstanding Wall-2 lemma.

## Axiom status

All load-bearing declarations report `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`.

## Build / wiring

- Modules: `lean/YMGap/Continuum/DiffProduct.lean` (the finite Leibniz engine)
  and `lean/YMGap/Continuum/JTPIdentity.lean` (imports `DiffProduct`); both build
  green via `cd lean && lake build YMGap.Continuum.DiffProduct
  YMGap.Continuum.JTPIdentity`.
- To include in the default build, add to `lean/YMGap.lean` (after the
  `UTelescope` / `ThetaConvGen` imports):
  `import YMGap.Continuum.DiffProduct`
  `import YMGap.Continuum.JTPIdentity`.
