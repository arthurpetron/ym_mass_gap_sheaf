# JTP convergence-assembly — how Gauss's q-binomial feeds the theta machinery

Companion to the Wall-2 (analytic, differentiated–Jacobi-triple-product) route.
This note specifies, precisely, how the finite **Gauss q-binomial identity**
(`GaussQBinom.gauss_qbinom_all`) plugs into the existing constructive convergence
machinery (`ThetaConv` / `ThetaConvGen`, `crealOfGeoIncrementBase`,
`geom_series_le_base`, `pow_base_le`) to assemble the full Jacobi triple product
(JTP) as a `CReal` limit, and then states the single genuinely-hard analytic
obligation — the term-by-term differentiation step — sharply, as a `CReal`
limit obligation.

All numerical claims below were re-verified with mpmath at 40 digits
(`.venv/bin/python`); the verifying snippets are summarized inline. All algebraic
finite identities were checked exactly in sympy before being written down.

Conventions (matching `heat-kernel-pos-notes.md` and the Lean sources):

- `a ∈ (0,1)` is the nome (`q = a` in the theta weight `a^{n²}`).
- `θ ∈ (0,π)`, `x = cos θ ∈ [−1,1]`, `s = sin θ > 0`, `z = e^{iθ}` (so `x = (z+z⁻¹)/2`).
- `factor c x = 1 + 2c·x + c²` (Lean `HKPos.factor`); for `c = a^{2k+1}`,
  `factor = (1 + a^{2k+1} z)(1 + a^{2k+1} z⁻¹)`.

---

## 0. The two finite objects and the one finite identity

**Gauss product (one-sided), Lean `GaussQBinom.qProd`:**
```
qProd z q N = ∏_{j=1}^{N} (1 + z·q^{2j−1}).
```

**Gauss sum (Gaussian-weight, q-binomial), Lean `GaussQBinom.gaussSum`:**
```
gaussSum z q N = Σ_{k=0}^{N} q^{k²} · ⟨N,k⟩_{q²} · z^k,     ⟨N,k⟩_Q = qbin Q N k.
```

**The VERIFIED-exact finite identity, Lean `GaussQBinom.gauss_qbinom_all`:**
```
qProd z q N  ≈  gaussSum z q N           (for every N, every z, q).        (G)
```
(sympy: `qProd z q N − gaussSum z q N ≡ 0` symbolically for `N ≤ 4`; the Lean
proof is the full induction via the q-Pascal recurrence `gaussTerm_pascal` /
`gaussSum_step`.)

Identity (G) is the *finite Gaussian-weight engine*: it converts a finite
**product** `∏(1+z q^{2j−1})` into a finite **Gaussian-weighted sum**
`Σ q^{k²}⟨N,k⟩ z^k`. The whole JTP-assembly is "let `N → ∞` on both sides of a
symmetrized version of (G)".

---

## 1. From Gauss(z)·Gauss(z⁻¹)·∏(1−q^{2j}) to ϑ₃ (series = product)

### 1.1 The exact finite bridge to the repo's `Ppart`

The theta partial product already carried as a `CReal` in
`ThetaConv.Ppart` / `ThetaConvGen` is, dropping the `(1−a^{2n})` prefactors,
exactly the **two-sided** Gauss product:

```
∏_{k<L} factor (a^{2k+1}) x  =  qProd z a L · qProd z⁻¹ a L,    z = e^{iθ}.   (B1)
```

(sympy/mpmath: `|qProd(z;L)·qProd(z⁻¹;L) − ∏_{k<L} factor| < 10^{-40}` for
`a=0.7, θ=1.1, L∈{3,6,10}`; the index match is `j = k+1`, `2j−1 = 2k+1`.)

So **applying (G) to each one-sided factor** rewrites the repo's finite
`factor`-product as a product of two finite Gaussian sums:

```
∏_{k<L} factor (a^{2k+1}) x  =  gaussSum z a L · gaussSum z⁻¹ a L.           (B2)
```

This is the precise sense in which Gauss's identity "is" the partial theta
product: **the product side of (G) already equals the partial JTP factor product
up to the `(1−q^{2j})` normalization** — no separate `1/(q²;q²)_k` limit of the
binomial is needed at finite `N`; the `⟨N,k⟩_{q²} → 1/(q²;q²)_∞·…` limit is the
*coefficient-wise* shadow of (B2) once `N→∞`, but the constructive route never
takes that coefficient limit in isolation — it takes the limit of the whole
products (B2), which is already engineered in `ThetaConvGen`.

### 1.2 The full ϑ₃ as the `N→∞` limit

Multiply (B2) by the prefactor product `∏_{j=1}^{L}(1−a^{2j})` and let `L→∞`:

```
ϑ₃(θ)  =  lim_{L→∞}  ( ∏_{j=1}^{L}(1−a^{2j}) ) · gaussSum z a L · gaussSum z⁻¹ a L
       =  Σ_{n=−∞}^{∞} a^{n²} z^n  =  1 + 2 Σ_{n≥1} a^{n²} cos(nθ).            (JTP)
```

(mpmath, 40 digits: `|Gauss(z;40)·Gauss(z⁻¹;40)·∏_{j≤40}(1−q^{2j}) − Σ_{|n|≤200} a^{n²}z^n|`
is `1.9·10^{−24}` at `a=0.5,z=1.3`, `2.3·10^{−7}` at `a=0.8` (slower, expected),
`2.0·10^{−31}` at `a=0.3` — convergence governed by `a^{N²}`-tails.)

The **series = product** equality `Σ a^{n²}cos nθ` vs `∏(1−a^{2n})(1+2a^{2n−1}cosθ+a^{4n−2})`
is itself verified exact (mpmath `< 10^{−40}`, `a=0.5`, `θ∈{0.3,π/2}`); in Lean it
is **(JTP) restricted to the diagonal** of (B2)·prefactor and is what
`gauss_qbinom_all` + the `Ppart`-limit deliver.

### 1.3 Which engine discharges each limit step

The convergence of (JTP) is **already constructively closed** for all `a∈(0,1)`,
because the limit of the *product side* is exactly the `CReal` built in this
session:

| Limit step | Engine | Lean theorem |
|---|---|---|
| `∏_{k<L} factor(a^{2k+1}) x` (with the `(1−a^{2n})` prefactors folded in) converges as a `CReal` | general-base geometric increment, base `r=a·a`, constant `Cgen a` | `ThetaConvGen.thetaConvCRealGen` (this session; `a≤1/16` removed) |
| single-step increment majorant `|Ppart(l+1)−Ppart l| ≤ Cgen a·(a·a)^l` | `crealOfGeoIncrementBase` | `ThetaConvGen.incr_le_gen`, `neg_incr_le_gen` |
| `(a·a)^l → 0` modulus (general base) | multiplicative Bernoulli + Archimedean | `HKConvGen.pow_base_le` (closes the old `KPLimit` gap) |
| geometric tail `Σ_{i<d}(a·a)^i ≤ 1/(1−a·a)` | geometric recurrence | `HKConvGen.geom_series_le_base` |
| product-magnitude bound `Ppart ≤ Bmag a` (the only place smallness entered) | prefix split at cutoff `K=thetaCutoff a` + Weierstrass `prodUpBound` on the shifted sequence | `ThetaConvGen.prodUp_Tcoef_le_Bmag`, `shift_smallness` |
| `S(x) = Σ 2a^{2n−1}/factorₙ` as `CReal`, all `a` | general-base geometric increment | `HKConvGen.sConvCReal_general` |

**Explicit remainder/modulus actually used.** The constructive route does *not*
bound the JTP via a Gaussian `a^{N²}` remainder (which would need the diagonal
coefficient form). Instead it uses the **geometric** single-step product
increment, whose modulus is the rational cutoff
```
N(ε) = powBaseCutoff (a·a) δ(ε),   δ(ε) = ε / ( Cgen a · 1/(1−a·a) ),
```
delivered by `pow_base_le` (so `(a·a)^{N(ε)} ≤ δ(ε)` and the telescoped tail
`(Cgen a/(1−a·a))·(a·a)^N ≤ ε`). The Gaussian super-geometric decay `a^{N²}` is
*faster* than this geometric rate; the geometric rate is what the engines
actually discharge, and it suffices.

So: for the **convergence of ϑ₃ (series=product)**, Gauss's identity (G) supplies
the *finite-N coefficient form* (B2) but is **not on the critical path** of the
constructive CReal limit — `ThetaConvGen` reaches the product limit directly via
the geometric engine. Where (G) becomes load-bearing is the **differentiated**
identity, §2: matching the *series* derivative against the *product* derivative
requires the Gaussian-weight sum form that only (G)/(JTP) provides.

---

## 2. The differentiated identity (the one genuinely-hard step)

### 2.1 The three derivative facts (all mpmath-verified to 40 digits)

With `D(θ) = Σ_{n≥1} n a^{n²} sin(nθ)`:

- **(A) Series derivative.** `ϑ₃'(θ) = −2 D(θ) = −2 Σ_{n≥1} n a^{n²} sin(nθ)`.
  (mpmath: `|`finite-difference `ϑ₃' − (−2D)| ≈ 10^{−22}`.)
- **(B) Product / log-derivative.** `ϑ₃'(θ) = −sin θ · ϑ₃(θ) · S(x)`, where
  `S(x) = Σ_{n≥1} 2a^{2n−1}/factor(a^{2n−1}) x` is the repo's `S`-factor. This is
  the term-by-term log-derivative of the JTP product:
  `d/dθ log factor(c) = (−2c sin θ)/factor(c)`, summed, times `ϑ₃`.
  (mpmath: `|ϑ₃'(product) − (−s·ϑ₃·S)| < 10^{−36}`; and the per-factor
  log-derivative sum matches the numeric `d/dθ log ∏` to `10^{−16}`.)
- **(C) The target G2 identity.** Combining (A),(B) with the Chebyshev reindexing
  `K_t·sin θ = a^{−1} D` (notes §2) gives
  `K_t(x) = ϑ₃(θ)·S(x)/(2a)`, the manifestly-nonneg product object `R`.
  (mpmath: `|K_t − ϑ₃·S/(2a)| < 10^{−39}` across `a∈{0.1,0.5,0.9}`,
  `θ∈{0.3, π/2, 2.5}` — note `ϑ₃` takes `θ`, `S` takes `x=cos θ`; conflating the
  two arguments is the easy numerical foot-gun.)

The equality of **(A) and (B)** — series-derivative `= −2D` vs product-derivative
`−sin θ·ϑ₃·S` — is the analytic crux. It is equivalent to differentiating the JTP
`Σ a^{n²}z^n = ∏(1−a^{2n})(1+a^{2n−1}z)(1+a^{2n−1}z⁻¹)` term by term in `θ` and
recognizing the result. Gauss's identity (G)/(JTP) is exactly what makes the two
sides the *same function* of `θ`; the derivative match is then a statement that
**differentiation commutes with the `N→∞` limit** on both representations.

### 2.2 The precise `CReal` differentiation obligation

State `D` and the product-derivative as `CReal`s and assert their equality. Two
convergent `CReal` sequences are in hand:

- **`Dseries`** — partial sums `D_M(θ) = Σ_{n=1}^{M} n a^{n²} sin(nθ)`. Term
  majorant `|n a^{n²} sin nθ| ≤ n a^{n²} ≤ n a^{n}` (since `a^{n²}≤a^{n}`), which
  is geometric-times-linear, hence a `CReal` via a `crealOfGeoIncrementBase`-style
  engine at base `a` with a linear prefactor (the same `(1+n(1−r))r^n≤1` Bernoulli
  trick already in `HKConvGen.bernoulli_pow`, applied to `n·a^n`). **This piece is
  mechanical** — no new mathematics, only wiring a `n·r^n` majorant.

- **`Dprod := (s/2)·ϑ₃·S`** — already a `CReal` (product of the
  `thetaConvCRealGen` and `sConvCReal_general` reals, times the rational `s/2`).

The obligation is then the single `CReal` equality
```
  Dseries  ≈  Dprod          i.e.   Σ_{n≥1} n a^{n²} sin nθ  =  (sin θ / 2)·ϑ₃(θ)·S(x).   (DIFF)
```
Equivalently, in the trig-free `U`-form used by `UTelescope`,
`K_t = a^{−1}·Dseries/s` and `R = ϑ₃·S/(2a)`, so **(DIFF) ⟺ `K_t = R`**
(`UTelescope.Kt_nonneg_of_residual` already reduces `K_t≥0` to exactly the single
convergence `Rtrunc M ≈ R`; (DIFF) is the content of that residual).

> **The `1/2` is load-bearing.**  In the `U`-grading the Lean `dSeriesCReal`
> realises `Dseries/s = Σ_{n≥1} n a^{n²} U_{n−1}(x)`, and the bare product object
> `ϑ₃·S` equals `2·dSeriesCReal` (NOT `dSeriesCReal`) — verified to 40 digits,
> ratio `= 2.0`.  The Lean residual must therefore target `(1/2)·ϑ₃·S` (`Rhalf`
> in `JTPIdentity.lean`), not the bare `ϑ₃·S`.  A previous Lean round dropped the
> `1/2`; corrected 2026-06-12 (see `docs/jtp-closure-progress.md`).

### 2.3 Why it is hard, stated sharply

(DIFF) is **not** a termwise rational identity at finite truncation: at finite
`M`/`L`,
```
  D_M(θ)   vs   (sin θ/2)·Ppart_L(θ)·S_{L'}(x)
```
do **not** agree — the truncations live in different gradings (linear-Gaussian
`n a^{n²}` partial sums vs a product of two geometric truncations). What is true
is the **limit** equality, and proving it constructively requires a
**derivative-of-a-convergent-product lemma**:

> **Lemma (the missing analytic input).** Let `P_L → P` be a `CReal` limit of a
> product `P_L(θ) = ∏_{k<L} g_k(θ)` with each `g_k` differentiable, `g_k > 0`,
> and suppose the log-derivative series `Σ_k g_k'/g_k` converges uniformly (here:
> with explicit geometric modulus, `|g_k'/g_k| ≤ 2a^{2k+1}/(1−a^{2k+1})² ≤ C·(a·a)^k`).
> Then `P` is differentiable and `P'(θ) = P(θ)·Σ_k g_k'/g_k` as a `CReal`, i.e.
> the finite-difference quotients `(P_L(θ+h) − P_L(θ))/h` converge (in `L` then
> `h→0`, uniformly) to `P(θ)·Σ g_k'/g_k`.

Concretely the obligation is a **double-limit interchange** `lim_{h→0} lim_{L→∞}
= lim_{L→∞} lim_{h→0}` with an explicit joint modulus. The geometric majorants
needed for the uniformity are *already available*:

- `|g_k'/g_k| = 2a^{2k+1} sin θ / factor(a^{2k+1}) ≤ 2a^{2k+1}/(1−a^{2k+1})²`,
  bounded by `C·(a·a)^k` via `HKPos.factorLB_pos` + the `geoAmp_eqv` exact
  `a^{2k+1}=a·(a·a)^k` — the same bound `ThetaConvGen.dBound_le_geo` uses.
- the second-derivative / remainder control for the `h→0` direction needs
  `|g_k''/g_k|`-type bounds, also `O((a·a)^k)` (the numerators are degree-≤2 in
  `c=a^{2k+1}`), giving a uniform `O(h)` Taylor remainder summable by
  `geom_series_le_base`.

What is **not** in the repo is the generic "differentiate a uniformly-convergent
constructive product/series term-by-term" engine (a constructive
`HasDerivAt`-of-`tsum` with explicit modulus). That engine — the bracketed Lemma
above, specialized to the geometric log-derivative modulus — is the *single*
remaining analytic obligation for Wall 2. Everything feeding it (the JTP equality
of the two function representations, both factors as `CReal`s for all `a`, the
finite telescoping `uTelescope_all`, the geometric moduli) is closed.

### 2.4 Honest status

- **Convergence (G1): CLOSED for all `a∈(0,1)`.** `ϑ₃` (`thetaConvCRealGen`),
  `S` (`sConvCReal_general`), and the product `R = ϑ₃·S ≥ 0` (`R_geRat_zero_gen`)
  are all genuine `CReal`s with explicit geometric moduli, axiom-clean.
- **Gauss engine (B2): exact and Lean-closed.** `gauss_qbinom_all` gives the
  finite Gaussian-sum form of each one-sided product; (B1)/(B2) are the exact
  bridges to `Ppart` (sympy-verified).
- **Differentiation (DIFF)/(G2): OPEN, and sharply localized.** The remaining gap
  is exactly the bracketed term-by-term differentiation lemma — a constructive
  derivative-of-convergent-product statement with the explicit `O((a·a)^k)`
  log-derivative modulus — equivalently the residual convergence
  `Rtrunc M ≈ R` of `UTelescope.Kt_nonneg_of_residual`. It is one analytic
  lemma, not a family; it introduces no new positivity content (positivity is
  already in `R ≥ 0`); it is the only place a genuine analysis engine
  (commuting `d/dθ` with the limit) is still required.

---

## Appendix — verification snippets (mpmath, 40 digits)

- **Gauss identity (G):** `qProd z q N − gaussSum z q N ≡ 0` (sympy, `N≤4`).
- **Bridge (B1):** `|qProd(z;L)·qProd(z⁻¹;L) − ∏_{k<L}factor| < 10^{−40}`
  (`a=0.7,θ=1.1,L∈{3,6,10}`).
- **JTP series=product:** `< 10^{−40}` (`a=0.5,θ∈{0.3,π/2}`).
- **Assembly (1.2):** `|Gauss(z;40)Gauss(z⁻¹;40)∏(1−q^{2j}) − Σ_{|n|≤200}a^{n²}z^n|`
  `= 1.9e−24 / 2.3e−7 / 2.0e−31` at `a=0.5/0.8/0.3`.
- **(A):** `|`fin-diff `ϑ₃' − (−2D)| ≈ 10^{−22}`.
- **(B):** `|ϑ₃'(product) − (−sinθ·ϑ₃·S)| < 10^{−36}`.
- **(C):** `|K_t − ϑ₃(θ)·S(cosθ)/(2a)| < 10^{−39}` (`a∈{0.1,0.5,0.9}`,
  `θ∈{0.3,π/2,2.5}`).
