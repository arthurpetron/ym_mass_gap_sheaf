# Heat-kernel pointwise positivity — notes

Companion to `lean/YMGap/Continuum/HeatKernelPos.lean` (namespace
`YMGap.Continuum.HKPos`).  This is "Piece A" of the uniform SU(2) heat-kernel
PSD program: the pointwise bound `K_t(θ) ≥ 0` for `θ ∈ (0,π)`.

## 1. The statement

The SU(2) class-function heat kernel is

```
K_t(θ) = Σ_{s≥0} (s+1) · a^{s(s+2)} · χ_s(θ),   χ_s(θ) = sin((s+1)θ)/sin θ,
```

with `a = e^{−t/2} ∈ (0,1)`.  We want `K_t(θ) ≥ 0` for `θ ∈ (0,π)`.

## 2. The analytic reduction (numerically verified to 40 digits)

Reindex the Chebyshev sum.  With `sin θ > 0` on `(0,π)`:

```
K_t(θ)·sin θ = a^{-1}·D(θ),     D(θ) = Σ_{n≥1} n a^{n²} sin(nθ) = −½ ϑ₃'(θ),
```

where the theta function is `ϑ₃(θ) = 1 + 2 Σ_{n≥1} a^{n²} cos(nθ)`.  Hence

```
K_t ≥ 0 on (0,π)   ⟺   ϑ₃'(θ) ≤ 0   ⟺   ϑ₃ is decreasing on [0,π].
```

The numerical check (`/tmp/heat_verify.py`, reproduced below in spirit) confirms
`K_t(θ) ≥ 0`, the identity `K_t·sin θ − a^{-1}D = 0`, and the series-vs-product
agreement of `ϑ₃` to `< 10^{-35}` across `a ∈ {0.1, 0.5, 0.9}`,
`θ ∈ {0.3, π/2, 3.0}`.

### Jacobi triple product

```
ϑ₃(θ) = ∏_{n≥1} (1 − a^{2n}) · (1 + 2 a^{2n-1} cos θ + a^{4n-2}).
```

Each factor is positive:

* `(1 − a^{2n}) ∈ (0,1)` for `a ∈ (0,1)`;
* `1 + 2 a^{2n-1} cos θ + a^{4n-2} = |1 + a^{2n-1} e^{iθ}|² ≥ (1 − a^{2n-1})² > 0`.

So `ϑ₃ > 0`.

### Monotonicity (the log derivative)

```
ϑ₃'(θ)/ϑ₃(θ) = Σ_{n≥1}  (−2 a^{2n-1} sin θ) / (1 + 2 a^{2n-1} cos θ + a^{4n-2}).
```

For `θ ∈ (0,π)`: `sin θ > 0`, every denominator `> 0`, so every term is `≤ 0`.
Thus `ϑ₃'/ϑ₃ ≤ 0` and (since `ϑ₃ > 0`) `ϑ₃' ≤ 0`.  Therefore `D ≥ 0` and
`K_t ≥ 0`.

## 3. What is formalized constructively (the heart)

The genuinely-constructive, genuinely-closeable core is the **termwise algebra**,
formalized as exact `Q'` inequalities over the project's constructive rationals.
The per-factor amplitude `c = a^{2n-1}`, the angle datum `x = cos θ ∈ [−1,1]`,
and `s = sin θ ≥ 0` are carried as rational parameters.

Define (Lean: `HKPos.factor`, `HKPos.factorLB`):

```
factor   c x = 1 + (2c·x + c·c)     (the n-th Jacobi factor)
factorLB c   = (1 − c)·(1 − c)       (its square-completion lower bound)
```

Proved theorems (all axiom-clean: `[propext]` or `[propext, Quot.sound]`):

| Lean name | Statement |
|---|---|
| `factor_sub_factorLB_eqv` | `factor c x − factorLB c ≃ 2c·x + 2c` (the exact square-completion identity `= 2c(x+1)`) |
| `two_c_x_plus_two_c_nonneg` | `0 ≤ 2c·x + 2c` for `−1 ≤ x`, `0 ≤ c` |
| `factorLB_le_factor` | `(1−c)² ≤ 1 + 2c·x + c²` for `−1 ≤ x`, `0 ≤ c` — **the square completion** |
| `one_sub_pos` | `0 < 1 − c` for `c < 1` |
| `factorLB_pos` | `0 < (1−c)²` for `c < 1` |
| `factor_pos` | `0 < 1 + 2c·x + c²` for `0 ≤ c`, `c < 1`, `−1 ≤ x` — **each Jacobi factor is positive** |
| `logderiv_term_numer_nonpos` | `−2c·s ≤ 0` for `0 ≤ c`, `0 ≤ s` — **each log-derivative term is `≤ 0`** |
| `thetaTrunc_pos` | `0 < ϑ₃^{(M)}(x) = ∏_{n<M} factor cₙ x` (finite product of positive factors) |
| `thetaTrunc_geo_pos` | the same at the **actual** amplitudes `cₖ = a^{2k+1}`, for `a ∈ (0,1)`, `x ∈ [−1,1]`, any depth `M` |

Supporting `Q'` lemmas proved here (not in the base API): `q_mul_pos`
(strict product positivity), `q_lt_of_le_of_lt` (≤-then-< transitivity),
`pow_le_one`, `pow_succ_le_self`, `pow_pos`, `pow_succ_pos_lt_one` (powers of
`a ∈ (0,1)` lie in `(0,1)`).

The key algebraic identity, verified symbolically:

```
1 + 2cx + c² − (1−c)² = 2cx + 2c = 2c(x+1)   ≥ 0   when x ≥ −1, c ≥ 0.
```

This is the whole content of "each Jacobi factor dominates `(1−c)² > 0`", and
it is what `factorLB_le_factor` + `factorLB_pos` ⟹ `factor_pos` encode.

## 4. The precise remaining gap (honest)

The module does **not** close the full infinite-product monotonicity
`ϑ₃'(θ) ≤ 0` as a single `CReal` statement.  Two steps are deliberately left,
both named in the Lean header:

* **(G1) Convergence as `CReal` with explicit modulus.**  The decay `a^{n²}` is
  super-geometric, so the infinite product `ϑ₃` and the series `D` converge with
  an explicit modulus (engine: `Continuum/KPLimit.lean`'s `crealOfGeoIncrement`,
  driven by the geometric-tail bounds in `Constructive/GeometricTail.lean`).
  Wiring the `a^{2n-1}`-amplitude product through that engine is mechanical but
  lengthy and is not done here.

* **(G2) Partial-sums ⟹ limit for the sign.**  Passing the termwise sign
  `Σ_{n<M} (term_n) ≤ 0` to `ϑ₃'/ϑ₃ ≤ 0` in the limit is a monotone-limit /
  `geRat`-style step (the `geRat` dual lower-bound machinery in
  `Constructive/ExpPos.lean` is the right tool: every partial sum of nonpositive
  terms is `≤ 0`, and `geRat`/`leRat` lifts that to the `CReal` limit).

Neither is faked or stubbed.  What is delivered is the complete termwise
algebra (factor positivity + log-derivative term sign), the finite-truncation
positivity, and the discharge of the amplitude-range side conditions at the real
heat-kernel amplitudes.  Everything is axiom-gated; the file contains no `sorry`.

## 5. Verdict

The constructive *algebraic engine* of the heat-kernel positivity proof is fully
in place and machine-checked: the square completion that makes every Jacobi
factor positive, the sign of every log-derivative term, and the positivity of
every finite truncation of `ϑ₃` at the actual amplitudes.  What remains (G1, G2)
is the analytic plumbing — constructive convergence with modulus, and a
monotone-limit pass from partial sums — for which the repo already has the
engines (`crealOfGeoIncrement`, `geRat`).  This is exactly the "do as much as
genuinely closes, honestly" outcome: the hard *positivity content* is closed;
the remaining work is wiring, not new mathematics.

## 6. Part 2 — the CReal-level positive object `R = (ϑ₃/2a)·S`

A second module (namespace `YMGap.Continuum.HKPos2`) carries the Part-1 termwise
algebra up to the `CReal` order, formalizing the genuinely-closeable parts of
the PRODUCT representation.

### 6.1 The trig-free target and its product form

In `x = cos θ ∈ [−1,1]`, `a ∈ (0,1)`:

```
K_t(x) = a^{-1} Σ_{n≥1} n·a^{n²}·U_{n-1}(x)          (Chebyshev-U series)
       = (ϑ₃(x)/2a)·S(x),                            (product representation)
S(x)   = Σ_{n≥1} 2·a^{2n-1} / (1 + 2·a^{2n-1}·x + a^{4n-2}),
ϑ₃(x)  = ∏_{n≥1} (1 − a^{2n})·(1 + 2·a^{2n-1}·x + a^{4n-2}).
```

Both factors are manifestly nonnegative, so `R := (ϑ₃/2a)·S ≥ 0`; via the
identity `K_t = R`, `K_t ≥ 0`.  The identity `K_t(x) = R(x)` was verified
symbolically (mpmath, 40 digits) across `a ∈ {0.1,0.5,0.9}`,
`x ∈ {−1,−0.5,0,0.7,1}` — agreement `< 10^{-35}`, both sides positive (including
the worst case `x = −1`).

### 6.2 What Part 2 proves (all axiom-clean)

| Lean name (`HKPos2.*`) | Statement |
|---|---|
| `sTermNum_nonneg` | the `S`-summand numerator `2c ≥ 0` for `0 ≤ c` |
| `sTruncNonneg` | `S^{(M)}(x) = Σ_{n<M} tₙ ≥ 0` for any nonnegative realized quotient sequence `tₙ = 2·a^{2n-1}/factorₙ` (division-free: numerator `≥ 0`, denominator `> 0`) |
| `thetaTruncCReal_isPositive` | the constant `CReal` at `ϑ₃^{(M)}(x)` is `CReal.IsPositive` |
| `thetaTruncCReal_geRat_zero` | its limit is `≥ 0` (`ExpPos.geRat … 0`) |
| `mul_geRat_zero` | **product-of-nonnegatives engine:** two `CReal`s with pointwise-nonnegative approximations have `geRat (CReal.mul Θ Sx) 0` |
| `RTrunc_geRat_zero` | **worked `R ≥ 0`:** `R^{(M,M')} = ϑ₃^{(M)}(x)·S^{(M')}(x)` has limit `≥ 0` |
| `Kt_geRat_zero_of_product` | **the closing step modulo (G1)+(G2):** if `Kt = CReal.mul Θ Sx` with `Θ, Sx` nonneg-approx, then `geRat Kt 0` |

`Q'` has no division, so the `S`-summands are carried by numerator/denominator
data rather than realized quotients in the abstract lemmas; the realized
quotient sequence (each term `≥ 0` since its numerator `≥ 0` and denominator
`> 0`) is the only thing `sTruncNonneg` consumes.

### 6.3 The precise remaining gap of Part 2 (honest)

`mul_geRat_zero` is the clean win: it reduces `R ≥ 0` (hence `K_t ≥ 0`) to
exhibiting `ϑ₃/2a` and `S` as `CReal`s with nonnegative approximations and the
product identity.  Two infinite-limit steps remain, named not faked:

* **(G1) Convergence as `CReal`s with explicit modulus.**  `ϑ₃`, `S` decay
  geometrically (ratio `a²`); `K_t`'s term majorant is `|n·a^{n²}·U_{n-1}(x)| ≤
  n²·a^{n²}` (super-geometric).  The engine `Continuum.crealOfGeoIncrement`
  applies, but its `C·(1/2)^l` interface needs an `a`-dependent geometric
  majorant with an `a`-dependent cutoff `n₀(a)` — the increment ratio
  `(1+1/n)²·a^{2n+1}` drops below `1/2` only past `n₀(a)` (numerically:
  `n₀ = 1, 5, 37` for `a = 0.5, 0.9, 0.99`).  Wiring this general majorant is
  mechanical but lengthy; not done.

* **(G2) The identity `K_t(x) = R(x)`** — the differentiated Jacobi triple
  product.  Verified symbolically to 40 digits; not formalized (the one
  genuinely-hard analytic step).  The crux sub-fact `|U_{n-1}(x)| ≤ n` on
  `[−1,1]` is itself a sin-structure bound NOT provable by the naive `Q'`
  triangle recurrence (which gives only the Pell bound `B_{n-1} ∼ 2.414^n`),
  and is folded into (G2).

### 6.4 Verdict

The positive-object content of the product representation is now closed at the
`CReal` level: `mul_geRat_zero` proves the product of two nonneg-approx
constructive reals is `≥ 0`, and `RTrunc_geRat_zero` lands this end-to-end on
the truncated `R^{(M,M')}`.  The full `K_t ≥ 0` does NOT close here: it is gated
on (G1) constructive convergence with an `a`-dependent geometric majorant and
(G2) the differentiated Jacobi-triple-product identity (plus the tight
Chebyshev bound).  Honest verdict: sub-target 2 (the manifestly-positive object
`R ≥ 0`) is closed as a `CReal` statement modulo the existence of the two
limit `CReal`s; sub-targets 1 and 3 are partial, with the convergence wiring and
the infinite identity as the precisely-stated outstanding gaps.
