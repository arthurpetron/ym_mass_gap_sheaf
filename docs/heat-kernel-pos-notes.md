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
