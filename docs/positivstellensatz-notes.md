# `[−1,1]` Positivstellensatz consumer — notes

The certificate layer of Piece B (the integration bridge). It upgrades the
bare sum-of-squares consumer `TrigAvg.avg_nonneg_of_sos` (`f = Σ g_j² ⟹
avg f ≥ 0`) to the **Markov–Lukács / `[−1,1]`-Positivstellensatz** form: a
polynomial `p(x)` on `[−1,1]` carrying a certificate

    p(x) = σ₀(x) + (1 − x²)·σ₁(x),     σ₀, σ₁ sums of squares,

has nonnegative average against the heat-kernel (cosine) functional.

Lean module: `YMGap/Continuum/Positivstellensatz.lean`, namespace
`YMGap.Continuum.PSatz`.

## The trigonometric dictionary (`x = cos θ`)

With `x = cos θ`, `[−1,1]` is the image of `[0,π]` and the average
`(1/π)∫₀^π · dθ` is a positive linear functional `ν` on `[−1,1]`. The two
generators of the cone for the compact interval `[−1,1]` are the boundary
inequalities `1 − x ≥ 0` and `1 + x ≥ 0`, whose product is the weight
`1 − x² = sin²θ`. Under the substitution:

- `A(x) = Σ a_k x^k` pulls back to a **cosine series**
  `A(cos θ) = Σ c_k cos(kθ)`; the average of its square is the
  Fejér–Riesz constant term `cosSqAvg [c₀,c₁,…] = c₀² + ½ Σ_{k≥1} c_k²`
  (from `TrigAverage.lean`, already proved `≥ 0`).
- `(1 − x²)·B(x)² = (sin θ · B(cos θ))²` pulls back to the square of a
  **sine series** `Σ s_k sin(kθ)`; its average is the sine-Parseval constant
  term `sinSqAvg [s₁,…] = ½ Σ_{k≥1} s_k²` (no bare constant term, since
  `sin(0·θ) = 0`).

So averaging the certificate gives

    ⟨p, ν⟩ = Σ_j cosSqAvg(Â_j) + Σ_j sinSqAvg(Ŝ_j) ≥ 0,

a finite sum of (cosine-Parseval) + (sine-Parseval) atoms, each `≥ 0`. This
is the genuine `∫(≥0) ≥ 0` content, now in the `[−1,1]` form the bridge
consumes.

## Symbolic verification (sympy)

The small-degree certificate identities were checked symbolically before
encoding as `QPoly` `decide`-identities:

- `2(1 − x)      = (1 − x)² + (1 − x²)·1²`            ✓
- `2(1 + x)      = (1 + x)² + (1 − x²)·1²`            ✓
- `1 − x²        = 0² + (1 − x²)·1²`                  ✓
- `2(2 − 3x + x²) = 3·(x − 1)² + (1 − x²)·1²`         ✓
  (i.e. `2 − 3x + x² = (3/2)(x−1)² + (1/2)(1−x²)`; the `2·` clears the
  rational weights so the certificate stays over `ℤ ⊂ Q'`).

`2 − 3x + x² = (1−x)(2−x)` is a generic nonnegative-on-`[−1,1]` quadratic
with a sign-indefinite linear coefficient — the case where the cone
positivity of `WilsonFunctional.coneExp_nonneg` does not apply directly and
the `(1 − x²)` generator is genuinely needed.

## What is proved (axiom-clean)

| Lean name | statement | axioms |
|---|---|---|
| `sinSqAvg` / `sinSqAvg_nonneg` | `½ Σ s_k²`, the `(1−x²)`-Parseval atom; `≥ 0` | `[propext]` |
| `sinSosAvg` / `sinSosAvg_nonneg` | `Σ_j sinSqAvg(S_j)`; `≥ 0` | `[propext]` |
| `psatzAvg` / `psatzAvg_nonneg` | **the certificate average** `sosAvg σ₀ + sinSosAvg σ₁`; `≥ 0` | `[propext]` |
| `weightedSum` / `weightedSum_nonneg` | nonneg-weighted sum of nonneg atoms; `≥ 0` | `[propext]` |
| `wpsatzAvg` / `wpsatzAvg_nonneg` | **weighted** certificate `Σ d_j cosSqAvg + Σ e_j sinSqAvg`; `≥ 0` | `[propext]` |
| `geRat_psatzAvg`, `geRat_wpsatzAvg` | `CReal`-level (`ExpPos.geRat`) corollaries | `[propext]` |
| `cert_oneMinusX`, `cert_onePlusX`, `cert_oneMinusXSq`, `cert_quad` | small-degree witnesses, `decide`-checked `QPoly` identities | `[propext, Quot.sound]` |

No `Classical.*`, no `sorryAx`, no `native_decide`. The `Quot.sound` on the
`cert_*` lemmas is inherited from the reflective `QPoly.poly_eqv` ring they
reuse (the same gate as `QPoly.pivot2_factor`).

## What is delivered vs. open

- **Consumer (sub-target 1) — CLOSED, fully general.** `psatzAvg_nonneg` /
  `wpsatzAvg_nonneg` accept *any* certificate of *any* degree and prove the
  average `≥ 0`. This is the upgrade of `avg_nonneg_of_sos` to the `[−1,1]`
  Positivstellensatz form actually needed.
- **Producer (sub-target 2) — small degrees only.** The `cert_*` theorems
  exhibit and `decide`-verify explicit certificates for the degree-≤2
  nonnegative-on-`[−1,1]` polynomials reachable by closed-form
  factorization (the boundary generators, the weight itself, and a generic
  sign-indefinite quadratic).
- **General producer — OPEN (honest gap).** Producing `(σ₀, σ₁)` from the
  *mere* hypothesis `∀ x ∈ [−1,1], p(x) ≥ 0` is the constructive
  Markov–Lukács / Fejér–Riesz spectral factorization, requiring a
  root-finding / companion-matrix step beyond the rational `decide`
  substrate. It is recorded — *as a `Prop` definition, not asserted as a
  theorem* — as `PSatz.OpenProblem.markov_lukacs_existence`
  (`∀ p, NonnegOn p → Nonempty (Certificate p)`), with `Certificate p`
  carrying the SOS data together with the `QPoly` identity it must satisfy.

## Connection to the application

`psatzAvg`/`wpsatzAvg` are the off-cone counterpart of
`TrigAvg.momentPairing` / `WilsonFunctional.coneExp_nonneg`: the cone route
handles observables with nonnegative coefficients directly, while the
Positivstellensatz route handles a pointwise-nonnegative `p` whose
coefficients are sign-indefinite — *once a Markov–Lukács certificate is
supplied*. The `geRat_*` corollaries embed the rational averages as constant
`CReal`s in the `ExpPos.geRat` lower-bound sense, so the certificate
consumer composes with the heat-kernel moment machinery in
`WilsonFunctional.lean`.
