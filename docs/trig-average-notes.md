# Trig-average integration bridge — notes

Piece B of the uniform SU(2) heat-kernel PSD program: the **integration
bridge**, a constructive proof that the average of a nonnegative
trigonometric polynomial is nonnegative — the "∫(≥0) ≥ 0" that turns a
pointwise heat-kernel positivity `K_t ≥ 0` into a moment-functional
positivity `E(q²) ≥ 0`.

Lean module: `YMGap/Continuum/TrigAverage.lean`, namespace
`YMGap.Continuum.TrigAvg`.

## Conventions

A cosine trigonometric polynomial is a coefficient list
`[b₀, b₁, …, b_m] : List Q'` denoting

    f(θ) = b₀ + 2 · Σ_{k≥1} b_k cos(kθ)      ("b-convention").

Average over `[0,π]` w.r.t. `dθ/π` is the **constant term** `b₀`, because
`(1/π)∫₀^π cos(kθ) dθ = 0` for `k ≥ 1`.

A *cosine series* `g(θ) = Σ_{k=0}^{m} g_k cos(kθ)` is the same list
`[g₀,…,g_m]`; this is the building-block form for sum-of-squares
certificates.

## Symbolic verification (sympy)

All three coefficient-level identities were checked symbolically:

- avg of `f` (b-convention) = `b₀`.
- avg of `f·h` (both b-convention) = `b₀h₀ + 2 Σ_{k≥1} b_k h_k`
  (the moment pairing).
- avg of `g²` for cosine series `g` = `g₀² + ½ Σ_{k≥1} g_k²`
  (Parseval / Fejér–Riesz constant term), confirmed for `m = 0,…,3`.

The `½` on the tail and the bare `g₀²` come from
`cos(jθ)cos(kθ) = ½[cos((j+k)θ) + cos(|j−k|θ)]`: the diagonal `j=k>0` term
`cos(jθ)²` has constant part `½`, while `cos(0·θ)=1` contributes the full
`g₀²`.

## What is proved (axiom-clean, `[propext]` only)

| Lean name | statement |
|---|---|
| `constTerm` | average extractor = list head (`b₀`) |
| `momentPairing b m` | `b₀m₀ + 2 Σ b_k m_k` ("average of product") |
| `momentPairing_cons` | defining unfold of the pairing |
| `dotTail_nonneg` | `Σ b_k m_k ≥ 0` for nonneg lists |
| `momentPairing_nonneg` | **cone positivity**: pairing `≥ 0` when both lists nonneg |
| `cosSqAvg g` | `g₀² + ½ Σ_{k≥1} g_k²` = avg of `g²` |
| `cosSqAvg_nonneg` | **Parseval positivity**: `0 ≤ cosSqAvg g` |
| `sosAvg gs` | `Σ_j cosSqAvg(g_j)` = avg of `Σ_j g_j²` |
| `avg_nonneg_of_sos` | **integration bridge**: `0 ≤ sosAvg gs` |
| `geRat_sosAvg` | CReal-level: embedded avg `≥ 0` (`ExpPos.geRat`) |
| `geRat_momentPairing` | CReal-level cone pairing `≥ 0` |
| `oneMinusCos_sq_avg(_nonneg)` | worked example `(1−cos θ)²`, avg `= 3/2 ≥ 0` |

The genuine mathematical content is the **nonnegativity of the constant term
of a sum of squares** (Parseval positivity, `cosSqAvg_nonneg`) and its
assembly into the SOS bridge (`avg_nonneg_of_sos`) and the cone/moment
pairing (`momentPairing_nonneg`). Each rests on the SOS primitives in
`Constructive/SumOfSquares.lean` (`q_mul_self_nonneg`) and the `Q'`
nonnegativity arithmetic (`mul_nonneg`, `zero_le_add`).

## Connection to the application

`momentPairing` is the coefficient-level form of `E(f) = Σ_k (coeff_k f)·m_k`.
With `m` the SU(2) heat-kernel character-moment list
(`WilsonFunctional.wilsonCharExp t s`, each `≥ 0`) and `b` an observable's
nonnegative coefficients, `momentPairing_nonneg` is the rational shadow of
`WilsonFunctional.coneExp_nonneg` — the heat-kernel functional is positive on
the cone of nonnegative-coefficient observables. The SOS bridge
`avg_nonneg_of_sos` is the complementary route covering the off-cone (sign-
indefinite) directions *once a Fejér–Riesz SOS witness is supplied*: a
trig polynomial that is pointwise `≥ 0` but has sign-indefinite coefficients
is handled by writing it as `Σ_j g_j²` and averaging termwise.

## Precise gap (honest scope)

Two items are taken as **input**, not constructed:

1. **Fejér–Riesz existence.** That *every* pointwise-nonnegative cosine
   polynomial admits `f = Σ_j g_j²` is the hard spectral-factorization step
   and is NOT formalized. We prove the *consumer* (`avg ≥ 0` GIVEN the SOS
   presentation), which is exactly the scoped deliverable. The remaining work
   to close the full pointwise-`f≥0 ⟹ avg f ≥ 0` chain is the constructive
   Fejér–Riesz factorization (or, alternatively, route 2 below).

2. **Trig model.** `cosSqAvg g = g₀² + ½ Σ g_k²` is taken as the *definition*
   of the average of `g²` (justified by the product-to-sum identity and
   sympy-verified). A `CReal`-valued `cos` and an actual Riemann-integral
   average are NOT formalized; we work entirely at the coefficient level,
   which is where the `∫(≥0) ≥ 0` content lives. Building the Riemann-sum
   route (route 2 of the spec: `b₀ = lim_M (1/M)Σ_i f(θ_i) ≥ 0`, using the
   explicit Lipschitz constant of trig polynomials and `Constructive/Reals.lean`
   CReal convergence) would remove this modeling assumption but is a separate,
   heavier analytic build-out.

## Axioms

`#print axioms` reports `[propext]` for every load-bearing theorem
(`oneMinusCos_sq_avg` reports none). No `Classical.*`, no `Quot.sound`, no
`sorryAx`, no `native_decide`.
