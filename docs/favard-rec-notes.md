# Favard recurrence notes — the `β_k` coefficient and the uniform SU(2) heat-kernel Gram positivity

Companion to `lean/YMGap/Continuum/FavardRec.lean`. Records the discovery work
(sympy, exact through `k = 6` / `N = 7`) behind the Favard-recurrence route to
uniform-in-`N` SU(2) heat-kernel Gram positivity, and the **honest verdict** on
whether the route closes the uniform proof.

## Setup

Single base variable `a = e^{−t/4} ∈ (0,1]`. Moments `m_s = (s+1)·a^{s(s+2)}`.
Character Gram `G_{ij} = Σ_{c=|i−j|, step 2}^{i+j} m_c`. Leading minor
`Δ_N(a) = det G[0..N−1]`. Uniform factorization (computer algebra, exact):

    Δ_N = S_N²·P_N,   S_N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j},

with `P_N` nonneg-coefficient, `P_N(0) = 1`, lead coeff `(2N−1)!!`, even powers
only. Verified `nonnegCoeffs P_N` through `N = 7` (degrees 4, 16, 40, 80, 140,
224; lead coeffs 3, 15, 105, 945, 10395, 135135).

## 1. The closed form of `β_k`

The monic OP three-term recurrence `Q_{k+1} = (x−α_k)Q_k − β_k Q_{k−1}` has
`β_k = Δ_{k+1}·Δ_{k−1}/Δ_k²`. Substituting `Δ_N = S_N²·P_N`:

    β_k = (S_{k+1}·S_{k−1}/S_k²)² · (P_{k+1}·P_{k−1}/P_k²).

**Cyclotomic content is a single perfect square.** The square factors
telescope (exact, verified `s = 2..7`):

    S_{s}·S_{s−2} = (a^{2(s−1)}−1)·S_{s−1}²,

so `(S_{k+1}·S_{k−1}/S_k²)² = (a^{2k}−1)²` and

    ┌─────────────────────────────────────────────────────────┐
    │  β_k(a) = (a^{2k}−1)² · ( P_{k+1}·P_{k−1} / P_k² )       │
    └─────────────────────────────────────────────────────────┘

i.e. the entire cyclotomic part of `β_k` is the single manifestly-nonneg square
`(a^{2k}−1)² = qFac(k)²`. The remaining factor `γ_k := P_{k+1}P_{k−1}/P_k²` (a
theta-q-Hermite rational function) is **genuinely not a polynomial**: through
`k = 6`, its reduced denominator `P_k²` does not cancel.

Exact `β_k` factorizations (sympy), `k = 1,2`:

    β_1 = (a−1)²(a+1)²·(3a⁴+2a²+1)
    β_2 = (a−1)²(a+1)²(a²+1)²·(15a¹⁶+…+1)/(3a⁴+2a²+1)²

The pattern: `β_k = qFac(k)² · P_{k+1}P_{k−1}/P_k²` with `qFac(k)² = (a^{2k}−1)²`
the new cyclotomic square and `P_{k}` the residual q-Hankel numerators.

`α_k` (diagonal recurrence coeff): a ratio of the bordered minors
`Δ_k`/`Δ̃_k`; it is **not** needed for positivity (Favard positivity is
controlled by `β_k ≥ 0` alone), so it was not pursued to closed form.

## 2. Does a nonneg-coefficient-preserving recurrence exist? — NO (the honest crux)

Two natural recurrences, both of which fail to yield a *division-free,
coefficient-nonneg* induction for the family `P_N`:

### (a) Favard quadratic
`P_{k+1}·P_{k−1} = γ_k·P_k²`, `γ_k` rational. Solving `P_{k+1} = γ_k·P_k²/P_{k−1}`
requires dividing by `P_{k−1}`, and the division does **not** dissolve:

    P_{k−1} ∤ P_k²   for k = 3, 4, 5   (exact polynomial division leaves nonzero remainder).

So `β_k`'s value-nonnegativity does **not** become a polynomial recurrence on
the `P_N` coefficients.

### (b) Desnanot–Jacobi (Dodgson)
`Δ_N·Δ_central = Δ_{N−1}·BR − TR²` (verified `N = 2..5`), where `BR` = shifted
leading minor (rows/cols `1..N−1`), `TR` = off-diagonal corner, `TR = BL` by
Gram symmetry.

A *positive* sub-finding: every corner minor shares the
even-cyclotomic-multiplicity structure — pulling out the perfect-square content
leaves a **nonneg-coefficient residual** for *all* of `Δ_N, Δ_{N−1}, BR, TR,
Δ_central` (verified through `N = 5`). But the identity is a **difference**
`Δ_{N−1}·BR − TR²`, and dividing out the square content produces square
**ratios** (negative `a`-powers), not nonneg-coefficient multipliers, so it does
not rearrange into a subtraction-free recurrence for `P_N`.

**Verdict (coefficient positivity).** No division-free, coefficient-nonneg
recurrence for `P_N` exists via the Favard or Dodgson identities. The
`decide`-checked per-`N` factorizations (extended to `N = 5` in Lean here) remain
the only certificates of `nonnegCoeffs P_N`; an `N`-indexed proof is **OPEN**.

## 3. The value-positivity route IS uniform (the right target for the mass gap)

The mass-gap input is not `nonnegCoeffs P_N` but the *value* `Δ_N(a) ≥ 0` for
`a ∈ (0,1]`. This is uniform with no recurrence:

The heat-kernel representing measure on the maximal torus,

    dν(θ) = [ Σ_{c≥0} (c+1)·a^{c(c+2)}·χ_c(θ) ] · (2/π)sin²θ dθ,   χ_c(θ) = sin((c+1)θ)/sin θ,

is a **positive measure** on `(0,π)` (numerically verified: min density
`> 0` at `a = 0.3, 0.6, 0.9`). Since `χ_i(θ) = U_i(cos θ)` are the Chebyshev-`U`
polynomials, the Andréief/Heine identity gives

    Δ_N = (1/N!) ∫···∫ ∏_{i<j}(cos θ_i − cos θ_j)² ∏_{k} dν(θ_k) ≥ 0,

a manifestly nonnegative integral (Vandermonde² × positive measure), **uniform
in `N`**. Coefficient positivity of `P_N` is strictly finer than this (`Δ_N`
itself has negative coefficients) and is *not required* for Gram-PSD / Sylvester.

## 4. What is formalized in `FavardRec.lean` (axiom-clean: `[propext, Quot.sound]`)

- `betaCyclo_1 … betaCyclo_5` — the β-cyclotomic-square identity
  `S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²` (`decide`), exhibiting `β_k`'s cyclotomic
  content as the single square `(a^{2k}−1)²`.
- `betaNumer_nonneg_of_factor` — the division-free Favard reduction, re-exported
  in `β`-indexing (value `Δ_{k+1}·Δ_{k−1} = (S_{k+1}S_{k−1})²·(P_{k+1}P_{k−1}) ≥ 0`).
- `P5`, `P5_nonneg`, `P5_ge_one` — the order-5 residual, `nonnegCoeffs` by
  `decide`, with the constant-term-`1` floor `P_5(a) ≥ 1`.
- `beta5Numer`, `beta5_numer_nonneg`, `beta5_numer_nonneg_at` — the
  `β_5`-numerator `(S_5·S_3)²·(P_5·P_3) ≥ 0` (value), extending the verified
  chain `β_{1..4}` (in `Favard.lean`) to `β_5` through the uniform nonneg-cone
  engine `nonnegCoeffs_pmul`. Stated in factored form to avoid the degree-160
  expanded `Δ_5` literal.

## 5. Honest verdict on the uniform proof

- **For coefficient positivity `nonnegCoeffs P_N`:** the Favard-recurrence route
  does **not** close it. The recurrence is irreducibly rational (`γ_k`) /
  subtractive (Dodgson); coefficient positivity of `P_N` is a standalone
  combinatorial fact with no manifestly-nonneg recurrence. OPEN, and this is the
  *wrong target* for the uniform proof.
- **For the actual mass-gap input (value `Δ_N(a) ≥ 0`, all `N`):** the recurrence
  route is **unnecessary**. The Andréief expansion over the positive heat-kernel
  measure `ν` proves it uniformly in one stroke. The cleanest path to the
  uniform all-`N` PSD theorem is to formalize **(i)** positivity of `ν` (a 1-D
  trigonometric-series positivity, `a`-uniform) and **(ii)** the Andréief /
  Vandermonde-squared expansion — not the `P_N`-coefficient recurrence.

`FavardRec.lean` pins down the Favard structure precisely (closed `β_k`,
cyclotomic square, division-free reduction, `β_5` extension) and documents the
obstruction sharply; it does not — and per this analysis cannot — close
`nonnegCoeffs P_N` uniformly via the recurrence.
