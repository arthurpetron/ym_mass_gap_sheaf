# Favard / three-term-recurrence route to uniform SU(2) heat-kernel positivity

Notes on the all-orders SU(2) heat-kernel Gram positivity via the Favard
form, complementing the structural engine in `MomentPositivity.lean`. The
new formal results live in `YMGap/Continuum/Favard.lean` (Lean 4,
Mathlib-free, axiom-clean: `[propext]` / `[propext, Quot.sound]` only).

## Setup

Base variable `a = e^{−t/4} ∈ (0,1]`, moments `m_s = (s+1)·a^{s(s+2)}`. The
leading principal Gram minors `Δ_N(a) = det G[0..N−1]` (with
`G_{ij} = Σ_c N^c_{ij} m_c`, SU(2) fusion `χ_iχ_j = Σ_{k=|i−j|,step 2}^{i+j} χ_k`)
factor uniformly as

    Δ_N(a) = S_N(a)² · P_N(a),

`S_N` an integer-coefficient polynomial, `P_N` all-nonnegative coefficients,
even exponents, constant term `1`.

For the monic orthogonal polynomials the three-term recurrence
`Q_{s+1} = (x−α_s)Q_s − β_s Q_{s−1}` has

    β_s = Δ_s·Δ_{s−2} / Δ_{s−1}²,

and Favard ⟹ Gram-PSD at all orders ⟺ `β_s ≥ 0 ∀ s`. With the
factorization,

    β_s = (S_s·S_{s−2}/S_{s−1}²)² · (P_s·P_{s−2}/P_{s−1}²).

Since `Δ_{s−1}² ≥ 0` for free, the division-free content is

    Δ_s·Δ_{s−2} = (S_s·S_{s−2})² · (P_s·P_{s−2})  ≥ 0,

a perfect square times a product of two nonneg-coefficient polynomials.

## Computer-algebra verification (sympy)

Factorizations computed directly from the moments and confirmed through
`N = 6`. Every cyclotomic factor of `Δ_N` has **even** multiplicity (so the
cyclotomic part is a perfect square `S_N²`); the residual `P_N` always has
all-nonnegative coefficients and constant term `1`.

Cyclotomic multiplicities in `Δ_N` (N = 2..6):

| factor | N=2 | N=3 | N=4 | N=5 | N=6 |
|---|---|---|---|---|---|
| Φ₁Φ₂ = (a−1)(a+1) | 2 | 6 | 12 | 20 | 30  (= N(N−1)) |
| Φ₄ = a²+1 |  | 2 | 4 | 8 | 12 |
| Φ₃Φ₆ = a²±a+1 |  |  | 2 | 4 | 6 |
| Φ₈ = a⁴+1 |  |  |  | 2 | 4 |
| Φ₅Φ₁₀ = a⁴±a³+a²±a+1 |  |  |  |  | 2 |

`P_N` leading coefficient = `(2N−1)!! = 1, 3, 15, 105, 945, 10395`
(odd double factorial), constant term `1`.

## What is formally proved (axiom-clean) in `Favard.lean`

1. `geRat_ceval_ge_const` — Horner floor: a nonneg-coefficient polynomial
   evaluated at `x ≥ 0` is `≥` its constant term. Hence
   `geRat_ceval_ge_one_of_headGeOne`, and concretely `P_2,P_3,P_4 ≥ 1` at
   `a ≥ 0` (`P2_ge_one`, `P3_ge_one`, `P4_ge_one`). This is the constant-
   term-`1` strengthening of `geRat_ceval_of_nonnegCoeffs`.

2. Closure of the nonneg-coefficient cone under `+`, nonneg-scaling, and `·`
   (`nonnegCoeffsB_padd`, `nonnegCoeffsB_pscale`, `nonnegCoeffs_pmul`) — so
   `P_s·P_{s−2}` is again nonneg-coefficient.

3. `favard_numer_nonneg` — the **division-free Favard reduction**: given
   `Δ₁ = S₁²·P₁`, `Δ₂ = S₂²·P₂` with `P₁,P₂` nonneg-coefficient and `x ≥ 0`,
   the recurrence numerator `Δ₁·Δ₂ = (S₁·S₂)²·(P₁·P₂) ≥ 0`. Consumes the
   per-order `(S_k, P_k)` lists exactly.

4. `ceval_factor_nonneg` (single-minor bridge) and the concrete
   `β_s`-numerators `Δ_s·Δ_{s−2} ≥ 0` for `s = 1,2,3,4`
   (`beta1/2/3/4_numer_nonneg`), with the `s = 4` case using the genuine
   product `Δ_4·Δ_2 = (S_4·S_2)²·(P_4·P_2)`. Also the heat-kernel-point
   versions `betaK_numer_nonneg_at t` at `a = aVar t = e^{−t/4} ≥ 0`. The
   factorization identities `delta2_factor`, `delta4_factor`,
   `beta4_numer_factor` are `decide` certificates on `Q'` coefficient lists.

All stated about the *polynomial* `ceval Δ_N a` (as `delta3_nonneg` is); they
do **not** invoke the `MomentPositivity` moment-bridge OPEN.

## OPEN: the uniform N-indexed step

Missing is the `N`-indexed theorem that `Δ_N = S_N²·P_N` with `P_N`
nonneg-coefficient and `P_N(0) = 1` holds for **all** `N` (here per-`N` by
`decide` through `N = 4`, pattern verified through `N = 6`). Two halves:

- **(i) Evenness of cyclotomic multiplicities** in `Δ_N` — the single fact
  that makes the cyclotomic part a perfect square `S_N²`. Most promising
  route: a representation-theoretic / Vandermonde-squared origin (the Gram
  determinant as a squared Slater/Vandermonde object on the discrete
  heat-kernel spectrum, vanishing to even order in the `a → root-of-unity`
  degenerations).

- **(ii) Positivity of the residual `P_N`** coefficients, `N`-indexed — a
  Hankel/Selberg-type product formula with leading coefficient `(2N−1)!!`
  would supply it.

**Favard restatement of the same obstruction.** Equivalently, prove
`β_s(a) ≥ 0 ∀ s` from a closed form / monotone structure of the heat-kernel
orthogonal-polynomial recurrence coefficients. `favard_numer_nonneg` already
consumes the per-`s` factorization; what is missing is a *uniform* supply of
`(S_s, P_s)`.

**Assessment.** The cleanest target is (i): evenness of every cyclotomic
multiplicity is the crux that yields `S_N²` uniformly, with a plausible
Vandermonde-squared proof; combined with a `(2N−1)!!` Hankel product formula
for `P_N` this would close the uniform step. The per-`N` `decide`
factorizations plus the `N ≤ 6` pattern are strong evidence but not an
induction. The Sylvester step `(Δ_N ≥ 0 ∀N) ⟹ PSD ∀N` for Hankel/Gram
matrices remains separately unformalized.
