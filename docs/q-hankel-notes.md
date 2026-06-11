# The q-Hankel closed form for the SU(2) heat-kernel Gram minors

## Setup

Single base variable `a = e^{−t/4} ∈ (0,1]`. The SU(2) heat-kernel moments are

```
m_s = (s+1) · a^{s(s+2)}          (s = 0,1,2,…;  s(s+2) = (s+1)² − 1)
```

(each moment a *monomial* in `a`). The SU(2) character Gram matrix is

```
G_{ij} = ⟨χ_i χ_j⟩_t = Σ_{c = |i−j|, step 2}^{i+j} m_c     (Clebsch–Gordan fusion)
```

and `Δ_N(a) = det[G_{ij}]_{0 ≤ i,j < N}` is the leading principal minor (the
heat-kernel q-Hankel determinant). PSD of the moment matrix at all orders is
equivalent, by Sylvester, to `Δ_N(a) ≥ 0` for all `N` and all `a ∈ [0,1]`.

## The q-product (Selberg-type) closed form — found and verified

Exact computer algebra (sympy, verified **exactly through N = 8**) gives the
closed factorization

```
            ┌─────────────────────────────────────────────────────────────┐
   Δ_N(a) = │  S_N(a)² · P_N(a),    S_N(a) = ∏_{j=1}^{N−1} (a^{2j} − 1)^{N−j}  │   (★)
            └─────────────────────────────────────────────────────────────┘
```

with:

- `S_N` the **perfect-square** (cyclotomic) factor, given *explicitly and
  uniformly in N* by the q-product above. In q-integer form, since
  `a^{2j} − 1 = (a − 1)·[2j]_a` with `[n]_a = (a^n−1)/(a−1)`,

  ```
  S_N(a) = (a − 1)^{N(N−1)/2} · ∏_{j=1}^{N−1} [2j]_a^{ N−j }.
  ```

  Every cyclotomic factor `Φ_d` of `Δ_N` thus carries **even** multiplicity
  (it is a square), so `S_N² ≥ 0` for free.

- `P_N` a polynomial with **all-nonnegative coefficients**, constant term `1`,
  leading coefficient `(2N−1)!! = ∏_{k=1}^{N−1}(2k+1)`, and only even powers of
  `a` (a positive combination of monomials in `a²`). Hence `P_N(a) ≥ 1` for
  `a ≥ 0`.

Therefore, for `a ≥ 0`,

```
Δ_N(a) = (square) · (nonneg-coefficient poly ≥ 1) ≥ 0,    uniformly in N.
```

### How (★) was found

1. Factor `Δ_N` exactly (sympy `factor`) through `N = 7,8`; confirm every
   non-trivial cyclotomic factor `Φ_d` has even exponent and the remaining
   factor `P_N` has nonnegative coefficients (reconnaissance reproduced).
2. Tabulate the half-exponent (multiplicity in `S_N`) of each `Φ_d`. Möbius-
   invert over the divisor lattice — expressing the `S_N`-content in the basis
   `{ a^n − 1 = ∏_{d|n} Φ_d }` — to obtain the multiplicity `b_n` of
   `(a^n − 1)` in `S_N`. The result is the clean pattern

   ```
   b_n = N − j   for n = 2j   (j = 1 … N−1),    b_n = 0 otherwise,
   ```

   i.e. `S_N = ∏_{j=1}^{N−1}(a^{2j} − 1)^{N−j}` — formula (★).
3. Verify directly: `Δ_N / S_N²` divides exactly and is nonneg-coefficient,
   constant term 1, leading coeff `(2N−1)!!`, even powers only — **N = 1 … 8**.
4. Cross-check (★) reproduces the repo's hand-factored square factors
   `S₂ = a²−1`, `S₃ = a⁸−2a⁶+2a²−1`, `S₄` (degree 20) **exactly**.

### The telescoping recurrence (single square per Favard step)

A consequence of (★), verified through `s = 7`:

```
S_s · S_{s−2} = (a^{2(s−1)} − 1) · S_{s−1}²            (telescope)
```

so the cyclotomic content of the Favard recurrence coefficient
`β_s = Δ_s Δ_{s−2} / Δ_{s−1}²` is the *single* perfect square
`(a^{2(s−1)} − 1)²`. Each order contributes exactly one new q-factor
`a^{2(s−1)} − 1`; this is the cleanest manifestly-nonnegative uniform form of
the square structure.

## The orthogonal-polynomial family

With `x = χ_1 = 2cosθ`, the underlying 1-variable moments are

```
μ_n = L[x^n] = Σ_k (k+1)·N^k_{1ⁿ}·a^{k(k+2)},   μ_0=1, μ_1=2a³, μ_2=1+3a⁸, …
```

The dominant term of `μ_n` is `(n+1)a^{n(n+2)}` — Gaussian/theta growth
`a^{n²}` with **q = a²** (`s(s+2)=(s+1)²−1`). This is the SU(2) heat-kernel
(Sugawara / theta) deformation of the semicircle weight on `[−2,2]`; the monic
orthogonal polynomials are the **renormalized continuous q-Hermite polynomials
(q = a²)** — equivalently the SU(2) characters `χ_k` themselves are the
orthogonal family for the heat-kernel functional, and `Δ_N = ∏_{k<N} h_k` with
`h_k = Δ_{k+1}/Δ_k` the squared OP norms. The `(2N−1)!!` leading coefficient
and the q-integer cyclotomic product are the signature of this q-Hermite /
theta-Hankel determinant.

## What is formalized in Lean (axiom-clean)

File `YMGap/Continuum/QHankel.lean`, namespace `YMGap.Continuum`. Every theorem
builds green under `lake build YMGap.Continuum.QHankel`; `#print axioms` gives
`[propext, Quot.sound]` (or none) for each — no `Classical`, no `sorry`/
`sorryAx`, no `native_decide`.

Uniform (`N`-indexed) results:

- `SN : Nat → QPoly.Poly` — the explicit `N`-indexed realization of (★),
  `SN N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}`, built by `pmul`/`ppow`/`qFac` for
  *every* `N` (not a per-`N` literal).
- `geRat_SN_sq_nonneg (N) (a)` — **uniform square-positivity**:
  `(ceval (SN N) a)² ≥ 0` for every `N` and every `a`. The perfect-square
  factor of `Δ_N` is nonnegative at all orders simultaneously.
- `geRat_minor_SN_factored (N) (P) …` — **uniform minor reduction**: for every
  `N`, a minor equal to `(ceval (SN N) a)²·(ceval P a)` with `P`
  nonneg-coefficient and `a ≥ 0` is `≥ 0`. Supplying only the list `P_N`
  discharges `Δ_N ≥ 0` at order `N`; the square factor is produced uniformly.

Certification that (★) is correct, and instantiations:

- `SN_eq_S2`, `SN_eq_S3`, `SN_eq_S4` (`decide`) — `SN N` equals the repo's
  hand-derived square factors `S₂, S₃, S₄`.
- `SN_telescope_2 … SN_telescope_5` (`decide`, via `QPoly.poly_eqv`) — the
  telescoping identity `S_s·S_{s−2} = (a^{2(s−1)}−1)·S_{s−1}²` for s = 2,3,4,5.
- `delta2_nonneg_uniform`, `delta3_nonneg_uniform`, `delta4_nonneg_uniform`
  and their `…_at` heat-kernel-point (`a = e^{−t/4}`, every `t ≥ 0`) versions —
  the 2,3,4 leading minors proved `≥ 0` through the *uniform* `SN`-engine: the
  square comes from `SN N`, only `P_N` is supplied per order.

These reuse the existing engines `MomentPositivity.{ceval, geRat_ceval_of_
nonnegCoeffs, geRat_minor_factored}` and `Favard.{nonnegCoeffs lemmas, S/P/Δ
lists}` and the `QPoly` ring.

## OPEN — the precise remaining gap

The square factor `S_N` is now **uniform and proved nonnegative for all N**.
The remaining mathematical gap for all-`N` minor positivity is exactly:

> **OPEN.** `P_N(a) := Δ_N(a) / S_N(a)²` has nonnegative coefficients for
> **every** `N`.

This is *exact computer algebra through N = 8* (nonneg-coefficient, constant
term 1, leading coeff `(2N−1)!!`, even powers only), supplied in Lean as a
per-`N` literal list (`P_1,…,P_4`) feeding the uniform engine — but it is **not
yet an `N`-indexed theorem**. The promising levers:

- a manifestly-nonnegative recurrence for the family `P_N` (Favard `β_s ≥ 0`,
  whose cyclotomic content is already the single square `(a^{2(s−1)}−1)²` by
  the telescope above — so the open content is the *positive* factor
  `P_s P_{s−2}/P_{s−1}²` of `β_s`), or
- a combinatorial positivity for the q-Hankel cofactor expansion (Lindström–
  Gessel–Viennot / non-intersecting-paths interpretation of the q-Hermite
  Hankel determinant, which would give `P_N` a nonnegative path-count
  expansion).

Two further obligations are **bookkeeping, not new mathematics**:

- (moment-bridge) the actual CReal Gram minor built from the `expNeg` moments
  equals `ceval (Δ_N list) (e^{−t/4})` — the order-`N` analogue of
  `Pivot2Moments`, a mechanical `expNeg`-folding plus determinant expansion.
- (Sylvester) `Δ_N ≥ 0 ∀N ⟹ moment matrix PSD ∀N`, standard for Hankel/Gram
  matrices, not yet formalized in this repo.

## Honest status summary

- **Proved, uniform in N (Lean, axiom-clean):** the q-product square factor
  `S_N = ∏(a^{2j}−1)^{N−j}` and its square-positivity `(S_N)² ≥ 0`; the uniform
  reduction `Δ_N = S_N²·P_N ⇒ Δ_N ≥ 0` given `nonnegCoeffs P_N`; the
  telescoping `S_s·S_{s−2} = (a^{2(s−1)}−1)·S_{s−1}²` (s ≤ 5); the 2,3,4 minors
  `≥ 0` (including at the heat-kernel point).
- **Verified exactly by computer algebra (N ≤ 8), not yet an N-indexed Lean
  theorem:** `nonnegCoeffs P_N` for all `N` (the single remaining math gap).
- **Not attempted / out of scope here:** moment-bridge and Sylvester
  bookkeeping.

The uniform all-`N` PSD proof does **not** close; the precise and only
remaining mathematical obstruction is the uniform nonnegativity of the
coefficients of `P_N = Δ_N / S_N²`.
