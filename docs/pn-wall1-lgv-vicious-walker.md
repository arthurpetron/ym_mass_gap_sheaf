# Wall-1: the non-principal vicious-walker / LGV attack on `nonnegCoeffs P_N`

The surviving Wall-1 route (the algebraic alternative to Wall 2) is a
**non-principal (charge / major-index) vicious-walker LGV path-sum model** for
`p_N(q)` (`q = a²`, `Δ_N = S_N²·P_N`, `P_N` irreducible over ℚ, `P_N(0)=1`,
lead `(2N−1)!!`, even powers, all coefficients nonneg — exact-verified through
`N = 10`).

This pass produced **a new LGV-lattice reading** of the (already-known) value
`p_N(1)` — re-factoring it as a per-box Gaussian-binomial product `N!·∏[2k+1,k]_q`
that pins down the nested-box geometry of the walker model — and **two sharpened
negatives** that constrain the model. It did **not** close the
coefficient-positivity. All claims are exact rational/symbolic sympy (no floats
for any coefficient statement); methodology in `/tmp/pn_*.py`. Base data
reproduces the Lean ground truth (`P_2=[1,2,3]`, `P_3` matches
`MomentPositivity.P3`, `P_4` matches the docs).

---

## 0. The box-factored product formula for the value `p_N(1)`

The single sharpest handle (the value is prior-known; the box factoring is the
new content — see "Provenance" below). Exact-verified **N = 1 … 9** (the value
formula); the underlying nonneg/degree/lead facts hold N ≤ 10:

```
            ┌───────────────────────────────────────────────────────┐
   p_N(1) = │   N!  ·  ∏_{k=1}^{N−1}  C(2k+1, k)                     │     (♣)
            └───────────────────────────────────────────────────────┘
```

with `C(2k+1,k) = (2k+1)!/(k!(k+1)!) = C(2k+1,k+1)` the number of lattice paths
across the **`k × (k+1)` box** (a ballot number; `q→1` value of the Gaussian
binomial `[2k+1 choose k]_q`).

`p_N(1) = 1, 6, 180, 25200, 15876000, 44008272000, 528627363264000,
27213736660830720000, …` — the closed form (♣) reproduces every term, and the
ratio `p_N(1)/∏_{k} C(2k+1,k)` is **exactly `N!`** on the nose (N ≤ 9).

Equivalently, the clean **order-1 value recurrence** (verified N ≤ 9):

```
   p_N(1) = N · C(2N−1, N−1) · p_{N−1}(1),       p_1(1) = 1.                (♣′)
```

The per-step factor `N·C(2N−1,N−1) = 6,30,140,630,2772,…` (the new `(N−1)×N`
box, counted `N`-fold) is the `q→1` shadow of the new box's q-binomial weight
times the `N`th walker's `N` labelings.

**Provenance / honesty.** The *value* `p_N(1)` was already known in the
prior memory in the equivalent form `∏_{k=1}^{N−1}(2k+1)!/(k!)²` (Legendre-norm
form). The two are algebraically identical:
`∏(2k+1)!/(k!)² = N!·∏(2k+1)!/(k!(k+1)!) = N!·∏C(2k+1,k)`. What is **new here**
is the *re-factoring* into `N! · ∏[2k+1 choose k]_q` — exposing the **box-by-box
q-binomial LGV reading** below (per-box Gaussian binomial `[2k+1,k]_q` + `N!` as
an `S_N` charge sum), pinned by the **exact degree/lead box bookkeeping**
(`deg p_N = Σk(k+1) = deg ∏[2k+1,k]_q`, `lead = ∏(2k+1)`) and the per-step Favard
box `(N−1)×N`. The bare value is *not* the new content; the LGV-lattice reading
of it is.

### Why (♣) pins down the lattice — and why the model is *non-principal*

* **Degree match (exact, N ≤ 10).** `deg_q p_N = N(N²−1)/3 = Σ_{k=1}^{N−1}
  k(k+1)`, which is **exactly** `deg_q ∏_{k=1}^{N−1}[2k+1 choose k]_q` (each box
  `k×(k+1)` has max area `k(k+1)`). The Favard step `N−1 → N` adds degree
  `(N−1)·N` — the *new* `(N−1)×N` box (`k = N−1`). So `p_N` is built **box by
  box**, one nested `k×(k+1)` box per order.

* **Lead match.** `lead p_N = (2N−1)!! = ∏_{k=1}^{N−1}(2k+1)`, while
  `lead ∏[2k+1 choose k]_q = 1`. The extra `(2k+1)` per box is the
  multiplicity with which the top (max-area) path of box `k` is counted.

* **The `N!` does NOT come from a q-factorial.** `[N]_q!` would add degree
  `C(N,2)` to `∏[2k+1,k]_q`, overshooting `deg p_N` by exactly `C(N,2)`
  (checked N ≤ 5). So the `N!` of (♣) enters as a **sum over `S_N`** (a
  charge / major-index statistic on the labeled walkers), **not** a product
  factor. This is precisely the *non-principal* signature: a principal
  specialization would factor (`∏[2k+1,k]_q · [N]_q!`), but `p_N` is irreducible
  over ℚ, so the `N!` must be distributed as a `q^{stat(σ)}` sum that entangles
  the boxes into an irreducible polynomial.

**Reading of (♣): the LGV model.** `N` (or `N−1`) vicious walkers traversing the
nested boxes `1×2, 2×3, …, (N−1)×N`; box `k` carries the Gaussian-binomial
weight `[2k+1 choose k]_q`; the `N!` is the sum over the `S_N` labelings of the
walkers, q-weighted by a charge/major-index descent statistic. Coefficient
positivity would be manifest (q-binomials and `q^{stat}` are nonneg-coefficient)
**once the precise statistic is identified**. It was not identified here.

---

## 1. Sharpened negatives (constrain the model)

### 1a. `p_N` is NOT a Hankel determinant — the LGV must be N-walker, not 1D

Treating `p_N` itself as a candidate Hankel-determinant sequence
`p_N = det[μ_{i+j}]`, the would-be Favard coefficient is
`β_k = p_{k+1}p_{k−1}/p_k²`. Exact (k ≤ 5): the **denominator of `β_k` in lowest
terms is exactly `p_k²`**, and `p_k² ∤ p_{k−1}p_{k+1}` (remainder nonzero —
`p_N` irreducible). So `β_k` is a genuine rational function with `p_k` in the
denominator: **`p_N` is not a Hankel determinant of any moment sequence.**

Consequence: there is **no single-walker Motzkin / J-fraction / Stieltjes LGV
model for `p_N`** (those produce Hankel determinants). Any working LGV model is
necessarily **multi-row / N-walker** (a genuine 2-dimensional non-intersecting
family), consistent with the box reading of (♣). This sharpens the prior
"J-fraction model is rational" dead-end into an *impossibility* of the 1D model.

### 1b. The cancellation is numerator-vs-denominator, not a clean determinant

The Leibniz expansion of `det(a·G) = aᴺΔ_N` over (`σ ∈ S_N`, step-choices
`r_i ∈ supp(i,σ(i))`) was reconstructed exactly (N = 3): every term is
`sgn(σ)·∏_i r_i · a^{Σ r_i²}`, a signed theta-monomial sum. A Gessel–Viennot
sign-reversing involution on this expansion would prove positivity of **`Δ_N`** —
but `Δ_N` is itself **sign-mixed in its coefficients** (`Δ_2` ends `…,−4,0,3`;
`Δ_N` sign-mixed for N = 2…5). And `h_n = [x^n]θ(x)/(1−x²)`, though
nonneg-coefficient, is **not** a wall-respecting transfer function: the naive
Karlin–McGregor reflection determinant `det[h_{i+j}−h_{|i−j|−2}]` is *not* a
positive walker sum (it equals the sign-mixed `Δ_N`).

So the positivity of `p_N` is created **entirely by the cancellation between the
sign-mixed numerator `Δ_N` and the sign-mixed denominator `S_N²`**, not by a
positive determinant for either one. This is the precise reason a direct
"`p_N = det(nonneg-coefficient matrix)`" model is so elusive: the natural
determinant (`Δ_N`) is the wrong, sign-mixed object, and `p_N` (the right
object) is provably not a determinant of the Hankel type (§1a).

---

## 2. LDL diagnostic — the rational obstruction localized

The symmetric LDL factorization of `a·G` (N = 4, exact) is illuminating:

* **First column is clean.** `L[i,0] = (i+1)·a^{(i+1)²−1}` — pure positive
  monomials. The Schur-complement rationality only appears from column 1 on.
* **The pivots carry `P_N/P_{N−1}`.** `D[k,k]` has the residual `P_{k}`
  (numerator) over `P_{k−1}` (denominator): e.g. `D[2]`'s numerator is exactly
  the `P_3` coefficient list and its denominator is `P_2 = 3a⁴+2a²+1`; `D[3]`
  has `P_4` over `P_3`. This is the same `P_k`-in-denominator obstruction as the
  Favard/J-fraction route (`λ_k` rational), now seen in the off-diagonal
  multipliers `L[i,j]` (j ≥ 1) as well.

So no naive triangular factorization of `a·G` produces nonneg-coefficient pivots.

---

## 3. Formalizable fragment (status, unchanged + reconfirmed)

The uniform-in-`N` bottom-strip columns `c_k(N) = [q^k]p_N` (genuine degree-`k`
polynomials in `N`, leading coeff `2^k/k!`), exact-validated with leave-one-out
over `N ≤ 10`:

```
c_0(N) = 1                                    [9 validation pts]
c_1(N) = 2(N−1)                               [7]
c_2(N) = (N+1)(2N−3)                          [6]
c_3(N) = (2/3)(2N−1)(N²+2N−9)                 [4]
c_4(N) = (4N⁴+20N³−97N²+73N−30)/6             [3 — first valid only at N≥4]
```

`c_0,…,c_3` are formalized as `∀N` theorems in `LGVPositivity.lean`; `c_4` in
`PNDeterminant.lean` (`cCol4_nonneg`, `∀N ≥ 4`). Columns `k ≥ 5` are **not yet
in their interior regime** even at `N = 10` (leave-one-out fails: fitted lead of
`c_5` is `1/4 ≠ 2⁵/5! = 4/15`), so they are not pinned by feasible data. This is
the same two-wall limitation as before: the fragment covers the lowest `O(1)` of
the `Θ(N³)` columns; the bulk (at `k ∼ N³`) is unreachable.

The first-difference bottom strip `[q^k]D_N` (`D_N = p_N − p_{N−1}`), exact:
`[q¹]D_N = 2`, `[q²]D_N = (N³−12N²+59N−69)/3`, `[q⁴]D_N` a degree-5 polynomial in
`N` — each manifestly `≥ 0` only in its interior regime (same threshold wall).

---

## 4. Verdict and the single sharpest open statement

**New this pass.** The value formula (♣) `p_N(1) = N!·∏_{k=1}^{N−1}
C(2k+1,k)` (exact N ≤ 9; equivalent to the prior-known `∏(2k+1)!/(k!)²`)
identifies the LGV lattice — **`N−1` nested `k×(k+1)` boxes,
box `k` weighted by the Gaussian binomial `[2k+1 choose k]_q`, with the `N!`
entering as a charge/major-index sum over `S_N` (non-principal)** — and the
degree/lead bookkeeping (`deg p_N = Σk(k+1) = deg ∏[2k+1,k]_q`,
`lead = ∏(2k+1)`) confirms the box-by-box build. Two negatives are sharpened:
`p_N` is **provably not a Hankel determinant** (§1a — so the LGV must be
N-walker, not 1D), and the positivity is a **numerator-vs-denominator
cancellation** (`Δ_N` and `S_N²` both sign-mixed), not a positive determinant
for either (§1b).

**OPEN — the single sharpest remaining statement.**

> Identify the charge / major-index statistic `stat : S_N × (box paths) → ℕ`
> realizing
>
>     p_N(q) = Σ_{σ ∈ S_N}  q^{stat(σ, ·)}  ·  ∏_{k=1}^{N−1} [box-k path weight]_q
>
> as a non-intersecting (vicious-walker) sum over the nested boxes
> `1×2, …, (N−1)×N`, specializing at `q=1` to (♣). Coefficient-positivity
> (`nonnegCoeffs P_N`, equivalently `UniformPNDiffNonneg`) would then be
> manifest and **uniform in N**.

The combinatorial objects and their count (♣) are now known; the missing piece
is the explicit `q`-statistic that distributes the `N!` over `S_N` while
entangling the boxes into the irreducible `p_N(q)`. Value-positivity
(`p_N(1) > 0`, trivially from (♣)) is strictly weaker and is **not** the target.
The Wall-2 (analytic differentiated-Jacobi-triple-product) route to the same
uniform PSD is unaffected by these findings.
