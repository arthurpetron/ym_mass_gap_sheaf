# LGV / column-coefficient positivity notes — `P_N = Δ_N/S_N²`

**Goal.** The last lemma for uniform all-orders SU(2) heat-kernel PSD:
`P_N` has nonnegative coefficients for every `N`, where
`Δ_N = det[μ_{i+j}]` is the heat-kernel q-Hankel determinant,
`S_N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}`, and `P_N = Δ_N / S_N²`.

**Approach attempted.** LGV / positive combinatorial formula for the
coefficients `c_j(N)` of `P_N(a) = Σ_j c_j(N) a^{2j}`.

---

## 1. Data (sympy, exact, verified `N = 1 … 8`)

`P_N` is, exactly through `N = 8`:

- all coefficients **nonnegative**,
- **only even** powers of `a` (a positive polynomial in `a²`),
- constant term `1`, leading coefficient `(2N−1)!! = 1,3,15,105,945,…`,
- degree `deg_a P_N = 4·C(N+1,3)`  (so `Θ(N³)` nonzero coefficients),
- coefficient sequence **log-concave** and **unimodal** (`N = 2,3,4`).

The first few coefficient rows (`c_j(N)`, the coeff of `a^{2j}`):

```
P_2: 1, 2, 3
P_3: 1, 4, 12, 20, 32, 36, 36, 24, 15
P_4: 1, 6, 25, 70, 169, 340, 616, 988, 1462, 1956, 2446, 2796, 2982, 2904, ...
P_5: 1, 8, 42, 156, 485, 1288, 3074, 6640, ...
P_6: 1, 10, 63, 286, 1070, 3432, 9839, ...
P_7: 1, 12, 88, 468, 2032, 7552, ...
P_8: 1, 14, 117, 710, 3495, 14686, ...
```

(All eight rows are reproduced and re-checked nonneg in the scratch sympy.)

---

## 2. The column-coefficient closed forms (the genuine uniform fragment)

Reading **columns** `c_j(N)` (fixed `j`, varying `N`), the lowest four
columns are exact polynomials in `N`:

```
c_0(N) = 1
c_1(N) = 2(N − 1)
c_2(N) = (N + 1)(2N − 3)
c_3(N) = (2/3)(2N − 1)(N² + 2N − 9)
```

These are verified by interpolation **and** by leave-one-out prediction
(refit dropping the largest `N`, predict it — matches) over `N ≤ 8`.

Each is `≥ 0` exactly on the range where the column actually occurs in
`P_N`:

```
c_0 ≥ 0  all N
c_1 ≥ 0  N ≥ 1        (and c_1 = 0 at N = 1)
c_2 ≥ 0  N ≥ 2        (c_2(1) = −2 < 0)
c_3 ≥ 0  N ≥ 3        (c_3(1) = −4, c_3(2) = −2 < 0)
```

This is the fragment that is genuinely **uniform in `N`** and was formalized
(see §5).

---

## 3. Why the column approach does NOT close the uniform proof

Two structural obstructions, both established from the data:

**(a) The column forms are only conditionally positive.** Each `c_j(N)` is a
polynomial in `N` valid only in the *interior regime* — `N` large enough
that `a^{2j}` lies in the low part of `P_N`. Outside that regime the same
polynomial is **negative** (`c_2(1) = −2`, `c_3(1) = −4`, `c_3(2) = −2`). A
uniform certificate would need, for each `j`, the closed form *and* its
validity threshold, and the thresholds grow with `j`.

**(b) There are `Θ(N³)` columns, and the higher ones are not pinned by the
data.** `deg_a P_N = 4·C(N+1,3)`, so `P_N` has order `N³` nonzero
coefficients. Columns `c_j` with `j ≥ 4` enter their interior regime only
around `N ≈ j`; with the symbolic Gram determinant feasible only to `N = 8`,
those columns are not determined. Concretely, naive interpolation of
`c_4,…,c_7` from `N ≤ 8` data fails the leave-one-out prediction test (they
are not yet polynomial in the available window).

So the column-polynomial phenomenon is real but covers only the lowest
`O(1)` of the `Θ(N³)` coefficients; it gives no uniform statement.

---

## 4. The Hankel / Jacobi (LGV-on-moments) route, and why it is rational

`Δ_N = det[μ_{i+j}]` with the moment sequence (verified `= det` of the
character-Gram through `N = 6`):

```
μ_k = L[(2cosθ)^k] = Σ_n d_{k,n} (n+1) a^{n(n+2)},
```

where the connection coefficients `d_{k,n}` are exactly the **ballot /
Catalan-triangle numbers** `C(k,(k−n)/2) − C(k,(k−n)/2 − 1) ≥ 0` (verified
`k ≤ 7`). So `μ_k` is a nonnegative-integer combination of the monomial
weights `w_n = (n+1)a^{n(n+2)} ≥ 0` — a clean theta-like moment sequence.

The standard Hankel↔Jacobi correspondence gives
`Δ_N = ∏_{k=1}^{N−1} λ_k^{N−k}` with off-diagonal Jacobi coefficients
`λ_k = Δ_{k+1}Δ_{k−1}/Δ_k²`. Computed exactly (`k ≤ 5`):

```
λ_k = (S_k S_{k−2} / S_{k−1}²)² · (P_k P_{k−2} / P_k²)     [schematically]
```

i.e. the `P`-factors reappear in the **denominators** — `λ_k` is a *rational*
function, not a nonneg-coefficient polynomial. So the Motzkin/Karlin–McGregor
non-intersecting-path model built from `(λ_k)` has rational weights and does
**not** exhibit a manifestly-nonneg monomial path model for `P_N`.

The natural Cauchy–Binet factorization `μ_{i+j} = Σ_n B[i,n]B[j,n] w_n`
(which would give `Δ_N = Σ (squared minor)·∏w ≥ 0` directly) **fails**: the
moment matrix is genuinely Hankel (`d_{i+j,n}`), not separable as
`B[i,n]B[j,n]` — the ballot numbers do not factor that way (checked
`i,j ≤ 5`). The spectral measure `dν = Σ_n w_n p_n(t) dμ_arcsine(t)` has a
**signed** density (the `p_n` oscillate), so the point-measure /
squared-Vandermonde positivity does not apply.

---

## 5. What was formalized (Lean, `YMGap/Continuum/LGVPositivity.lean`)

All axiom-clean (`[propext]` / `[propext, Quot.sound]`; no
`Classical`/`sorry`/`native_decide`), build green.

| theorem | content |
|---|---|
| `cCol0_nonneg` | `0 ≤ c_0(N) = 1`, all `N` |
| `cCol1_nonneg` | `0 ≤ c_1(N) = 2(N−1)`, `N ≥ 1` (uniform `∀N`) |
| `cCol2_nonneg` | `0 ≤ c_2(N) = (N+1)(2N−3)`, `N ≥ 2` (uniform `∀N`) |
| `cCol3x3_nonneg` | `0 ≤ 3·c_3(N) = 2(2N−1)(N²+2N−9)`, `N ≥ 3` (uniform `∀N`) |
| `cCol{0,1,2,3x3}_matches` | closed forms `= P_2,P_3,P_4` actual coeffs (`decide`) |
| `P5_nonneg`, `P5_ge_one` | `nonnegCoeffs P_5`, `P_5 ≥ 1` — base extended to `N = 5` |
| `cCol_matches_P5` | the four closed forms continue to match at `N = 5` |

The `cColj_nonneg` are **genuine `∀N` theorems** (over `Q'`, via
`zero_le_iff_num_nonneg` + `omega`/factoring on `Int`), not per-`N`
`decide`s — that is the uniform content the column structure delivers.

---

## 6. Sharp OPEN statement and verdict

**OPEN.** A uniform (N-indexed) proof that `P_N(a) = Δ_N(a)/S_N(a)²` has
nonnegative coefficients for **all** `N`. Exact through `N = 8`; not reduced
to an `N`-indexed theorem.

**Verdict.** The LGV / column-polynomial approach **does not** close the
uniform proof. The low columns are uniformly nonnegative (now proved), but
(i) the column closed forms are only conditionally positive and (ii) there
are `Θ(N³)` columns whose higher members are not determined by feasible data;
and the Hankel↔Jacobi LGV route yields rational, not nonneg-polynomial,
weights. A genuine non-intersecting-path / Schur-positive model for `P_N`
(its coefficients are log-concave and unimodal, consistent with one) would
close the gap, but none was found.

The standing uniform pieces are: the perfect-square factor `S_N²`
(`QHankel.SN`, uniform), the division-free Favard reduction
(`Favard.favard_numer_nonneg`, uniform), and now the lowest-column
nonnegativities of `P_N` (this work). The missing piece is the *all-column*
nonnegativity of `P_N`.
