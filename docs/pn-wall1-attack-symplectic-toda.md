# Wall-1 attack: symplectic/LGV determinant model + Dodgson–Toda induction

A fresh pass at `nonnegCoeffs P_N` (the SU(2) heat-kernel Gram residual
`P_N = Δ_N/S_N²`, `q = a²`) pursuing **both** named research routes:
(1) a sign-clean symplectic `Sp(2N)` / non-intersecting-path (LGV) determinant
model, and (2) a Dodgson–Toda induction off the recurrence-coefficient relation.
All claims below are exact sympy (rational/symbolic, no floats for any
coefficient statement); methodology in `/tmp/pn_*.py`.

**Bottom line: neither route closes.** Both are now ruled out as self-contained
closers by exact computer algebra, sharpening (and in two places correcting) the
prior status notes. One genuinely-new, axiom-clean Lean partial was added
(column-4 uniform nonnegativity); the verified base for `nonnegCoeffs P_N` was
extended by exact CA to **N = 10**. The sharp open statement is unchanged.

---

## 0. Data regenerated from scratch (matches Lean ground truth)

`m_s = (s+1)a^{s(s+2)}`, `G_{ij} = Σ_{c=|i−j|, step 2}^{i+j} m_c` (CG fusion),
`Δ_N = det G[0..N−1]`, `S_N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}`, `P_N = Δ_N/S_N²`.
Recomputed exactly and confirmed:

- `deg_q p_N = N(N²−1)/3`, `p_N(0)=1`, lead `(2N−1)!!`, even powers only,
  **all coefficients nonnegative — verified N = 1 … 10** (extends the prior
  exact-CA range N ≤ 8; `P_9` deg 240, `P_10` deg 330, both all-nonneg).
- `p_3 = 1+4q+12q²+20q³+32q⁴+36q⁵+36q⁶+24q⁷+15q⁸` matches `MomentPositivity.P3`.

---

## 1. Route 1 — symplectic / LGV determinant model

### 1a. The structure is exactly as documented (re-confirmed)

- **Hankel−minus−Toeplitz (symplectic) signature.** `G_{ij} = h_{i+j} − h_{|i−j|−2}`
  with `h_n = Σ_{t≥0} m_{n−2t}`, verified N ≤ 4 — the Okada/Krattenthaler
  `Sp(2N)`/`SO(2N+1)` determinantal form.
- **`a·G` is a nonneg-coefficient matrix.** With `t_r = r·a^{r²}` (the
  differentiated-Jacobi-theta coefficients), `a·G_{ij} = Σ_{p=0}^{min(i,j)}
  t_{|i−j|+1+2p}`, so `a^N·Δ_N = det(a·G)` and every entry of `a·G` is a finite
  sum of positive theta-monomials (verified N=2,3). **All** sign content of `Δ_N`
  is the determinantal cancellation of a nonneg-coefficient matrix.

### 1b. Why every positive-model variant fails (re-derived exactly)

- **Heine/Andréief gives only value-positivity.** The lacunary measure
  `μ = Σ_{r≥1} r·δ_{x_r}`, `x_r = a^{r²}`, has positive weights, and the Heine
  identity `det[μ_k] = Σ_{r_1<…<r_N} ∏r_k · Vandermonde(x)²` holds (verified
  N=2,3). But this Hankel of `μ_k = Σ_r r·a^{k r²}` is **not** the character
  `Δ_N` (checked N=2,3,4: not equal) — the character Gram is the *fusion*
  (symplectic Hankel−Toeplitz) form, not the naive Hankel. So the clean positive
  Heine sum is for the wrong determinant; for the right one it only reproduces
  the (already known) value-positivity `Δ_N ≥ 0`.
- **The staircase `h_n` is not a positive moment sequence.** `det[h_{i+j}]` is
  **sign-mixed** already at N=2 (`1·q² − 4q + 3`, coeffs `[1,0,0,−4,3]`) — so the
  symplectic-Schur positivity theorems (which require a TN / positive-moment
  kernel) do **not** apply. `h_n` is the *cumulative* (Toeplitz partial-sum) of
  the theta atoms, `h_n = [x^n] θ(x)/(1−x²)`, not `∫x^n dν`.
- **The fusion atoms are not rank-1.** Writing `a·G = Σ_s t_{s+1} E_s` with `E_s`
  the 0/1 fusion-indicator matrix, the `E_s` have rank `2,3,4,…` (not 1), so
  Cauchy–Binet does **not** factor `det(a·G)` into a positive sum. (Checked the
  fusion indicators `[r ∈ S(i,j)]` for r=1..6: ranks `4,4,3,4,3,2`.) The
  Gaussian exponent `r²` makes `t_r` non-factorizable across `i,j`, so `a·G` is
  not a TN/path kernel — the theta/Gaussian obstruction, made explicit.
- **`P_N` is not a positive principal character combination** (prior Farkas
  result, unchanged): exact infeasibility at N=2,3; `P_N` irreducible over ℚ.
- **No nonneg-coefficient real factorization.** `P_N` has **no positive real
  roots** (verified N=2,3,4), consistent with value-positivity, but its real
  quadratic factors `q²+bq+c` (from conjugate root pairs in the right
  half-plane) carry **negative** `b` — so even over ℝ there is no
  nonneg-coefficient product. Irreducibility over ℚ already forbids a rational
  product.

**Verdict (Route 1):** every *positive-combination / total-nonnegativity /
positive-moment* incarnation of the symplectic model is dead. The lone surviving
sub-route — a **non-principal** (charge / major-index) vicious-walker LGV path
sum exhibiting the Gessel–Viennot sign-reversing involution on the permutation
expansion of `det(a·G)/(a^N S_N²)` — was **not** constructed. It remains a
genuine research problem.

## 2. Route 2 — Dodgson–Toda induction

### 2a. The relation is exact (corrects §5b's schematic prefactor)

With `β_k = Δ_{k+1}Δ_{k−1}/Δ_k²` (the Favard coefficient), verified k = 2 … 7:

    β_k = (q^k − 1)² · P_{k+1} · P_{k−1} / P_k².

Equivalently `R_k := P_{k+1}P_{k−1}/P_k² = β_k/(q^k−1)²`, and the denominator of
`R_k` (in lowest terms) is **exactly `P_k²`** (verified k=2…7: `den(R_k) = P_k²`,
and `P_k² ∤ P_{k−1}P_{k+1}`, remainder nonzero — `P_N` irreducible).

### 2b. Why it does not induct (re-confirmed) — and the log-concavity check fails

- **Circular.** `β_k`'s numerator literally contains `P_{k+1}`; there is no
  `q`-rational multiplier free of the higher `P`. The relation is an *identity*
  expressing `λ_k` and `P_{k+1}` in terms of each other, not a recurrence.
- **Not coefficient-log-concave in N.** The natural rescue — Newton/log-concavity
  `P_k² ≥ P_{k−1}P_{k+1}` coefficientwise (which would make the multiplier
  manifestly bounded) — **fails**: `P_k² − P_{k−1}P_{k+1}` is sign-mixed for all
  k=2…7 (it is nonneg in the bottom strip but the **leading** coefficients are
  negative, e.g. ends `…,−2`). So `P_N` is log-concave at the bottom and
  log-convex at the top in N; no uniform sign.

**Verdict (Route 2):** dead as a self-contained induction (circular; no
`q`-rational multiplier; no coefficient log-concavity to tame it).

## 3. Column structure — the formalizable fragment (extended)

Writing `P_N = Σ_k c_k(N) q^k`, each low column `c_k(N)` is a degree-`k`
polynomial in `N` with leading coefficient `2^k/k!` **in its interior regime**
`N ≳ k`. With the extended data (N ≤ 10) the reliability boundary is now sharp:

| k | closed form (`m_k·c_k(N)`) | fitted lead vs `2^k/k!` | reliable? |
|---|---|---|---|
| 0 | `1` | `1 = 1` | ✔ (9 val. pts) |
| 1 | `2(N−1)` | `2 = 2` | ✔ |
| 2 | `(N+1)(2N−3)` | `2 = 2` | ✔ |
| 3 | `(2/3)(2N−1)(N²+2N−9)` | `4/3 = 4/3` | ✔ |
| 4 | `(4N⁴+20N³−97N²+73N−30)/6` | `2/3 = 2/3` | ✔ (2 val. pts) |
| 5 | — | `4/15 = 4/15` but **0 val. pts** | ✘ (pinned, not validated) |
| 6 | — | `17/180 ≠ 4/45` | ✘ (not yet in interior regime) |
| 7 | — | `109/2520 ≠ 8/315` | ✘ |

Column 4 is the **last solidly-reliable** column (fitted lead `2/3` matches
theory, with 2 independent leave-one-out validation points). Its closed form
`6·c_4(N) = 4N⁴+20N³−97N²+73N−30` matches the genuine `c_4(N)` for N=4…9
exactly, equals `169,485,1070,2032,3495,5599` there, and is `≥ 0` for all N≥3
(largest real root ≈ 2.42; substituting `N=M+4` gives the all-positive-coeff
form `4M⁴+84M³+527M²+1281M+1014`).

**Why this is only a fragment.** Two structural walls, unchanged: (i) each
`c_k(N)` is only *conditionally* positive — valid and nonneg only for `N ≥ N₀(k)`
with `N₀(k)` growing in `k`; (ii) `P_N` has `Θ(N³)` columns and the *bulk* sits
at `k ∼ N³`, deep in the boundary region the column-in-N description cannot
reach. The fragment covers the lowest `O(1)` columns for all N; it does not touch
the bulk.

## 4. What was added to Lean (axiom-clean)

`YMGap/Continuum/PNDeterminant.lean` (namespace `YMGap.Continuum.PNDet`), builds
green under `lake build YMGap.Continuum.PNDeterminant`:

- `cCol4` / `cCol4_nonneg` — the column-4 closed form, proved **nonnegative for
  every N ≥ 4** as a genuine `∀N` theorem over `Q'` (mathlib-free: core `Int`
  ring lemmas + `omega`, via the grouping `N²(4N²+20N−97)+(73N−30)`). Extends
  `LGVPositivity`'s `c_0…c_3` by one reliable column.
- `cCol4_matches`, `cCol4_matches_P5` — agreement with the actual `P_4`, `P_5`
  column-4 coefficients (`c_4(4)=169`, `c_4(5)=485`), `decide`-certified.

`#print axioms`: `cCol4_nonneg → [propext, Quot.sound]`; the `matches` lemmas
`→ [propext]`. No `Classical`, no `sorryAx`, no `native_decide`.

**Import line needed** (do NOT auto-edit `YMGap.lean`):

    import YMGap.Continuum.PNDeterminant

## 5. The single sharpest remaining open statement

> **OPEN.** A uniform (N-indexed) proof of `nonnegCoeffs P_N` for all N —
> equivalently (`PNInduction.UniformPNDiffNonneg`) that `P_{N+1} − P_N` is
> coefficient-nonneg for all N. Exact-CA verified through **N = 10**; not reduced
> to an N-indexed theorem.

The lone route with residual headroom is a **non-principal vicious-walker / LGV
path sum** realizing `p_N(q)` with a charge / major-index statistic, in which the
Gessel–Viennot involution resolves the determinantal cancellation of the
nonneg-coefficient matrix `a·G` (§1a) into a manifestly positive sum. Concrete
handles: the symplectic Hankel−Toeplitz form (§1a), the `e^{2Nq}` walker envelope
(`[q^k]P_N ∼ (2N)^k/k!`), and the lacunary node lattice `{a^{r²}}` with drift
`t_r = r a^{r²}`. Value-positivity (the heat kernel being a positive measure,
hence the Andréief integral `≥ 0`) is strictly weaker and is **not** the target.
The Wall-2 (analytic differentiated-Jacobi-triple-product) route to the same
uniform PSD remains the alternative and is unaffected by these findings.
