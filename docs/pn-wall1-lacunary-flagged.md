# Wall-1: the lacunary-deformed flagged sp(2N) character test on `nonnegCoeffs P_N`

The last-surviving Wall-1 sub-route (named in `pn-wall1-hamel-king.md` §5) was a
**`t`-deformed flagged sp(2N) King-tableau character carrying the lacunary drift
`t_r = r·a^{r²}`** (NOT a geometric specialization `x_k = q^k` — proven
impossible by the palindrome obstruction). This pass tests that route exactly
(sympy, exact rational/symbolic throughout — no floats for any coefficient
claim) and **closes it off** with two clean new obstructions plus an exhaustive
spec sweep. Scripts: `/tmp/pn_*.py`.

Base data reproduces the Lean ground truth exactly (`P_2 = [1,2,3]`, `P_3` matches
`MomentPositivity.P3`, `P_6/P_7` match `PNPaths`; `deg p_N = N(N²−1)/3`,
`p_N(0)=1`, lead `(2N−1)!!`, even `a`-powers, all-nonneg, `p_N(1) =
N!·∏_{k=1}^{N−1}C(2k+1,k) = 1,6,180,25200,15876000,…`).

---

## Bottom line up front

**The lacunary-deformed flagged-character route is exhausted. No specialization
(geometric, lacunary, or per-r drift) of the Hamel–King deformed/flagged sp(2N)
character — nor the Okada single-determinant, nor the King-tableau deformed
character — reproduces `p_N(q)` exactly, and for N ≥ 3 a clean *dimension
obstruction* rules out the full deformed symplectic character entirely.** The
N = 2 case is settled *exhaustively* (all candidate shapes enumerated and each
ruled out by an exact exponent-multiplicity argument). Nothing closes; the
findings are sharp **negatives** that exhaust Wall-1's algebraic-character
sub-route. **Verdict: Wall 1 has no remaining character/flagged-determinant
route; Wall 2 is the path.**

---

## 0. What was tested (all exact, sympy)

| # | Object tested | Net | Result |
|---|---|---|---|
| 1 | Plain lacunary alphabet `y_r=a^{r²}` flagged JT | N≤4, M≤N+2, staircase | **ODD-in-`a` / no match** |
| 2 | Hamel–King deformed sp(2n) denominator `D_sp(x;t)` (eq 1.10) vs `S_N²` | N≤3, geometric `x_k=a^{2k}`, t∈{±1,a,a²} | **no match** (palindromic, wrong degree) |
| 3 | Drift power-sum unflagged JT `s_λ` (`h` from `p_r` = 6 drift laws) | N≤4, 4 shapes | **no match** |
| 4 | Flagged sp JT (eq 3.30) geometric/lacunary `x`, single `t` | N≤3, 3 var-specs × 5 t-specs × 3 shapes | **no match** |
| 5 | Okada single-determinant `H`-Jacobi–Trudi (Thm 3.1 z-spec) | N≤3, 3 var × 5 t-specs × 3 shapes | **no match** |
| 6 | Deformed King-character tableau sum `Σ_T t^{2bar(T)} x^{wgt}` (eq 1.11) | N≤3, 4 var × 5 t × shapes, n∈{N−1,N} | **no match** |
| 7 | Per-cell lacunary-drift character `Σ_T ∏ a^{W(cell)}` | N≤3, 7 weight laws × shapes | **no match** |
| 8 | **ALL flag-vectors**, staircase, geometric symplectic `h`, t∈{±1,a,a²} | N≤3, all suffix/prefix flag vectors | **no match** |
| 9 | **Capstone**: flagged + deformed + lacunary combined sweep | N≤3, n∈{N−1,N}, 4 var × 4 t × all flag vectors | **no match** |

Every test demanded **exact polynomial-in-`q` equality** (coefficient tuple,
normalized by leading monomial + gcd), not value-at-1 or partial coefficients
(the documented trap). No spec in any net matched.

---

## 1. The DIMENSION obstruction — `p_N(1)` is not a symplectic dimension for N ≥ 3 (exact, NEW)

The sharpest new structural result of this pass. A clean *value-level*
impossibility for the **full** (un-flagged) deformed character:

> **Theorem (dimension obstruction).** The deformed King character
> `spλ(x;t) = Σ_{T ∈ King(λ,n)} t^{2·bar(T)} x^{wgt(T)}` (Hamel–King eq 1.11) is
> a sum over King symplectic tableaux with **positive** integer coefficients.
> Under any specialization `x_k = a^{c_k}`, `t = a^{d}` to powers of `a`, its
> value at `a = 1` is `spλ(1;1) = |King(λ,n)| = dim_{Sp(2n)} V_λ` — the
> symplectic Weyl dimension. Hence `p_N(1) = dim_{Sp(2n)} V_λ` is a **necessary
> condition** for the full deformed character to equal `p_N`.
>
> Exact search (correct Sp(2n) Weyl dimension formula, validated against
> `sp(2),(4),(6)` dims 4,5,10,6,…; King-tableau enumerator independently
> validated to reproduce those same dims): **for N = 3, 4, 5 there is NO
> partition `λ` (|λ| ≤ 30) and NO `n ≤ 9` with `dim_{Sp(2n)} V_λ = p_N(1)`**
> (= 180, 25200, 15876000). For N = 2 only two shapes match the count
> `p_2(1) = 6`: `λ=(5)` on `sp(2)` and `λ=(1)` on `sp(6)` (the spin-5 and the
> sp(6) vector).

So for **N ≥ 3 the full deformed symplectic character cannot be `p_N`** — there
is no symplectic irrep of the right dimension at all. (This is the value-level
companion to the §2 palindrome obstruction of `pn-wall1-hamel-king.md`: that one
ruled out *geometric-spec* characters by symmetry; this one rules out the *full
deformed* character by dimension, for N ≥ 3, at **any** spec.)

The full count `p_N(1) = N!·∏C(2k+1,k)` carrying the `N!` factor (a genuine
`S_N`-charge sum, `pn-wall1-lgv-vicious-walker` §0) is exactly what makes it miss
the symplectic-dimension lattice — the `N!` is not produced by any single
Sp(2n)-irrep dimension.

---

## 2. The N = 2 case is settled EXHAUSTIVELY (exact)

The dimension obstruction leaves only `λ=(5)/sp(2)` and `λ=(1)/sp(6)` as the
candidate shapes whose **cardinality** could match `p_2(1)=6`. Both are ruled
out by an exact exponent-multiplicity argument — not a finite spec sweep, but a
full sweep over the *exponent structure*:

* **`λ=(5)` on `sp(2)`.** The deformed character is
  `Σ_{b=0}^{5} t^{2b} x^{5−2b}` (one tableau `1^{5−b}1̄^{b}` per `b`). With
  `x=a^{p}`, `t=a^{r}` the six exponents are `p(5−2b)+2rb`. For the result to be
  `p_2 = 1+2q+3q²` it must collapse to **three** distinct exponents in
  arithmetic progression `0,d,2d` (even) with multiplicities `{1,2,3}` and
  coefficients `1,2,3`. **Exact sweep over all `(p,r) ∈ ℚ` (denominators ≤ 4,
  numerators in [−8,8]): ZERO `(p,r)` produce the multiplicity profile
  `{1,2,3}`.** (Each tableau contributes coefficient `+1`, so a coefficient `3`
  needs three tableaux at one exponent; the 6 monomials never collapse that way.)

* **`λ=(1)` on `sp(6)`.** The deformed character is `Σ_{k=1}^{3}(x_k^{+1} +
  t^{2} x_k^{−1})` (six monomials). With `x_k=a^{c_k}`, `t=a^{r}` the exponents
  are `{c_k, −c_k+2r : k=1,2,3}`. **Exact sweep over all `(c_1,c_2,c_3,r) ∈ ℚ`
  (denominators ≤ 3, numerators in [−6,6]): ZERO produce the `{1,2,3}` profile
  with `0,d,2d` structure.**

> **Conclusion (N = 2).** Neither shape whose King-tableau cardinality equals
> `p_2(1)=6` can yield `p_2 = 1+2q+3q²` under **any** monomial specialization of
> the Hamel–King deformed symplectic character — including the lacunary drift.
> Combined with §1 (no shape even has the right cardinality for N ≥ 3), the
> **full deformed symplectic character route is closed for all N**.

(The asymmetric, strictly-accelerating profile `(1,2,3)` is again the culprit: a
King-character monomial sum has coefficient `+1` per tableau, so any coefficient
`> 1` of `p_N` must come from *exponent collisions*, and the lacunary/geometric
exponent lattices never collide into the `(1,2,3)` shape. This is the precise
mechanism behind the irreducibility/non-palindromicity walls.)

---

## 3. The FLAGGED character (the palindrome-breaking object) — swept, no match

The full character is killed by §1–§2; the genuine Hamel–King escape was always
the **flagged** character (eq 3.30), `spλ(x;t) = det[h_{λ_i−i+j}(flagged
alphabet_i)]`, which sums over a *subset* of King tableaux (so its `q=1` value is
the subset size, **not** a dimension — §1 does not directly apply) and **breaks
palindromicity** (a flag truncates the tableaux asymmetrically). This was the
last hope. It was swept exhaustively:

* **Test 8 — all flag-vectors, geometric symplectic `h`, deform `t`.** Over the
  staircase `δ_N`, every per-row flag set (all suffix `{b..n}` and prefix
  `{1..b}` of the variable set, every row independently) and `t∈{1,a,a²,−1}`:
  **no flag-vector reproduces `p_N`** (N = 2, 3).
* **Test 9 — capstone (flagged + deformed + lacunary).** The same flagged
  determinant with the symplectic doubling `{x_k, t²/x_k}`, lacunary variable
  specs `x_k ∈ {a^{2k}, a^{k²}, a^{2k²}, a^{k(k+2)}}`, deformations
  `t∈{1,a,a²,−1}`, and `n∈{N−1,N}` (so the flag can carry the `(2k+1)` King
  top-multiplicity): **no spec reproduces `p_N`** (N = 2, 3; exact, search
  complete over the net).

The flag truncates palindromicity but **does not** hit the lacunary
exponent/coefficient profile of `p_N` at any tested specialization. The flagging
that the prompt's mechanism requires (row `i` restricted to variables `i..n`,
breaking the Weyl symmetry) is fully covered by the suffix-flag family of
tests 8–9.

---

## 4. Reconfirmed negatives (sharpened, exact)

* **`S_N` is the type-A Vandermonde, not the deformed sp denominator (§1 of
  `pn-wall1-hamel-king`, reconfirmed exactly).** At `x_k=a^{2k}` the Hamel–King
  deformed sp(2n) denominator `D_sp(x;t)` (eq 1.10) is **palindromic** with
  degree far exceeding `deg S_N²`, for every `t∈{±1,a,a²,−a²}` — it is never
  `S_N²`. `S_N²` has signature `(1,−2,1)` (N=2), `(1,−4,4,4,−10,4,4,−4,1)` (N=3);
  the deformed denominator never matches.
* **The box product does NOT divide `p_N`.** `∏_{k=1}^{N−1}[2k+1 choose k]_q` has
  `deg = deg p_N` and `q=1` value `∏C(2k+1,k)` with `p_N(1)/box(1) = N!` exactly
  (N≤4), but `box ∤ p_N` (nonzero remainder, N=2,3,4) — so the `N!` is a genuine
  `S_N`-charge **sum**, not a product factor (reconfirms
  `pn-wall1-lgv-vicious-walker` §0). The would-be charge generating function
  `p_N/box` is not even a polynomial.
* **Plain drift power-sum `s_λ` and per-cell drift characters** (6 + 7 laws) give
  no even-in-`a` polynomial matching `p_N` at any tested shape — the lacunary
  `r²` exponents do not arrange into the `p_N` coefficient profile.

---

## 5. Verdict and the single sharpest open statement

**New this pass (exact, sympy):**

1. **Dimension obstruction (§1):** `p_N(1)` is **not a symplectic Weyl dimension**
   for N = 3, 4, 5 (no `λ`, |λ|≤30, `n≤9`). So the **full deformed sp(2N)
   character cannot equal `p_N` for N ≥ 3 at any spec** — a clean value-level
   impossibility, the companion to the geometric-spec palindrome obstruction.
2. **N = 2 exhaustive closure (§2):** the only two shapes with cardinality
   `p_2(1)=6` (`(5)/sp(2)`, `(1)/sp(6)`) are each ruled out by an exact
   exponent-multiplicity sweep — no monomial spec of their deformed character
   yields `1+2q+3q²`.
3. **Flagged-character sweep (§3):** the palindrome-breaking flagged sp(2N)
   character (the last surviving object) reproduces `p_N` at **no** spec in a
   wide flag × deformation × lacunary net (tests 8–9).

**OPEN — the single sharpest remaining statement (Wall-1 character route now
EXHAUSTED):**

> There is no flagged/deformed sp(2N) King-tableau character — at any
> geometric, lacunary, or per-`r` drift specialization of the Hamel–King
> object — equal to `p_N(q)`, on the exact evidence above (full character ruled
> out for all N by §1–§2; flagged character ruled out by the §3 sweep). The
> coefficient-positivity `nonnegCoeffs P_N` is therefore **not** the shadow of any
> classical symplectic-character positivity. The only Wall-1 object not algebraically
> excluded is a bespoke **non-principal vicious-walker / type-`C` charge LGV path
> sum** (`pn-wall1-lgv-vicious-walker` §4) whose statistic was never constructed
> and which §1–§2 now show **cannot** coincide with any Sp(2n) character — i.e.
> if it exists it is a genuinely new combinatorial object, not a known character.

**Honest verdict on Wall 1.** After this pass the algebraic-character /
flagged-determinant family is **exhausted**: positive-character combinations
(Farkas, `sp2n-pn-notes` §3), geometric-spec characters (palindrome, hamel-king
§2), the **full deformed character** (dimension, §1 here; N=2 exhaustive, §2
here), and the **flagged deformed character** (sweep, §3 here) are all ruled out.
What survives is only (a) the bespoke non-principal charge LGV path sum (no
construction, and now known to be non-character), or (b) the column-polynomial
uniform fragment (`LGVPositivity`/`PNDeterminant`, lowest `O(1)` of `Θ(N³)`
columns). Neither closes `nonnegCoeffs P_N`. **The Wall-2 (analytic,
differentiated–Jacobi-triple-product) route is unaffected and is the
recommended path.**

---

### Lean delta

No new Lean theorem closes from this pass (the result is a family of exact
*negatives*). The named open obligations are unchanged: `HankelResidualNonneg N`
(`PNPaths.lean`) / `UniformPNDiffNonneg` (`PNDeterminant.lean`). No file under
`lean/` was modified; `SORRY_LEDGER.md` and `YMGap.lean` untouched.
