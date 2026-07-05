# Theta branch of the R1 curvature-floor corner — finite/uniform reduction

**Scope.** The θ-branch of `Δ²V(s)+2 ≥ 0` for `w∈[1/2,1]`, `s≥7`, on the region
`(35+4K)w ≤ 4K` (`K=s²+6s+7`), i.e. `u=w² ∈ [1/4, u_θ(s)]` with
`u_θ(s) := (4K/(35+4K))²`.  On this branch the truncation `|D|≤t` is negligible and the
exact-defect infinite-θ lower bound `LBθ(u,s)` applies, with `Δ²V+2 ≥ LBθ` (since `Δ²tail≥0`).

**Headline result (all numerically verified, mpmath dps 35–40, exact-rational load-bearing constants).**
The θ-branch reduces to **ONE uniform rational inequality valid for every `s≥7`**

> `LBθ(u,s) ≥ 93/50 − Def(u,s) ≥ 93/50 − 39/50 = 27/25 = 1.08 > 0`,

resting on exactly **four single-variable θ-moment lemmas** (in `u` only, `s`-free) plus trivial
rational algebra and two manifestly-nonnegative edge polynomials.  No enumeration over `s` is
needed for positivity.  (The true branch minimum is `LBθ = 1.746` at `s=7, u=u_θ(7)=0.8428`; the
certificate `1.08` is a valid, comfortable lower bound.  Note: the earlier documented floor
"`≥1.78`" is slightly optimistic — the honest branch-edge minimum is `1.746`.)

---

## 0. Objects (exact)

Parity-`p` infinite-θ moments of `D²`, `u=w²`:
```
even:  A=Σ_k u^{k²},  B=Σ_k 4k² u^{k²},  C=Σ_k 16k⁴ u^{k²}         (k∈ℤ)
odd :  a=Σ_{k≥0} u^{k(k+1)},  b=Σ (2k+1)² u^{k(k+1)},  c=Σ (2k+1)⁴ u^{k(k+1)}
V_e^∞=B/A,  V_o^∞=b/a,   Var_e=(AC−B²)/A²,  Var_o=(ac−b²)/a²,   ϑ₄(u)⁴ = V_o^∞−V_e^∞
```
With `m=s+2`, `p` = parity of `s`, `p'` the opposite parity:
```
LBθ(u,s) = plateau − Def,
plateau  = 2 ∓ 2ϑ₄(u)⁴          (− for even s, + for odd s),
Def      = Var_p[1/(m²−V_p^∞) + 1/((m+2)²−V_p^∞)] − 2Var_{p'}/((m+1)²−V_{p'}^∞).
```

---

## 1. The four θ-moment lemmas (single-variable, the entire analytic content)

All four are `s`-free statements in `u∈[1/4,1)`. Verified sups over a fine `u`-grid incl. `u→1`:

| # | Lemma | statement | verified sup / status |
|---|---|---|---|
| **M1** | mean envelope | `V_e^∞(u)·(1−u) ≤ 2` and `V_o^∞(u)·(1−u) ≤ 2` | sup **= 2** (`u→1`) |
| **M2** | variance envelope | `Var_e(u)·(1−u)² ≤ 8` and `Var_o(u)·(1−u)² ≤ 8` | sup **= 8** (`u→1`) |
| **U3** | plateau anchor | `ϑ₄(u)⁴` decreasing on `[1/4,1)`, and `ϑ₄(1/4)⁴ ≤ 7/100` | monotone ✓; max `0.06649 < 0.07` |
| **U4** | parity-gap of Var | `|Var_e(u) − Var_o(u)| ≤ 1` on `[1/4,1)` | max **0.98224 < 1** (at `u=1/4`) |

M1, M2 are the **discrete-Gaussian moment envelopes**: for weight `u^{k²}=e^{−εk²}`,
`V_p^∞ = 4⟨k²⟩_disc ≤ 4·1/(2ε) = 2/ε ≤ 2/(1−u)` (using `−ln u ≥ 1−u`); the sup `=2` is the exact
Gaussian value, approached only as `u→1`.  `Var_p ≈ 2(V_p^∞)²` (Gaussian kurtosis of `D²`), whence
the `8/(1−u)²` envelope.  U3's anchor `ϑ₄(1/4)⁴ ≤ 7/100` is **already proved in the codebase**
(`R1RegimeGE.theta4QuarterAnchor`, alternating-series bracket `ϑ₄(1/4)∈[0,65/128]`, `(65/128)⁴≤7/100`).

---

## 2. Deliverable 3 — plateau reduction (exact, essentially done)

`plateau (even s) = 2 − 2ϑ₄(u)⁴ ≥ 93/50  ⟺  ϑ₄(u)⁴ ≤ 7/100` on the branch.
Since `ϑ₄(u)⁴` is **decreasing in `u`** (U3) with maximum at the left endpoint `u=1/4`, and
`ϑ₄(1/4)⁴ ≤ 7/100` is the **proved anchor**, we get `ϑ₄(u)⁴ ≤ ϑ₄(1/4)⁴ ≤ 7/100` for all `u∈[1/4,1)`.
Odd-`s` plateau `= 2 + 2ϑ₄⁴ ≥ 2` is immediate.  **Exact reduction:**
`plateau ≥ 93/50  ⟸  {ϑ₄⁴ monotone-↓ in u}  +  {ϑ₄(1/4)⁴ ≤ 7/100, PROVED}`.
The only new obligation vs the codebase is the monotonicity `∂_u ϑ₄(u)⁴ ≤ 0`.

---

## 3. Deliverable 2 — uniformity in `s` (the defect bound)

The defect terms are individually `O(m²)`, but a **second-difference cancellation** collapses `Def`
to `O(1)` (`Def → 0.234`, never exceeds `0.254`).  Dropping the positive `+2Var_{p'}/…` term is
**invalid** (that surrogate grows like `Def_dropPos ≈ 6.4 → ∞`).  The cancellation is exposed by the
exact identity (with `g_V(x)=1/(x²−V)`, verified algebraically):

```
Def = Var_p · Δ²g_{V_p^∞}(m)  +  2[ Var_p·g_{V_p^∞}(m+1) − Var_{p'}·g_{V_{p'}^∞}(m+1) ]
    = term1 + t2,     where the exact closed form of the second difference is
Δ²g_V(m) = g_V(m) − 2g_V(m+1) + g_V(m+2) = 2(3m²+6m+2+V) / [(m²−V)((m+1)²−V)((m+2)²−V)].
```

### 3a. The uniform edge facts (rational, PROVED for all s≥7)

Let `δ(s) := 1−u_θ(s) = 35(35+8K)/(35+4K)²` (exact).  On the branch `u≤u_θ(s)` so `1−u≥δ(s)`,
hence from M1/M2:  `V_p^∞ ≤ 2/(1−u) ≤ 2/δ(s)` and `Var_p ≤ 8/(1−u)² ≤ 8/δ(s)²`.  Two edge
polynomials convert these to the `m`-scale (both verified: only positive real root `< 7`, and the
`s=t+7` shifts have **all-nonnegative coefficients**, so positivity for `s≥7` is a one-line Lean fact):

```
(Pc)  m²·δ(s) ≥ 12        ⟺  Pc(s)=88s⁴+496s³−1935s²−16828s−34888 ≥ 0
      Pc(t+7)=88t⁴+2960t³+34353t²+149730t+133917  (all coeffs ≥0)   [min m²δ = 12.734 at s=7]
      ⇒  V_p^∞ ≤ 2/δ(s) ≤ m²/6.                               (margin c = 1/6; true sup 0.1444)

(Pd)  m⁴·δ(s)² ≥ 160      ⟺  Pd(s)=1225 m⁴(35+8K)² − 160(35+4K)⁴ ≥ 0  (deg 8)
      Pd(t+7) has all 9 coeffs ≥0                              [min m⁴δ² = 162.17 at s=7]
      ⇒  used directly in the term1 bound below.
```

### 3b. The uniform defect bound  `Def ≤ 39/50`  (all s≥7)

**term1.** With `V_p^∞ ≤ m²/6` (Pc): denominator `≥ (5m²/6)³`, numerator `2Var_p(3m²+6m+2+V_p)`
with `3m²+6m+2+V_p ≤ 25m²/6` (uses `6m+2≤m²` for `m≥9`) and `Var_p ≤ 8/δ²`:
```
term1 ≤ 115.2 / (m⁴·δ(s)²)  ≤  115.2/160 = 18/25 = 0.72.        (Pd)   [true term1 ≤ 0.254]
```

**t2 (parity mismatch).** `t2 = 2·N/[(M−V_p)(M−V_{p'})]`, `M=(m+1)²`,
`N = M(Var_p−Var_{p'}) − (Var_p·V_{p'}^∞ − Var_{p'}·V_p^∞)`.  Bounding with U4 (`|Var_p−Var_{p'}|≤1`),
U3 (`|V_p^∞−V_{p'}^∞|=ϑ₄⁴≤7/100`), M1 (`V_p^∞≤m²/6`), M2 (`Var_p≤8/δ²`):
```
|t2| ≤ 3/50 = 0.06.                                              [true t2 ≤ 0.016]
```

**Total.** `Def = term1 + t2 ≤ 18/25 + 3/50 = 39/50 = 0.78`, hence
`LBθ ≥ 93/50 − 39/50 = 27/25 = 1.08 > 0` for **all `s≥7`** on the branch.

> **Consequence for the moderate/large split (deliverable 2a/2b).**  Because the constants
> `c=1/6`, and the edge facts (Pc),(Pd) hold for **every** `s≥7` (their minima sit at `s=7`), the
> single uniform bound of §3b already discharges the whole branch — there is **no residual finite
> `s`-enumeration and no `S1`**.  The "large-`s` uniform defect bound" of deliverable 2b **is** §3b,
> with explicit margin `c<1` (true `V_p^∞/m² ≤ 0.1444`, threshold `1/6`, asymptote `4/35≈0.1143`).
> A moderate/large split is only forced if one declines to prove M1/M2 up to `u→1` (see §5).

---

## 4. Deliverable 1 — truncation with rational geometric tails (per `s`)

For fixed `s`, `u_θ(s)<1` is an explicit rational, so each θ-moment truncates at `k≤N(s)` with a
**rational geometric tail**.  With `r := u^{2(N+1)}` (`< 1`):
```
0 ≤ A − A_N = 2Σ_{k>N} u^{k²}          ≤  2 u^{(N+1)²}/(1−r)
0 ≤ B − B_N = 8Σ_{k>N} k² u^{k²}       ≤  8 u^{(N+1)²}·[ 2(N+1)²/(1−r) + 2r(1+r)/(1−r)³ ]
0 ≤ C − C_N = 32Σ_{k>N} k⁴ u^{k²}      ≤  32 u^{(N+1)²}·[ polynomial in (N+1),r over (1−r)^{≤5} ]
```
(bound `(N+1+j)² ≤ 2(N+1)²+2j²`, `Σ j^{2i} r^j` = rational; same shape for `a,b,c` with
`u^{k(k+1)}`).  Ratio bounds use numerator+`tail_upper` over the truncation (a valid lower bound of
the denominator).  The term count and (after clearing denominators) the `u`-polynomial degree grow
**linearly / quadratically in `s`**:

| `s` | `u_θ(s)` | `ε=−ln u_θ` | `N(s)` terms | `u`-poly deg `≈N²` | tail `R_N` |
|---|---|---|---|---|---|
| 7 | 0.84278 | 0.171 | 19 | 361 | `<2e−30` |
| 10 | 0.90291 | 0.102 | 24 | 576 | `<2e−28` |
| 20 | 0.96760 | 0.033 | 42 | 1 764 | `<4e−27` |
| 30 | 0.98409 | 0.016 | 60 | 3 600 | `<1e−26` |
| 50 | 0.99379 | 0.0062 | 97 | 9 409 | `<2e−26` |
| 100 | 0.99835 | 0.0017 | 187 | 34 969 | `<1e−25` |

`N(s) ≈ 1.3–1.9·s` (since `N ≈ √(c/ε)` and `ε ≈ 35/(2K) ∼ 35/(2s²)`).  **This is why per-`s`
Bernstein is the wrong tool**: the degree blows up.  The §3b uniform route avoids truncation
entirely (it uses only the closed-form envelopes M1/M2), which is the recommended reduction.

**If a moderate/large split is nonetheless wanted** (to confine M1/M2 to a corner): pick a rational
cutoff `u*` (e.g. `u*=49/50`), set `S1 = max{ s : u_θ(s) ≤ u* }` (`u*=49/50 ⇒ S1≈35`).
* **moderate `s = 7…S1`** (`u_θ(s) ≤ u*`): prove `LBθ≥0` by the §4 truncation + a Bernstein/`decide`
  positivity of the resulting `u`-polynomial on `[1/4,u_θ(s)]`; degree up to `≈N(S1)²` (`≈5000` at
  `S1=35`).  Needs only U3's anchor (no M1/M2).
* **large `s > S1`**: the §3b bound, but now M1/M2 are only required on `u∈[u*,1)`.

---

## 5. Lean-feasibility judgment (honest)

**Trivial / already done (rational algebra + `decide`/`omega`):**
* Edge polynomials (Pc),(Pd): positivity for `s≥7` is immediate from the all-nonnegative `s=t+7`
  coefficient lists above — a few lines.
* The `Def ≤ 39/50` algebra (§3b): the closed-form `Δ²g_V(m)`, the `term1 ≤ 115.2/(m⁴δ²)` and
  `|t2|≤3/50` derivations, and `93/50−39/50=27/25>0` are all exact `Q'` inequalities.
* Plateau: `ϑ₄(1/4)⁴ ≤ 7/100` is **already a theorem** (`theta4QuarterAnchor`).
* §4 geometric tails are rational and reuse the existing θ-truncation toolkit.

**The genuine remaining obligations (all single-variable in `u`, `s`-free):**
1. **M1** `V_p^∞(u)(1−u) ≤ 2` and **M2** `Var_p(u)(1−u)² ≤ 8`, valid **up to `u→1`**.
2. **U3-monotone** `ϑ₄(u)⁴` decreasing in `u` on `[1/4,1)`.
3. **U4** `|Var_e(u)−Var_o(u)| ≤ 1` on `[1/4,1)`.

These are the discrete-Gaussian **moment-envelope** and **parity-gap** inequalities.  **Honest
blocker:** M1/M2 are *not* finitely truncatable — they are tight exactly at `u→1` (sups `2`, `8` are
the Gaussian constants), so no finite polynomial + geometric-tail certificate can prove them on all
of `[1/4,1)`; they need a genuine analytic argument (Poisson/Jacobi comparison, or log-concavity of
`k↦u^{k²}` giving `⟨k²⟩_disc ≤ 1/(2ε)`).  For any cutoff `u≤u*<1` they *do* reduce to a finite
polynomial inequality (via §4), which is what the moderate/large split buys — but the split cannot
remove the `u→1` corner, only relocate the analytic content there.

**Net assessment.**  The θ-branch is reduced from the opaque numerical claim "`min LBθ≥1.78`" to a
crisp, mostly-finite certificate: **one exact rational inequality `LBθ≥27/25`** whose only
non-elementary inputs are the **two Gaussian-envelope moment bounds M1/M2 (+ monotonicity U3, +
bounded gap U4)** — four clean, classical, single-variable θ-series inequalities.  Everything else
(edge polynomials, defect algebra, plateau, tails) is machine-level rational arithmetic.  The
envelopes M1/M2 near `u=1` are the one true analytic lemma that remains; they are standard and
self-contained, but are **not** reducible to the codebase's finite-truncation machinery.

## 6. Verification log

| check | precision | result |
|---|---|---|
| `min LBθ` on branch, `s=7..200`, `u∈[1/4,u_θ]` | dps 40 | **1.746** at `(7, u_θ(7))`; 0 invalid |
| M1 `sup V_p^∞(1−u)` on `[1/4,1)` | dps 40 | **2.000** (`u→1`) |
| M2 `sup Var_p(1−u)²` | dps 40 | **8.000** (`u→1`) |
| U3 `ϑ₄⁴` monotone-↓, `max` on `[1/4,1)` | dps 40 | monotone ✓; `0.06649 < 0.07` |
| U4 `max|Var_e−Var_o|` | dps 40 | **0.98224 < 1** |
| `sup V_p^∞/m²` on branch (margin `c`) | dps 40 | **0.14436** (`< 1/6`; asympt `4/35`) |
| (Pc) `min m²δ`, s=7..2000 | exact `F` | `12.734`; `Pc(t+7)` coeffs ≥0 |
| (Pd) `min m⁴δ²`, s=7..2000 | exact `F` | `162.17`; `Pd(t+7)` coeffs ≥0 |
| worst-case `term1 ≤ 18/25`, `t2 ≤ 3/50` | exact `F` | 0 violations, s=7..399 |
| all rational bounds ≤ true quantities | dps 35 | 0 violations, s=7..200 |
| **uniform floor** `LBθ ≥ 27/25` | exact `F` | `1.08 > 0`, all `s≥7` |

Scripts: `/Users/darthur/.claude/jobs/1c30fec5/tmp/theta{1..7}_*.py`.

---

## Addendum (2026-07-05) — the modular-dual route for M1/M2 (visualized)

The two analytic residuals **M1** `V_p^∞(1−u)≤2` and **M2** `Var_p(1−u)²≤8` are "not finitely
truncatable" ONLY in the θ (`q`-series) basis, which diverges as `u→1`. This is a **basis artifact**:
the Jacobi/Poisson **dual** series converges instantly there. Verified: at `u=0.98` the θ-series needs
**31 terms** to tolerance 1e-9; the Poisson dual needs **1**. So the recommended attack is to
re-express `V_p^∞, Var_p` via the modular transform (`ϑ₃(τ)=(−iτ)^{−1/2}ϑ₃(−1/τ)`, codebase
`JTPIdentity`); near `u=1` M1/M2 become **leading terms of a convergent dual expansion**, provable
finitely, with the free constants `2, 8` as the leading (continuum-Gaussian) values.

Interactive visualization: `computations/r1_corner_localCLT_viz.html` (self-contained; generator
`r1_corner_localCLT_viz_data.py`) — shows (i) the fusion measure's parabola→Gaussian collapse, (ii)
the M1/M2 ceilings pressed against `2` and `8`, (iii) the θ-vs-dual term-count blow-up, (iv) Lemma C's
tilted curvature touching its free maximum at `q=1`. Physics reading: every residual is one statement —
the lattice theory is free-Gaussian at the free rate — read off at a different moment; the uniform-in-s
wall is the algebraic basis, not the mathematics.
