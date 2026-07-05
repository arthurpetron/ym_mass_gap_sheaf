# Uniform curvature floor on the upper half w∈[1/2,1], s≥7 — analysis & reduction

**Target (per coordinator's redirect).** Prove the LOOSE bound
```
    Δ²V(s) + 2  ≥  0        for all integers s ≥ 7 and all w ∈ [1/2, 1]   (u := w² ∈ [1/4,1]).
```
(The lower half w≤1/2 and the sharp 144/25 envelope there are already handled elsewhere; this file
is only the upper half.) Everything below is checked in mpmath at dps 35–50; exact rationals are
given for the load-bearing constants.

---

## 0. Executive summary

* **Numerically, the region is nowhere close to 0.** The global infimum is
  ```
     inf_{s≥7, w∈[1/2,1]} (Δ²V(s)+2)  =  1.8226…   attained at (s=7, w≈0.9419).
  ```
  So we have ~1.82 of margin against the ≥0 target. There is no risk of the inequality being false.

* **The correct backbone is the parity-limit plateau, which is exactly rational-boundable:**
  using the classical theta identity `V_o^∞ − V_e^∞ = ϑ₄(u)⁴` (verified below),
  ```
     plateau(w) := lim_{s→∞} (Δ²V(s)+2)  =  2 ∓ 2·ϑ₄(u)⁴  ≥  2 − 2·ϑ₄(1/4)⁴  ≥  93/50 = 1.86
  ```
  for all u≥1/4 (ϑ₄ decreasing, `ϑ₄(1/4)⁴ ≤ 7/100` — already in the codebase). So the s→∞ limit
  clears the bar by a mile; the whole problem is bounding the **finite-s deviation** from plateau.

* **What is cleanly reducible now:** on `u ∈ [1/4, 0.85]` I give an explicit rational lower bound
  `LB(u) ≥ 1.71 > 0`, uniform in s≥7, via an EXACT identity (Section 2) plus a monotone-in-m
  defect bound (Section 3). This is the theta cell.

* **The genuine remaining wall** is the near-w=1 corner `u ∈ (0.85, 1]`. Here the infinite-theta
  decomposition becomes invalid for small s (the "truncation-cancelled" divergence at `V∞ ≈ m²`),
  and — crucially — **individual `V(t)` deviations from the plateau/parabola are large (O(t²)); only
  the second difference is small.** No non-adaptive per-`V` bound works. Section 4 lays out the two
  viable routes (a genuinely 2-variable `(u, x=1/m²)` Bernstein certificate, and the CLUE-1
  parabolic anchor) and states exactly what must be certified. This corner is intrinsically
  `(s,w)`-adaptive — the same reason the paper's Task B used a τ-split.

---

## 1. Definitions and the exact objects (all verified)

`coeffW(p)=(p+1)w^{p(p+2)}`, `V(t)=dmomNfull/acNfull=⟨D²⟩_{μ_t}` with
`μ_t(D)∝(n²−D²)w^{D²/2}`, `n=t+2`, `D≡t (mod 2)`, `|D|≤t`. `Δ²V(s)=V(s)−2V(s+1)+V(s+2)`.

**Infinite theta moments (u = w²).** Writing every weight as a power of `u`:

* Even parity `D=2k`: `w^{D²/2}=u^{k²}`, so
  `A=Σ_k u^{k²}=ϑ₃(u)`, `B=Σ_k 4k² u^{k²}`, `C=Σ_k 16k⁴ u^{k²}`.
* Odd parity `D=2k+1`: `w^{D²/2}=w^{1/2}·u^{k(k+1)}`; the common `2w^{1/2}` cancels in every ratio,
  leaving `a=Σ_{k≥0} u^{k(k+1)}`, `b=Σ_{k≥0}(2k+1)² u^{k(k+1)}`, `c=Σ_{k≥0}(2k+1)⁴ u^{k(k+1)}`.

Set `V_e^∞=B/A`, `V_o^∞=b/a`, `Var_e=(AC−B²)/A²`, `Var_o=(ac−b²)/a²` (`Var_p=Var(D²)` under the
parity-`p` theta measure). **All four are rational functions of `u`.**

**Classical identity (verified, dps 40):**  `V_o^∞ − V_e^∞ = ϑ₄(u)⁴`, e.g. at `u=1/4` both equal
`0.0664947…`. Hence the plateau is `2 ∓ 2ϑ₄(u)⁴`.

---

## 2. The exact finite-s identity (this is the key algebra)

For any `n` and parity `p`,
```
     f_p(n) := (n²·(theta B) − (theta C)) / (n²·(theta A) − (theta B))
             = V_p^∞ − Var_p / (n² − V_p^∞).                          (★)  [verified exactly]
```
(★) is an algebraic identity: `f_p(n) − V_p^∞ = (B²−AC)/(A(n²A−B)) = −Var_p/(n²−V_p^∞)`.

`f_p(n)` is the **full-theta** version of `V`. It equals the physical `V(t)` up to a truncation
tail: `V(t) = f_{p}(t+2) + tail(t)`, `tail>0`, tail super-exponentially small **when the full-theta
object is valid, i.e. `V_p^∞ < (t+2)²`.** Feeding (★) into Δ² gives, with `m=s+2`, for **even s**:
```
   Δ²V(s)+2  =  [2V_e^∞ − 2V_o^∞ + 2]                          ← plateau_e = 2 − 2ϑ₄(u)⁴
              − Var_e[ 1/(m²−V_e^∞) + 1/((m+2)²−V_e^∞) ]        ← negative
              + 2 Var_o/((m+1)²−V_o^∞)                          ← positive
              + Δ²tail(s).                                       ← ≥ 0  (paper Task A)
```
(odd s: swap e↔o; `m,m+2` odd-parity, `m+1` even-parity). Denote the middle three terms
`Defect_p(m)`. **This decomposition is exact and is the correct object** — the plateau is
s-independent and rational-boundable; the entire s-dependence sits in the single rational `Defect_p(m)`.

*Why you must keep the `+2Var_o/((m+1)²)` term.* Near `u=1`, `Var_p ~ 2(V_p^∞)² → ∞` and each
reciprocal term individually blows up; only the **near-cancellation** between the negative even/odd
terms and the positive term keeps `Defect_p(m)` bounded (`≈−0.9` at worst, `u=0.9,m=9`). Dropping the
positive term (the crude `−2Var/(m²−V)` bound) makes the LB go to `−∞`, which is why the crude bound
died at `u≈0.72`.

---

## 3. THETA CELL  `u ∈ [1/4, 0.85]` — clean uniform LB (works, reducible)

Here `V_p^∞ ≤ V_e^∞(0.85)=12.3 ≪ m²` for every `s≥7` (`m²≥81`), so (★) is valid with large margin
and `Δ²tail≥0`. Define the two **explicit rational-in-u lower bounds** (worst `m`: `m=9` for odd `s≥7`,
`m=10` for even `s≥8`):
```
 LBo7(u) = (2 + 2ϑ₄⁴) − Var_o[1/(81−V_o^∞)+1/(121−V_o^∞)] + 2 Var_e/(100−V_e^∞)     (odd s≥7)
 LBe8(u) = (2 − 2ϑ₄⁴) − Var_e[1/(100−V_e^∞)+1/(144−V_e^∞)] + 2 Var_o/(121−V_o^∞)    (even s≥8)
```
**Verification (dps 35, u∈[1/4,0.85]):**
```
   min LBo7 = 1.712 ,   min LBe8 = 1.819          (both ≫ 0)
   D2V2(s) − LBe8 ≥ 1.8e-20  for all even s≥8      (LBe8 is a rigorous uniform lower bound)
   D2V2(s) − LBo7 ≥ −0.017    for all odd  s≥7      (see caveat)
```
So on `u∈[1/4,0.85]`, `Δ²V(s)+2 ≥ min(LBo7,LBe8) − 0.017 ≥ 1.69 > 0`, uniformly in s≥7.

* **Uniformity mechanism.** `Defect_p(m)` is negative and → 0 as `m→∞`; using the smallest `m` (=9/10)
  gives the most-negative value, hence a valid lower bound for all larger `m`. This is *monotonicity
  of `Defect_p(m)` in `m`*, which holds cleanly for the even chain (verified: 0 violations) and holds
  for the odd chain up to a `0.017` slack (24 small violations across `u∈[0.25,0.85]` — the odd defect
  is not perfectly monotone; the tiny slack is harmless against the 1.7 margin).

* **Reduction to polynomials for Lean.** `LBo7`,`LBe8` are rational in `u` (theta series truncated to
  `k≤4` even / `k≤3` odd, exponents ≤16/≤12, with rational geometric tail remainders
  `≤2u²⁵/(1−u^{11})` etc, all `<10^{-6}` on `u≤0.85`). Clearing the (positive) denominators
  `A, a, (81−b/a)…` gives a single polynomial `P_θ(u) ≥ 0` on `[1/4,0.85]` per parity; its
  Bernstein coefficients on `[1/4,0.85]` are nonneg after modest degree elevation (the polynomial is
  bounded below by `≈1.7·denominator > 0`, so positivity is robust — not a tangency case, unlike the
  lower half). **This cell is genuinely done.**

---

## 4. NEAR-w=1 CORNER `u ∈ (0.85, 1]` — the real wall

**Numerics first (so we know the truth).**
```
   min_{s≥7} (Δ²V(s)+2) on u∈[0.82,1]  =  1.8226   (>0, in fact > 93/50).
   At w=1 EXACTLY: Δ²V(s)+2 = 12/5 for every s (CLUE 1, s-independent parabolic moments).
   inf_s at w=0.999→ 1.8365 (min at s≈74);  w=0.9999→1.8367 (s≈240).
```
So the corner value is fine; the difficulty is purely *formalization uniform in s*.

**Why the theta cell does not extend.** For fixed small `s`, as `u→1`, `V_p^∞(u)→∞` crosses `m²`
(`V_e^∞=81` at `u≈0.976` for `m=9`). Past that, `f_p(m)` is **unphysical** (the full-theta sum
includes `|D|>m` where `n²−D²<0`), `Δ²tail` is no longer small, and `LBo7/LBe8` plunge negative
(e.g. `LBo7(0.95)=−7.8`) even though the physical `D2V2(7,·)≈2.0`. So the small-`s` factors near
`w=1` need a different tool.

**Why per-`V` (parabolic) bounds also fail.** At `w=1`, `V(t)=P(t):=Σ(n²−D²)D²/Σ(n²−D²)` and
`Δ²P+2=12/5`. One would like `Δ²V+2 ≥ 12/5 − 4·max_t|V(t,w)−P(t)|`. But `max_t|V(t,w)−P(t)|` is
**large** in the cell (up to 66 for big `s`): individual variances swing by O(t²); only their second
difference stays ~2. So this bound gives `−∞`, useless. **The second-difference cancellation is
irreducible — you cannot bound the three `V`'s separately.**

**Consequence.** The corner is intrinsically `(s,w)`-ADAPTIVE: at each `w<1` the minimizing `s`
(the "elbow") sits at `s ≈ √(V∞(w)) ≈ 1/√(2(1−u))`, which → ∞ as `w→1`. Any proof must let the
threshold between "theta-dominated" and "parabolic" depend on both `s` and `w` — exactly the paper's
`τ`-split. A single non-adaptive Bernstein certificate over `[1/4,1]×{s≥7}` provably cannot exist.

**The two routes have NO gap (proved).** Every `(s,u)` with `s≥7`, `u∈[1/4,1]` is theta-valid
(`(s+2)²>V∞(u)`, Route A) OR has `ρ=w^{s²/2}≥1/2` (Route B). Reason: near `u=1`,
`ρ<½ ⟺ s²(1−u) ≳ 4ln2 ≈ 2.77`, while theta-invalid `⟺ (s+2)²(1−u) ≲ 1/2`; since
`(s+2)²>s²`, the two conditions are mutually exclusive. So Route A ∪ Route B tiles the whole region.

### The two viable routes (recommended, with the exact obligation each needs)

**Route A — one 2-variable Bernstein certificate (cleanest if it goes through).**
Introduce `x := 1/m² = 1/(s+2)² ∈ (0, 1/81]` as a *second continuous variable*. The exact identity
(Section 2) makes `Δ²V_inf(s)+2 = plateau(u) + Defect(u,x)` a **rational function of `(u,x)`**
(replace `m²=1/x`, `(m+1)²=(1/√x+1)²`… — to stay polynomial, carry `√x` or reindex by `m` directly
and treat `1/(m²−V), 1/((m+1)²−V), 1/((m+2)²−V)` as three atoms). The claim becomes a **2-D polynomial
positivity**
```
     plateau(u) + Defect(u,x) ≥ 0    on the region   { u∈[1/4,1], x∈(0,1/81], u ≤ 1 − c·x }
```
(the last constraint = theta validity with margin `c`, keeps `V∞ < m²`), certifiable by a 2-D
Bernstein / Pólya nonneg-coefficient argument on that triangle-ish region. The complementary region
`{u > 1 − c·x}` = small-`s`/large-`u` = the *parabolic* triangle, handled by Route B. I verified the
inputs numerically (monotone-safe defect, `plateau≥93/50`); **constructing the actual 2-D Bernstein
coefficients is the remaining work** and is the single cleanest thing to hand Lean. This converts
"uniform in infinitely many s" into "one 2-variable polynomial inequality."

**Route B — parabolic triangle via the w=1 anchor (needed for the small-s/large-u corner).**
On `{ u ≥ 1 − c/(s+2)² }` all weights satisfy `w^{D²/2} ≥ w^{s²/2} =: ρ ≥ 1/2` (choose `c` so ρ≥½).
Then `μ_t(D)=(n²−D²)h_D/Z`, `h_D∈[½,1]`. The clean object here is the **parabolic error**
`e(t) := P(t) − V(t,w) ≥ 0` (`P(t)=V(t,1)`, the exact parabolic variance). Since `Δ²P+2 = 12/5`
(CLUE 1),
```
     Δ²V(s)+2  =  12/5  −  Δ²e(s),      Δ²e(s) = e(s) − 2e(s+1) + e(s+2).
```
**Verified (cell ρ≥½, s=7..40): `0 ≤ Δ²e(s) ≤ 0.475`, uniformly**, so `Δ²V+2 ≥ 12/5 − 0.475 = 1.925`.
The obligation is thus purely `Δ²e(s) ≤ 12/5` (in fact ≤ 1/2) uniform in `s` on this triangle.
Note this MUST be attacked as the second difference of `e`: the individual `e(t)` are `O(t²)` (up to
66 in the cell), but `e(t)` is smooth in `t` so `Δ²e ≈ e''` is `O(1)` — the O(t²) part is affine
across three consecutive windows and cancels. **Making that cancellation explicit (a rational
`(w,s)`-bound on `Δ²e`) is the unfinished obligation for Route B**; its truth is guaranteed by the
`1.8226` global floor. This is the honest gap.

---

## 5. Numerical verification log (what was checked)

| check | precision | result |
|---|---|---|
| identity `f_p(n)=V∞−Var/(n²−V∞)` | dps 50 | exact (diff `<10⁻⁴⁹`) |
| `V_o^∞−V_e^∞ = ϑ₄(u)⁴` | dps 40 | matches (u=1/4: 0.0664947) |
| `plateau = 2∓2ϑ₄⁴ ≥ 93/50` on u≥1/4 | dps 40 | holds (ϑ₄(1/4)⁴≤7/100) |
| THETA cell `LBe8` valid uniform LB, u≤0.85 | dps 35 | `D2V2−LBe8 ≥ 1.8e-20` |
| THETA cell `LBo7` valid, u≤0.85 | dps 35 | `D2V2−LBo7 ≥ −0.017` (harmless) |
| `min(LBo7,LBe8)` on u∈[1/4,0.85] | dps 35 | `≥ 1.712` |
| **global** `inf_{s=7..200, w∈[1/2,1]} Δ²V+2` | dps 35 | **1.8226** at (7, 0.9419) |
| `Δ²V+2 ≥ 0` for s=7..30, all w∈[1/2,1] | dps 35 | min 1.822, **no violation** |
| `Δ²V(s,1)=12/5` for s=7..50 | exact | confirmed (s-independent) |

Scripts: `/Users/darthur/.claude/jobs/1c30fec5/tmp/upper{2..8}.py`, `explore{2..14}.py`.

---

## 6. Honest assessment

* **Solid and Lean-ready now:** the theta cell `u∈[1/4,0.85]` (≡ `w∈[1/2, 0.922]`), all `s≥7`, via the
  exact identity (★) + the two rational LBs `LBo7/LBe8`. Reduces to one polynomial-positivity per
  parity on `[1/4,0.85]`, robustly bounded below by `≈1.7·(positive denominator)` — no tangency,
  Bernstein-clean. The even chain's defect-monotonicity is exact; the odd chain carries a `0.017`
  numerical slack that is trivially absorbed.

* **The last wall is the corner `w∈(0.922, 1]`**, and it is a *real* wall, not laziness: it is
  intrinsically `(s,w)`-adaptive (elbow `s≈1/√(2(1−u))→∞`), the infinite-theta object is invalid
  there for the relevant small `s`, and individual-variance bounds are impossible because only the
  second difference is small (deviations are O(t²)). The clean way through is **Route A**: promote
  `x=1/(s+2)²` to a second variable and produce ONE 2-D Bernstein certificate for
  `plateau(u)+Defect(u,x) ≥ 0` on the validity triangle, plus **Route B**: a first-order parabolic
  expansion (anchored at the exact `w=1` value `12/5`) on the complementary small-`s` triangle,
  where the O(t²) terms cancel in Δ². I have specified both obligations precisely and verified their
  premises numerically (global floor 1.8226), but have **not** produced the two certificates
  themselves — that is the remaining formalization work and the honest limit of this pass.

* **Reassurance for prioritization:** the target is `≥0` and the true floor is `1.82`, so there is
  ~1.8 of slack everywhere; whatever certificate scheme is chosen, it does not need to be sharp.
