# Lemma C via log-concavity — the structural route, and an honest verdict

**Target (Lemma C, as convexity).** On the tilted parabolic ensemble
`ρ_t(D) ∝ c_D = (n²−D²) q^{D²}` (`D≡t mod 2`, `|D|≤t`, `n=t+2`), with `Var_q(t)=Var_{ρ_t}(D²)`,
`e(t):=Var_par(t)−Var_q(t)` (the tilt deficit, `≥0`, `=0` at `q=1`):

> **Lemma C  ⟺  `Δ²_t e(s) ≥ 0` for all `s≥7`, `q∈(0,1]`   (i.e. `e(t)` is convex in `t`).**

**One-paragraph verdict.** Log-concavity of `c_D` gives the correct *ensemble* (a discrete-Gaussian ×
downward-parabola, verified log-concave) and the correct *scaling limit*, and it lets me collapse the
whole uniform-in-`s` problem to **one explicit, `s`-free, one-variable inequality** — a genuine
sharpening of the prior "`L ≤ 110/63`" residual. But it does **NOT** structurally *close* Lemma C.
The reason is sharp and reproducible: the irreducible core inequality holds by **genuine
cancellation, not termwise positivity** (its Taylor coefficients follow a fixed `+,−,−` sign pattern),
so no log-concavity / TP / Lorentzian / SOS-coefficient argument makes it manifest. **The uniform-in-`s`
core survives, in a cleaner canonical form: a positivity of an explicit `erf`/`exp` special function.**

Every number below is `mpmath` dps 40–60 or exact `sympy`.

---

## 0. Foundation (verified, elementary — the part log-concavity really does give)

* **Log-concavity of `c_D`.** Exact identity `(n²−D²)² − (n²−(D−2)²)(n²−(D+2)²) = 8(n²+D²−2) ≥ 0`
  (sympy: `True`), and `q^{2D²} ≥ q^{2D²+8}` for `q∈(0,1]`. So `ρ_t` is a log-concave probability
  measure. ✔
* **`e(t) ≥ 0` and `Δ²_t e ≥ 0`** hold throughout (raw scan: `min Δ²e = 3.2·10⁻³` at `s=7, q→1`;
  all `>0`, `s=7..80`, `q∈[10⁻², 1−10⁻⁶]`). Lemma C is TRUE. ✔
* Exact edges (decidable polynomials in `s`, both provable): the `q→1` edge slope
  `∂_μ Δ²e|₀ = Δ²m₃_par(s) = 64(5s⁴+60s³+211s²+186s−42)/875 > 0` (so `Δ²e ↑` from `0` at `q=1`),
  and the `q→0` collapse `Δ²e → Δ²Var_par(s)=96(s²+6s+7)/175 > 0`. **Both endpoints are provably
  positive and finite-decidable.** The entire difficulty is the *interior* `q∈(0,1)`.

---

## 1. The main structural result: the interior collapses to one `s`-free profile `Ψ(τ)≥0`

**Scaling limit (from log-concavity ⇒ local CLT).** With `x=D/s∈[−1,1]`, `μ=−ln q`, and the natural
tilt variable `τ := μ s²`, the ensemble converges to the continuum density `∝ (1−x²)e^{−τx²}` on
`[−1,1]`. Define
```
   V(τ) := Var_{ρ_τ}(x²),   ρ_τ(x) ∝ (1−x²)e^{−τx²},   g(τ) := V(0) − V(τ)   (≥0, g(0)=0).
```
Then `Var_q(t) ≈ s⁴ V(τ)` and `e(t) ≈ s⁴ g(τ)`. Taking `Δ²_s ≈ ∂²_s` of `φ(s):=s⁴ g(μs²)` at fixed
`μ` gives the exact reduction (verified by direct differentiation):
```
   ∂²_s [ s⁴ g(μs²) ]  =  s² · Ψ(τ),      Ψ(τ) := 12 g + 18 τ g' + 4 τ² g''.
```

> **THE CORE:  `Ψ(τ) ≥ 0` for all `τ ≥ 0`  ⟺  the `s→∞` limit of Lemma C, uniformly in `s`.**

This is a single one-variable inequality with **no `s`**. Numerically `Ψ(τ) > 0` strictly on `(0,∞)`,
`Ψ(0)=0`, `Ψ'(0)=960/2625=0.36571>0`, rising to a peak `≈0.577` near `τ≈5` and settling to the exact
plateau `Ψ(∞)=12·V(0)=96/175=0.548571`. (`V(0)=8/175`, exact.)

**Euler-operator factorization (exact, sympy-verified).** With `θ:=τ d/dτ`,
```
   Ψ(τ) = 2 (2θ + 3)(θ + 2) g(τ).
```
This is the cleanest possible form: `(2θ+3)(θ+2)` acts on `τ^k` as `(2k+3)(k+2) > 0`. **So `Ψ≥0`
would be *termwise-trivial* IF `g(τ)` had nonnegative Taylor coefficients.** It is exactly here that
log-concavity fails to help — see §2.

**Discreteness helps (the finite-`s` correction has the right sign).** The discrete
`Δ²e(s,q)/s²` converges to `Ψ(τ)` **from above**, with a positive `O(1/s)` correction:
`min_{s=7..80, τ-grid} [ Δ²e − s²Ψ(τ) ] = +0.958` (at `s=7`). So the continuum `Ψ(τ)≥0` is the
**worst case** (`s→∞`); every finite `s≥7` sits strictly above it. Structurally:
```
   Δ²e(s,q) = s² Ψ(τ) + (positive discreteness correction),    both terms ≥ 0.
```

---

## 2. Why log-concavity does NOT close it — the obstruction, sharpened

Apply the factorization: `Ψ = 2 Σ_{k≥1} a_k (2k+3)(k+2) τ^k`, where `g(τ)=Σ_{k≥1} a_k τ^k`,
`a_k = −V^{(k)}(0)/k!`. The exact coefficients (sympy):

| k | `a_k` | sign |
|---|---|---|
| 1 | `32/2625` | **+** |
| 2 | `−288/336875` | **−** |
| 3 | `−15616/65690625` | **−** |
| 4 | `+272768/4138509375` | **+** |
| 5 | `−117248/27918515625` | **−** |
| 6 | `−1934674432/1838015476171875` | **−** |
| 7 | `+…` | **+** |
| … | | period-3 pattern **+,−,−** |

The coefficients are **not** all nonnegative — they follow a rigid `+,−,−,+,−,−,…` sign pattern.
Hence `Ψ(τ)` (and the tilt deficit `g` itself) is **positive only by cancellation**: the single large
positive lead term `a_1` dominates the infinitely many small negative corrections. Consequences:

* **No log-concavity / TP₂ / variation-diminishing argument works.** Those produce *termwise* or
  *sign-count* positivity. Here the object is positive *against* its own coefficient signs.
* **No Lorentzian / ultra-log-concavity (Brändén–Huh) closure.** Lorentzianness delivers exactly the
  CLT skeleton (`Ψ`'s continuum existence) and the log-concave sequence we already have; the *sign of
  the Edgeworth correction* — which is what `Ψ>0`-by-cancellation and the `O(1/s)` discrete term
  encode — is a refinement Lorentzianness does not see.
* **No pointwise cumulant route.** Equivalently `e(t)=½∫₀^μ m₃ dν`, `Δ²e=½∫₀^μ Δ²m₃ dν`, and
  `Δ²m₃` is not `≥0` pointwise (dips to `−116`). Same cancellation, confirming the prior memos.

**The irreducible object.** In closed form the continuum moments are
`M_p(τ)=∫_{-1}^1 x^{2p}e^{−τx²}dx ∈ span{ erf(√τ)·τ^{−p−½}, e^{−τ}·τ^{−k} }` (sympy), e.g.
`M_0=√π·erf(√τ)/√τ`, `M_1=−e^{−τ}/τ+√π erf(√τ)/(2τ^{3/2})`, … So
```
   Ψ(τ)  =  an explicit rational function of  erf(√τ)  and  e^{−τ}  (and √τ),   Ψ(τ) ≥ 0.
```
This is a **special-function positivity** — real-analytic, provable in principle (e.g. via the
parabolic-cylinder / error-function bounds), but **not `decide`-able, not termwise, not
log-concavity-reducible.** It is the same *character* as the prior "`L ≤ 110/63` theta-sup" residual,
but a cleaner canonical form: a *positivity* of one explicit function rather than a sup-ratio.

---

## 3. The four requested angles — how far each gets

1. **Total positivity / Karlin (variation-diminishing).** *Fails to close.* The tilt kernel
   `e^{−μD²}` is TP∞, but `Var` is a nonlinear functional and the target is positive *against* its
   coefficient signs (§2); a sign-count/VD argument cannot certify a cancellation. TP correctly
   yields the log-concave `ρ_t` and the CLT — the *setup*, not the *inequality*.
2. **Log-convexity of the partition function `Z_t(μ)=Σ(n²−D²)e^{−μD²}`.** *Same wall.*
   `Var_q(t)=∂²_μ ln Z_t`, and Lemma C `⟺ ∂²_μ ln Z_t` (as a function of `μ`, after `Δ²_t`) is
   *maximized at `μ=0`*. But `∂³_μ` of it is `−Δ²m₃`, which changes sign — so it is an interior
   extremum reached against non-monotonicity, i.e. the cancellation again, not a Turán/Hankel
   sign-definite determinant. The `Δ²_t` moment sequence is **not** a Turán-positive (log-concave)
   sequence, so the QHankel/Turán machinery does **not** apply here (it applies to M1/M2, not C).
3. **Lorentzian / ultra-log-concavity (Brändén–Huh).** *Gives the skeleton, not the closure.* Yields
   local CLT ⇒ existence of `Ψ` and the log-concave weights; does **not** control the sign of the
   Edgeworth/`O(1/s)` correction or the `+,−,−` cancellation in `Ψ`.
4. **Direct convexity of `e(t)` (summation-by-parts / SOS).** *This is the winning framing —* it
   produces the clean `Ψ = 2(2θ+3)(θ+2)g` factorization and the `Δ²e = s²Ψ + positive` split. But
   the manifest-square/positive-coefficient hope dies on the `+,−,−` sign pattern: `e(t)` is **not** a
   sum of squares of the log-concave weights; its positivity is a special-function inequality.

---

## 4. What a constructive Lean proof would actually need (honest decomposition)

Lemma C reduces to **three** obligations, of which two are finite/decidable and one is the surviving
continuum core:

* **(E) Endpoints — DECIDABLE.** `Δ²m₃_par(s)>0` and `Δ²Var_par(s)>0`: explicit polynomials in `s`,
  `decide`-checkable (Positivstellensatz on ℤ[s]).
* **(D) Discreteness correction — a local-CLT/Euler–Maclaurin lemma.** `Δ²e(s,q) ≥ s²·Ψ(μs²)`
  (discrete ≥ continuum), empirically a clean positive `O(1/s)` gap. Needs its own proof; log-concave
  (Lorentzian) weights are the right tool for the CLT part, but the *sign* of the correction is an
  extra input.
* **(C) The core — SURVIVES.** `Ψ(τ) ≥ 0` for all `τ≥0`, an explicit `erf`/`exp` positivity.
  **Not** decidable, **not** termwise, **not** delivered by log-concavity.

So the uniform-in-`s` obstruction is **not removed** — it is *relocated and cleaned*: from "a family
of growing-degree per-`s` Bernstein certificates" (the abandoned algebraic route) to **one `s`-free
special-function inequality `Ψ(τ)≥0` plus a positive discreteness correction.** That is a real
structural advance in *form*, but the hard analytic kernel is irreducible.

---

## 5. Codebase machinery mapping

| piece | best template file | role |
|---|---|---|
| (E) endpoint polynomials `Δ²m₃_par, Δ²Var_par > 0` | `Continuum/Positivstellensatz.lean` / `MarkovLukacs.lean` | `decide`/SOS on ℤ[s] |
| **factorization `Ψ=2(2θ+3)(θ+2)g`, `Δ²e = s²Ψ + corr`** | `Continuum/XMeanSecondDiffProgress.lean` + `MeanComplementLogConcave.lean` | *purpose-built* "second difference of a variance, cleared into two half-inequalities that add" (`xmsd_of_halves_core`, `meanExpConvex_of_halves`) — the natural home for the `Δ²e ≥ s²Ψ` split |
| (D) local-CLT / log-concave weights | `Continuum/FusionLogConcave.lean` (`LogConcave`,`lc_step`), `LineSumLogConcave.lean` | CLT skeleton from log-concavity |
| (C) `Ψ(τ)≥0` `erf`/`exp` positivity | `Continuum/JTPIdentity.lean` Gaussian-majorant engine (`nsq_aa_pow_le`,`gauss_le_geo`) + `Q'` Leibniz toolkit | the only place that estimates Gaussian/theta series with explicit tails — the tooling class the core needs |
| ~~Turán/QHankel/Favard/CyclotomicPositivity~~ | — | **does NOT apply to Lemma C**: the `Δ²_t` moment sequence is not Turán-positive (route 2). These are the M1/M2 template, not C. |

**Note.** The Turán/Favard/QHankel/Cyclotomic Hankel-positivity stack is the correct template for the
*sibling* residuals M1/M2 (log-concave moment sequences), but **not** for Lemma C — its second-
difference object is positive by cancellation, outside the Hankel-determinant sign-definite regime.

---

## 6. Numerical verification log

| check | method / precision | result |
|---|---|---|
| `c_D` log-concave identity `= 8(n²+D²−2)` | exact sympy | ✔ `True` |
| raw `Δ²e > 0`, `s=7..80`, `q∈[10⁻²,1−10⁻⁶]` | mpmath dps 40 | min `3.23·10⁻³` at `s=7,q→1`; **0 violations** |
| `V(0)=8/175`, `Ψ(∞)=96/175`, `Ψ'(0)=960/2625` | exact sympy limits | ✔ all exact |
| factorization `Ψ = 2(2θ+3)(θ+2)g` | exact sympy | ✔ matches `12g+18τg'+4τ²g''` |
| `Ψ(τ) > 0` on `(0,500]` | mpmath dps 40, 100-pt grid | min `3.66·10⁻⁴` (→0 only at `τ→0`); **strictly >0** |
| **`g` Taylor coeffs `a_k` sign** | exact sympy `k=1..14` | `+,−,−,+,−,−,…` — **NOT all ≥0** (cancellation) |
| discrete `Δ²e/s² → Ψ(τ)` from above | mpmath dps 50, `s=7,15,30,60` | converges, `O(1/s)`, **positive** correction |
| `Δ²e − s²Ψ ≥ 0`, `s=7..80`, τ-grid `[0.02,400]` | mpmath dps 40 | min `+0.958`; **0 violations** |
| continuum moments closed form | exact sympy | `∈ span{erf(√τ)τ^{−p−½}, e^{−τ}τ^{−k}}` |
| `q→1` edge slope `= Δ²m₃_par` (weight-1) | mpmath dps 50 | ratio `→2·(½)=1` in half-weight; `>0` |

Scripts (in `/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `lc_core.py` (ensemble, `Δ²e`),
`lc_continuum.py` (`Ψ` profile), `lc_taylor.py` (Euler factorization + `a_k` signs),
`lc_disc_vs_cont.py` (discreteness correction sign), `lc_adversarial.py` (uniform scans),
`lc_closedform.py` (moment closed forms).

---

## 7. Adversarial bottom line

**Does log-concavity structurally close Lemma C uniformly in `s`?  NO.**

What it *does* do (and this is genuine progress): it identifies the ensemble as log-concave, gives the
CLT scaling limit, and lets the entire uniform-in-`s` interior collapse to a single clean object,
`Ψ(τ)=2(2θ+3)(θ+2)g ≥ 0` — `s`-free, one variable, with the finite-`s` problem sitting *above* it
(positive `O(1/s)` correction) and both endpoints provably positive decidable polynomials. This is a
strictly cleaner residual than the abandoned per-`s` growing-degree Bernstein family and than the
second-order `L≤110/63` theta-sup bound.

But the **irreducible core survives**: `Ψ(τ)≥0` is true by **cancellation** (`+,−,−` coefficient
pattern), so it is *not* reachable by any coefficient-sign / TP / Lorentzian / SOS-of-log-concave-
weights argument. It is a positivity of an explicit `erf`/`exp` function — real analysis of exactly
the difficulty of Lemma C's own scaling profile. Log-concavity relocates and canonicalizes the
obstruction; it does not dissolve it.
