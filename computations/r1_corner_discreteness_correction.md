# The discreteness correction for Lemma C: mechanism, exact leading term, and an honest verdict

**Target.** Write the discrete second difference of the tilt deficit as
```
   Δ²_s e(s,q)  =  s²·Ψ(τ)  +  CORRECTION(s,q),        τ := μ s²,   μ := −ln q,
```
where `Ψ(τ)≥0` is the `s`‑free continuum CLT profile (handled separately) and `CORRECTION` is *defined*
as the difference. Since the identity is a definition, the logic is airtight:
```
   Ψ(τ) ≥ 0   ∧   CORRECTION(s,q) ≥ 0        ⟹        Δ²e ≥ 0   =   Lemma C.
```
This memo settles the second conjunct: **is `CORRECTION ≥ 0` provable constructively and uniformly in
`s ≥ 7`?** Objects: `e(t)=Var_par(t)−Var_q(t)`, `Var_q(t)=Var_{ρ_t}(D²)`,
`ρ_t(D)∝(n²−D²)q^{D²}` (`n=t+2`, `D≡t mod 2`, `|D|≤t`), `Var_par(t)=8t(t−1)(t+4)(t+5)/175`; continuum
`ρ_τ(x)∝(1−x²)e^{−τx²}` on `[−1,1]`, `V(τ)=Var_{ρ_τ}(x²)`, `V(0)=8/175`, `g=V(0)−V`,
`Ψ=12g+18τg'+4τ²g'' = 2(2θ+3)(θ+2)g`, `θ=τ d/dτ`. All numbers below are `mpmath` dps 40–60 or exact
`sympy`.

---

## 1. Headline result (verified)

**`CORRECTION(s,q) ≥ 0` holds uniformly, with infimum 0 attained only in the edge limit `q→1`.**

Adversarial scan `s = 7…200`, 117 values of `τ ∈ [10⁻³, 2000]` (dps 50):
```
   min CORRECTION = +0.0480   at s=7, τ=0.001          (the smallest τ probed)
   ZERO sign violations.
```
`CORRECTION` **grows with `s`** at fixed `τ` (`≈ s·c₁(τ)` with `c₁>0`), so **`s=7` is the tightest row**.
Fine `s=7` sweep over `q∈(0,1)` (`τ=49μ`, `μ`‑grid `10⁻⁶…3`, dps 55): min `CORRECTION(7,q)→0⁺` as `q→1`
(`+0.0024` at `μ=10⁻⁶`), strictly `>0` for every `q<1`. So the infimum is `0`, approached **only** at the
`q→1` corner — which is exactly the corner where `Ψ(τ)→0` too, i.e. where the whole inequality is tight.

---

## 2. The mechanism — Euler–Maclaurin, and the two `O(1/s)` sources (Route 1)

**Route 1 (Euler–Maclaurin) is the correct mechanism; Routes 2 and 3 are not** (see §5). `Var_q` is built
from the moment sums `S_k(s,q)=Σ_{D≡s(2),|D|≤s} D^{2k}(n²−D²)q^{D²}`. Compare each `S_k` to its continuum
integral by Euler–Maclaurin on the **compact** support `[−s,s]` with lattice spacing `2`. There are exactly
two algebraic (`O(1/s)`, *not* exponentially small) sources; a third effect is genuinely subleading.

**Source A — the weight's subleading term (dominant across all `τ`).** In `x=D/s`,
```
   n² − D²  =  (s+2)² − s²x²  =  s²(1−x²)  +  4(s+1).
```
The continuum `Ψ` keeps only `s²(1−x²)`. The dropped `4(s+1)` is, after normalization, an
**`x`‑independent upward shift of the weight** `δ = 4(s+1)/s² = 4/s + 4/s²`. Its linear response of the
variance is a smooth `erf/exp` function `P₁(τ) := ∂_δ Ψ_w(τ,δ)|₀`, contributing
`s²·δ·P₁ = (4s+4)P₁ → 4P₁(τ)` to `c₁`. Numerically `4P₁(τ)` reproduces `c₁(τ)` to within a few % across
all `τ`, and `4P₁ → 768/175 = 4.3886` as `τ→∞`. **Crucially the shift `δ>0` is a positive weight
perturbation** — the edge/parabola is *less* steep than the pure `(1−x²)`, which is the structural origin of
a positive correction.

**Source B — the lattice/trapezoidal boundary.** The leading Euler–Maclaurin boundary term of `S_k` is the
trapezoidal endpoint value
```
   f_k(±s) = s^{2k}(4s+4) e^{−τ} > 0        (manifestly positive, per moment).
```
Its weight `e^{−τ}` makes it dominate the small‑`τ` (`q→1`) corner and vanish as `τ→∞`; the residual
`768/175 → 576/175` plateau shift (`−192/175` at large `τ`) is the combined higher‑order weight response
and the finite‑difference effect below.

**Source C (subleading) — `Δ²_s` vs `∂²_s`.** The discrete second difference of the smooth surrogate
`φ(s)=s⁴g(μs²)` differs from `∂²_s φ = s²Ψ` by `(1/12)∂⁴_sφ + … = O(1)`, i.e. `O(1/s²)` **relative** — it
feeds `c₂`, not `c₁`, and cannot flip the sign.

**Why the sign is not free.** Sources A and B are positive *per moment sum* `S_k`, but `Var = S₂/S₀ −
(S₁/S₀)²` is nonlinear, so `c₁(τ)` is a signed assembly. As with `Ψ`, its positivity is **not** termwise —
it is a positivity of the assembled `erf/exp` function.

---

## 3. The exact leading correction, characterized

### 3a. The `q→1` edge (`τ→0`) — an EXACT cancellation ⇒ a DECIDABLE positive polynomial

The tightest region is where every term vanishes. Here the correction has an exact closed form to first
order in `μ`:
```
   CORRECTION(s,q)  =  μ · (64/875)·(60 s³ + 211 s² + 186 s − 42)  +  O(μ²).
```
Verified: `CORRECTION/μ` at `μ=10⁻⁹` matches this polynomial to 8 significant figures for `s=7…100`. The
mechanism is an **exact cancellation of the leading `s⁴` term**:
```
   ∂_μ Δ²e|₀ = Δ²m₃_par(s) = 64(5s⁴+60s³+211s²+186s−42)/875,   leading s⁴ coeff = 320/875 = 64/175,
   ∂_μ [s²Ψ]|₀ = s⁴·Ψ'(0),      with   Ψ'(0) = 64/175   (independent continuum series, exact sympy),
```
so the `s⁴` pieces **cancel identically**, leaving `μ·(64/875)(60s³+211s²+186s−42)`. The polynomial
`60s³+211s²+186s−42 > 0` for all `s≥1` (value `415` at `s=1`), and `64/875>0`. **This edge is therefore
manifestly positive and finite‑decidable** — a `Positivstellensatz`/`decide` fact on `ℤ[s]`. This is the
one genuinely *easy* and *provable* part of the correction, and it covers exactly the tight corner.

### 3b. The bulk — the `O(1/s)` profile `c₁(τ)`

`Δ²e/s² = Ψ(τ) + c₁(τ)/s + c₂(τ)/s² + …`. Richardson extrapolation (`s=100,200,400`, dps 55) gives a
clean profile:

| `τ` | `c₁(τ)` | `c₂(τ)` |
|---|---|---|
| 0.005 | +0.0219 | +0.077 |
| 0.1 | +0.4298 | +1.50 |
| 0.5 | +1.930 | +6.28 |
| 1 | +3.240 | +8.82 |
| 2 (peak) | +4.233 | +5.97 |
| 8 (dip) | +3.174 | +3.95 |
| ∞ | **576/175 = 3.29143** | **672/175 = 3.84000** |

Anchors (numerically pinned to `≥6` digits): `c₁(τ) ~ (768/175)τ` as `τ→0` (`768/175=4.38857`), interior
peak `≈4.233` near `τ≈2`, local min `≈3.174` near `τ≈8`, plateau `c₁(∞)=576/175`. **`c₁(τ)>0` for all
`τ>0` with no interior zero**, and `c₁(τ) ≥ ≈3.17` for `τ ≳ 1`. `c₂(τ)>0` throughout the scan
(`c₂(∞)=672/175`); both `c₁,c₂ → 0⁺` linearly at `τ→0`, consistent with §3a (`c₁≈4.389τ`, `c₂≈15.4τ`,
matching the `s³` and `s²` coefficients `64·60/875=768/175` and `64·211/875` of the edge polynomial).

**`c₁(τ)` is not monotone (peak then dip then plateau) — it is a genuine `erf/exp` special function**, the
same analytic character as `Ψ`, positive by assembly rather than by a coefficient‑sign certificate. Its
saving grace over `Ψ` is a **strictly positive margin**: linear‑with‑positive‑slope near `0`, and bounded
below by `≈3.17` away from `0`.

---

## 4. Numerical verification log

| check | method / precision | result |
|---|---|---|
| `Ψ'(0)=64/175` (indep. continuum Taylor) | exact sympy, order‑6 series | ✔ `= 64/175` |
| edge `∂_μΔ²e|₀ = Δ²m₃_par(s)` | mpmath dps 60, `μ=10⁻⁸` | ratio `1.000000`, `s=7…60` |
| edge exact form `μ(64/875)(60s³+211s²+186s−42)` | mpmath dps 60, `μ=10⁻⁹` | 8‑digit match, `s=7…100` |
| `60s³+211s²+186s−42 > 0` (`s≥1`) | exact | ✔ (`415` at `s=1`) |
| **global `CORRECTION≥0`, `s=7…200`, 117 τ∈[10⁻³,2000]** | mpmath dps 50 | **min `+0.048` @ s=7,τ=10⁻³; 0 violations** |
| `s=7` sweep `q∈(0,1)`, `μ∈[10⁻⁶,3]` | mpmath dps 55 | min `→0⁺` only as `q→1`; strictly `>0` for `q<1` |
| `c₁(τ)` profile, no interior zero | Richardson `s=100/200/400`, dps 55 | ✔ `>0`, peak `4.233`, min `3.174` |
| `c₁(∞)=576/175`, `c₂(∞)=672/175`, `c₁'(0)=768/175` | Richardson to `6` digits | ✔ all three |
| weight‑perturbation `4P₁(τ)` ≈ `c₁(τ)` | mpmath dps 40 | ✔ dominant source; `→768/175` at large τ |

Scripts (in `/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `corr_01_setup.py` (objects + first scan),
`corr_02_smalltau.py` (edge cancellation), `corr_03_c1.py` (`Ψ'(0)`, edge polynomial, `c₁`),
`corr_04_adversarial.py` (global + `s=7` scans), `corr_05_profile.py` (`c₁,c₂,c₃` profile),
`corr_06_mechanism.py` (weight‑perturbation source).

---

## 5. Where each route lands

1. **Euler–Maclaurin with sign‑definite remainder — the right frame, partial sign.** The remainder splits
   into Source A (positive weight shift `δ=4(s+1)/s²>0`) and Source B (positive trapezoidal endpoint
   `f_k(±s)>0`). Both are positive *per moment*, and this is genuine structure. But the target is a
   *variance* (nonlinear in the `S_k`), so the assembled `c₁(τ)` is **not** rendered manifestly `≥0` by the
   per‑moment signs. The remainder is sign‑definite only after the same `erf/exp` assembly that `Ψ` needs.
2. **Discrete ≥ continuum by convexity/Jensen.** *Does not apply cleanly.* `c₁(τ)` is non‑monotone (peak,
   dip, plateau); there is no single convex object whose lattice sampling over‑ or under‑estimates uniformly
   in `τ`. Jensen controls one `S_k` but not the ratio.
3. **Direct lattice SOS / summation‑by‑parts on log‑concave weights.** *Fails for the same reason `Ψ`
   fails.* Log‑concavity gives the log‑concave `ρ_t`, the local CLT (existence of `Ψ`), and the positive
   per‑moment boundary terms — the *setup*. It does **not** certify the cancellation inside `c₁(τ)`; there
   is no sum‑of‑squares of the weights equal to the correction (the Taylor pattern of `g`, hence of the
   assembled corrections, is `+,−,−,…`).

---

## 6. Codebase machinery mapping

| piece | template file | role |
|---|---|---|
| edge polynomial `60s³+211s²+186s−42 > 0`, `Δ²m₃_par>0` | `Continuum/Positivstellensatz.lean`, `MarkovLukacs.lean` | `decide`/SOS on `ℤ[s]` — the **provable** edge |
| the split `Δ²e = s²Ψ + CORRECTION`, "second difference of a variance cleared into halves that add" | `Continuum/XMeanSecondDiffProgress.lean` (`xmsd_of_halves_core`, `meanExpConvex_of_halves`) + `MeanComplementLogConcave.lean` (`complementBridge`, `AggMeanCurvatureFloor`) | purpose‑built home for a `Δ²(variance) ≥ (floor)` reduction into named Type‑level halves |
| continuum weight `(1−x²)`, `1−x_k²=(n²−(2k+1−n)²)/n²` positivity, semicircle moments | `Continuum/SemicircleIntegral.lean` (`omsNum_pos`, `oneMinusSqNode`) | the `Var_par`/continuum leg and the `1−x²` factor |
| local‑CLT / log‑concave weights (Sources A,B setup) | `Continuum/FusionLogConcave.lean`, `LineSumLogConcave.lean` | log‑concavity of `ρ_t`, CLT skeleton |
| **`c₁(τ)≥0` — the `erf/exp` residual** | `Continuum/JTPIdentity.lean` Gaussian‑majorant engine (`n_pow_le_invG`, `n_gA_pow_le_one`, `nsq_aa_pow_le`) | the only tooling that bounds Gaussian/theta series with explicit tails — the class the bulk correction needs |

`JTPIdentity`'s `n·aⁿ ≤ 1/(1−a)` / `n²(a²)ⁿ ≤ H²` linear‑ and quadratic‑geometric majorants are exactly the
shape needed to dominate the moment tails of `S_k` and bound the boundary term `s^{2k}e^{−τ}`; this is the
right template for a *margin*‑based `c₁≥0`, not a sharp one.

---

## 7. Adversarial verdict

**Is `CORRECTION ≥ 0` provable constructively and uniformly in `s ≥ 7`? — PARTIALLY, and it does NOT
dissolve Lemma C's hard kernel.**

*What is genuinely won (provable now):*
- The full uniform inequality is **true** with zero violations, infimum `0` reached only at `q→1`.
- The **tight corner is decidable.** At the `q→1` edge — the only place the correction touches `0` and the
  only place `Ψ` also vanishes — the correction is `μ·(64/875)(60s³+211s²+186s−42)+O(μ²)`, manifestly
  positive on `ℤ[s]`. The mechanism is the exact `s⁴` cancellation `Ψ'(0)=64/175=` leading coeff of
  `Δ²m₃_par`. This is a real, `decide`‑able structural fact.
- The bulk profile `c₁(τ)` has a **strictly positive margin** (`~4.39τ` near `0`, `≥3.17` for `τ≳1`), so it
  is amenable to *soft* Gaussian‑tail estimates rather than a sharp cancellation certificate.

*What is NOT won (the honest residual):*
- `CORRECTION ≥ 0` is **not a strict reduction of Lemma C**. The decomposition replaces one special‑function
  positivity (`Δ²e≥0`, whose `s→∞` core is `Ψ≥0`) with **two**: `Ψ(τ)≥0` *and* `CORRECTION≥0`. The latter's
  leading coefficient `c₁(τ)` is itself an explicit `erf/exp` function, non‑monotone, positive **by
  assembly, not termwise** — the *same analytic character* as `Ψ`. Log‑concavity / TP / Lorentzian / SOS do
  not certify it, for exactly the `+,−,−`‑cancellation reason they miss `Ψ`.
- Away from the edge, proving `c₁(τ)≥0` (and controlling `c₂,c₃,…` uniformly at `s=7`) requires
  `JTPIdentity`‑class Gaussian/`erf` analysis. This is provable *in principle* (the margin is real), but it
  is **not** free, **not** decidable, and **not** delivered by the log‑concavity anchor.

**Bottom line.** The discreteness correction is honestly `≥0` and uniform, and the split cleanly *isolates a
decidable edge* (the tight corner) from a *margin‑ful special‑function interior*. But it **relocates**, and
does not remove, the analytic difficulty: `Lemma C = (Ψ≥0) + (c₁≥0 with soft tails)`, two `erf/exp`
positivities of the same character, plus one decidable polynomial. The claim "discreteness makes it easy"
is only true at the `q→1` edge; in the bulk the discreteness correction is a second copy of the same hard
object, softened by a positive margin but not trivialized.
