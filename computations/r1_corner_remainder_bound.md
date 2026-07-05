# The terminating remainder bound for Lemma C — explicit `B(τ)`, `S₀`, and an honest verdict

**Target (the terminating move).** Prove, uniformly in integer `s ≥ 7` and all `μ ∈ (0, 35/(8E)]`,
`E = s²+6s+7`, that `Δ²e(s,q) ≥ 0`, where `e(t)=Var_par(t)−Var_q(t)`,
`Var_q(t)=Var_{ρ_t}(D²)`, `ρ_t(D)∝(n²−D²)q^{D²}` (`n=t+2`, `D≡t (2)`, `|D|≤t`),
`Var_par(t)=8t(t−1)(t+4)(t+5)/175`, `q=e^{−μ}`. With `τ:=μs²`, the established split is

```
    Δ²e(s,q) = s²·Ψ(τ) + s·c₁(τ) + ρ(s,τ),     ρ(s,τ) := Δ²e − s²Ψ − s c₁,          (★)
```

`Ψ(τ) ≥ 0` **PROVED** (`Psi_proof.md`) and `c₁(τ) ≥ 0` **PROVED** (`c1_proof.md`). This memo
settles the **remainder `ρ`** and the termination.

**Verdict up front (adversarial, honest).**

1. **The route TERMINATES.** `S₀ := sup_τ B(τ)/c₁(τ)` is finite. With the explicit majorant
   `B(τ)=4·c₁(τ)` we get `S₀ = 4 < 7`, so **no finite `s`-sweep is even needed**: for every valid
   `s ≥ 7`,
   ```
        Δ²e = s²Ψ + s c₁ + ρ  ≥  s c₁ − 4 c₁  =  (s−4) c₁  ≥  3 c₁  ≥  0.
   ```
2. **BUT the prompt's specific mechanism does NOT work on this domain.** The anticipated
   "rational‑core Euler–Maclaurin remainder `B(τ)`, positivity `48/(2τ−1)⁴`‑style" is *provably
   unavailable* here: the Gaussian‑moment core has a **pole inside the domain**, and the naive
   `μ`‑Taylor remainder has **no cancellation** and diverges. The working bound `ρ ≥ −4c₁` is an
   **erf/exp‑class positivity of the same character as `Ψ` and `c₁`** — it introduces **no new hard
   kernel**, but it is **not** a rational certificate. This is the honest correction to the prompt's
   EM/Gaussian‑core plan.

Every number below is `mpmath` dps 40 (sums), dps 60 (extrapolations), or exact `sympy`.

---

## 1. The domain is *small‑μ*, and `τ` is bounded — the crucial simplification

`μ ≤ 35/(8E)`, `E=s²+6s+7`, gives `τ = μs² ≤ 35s²/(8(s²+6s+7)) ≤ 35/8 = 4.375` for every `s`, and
`μ ≤ 35/(8·98)=0.0446` at `s=7` (smaller for larger `s`), i.e. `q ≥ 0.956`. So:

* **`τ ∈ (0, 35/8]` always** — we never enter the large‑`τ` "tail region" (`τ ≥ 5`) on which the
  `c1_proof`/`Psi_proof` rational cores were built. The critical `τ` (see §4) is `τ⋆≈0.11`,
  reachable already at `s=7` (whose cap is `τ≤35/16=2.19`), so the **`s`‑dependent** domain and the
  conservative superset `τ∈(0,35/8]` give the **identical** `S₀` (verified).

---

## 2. Adversarial: why the rational‑core remainder route FAILS here (two dead ends)

### 2a. The Gaussian‑moment core has a POLE inside the domain
The `c1_proof` core replaces the discrete sum by the Gaussian moment
`S_k^core = ½[(t+2)²G_k − G_{k+1}]`, `G_m=√(π/μ)(2m−1)!!/(2μ)^m`. Then
`Var_q^core = 2A²(β²−6Aβ+3A²)/(β−A)²`, `A=1/(2μ)=s²/(2τ)`, `β=(t+2)²` (sympy‑verified: `diff=0`).
Its denominator `β−A = (t+2)² − s²/(2τ)` **vanishes at**
```
    τ_pole(s) = s²/(2(s+2)²) ∈ [0.302, 0.5)   for s ≥ 7   (→ ½ as s→∞).
```
This pole sits **inside `(0, 35/8]`**. Correspondingly the exact core coefficients (rebuilt here,
matching `c1_proof` ★ exactly) carry `(2τ−1)^{k+3}` denominators that blow up at `τ=½`:
```
    Ψ_core = 48(32τ⁴−64τ³+48τ²+334τ+177)/(175(2τ−1)⁴),
    c₁_core = 288(64τ⁵−…−177)/(175(2τ−1)⁵),
    c₂_core = 8(768τ⁶+…+1387)/(25(2τ−1)⁶),   c₃_core = −54720τ(2τ+1)(4τ²+12τ+1)/(2τ−1)⁷.
```
Moreover `c₁_core(τ→0⁺)=50976/175=291.3 ≠ 0` and `c₂_core(0⁺)=11096/25=443.8 ≠ 0`, whereas the
**true** `c₁,c₂ → 0` linearly. The core is a *large‑τ* object; on `(0,35/8]` it is singular and its
`1/s` coefficients bear no resemblance to the truth. **The rational core cannot be used to bound the
remainder on this domain.**

### 2b. The naive `μ`‑Taylor (Lagrange) remainder has NO cancellation
`F_s(μ):=Δ²e(s,μ)` is entire in `μ`, `F_s(0)=0` (since `e(t,0)≡0`), `F_s'(0)=a₁(s)=
(64/875)(60s³+211s²+186s−42)>0`. Taylor–Lagrange `F_s(μ)=a₁μ+½F_s''(ξ)μ²` gives
`F_s≥0` on `(0,μ_max]` iff `μ_max ≤ 2a₁/max_{[0,μ_max]}|F_s''|`. Measured:

| s | 7 | 20 | 50 | 120 | 200 |
|---|---|---|---|---|---|
| `μ_max/(2a₁/max|F''|)` | 1.11 | 2.02 | 4.12 | 9.05 | 14.68 |

The ratio **grows without bound** in `s` (`max|F''| ~ s⁶` with no cancellation; the `s⁴`‑cancellation
that saves `a₁` does *not* recur in `F''`). The 3rd‑order variant is worse (`a₂(s)<0`). **The raw
`μ`‑Taylor does not terminate.** The cancellation that makes the true remainder bounded lives in the
**continuum‑limit (`1/s`) structure**, entangled with the erf/exp `Ψ, c₁` — not extractable as a
rational core (2a) nor visible in the raw `μ`‑derivatives (2b).

---

## 3. The correct remainder object `ρ` and its two structural facts

Do **not** sum the `1/s` tower `ρ = c₂ + c₃/s + c₄/s² + …` (its higher coefficients grow and the
series need not converge at `s=7`); bound `ρ(s,τ)` **directly** as a function. Two facts pin it down.

### 3a. Every `c_k(τ)=O(τ)` as `τ→0` — so `B(τ)=O(τ)`, matching `c₁~(768/175)τ`
The edge expansion (`discreteness_correction.md` §3a, from the exact `s⁴`‑cancellation
`Ψ'(0)=64/175=` lead coeff of `Δ²m₃_par`):
```
    Δ²e = μ·(64/875)(60s³+211s²+186s−42) + O(μ²),   μ=τ/s²
  ⇒  R(s,τ)=Δ²e/s²−Ψ = (64/875)τ(60/s + 211/s² + 186/s³ − 42/s⁴) + O(τ²/s⁶),
  ⇒  c_k(τ) = (64/875)·γ_k·τ + O(τ²),   (γ₁,γ₂,γ₃,γ₄) = (60, 211, 186, −42).
```
Verified at `τ=0.01` (dps 60): `c_k/τ = 4.380, 15.40, 13.69, −2.36` vs edge
`(64/875)γ_k = 4.389, 15.43, 13.60, −3.07`; `c₅,c₆ = O(τ²)` (an order smaller). Hence **`ρ(s,τ)/τ`
is bounded as `τ→0`**, so any valid `B(τ) ≥ sup_s|ρ|` is `O(τ)`, and `B/c₁ ~ (const)/(768/175)`
stays **bounded at the dangerous `τ→0` corner** (measured limit `3.946`). This is the crux the
prompt flagged, and it holds.

### 3b. `ρ ≥ 0` and `c₂ ≥ 0` on the whole domain (sign structure)
`ρ = c₂ + c₃/s + …` with `c₂(τ) ≥ 0` on `(0,35/8]` (Richardson min `0.154`), and directly
`ρ(s,τ) ≥ 0.0155 > 0` for all `s=7…1000` (§5). So the *truth* is `ρ ≥ 0`; the bound `ρ ≥ −4c₁`
below is a comfortable, robust relaxation.

---

## 4. The explicit `B(τ)`, and `sup_τ B/c₁ = S₀`

Define `B_emp(τ) := sup_{7≤s≤1000}|ρ(s,τ)|` (attained; `ρ→c₂(τ)` as `s→∞`, continuous). Dense
scan (dps 40, `τ` step `≤5·10⁻⁴` near 0):

| τ | 0.0005 | 0.02 | 0.07 | **0.11 (max)** | 0.19 | 0.5 | 1 | 2 | 3 | 4.375 |
|---|---|---|---|---|---|---|---|---|---|---|
| `c₁(τ)` | .0022 | .087 | .303 | .493 | .800 | 1.930 | 3.240 | 4.233 | 4.076 | 3.550 |
| `B_emp` | .0087 | .346 | 1.204 | 1.961 | 3.170 | 7.056 | 8.872 | 5.938 | 1.630 | 1.718 |
| `B_emp/c₁` | 3.946 | 3.957 | 3.976 | **3.9806** | 3.965 | 3.656 | 2.739 | 1.403 | 0.400 | 0.484 |

```
    S₀ = sup_{τ∈(0,35/8]} B_emp(τ)/c₁(τ) = 3.9806   (interior max at τ⋆≈0.11; →3.946 as τ→0).
```

**Explicit majorant (clean choice).** Since `B_emp(τ)/c₁(τ) ≤ 3.9806 < 4` everywhere,
```
    B(τ) := 4·c₁(τ)     satisfies  |ρ(s,τ)| ≤ B(τ)   and   sup_τ B/c₁ = S₀ = 4 < 7.
```
(For a 3 % headroom on the constant use `B=4.1 c₁`, `S₀=4.1`; either is `< 7`.) A purely elementary
`τ`‑envelope (`a τ e^{−τ}+b τ`) can also dominate `B_emp`, but `4c₁` is the tightest simple form and
is the natural Lean object because `c₁` is already in the development.

**Termination.** `S₀ = 4 < 7 ≤ s` for every valid `s`, hence `(s−4)≥3>0` and (★) gives
`Δ²e ≥ (s−4)c₁ ≥ 3c₁ ≥ 0`. **The finite sweep is empty.**

**Fallback (if only a cruder, `S₀'>7`, bound is used).** For each fixed `s`, `Δ²e(s,q)=Num(q)/Den(q)`
with `Den(q)=∏(S₀(s+i))² > 0`, `Num∈ℤ[q]` (for `s=7`, `deg Num=384`), `Num(1)=0`
(since `e(t,1)≡0`), and `Num(q)/(q−1)` has **no root in `[q_min,1)`** (`q_min=e^{−35/(8E)}`). So
`Δ²e(s,q) ≥ 0` on the compact `q`‑interval is a **Sturm/Bernstein‑decidable** univariate positivity,
one certificate per `s` — the standard finite sweep `s=7…⌈S₀'⌉−1`. This makes the route terminate
*even without* the sharp constant `4`, at the cost of a finite (still trivial) sweep.

---

## 5. Numerical verification log (dps 40; extrapolations dps 60; sympy exact)

| check | range / method | result |
|---|---|---|
| identity (★) `Δ²e = s²Ψ + s c₁ + ρ` | definition | ✔ (ρ computed as the residual) |
| **`R = Δ²e/s² − Ψ ≥ 0`** | `s=7…500`, `τ∈(0,35/8]` dense | **min `+8.84·10⁻⁶`; 0 violations** |
| **`ρ = s²R − s c₁ ≥ 0`** | `s=7…1000`, `τ` dense | **min `+0.01546`; 0 violations** |
| `B_emp/c₁ ≤ 3.9806` (`S₀`) | `s≤1000`, dense `τ`, valid & unif domains | **sup `3.9806` @ `τ≈0.11`; →`3.946` @ `τ→0`** |
| valid vs unif domain give same `S₀` | `τ≤35s²/(8E)` vs `τ≤35/8` | ✔ identical (`3.9806`) |
| `B(τ)=4c₁` dominates `B_emp` | dense `τ` | ✔ (`4 > 3.9806`) |
| `c_k(τ)=(64/875)γ_k τ+O(τ²)`, `k≤4` | `τ=0.01`, dps 60 | ✔ `4.38,15.40,13.69,−2.36` vs edge |
| `c₂(τ) ≥ 0` on domain | Richardson `s=300…1200` | ✔ min `0.154` |
| Gaussian core pole `τ=s²/(2(s+2)²)∈[.30,.5)` | sympy exact | ✔ inside domain (route 2a dead) |
| `μ`‑Taylor ratio `↑` in `s` (`1.11→14.7`) | dps 40, `s≤200` | ✔ diverges (route 2b dead) |
| `Δ²e(7,q)=Num/Den`, `Num(1)=0`, `Den>0` | sympy exact, `deg=384` | ✔ Sturm‑decidable per `s` |

Scripts (`/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `rb_01_empirical.py` (S₀, ρ scan),
`rb_02_core.py` (exact Gaussian core + pole), `rb_03_mu_route.py` (μ‑Taylor dead end),
`rb_04_true_cont.py` (true‑continuum split), `rb_05_tower.py` (c_k, edge scaling),
`rb_06_verify.py` / `rb_07_final.py` (definitive R≥0, ρ≥0, S₀, majorant, decidability).

---

## 6. Complete finite lemma list for the Lean formalization

```
  Lemma C:  Δ²e(s,q) ≥ 0   for all integer s ≥ 7, μ∈(0,35/(8E)], E=s²+6s+7.
  ─────────────────────────────────────────────────────────────────────────
  L1 (split, identity):  Δ²e = s²·Ψ(τ) + s·c₁(τ) + ρ(s,τ),  τ=μs²,  ρ := Δ²e−s²Ψ−s c₁.   [def]
  L2 (Ψ≥0):              Ψ(τ) ≥ 0 for τ≥0.                                    [PROVED, Psi_proof]
  L3 (c₁≥0):             c₁(τ) ≥ 0 for τ≥0.                                    [PROVED, c1_proof]
  L4 (domain):           μ≤35/(8E) ⟹ τ=μs² ≤ 35/8.                            [arithmetic, decide]
  L5 (REMAINDER BOUND):  |ρ(s,τ)| ≤ 4·c₁(τ)   for s≥7, τ∈(0,35/8].            [erf/exp — THE residual]
        supporting:  ρ(s,τ)=Σ_{k≥2} c_k/s^{k−2};  c_k(τ)=(64/875)γ_k τ+O(τ²)  ⟹ B=O(τ),
                     B/c₁ bounded at τ→0 (sup over domain = 3.9806 < 4).
  L6 (termination):      from L1–L5 with s≥7:
                         Δ²e = s²Ψ + s c₁ + ρ ≥ s c₁ − 4 c₁ = (s−4) c₁ ≥ 3 c₁ ≥ 0.   [ring, s≥7]
  ──  (S₀=4<7 ⟹ the finite sweep is EMPTY.) ──
  L5′ (fallback, only if a cruder rational bound forces S₀'>7):
        finite sweep s=7…⌈S₀'⌉−1:  Num_s(q)/(q−1) has no root on [q_min,1),  Den_s>0
        ⟹ Δ²e(s,q)≥0.                                                        [Sturm/Bernstein, decide]
```

`L5` may be stated in the stronger true form `ρ(s,τ) ≥ 0` (also erf/exp, also verified,
min `+0.0155`); `|ρ|≤4c₁` is preferred because it yields the explicit finite cutoff `S₀=4`.

---

## 7. Honest verdict — does this close Lemma C end‑to‑end?

**YES, modulo one erf/exp residual of the *same class already accepted* for `Ψ` and `c₁` — with
no new hard kernel, and the route provably TERMINATES.**

*What is won.*
- **Termination is unconditional and sweep‑free.** `S₀ = sup B/c₁ = 3.9806 < 4 < 7`. The dangerous
  `τ→0` corner is safe because *every* `c_k(τ)=O(τ)` (edge expansion), so `B(τ)=O(τ)` tracks
  `c₁(τ)=O(τ)`; the ratio has a bounded interior max at `τ≈0.11`, not a blow‑up. Since `s≥7>S₀`,
  `Δ²e ≥ (s−4)c₁ ≥ 0` with **no finite `s`‑sweep**.
- The finite‑`s` fallback (if a cruder bound is used) is a **genuinely decidable** per‑`s`
  rational‑in‑`q` positivity (Sturm), so termination is robust to the exact constant.
- `Ψ ≥ 0` and `c₁ ≥ 0` are already proved; the *only* new input is `L5`.

*What is NOT won (the honest residual — flagged, not overclaimed).*
- **`L5` (`|ρ| ≤ 4c₁`) is not reduced to a rational certificate.** The prompt's EM/Gaussian‑core
  plan is *provably inapplicable on `(0,35/8]`*: the Gaussian‑moment core has a pole in the domain
  (§2a) and the raw `μ`‑Taylor has no cancellation (§2b). The remainder `ρ` is an **erf/exp function
  positive by assembly** — the identical analytic character as `Ψ` and `c₁`, and it succumbs to the
  same tooling (incomplete‑Γ envelopes / `JTPIdentity` Gaussian‑geometric majorants), with a
  comfortable margin (constant `4` vs measured `3.98`). It is provable *in principle by those means*,
  but it is **not free, not rational, not `decide`‑able**.
- So the terminating move **relocates** the analytic difficulty one final time:
  `Lemma C = [Ψ≥0] ∧ [c₁≥0] ∧ [|ρ|≤4c₁]`, three erf/exp positivities of one character, plus the
  decidable domain arithmetic. It does **not** dissolve the last one into algebra — but it *bounds*
  it (explicit `S₀=4`), *scales* it correctly at the tight corner (`O(τ)`), and *removes the
  `s`‑sweep entirely*. That is a clean, honest termination, not a rational closure.

**Bottom line.** The remainder route **terminates end‑to‑end** with an explicit, `τ→0`‑safe bound
`B(τ)=4c₁(τ)`, `S₀=4<7`, empty finite sweep, and zero numerical violations across `s=7…1000`,
`τ∈(0,35/8]`. The single remaining Lean obligation `L5: |ρ| ≤ 4c₁` is an erf/exp bound of the same
difficulty class as the two already‑discharged pieces — no new kernel, but not a rational
Positivstellensatz. The prompt's optimistic "rational‑core EM remainder" is, on this specific
bounded‑`τ` domain, **impossible** (pole) — the honest correction — while the *termination itself* is
real and clean.
