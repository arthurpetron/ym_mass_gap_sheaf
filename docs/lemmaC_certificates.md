# Lemma C banking pass — the three certificates for `Δ²e ≥ 0`, uniform in `s ≥ 7`

**Scope.** `Δ²e(s,μ) = s²·Ψ(τ) + s·c₁(τ) + ρ(s,τ)`, `τ = μs²`, on the conservative superset
domain `τ ∈ (0, 35/8]`, integer `s ≥ 7`. `Ψ ≥ 0` and `c₁ ≥ 0` are already rigorously certified
(`r1_corner_Psi_proof.md`, `r1_corner_c1_proof.md`). This memo banks the remaining three pieces
— **(A)** the reduction of `min_s ρ`, **(B)** `ρ(7,τ) ≥ 0`, **(C)** `c₂(τ) ≥ 0` — into explicit
certificates and delivers an adversarial verdict. All numerics `mpmath` dps 35–40, `sympy` exact.

Objects (exactly as in the codebase scripts):
```
ρ_t(D) ∝ (n²−D²) e^{−μD²},  n=t+2, D≡t(mod 2), |D|≤t;   var_q(t,μ)=Var(D²)
var_par(t)=8t(t−1)(t+4)(t+5)/175;  e(t)=var_par−var_q;  Δ²e=e(s)−2e(s+1)+e(s+2)
Ψ(τ)=continuum limit;  Wexc(s,τ)=Δ²e−s²Ψ = s c₁ + c₂ + c₃/s + …
ρ(s,τ)=Wexc − s c₁ = c₂(τ) + c₃(τ)/s + c₄(τ)/s² + … ,   c₂(τ)=lim_{s→∞} ρ(s,τ)
```

---

## HEADLINE (adversarial): FACT A IS FALSE AS STATED — the endpoint-min reduction fails

The prior memo's **Fact A** — `min_{s≥7} ρ(s,τ) = min(ρ(7,τ), c₂(τ))` (min attained at an
endpoint `s∈{7,∞}`) — **does not hold on the superset domain `τ ∈ (0,35/8]`.** It is contradicted
by an explicit **interior-`s` minimum** that appears for `τ ∈ (τ₁*, τ₂*)`‑adjacent values and
migrates to large `s`. The prior "0 violations" verification (`rb6_02_global.py`) is an artifact of
a **τ‑grid capped at `τ = 1.0`** (`range(200,1001,20)/1000`), which never entered the danger zone.

**Exact numbers (dps 35, `s` up to 20000).** True `c₃(τ)` changes sign **twice**:
```
    c₃ crossovers:  τ₁* = 1.0966181 ,  τ₂* = 3.8645866   (c₃ < 0 strictly between).
```
At the second crossover `c₄ > 0` (`c₄(3.0)=+39.6, c₄(3.85)=+51.3`), so the `x=1/s` stationary point
`x* = −c₃/(2c₄)` is a **local MIN** in `s`, at `s* = −2c₄/c₃`, which `→ +∞` as `τ → τ₂*⁻`. Its depth
below `c₂` is `c₃²/(4c₄)`. Measured dip `min_s ρ − min(ρ(7,τ), c₂(τ))`:

| τ | 3.00 | 3.10 | 3.20 | **3.40** | 3.60 | 3.75 | 3.85 | 3.90 |
|---|---|---|---|---|---|---|---|---|
| argmin `s` | 7 | 8 | 10 | **14** | 26 | 59 | 420 | 20000 |
| dip | 0 | −0.019 | −0.063 | **−0.212** | −0.073 | −0.013 | −2.0e−4 | +2.5e−5 |

The dip reaches **−0.21** (τ≈3.4). So the "min lives at `s∈{7,∞}`" claim is false by a wide margin.
(Within the *reachable* domain `τ ≤ 35s²/(8(s²+6s+7))` the failing points `(14,3.4)`, `(26,3.6)`
are **out of range** — reachable dips are only ≈ −2e−4 at `(420, 3.85)` — but the superset domain,
which the whole one‑variable reduction relies on, genuinely breaks.)

**What survives, and closes Lemma C.** `ρ(s,τ)` is still **≥ 0 everywhere** — the interior dips
bottom out at `+0.30…+0.52`, nowhere near zero. Lemma C needs only `ρ ≥ −6c₁` (indeed `ρ ≥ 0`),
which holds. So **the CONCLUSION of Lemma C is intact**; it is the *proof route* (reduce infinite‑`s`
to two endpoint 1‑D inequalities) that is broken. The honest replacement is a genuine **2‑D**
positivity `ρ(s,τ) ≥ 0`, certified below by a **finite `s`‑window + monotone tail**, not by (B)+(C)
alone.

---

## CERTIFICATE (A) — replacement: direct `ρ(s,τ) ≥ 0` via window + tail

Because `ρ` has an interior minimum for `τ` near `τ₂*`, there is **no clean 1/s‑monotonicity** and
**no two‑row endpoint reduction**. The rigorous, Lean‑consumable certificate splits the `s`‑axis at
an explicit `S₀`:

**(A.window) `s ∈ {7,…,S₀}`.** A finite list of `S₀−6` one‑variable `τ`‑sweeps `ρ(s,·) ≥ 0`, each
of exactly the Fact‑B type (grid + Lipschitz + `τ→0` edge). Every `ρ(s,τ)=c₂+c₃/s+…` here is an
explicit finite‑sum/`erf`/`exp` function of `τ`.

**(A.tail) `s > S₀`.** For each `τ`, the tail is monotone in `s` beyond the (at most one) migrating
vertex, so
```
    inf_{s>S₀} ρ(s,τ) = min( c₂(τ),  m(τ),  ρ(S₀+1,τ) ),
    m(τ) := c₂(τ) − c₃(τ)²/(4c₄(τ))   used only when  s*=−2c₄/c₃ > S₀ and c₄>0.
```
with the explicit tail‑remainder bound `|ρ(s,τ) − c₂(τ)| ≤ T₁/s`, `T₁ = sup_{s≥S₀} s|ρ−c₂|`.

**Certified directly (the object this replaces reduces to): `cert_full.py`, `s` to 6000, `τ∈(0,35/8]`
step 0.01, dps 35:**
```
    min_{s≥7, τ∈(0,35/8]} ρ(s,τ) = +0.153990  at (s,τ)=(6000, 0.01),   0 violations (ρ < −1e−8).
    infimum = 0, approached only at the corner (τ→0, s→∞) where ρ→c₂(τ)~15.43τ→0⁺.
```
This is the honest closing fact: `ρ ≥ 0` on the entire superset domain, hence `ρ ≥ −6c₁` and
`Δ²e = s²Ψ + (s−6)c₁ + (ρ+6c₁) ≥ 0` for `s ≥ 7`. The window+tail split (`cert_tail.py`, `S₀=60`,
τ step 0.005) packages this same positivity into a Lean‑consumable finite list, with explicit
constants:
```
    WINDOW  s∈{7,…,60}: 54 Fact‑B‑type sweeps,   min ρ = 0.156241  at (s,τ)=(60, 0.01).
    TAIL    s>60:  inf ρ = min(c₂, m, ρ(61,·)) = 0.153967  at τ=0.01,
            explicit remainder  |ρ(s,τ) − c₂(τ)| ≤ T₁/s,  T₁ = sup_{s≥60} s|ρ−c₂| = 16.4947.
    ⇒ ρ(s,τ) ≥ 0.153967 > 0  on all s≥7, τ∈(0,35/8]  (grid floor; true infimum 0 at τ→0).
```

Honest status: (A) is **NOT** reducible to the clean 1‑variable rigor of `Ψ/c₁`. It is a genuine
2‑D certificate = (`S₀−6`) one‑variable sweeps + one monotone‑tail bound. It closes, but it is
structurally heavier than a single 1‑D sweep, and the `S₀` window must exceed the largest reachable
migrating‑vertex row.

---

## CERTIFICATE (B) — `ρ(7,τ) ≥ 0` on `τ ∈ (0, 35/8]`   [CLEAN, Ψ/c₁‑class]

`ρ(7,τ) = Δ²e(7, τ/49) − 49·Ψ(τ) − 7·c₁(τ)` is a fully explicit one‑variable function.

* **Edge `(0,h]`, exact `τ→0` slope (sympy):**
  ```
      ρ(7,τ) = (64/875)(γ₂ + γ₃/7 + γ₄/49)·τ + O(τ²),  (γ₂,γ₃,γ₄)=(211,186,−42)
             = (64/875)(11599/49)·τ = 106048/6125 · τ = 17.313959…·τ  > 0.
  ```
  numeric `ρ(7,τ)/τ = 17.3067 (τ=0.01), 17.3128 (τ=0.002)` → `106048/6125`. Positive slope ⇒
  `ρ(7,τ) > 0` on `(0,h]`.
* **Bulk `[h, 35/8]`, grid + Lipschitz (dps 35):**
  ```
      h = 1/400,  grid min ρ(7,τ) = 0.043281 (at τ=0.0025),
      Lipschitz L = 17.309 (dominated by the τ→0 slope),  guard = L·h/2 = 0.021645,
      ⇒ ρ(7,τ) ≥ 0.043281 − 0.021645 = 0.021635 > 0.
  ```
**Verdict (B): CERTIFIED to the same rigor as `Ψ≥0`/`c₁≥0`** — 1‑D grid + Lipschitz guard + exact
rational `τ→0` slope `106048/6125`. Margin 0.0216 ≫ guard.

---

## CERTIFICATE (C) — `c₂(τ) ≥ 0` on `τ ∈ (0, 35/8]`   [CLEAN, even simpler than Ψ/c₁]

Exact rational core (sympy, via `sp.limit` of `Δ²e^core/s²`):
```
    c₂_core(τ) = 8·(768τ⁶−2304τ⁵+2880τ⁴+108080τ³+248220τ²+65856τ+1387) / (25·(2τ−1)⁶).
```
**Manifestly‑positive rational majorant (the analogue of Ψ's `48/(2τ−1)⁴`):** the numerator is
`> 0` for every `τ > 0`, because
```
    768τ⁶−2304τ⁵+2880τ⁴ = τ⁴(768τ²−2304τ+2880),  disc(768τ²−2304τ+2880) = −3538944 < 0  (⇒ >0),
    108080τ³+248220τ²+65856τ+1387  has all‑positive coefficients (⇒ >0),
```
and `(2τ−1)⁶ ≥ 0`. So `c₂_core(τ) > 0` for all `τ ≠ ½`. (As with `c₁`, the core is a **tail tool**;
on the bulk `δc₂ = c₂ − c₂_core = O(e^{−τ})` cancels the `τ=½` pole, so bulk positivity is carried
by the direct sweep. **But the domain caps at `τ = 35/8 < 5`, so the tail region `τ≥5` is never
entered — no exponential‑tail lemma is needed at all.**)

* **Edge `(0,½]`, `τ→0` slope:** `c₂(τ) = (64/875)·211·τ + O(τ²) = 13504/875·τ = 15.4331·τ > 0`;
  numeric `c₂/τ → 15.43`. Grid min on `(0,½]` = `0.03085 > 0`.
* **Bulk `[½, 35/8]`, grid + Lipschitz (dps 35):**
  ```
      h = 1/500,  grid min c₂ = 0.291833 (at τ=4.004),
      Lipschitz L = 8.954,  guard = L·h/2 = 0.008954,
      ⇒ c₂(τ) ≥ 0.291833 − 0.008954 = 0.282879 > 0.
  ```
**Verdict (C): CERTIFIED, cleaner than `Ψ/c₁`** — the domain `τ<5` removes the exponential tail;
only the edge slope `13504/875` and one bounded `[½,35/8]` sweep (margin 0.283 ≫ guard 0.009)
remain. The manifestly‑positive rational core is a bonus (it alone gives `c₂_core>0`, though not the
bulk `c₂`).

---

## NUMERICAL VERIFICATION TABLE (dps 35–40; sympy exact)

| check | range / method | result |
|---|---|---|
| exact cores `Ψ,c₁,c₂,c₃,c₄` | `sp.limit` of `Δ²e^core/s²` | ✔ rational, `(2τ−1)^k` denom |
| `c₂_core` anchor `(∞)` | sympy | `96/25` ✔ |
| `c₂_core` numerator `> 0` ∀τ>0 | discriminant + positive coeffs | ✔ manifest majorant |
| `c₃_core = −54720 τ(2τ+1)(4τ²+12τ+1)/(2τ−1)⁷` | sympy | flips only at pole `τ=½` |
| **TRUE `c₃` crossovers** | dps 35 bisection | **`τ₁*=1.0966181, τ₂*=3.8645866`** |
| **interior‑`s` MIN (Fact A counterexample)** | `s` to 20000, `τ∈[3.0,3.9]` | **dip −0.212 @ τ=3.4, s=14** |
| **(B) `ρ(7,τ)` grid+guard** | h=1/400, dps 35 | **≥ 0.02164 > 0** |
| (B) `τ→0` slope | sympy | `106048/6125 = 17.31396` |
| **(C) `c₂` bulk `[½,35/8]`** | h=1/500, dps 35 | **≥ 0.28288 > 0** |
| (C) edge `(0,½]` slope | sympy | `13504/875 = 15.4331` |
| **(A) direct `min_{s≥7} ρ`** | `cert_full`, s→6000, τ→35/8 | **+0.153990 @ (6000, 0.01); 0 viol** |
| (A) window `s∈[7,60]` | `cert_tail`, τ step 0.005 | min +0.156241 @ (60, 0.01) |
| (A) tail `s>60` (+`T₁=16.49/s`) | `cert_tail`, ladder+`m(τ)` | inf +0.153967 @ τ=0.01 |
| **GLOBAL `ρ(s,τ) ≥ 0`** SUPERSET | `s` to 6000, `τ∈(0,35/8]` step 0.01 | **min +0.15399 @ (6000, 0.01); 0 viol** |
| GLOBAL `ρ` REACHABLE `τ≤35s²/8E` | same | **min +0.15399 @ (6000, 0.01); 0 viol** |
| infimum of `ρ` (corner `τ→0, s→∞`) | analytic + dps | `→ 0⁺` (approached from above) |

Scripts (`/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `cert_cores.py` (exact cores + positivity),
`cert_cross.py` (`c₃` crossovers), `cert_dip.py` (Fact‑A counterexample), `cert_fast.py` (B/C/verify),
`cert_full.py` (global 2‑D min), `cert_tail.py` (window+tail salvage).

---

## VERDICT

* **(B) `ρ(7,τ) ≥ 0`: CERTIFIED** to the same rigor as `Ψ≥0`/`c₁≥0` (grid + Lipschitz + exact
  rational `τ→0` slope `106048/6125`). Clean.
* **(C) `c₂(τ) ≥ 0`: CERTIFIED**, and *cleaner* than `Ψ/c₁` — the domain `τ<5` drops the exponential
  tail; a manifestly‑positive rational core `c₂_core` exists. Clean.
* **(A) Fact‑A monotonicity / endpoint‑min: NOT clean — FALSE as stated.** The sign of `c₃` flips
  **twice** (`τ₁*=1.097, τ₂*=3.865`), and at `τ₂*` the curvature `c₄>0` produces a genuine
  **interior‑`s` minimum** migrating to `s→∞`, so `min_s ρ ≠ min(ρ(7),c₂)` (fails by up to −0.21 on
  the superset). The prior "0 violations" was a τ‑grid‑capped‑at‑1.0 artifact.

**Is Lemma C a fully‑certified finite list via (A)+(B)+(C)?** **No — not via the endpoint reduction.**
(B) and (C) certify the two *profile* functions cleanly, but they are **insufficient** on their own
because the true minimum of `ρ` over `s` is *interior* in the window `τ∈(3.05,3.86)`. Lemma C still
closes — via `ρ(s,τ) ≥ 0` **directly** (2‑D), which is certified by the finite‑window `[7,S₀]` (a
finite list of Fact‑B‑type sweeps) **plus** a monotone‑tail bound `s>S₀` — but this is a genuinely
2‑D certificate, structurally heavier than "two 1‑D endpoint inequalities." The clean part of the
banking pass is (B)+(C); the honest residual is that closing the `s`‑direction requires the window+
tail 2‑D argument, not the (elegant but false) endpoint‑min reduction.
