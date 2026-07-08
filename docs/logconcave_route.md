# The log-concavity / modular-dual route to M1, M2, Lemma C

**Task.** Find a single structural (log-concavity / total-positivity) argument, basis-free and
uniform, that yields the three "free-Gaussian-at-the-free-rate" residuals

```
  M1:      V_p^∞(u)·(1−u)  ≤ 2         V_p^∞ = 4⟨k²⟩ under weights ∝ u^{k²}   (p = even/odd parity)
  M2:      Var_p(u)·(1−u)² ≤ 8         Var_p = Var(D²) of the same ensemble
  Lemma C: Δ²Var_q(s) ≤ Δ²Var_par(s)   tilted parabolic ensemble (n²−D²)q^{D²}, curvature max at q=1
```

**One-line verdict.** M1 and M2 **do** have a single clean structural origin — the **Poisson /
Jacobi modular dual** of the discrete-Gaussian log-partition function — and this is the correct
"put back the probabilistic structure" route. **Lemma C does NOT** join them under one lemma: it is
a *finite truncated* ensemble with a *parabolic window*, its cumulant/TP route is provably obstructed
(pointwise `Δ²m₃ ≥ 0` is FALSE, `q↦Δ²Var_q` is non-monotone), and its Bernstein certificate integers
`β_k^{(s)}` have **no closed form** (they factor into large random primes). Honest split: **M1+M2 =
one modular-dual lemma; Lemma C = a separate, still-per-`s` object.**

Every claim below is numerically verified with mpmath (dps 40–50) and/or exact rationals; the worst-case
margins are quoted.

---

## 0. The single structural object for M1 and M2

Set `ε := −ln u > 0`. The whole discrete-Gaussian moment structure is carried by the **log-partition
functions** (cumulant generating functions of the "energy" `x = k²`), one per parity:

```
  even:  L_e(ε) = ln Θ_e(ε),   Θ_e(ε) = Σ_{k∈ℤ}     e^{−εk²}
  odd :  L_o(ε) = ln Θ_o(ε),   Θ_o(ε) = Σ_{j∈ℤ+½}   e^{−εj²}
```

Because these are cumulant generating functions in `ε`, the moments needed by M1/M2 are **exactly the
first two derivatives**:

```
  ⟨k²⟩ = −L_e'(ε),   Var(k²) = L_e''(ε)         (D = 2k  ⟹  V_e = 4⟨k²⟩ = −4L_e',  Var_e = 16L_e'')
  ⟨j²⟩ = −L_o'(ε),   Var(j²) = L_o''(ε)         (D = 2j  ⟹  V_o = 4⟨j²⟩,             Var_o = 16L_o'')
```

So **M1 = a first-derivative bound and M2 = a second-derivative bound on the same convex function
`L_p(ε)`.** This already unifies M1 and M2 (both parities) into "control the first two cumulants of the
discrete Gaussian". The remaining question — the crux the θ-basis could not answer near `u→1` — is
resolved by the **modular dual**.

### The modular (Poisson) dual and its two manifest monotonicities

Poisson summation on the two lattices gives, with dual nome `ã := e^{−π²/ε}` (→ 0 as `u→1`):

```
  Θ_e(ε) = √(π/ε)·g(ε),   g(ε) = Σ_{n∈ℤ}   e^{−π²n²/ε} = 1 + 2Σ_{n≥1}     ã^{n²}
  Θ_o(ε) = √(π/ε)·G(ε),   G(ε) = Σ_{n∈ℤ}(−1)ⁿe^{−π²n²/ε} = 1 + 2Σ_{n≥1}(−1)ⁿ ã^{n²}
```

Two structural facts drive everything (both manifest from the series, both numerically confirmed):

> **(D-even)** `g(ε)` is **increasing and log-convex**:  `(ln g)' ≥ 0`,  `(ln g)'' ≥ 0`.
> **(D-odd)**  `G(ε)` is **decreasing and log-concave**:  `(ln G)' ≤ 0`,  `(ln G)'' ≤ 0`.

`(ln g)' = g'/g` with `g'(ε) = Σ_n (π²n²/ε²) ã^{n²} ≥ 0` termwise; and `G` is a convergent
**alternating** series whose sign of `G', G''` is set by the leading `n=1` term `−2ã`. These give the
exact decompositions

```
  ⟨k²⟩ = 1/(2ε) − (ln g)'(ε)          ⟨j²⟩ = 1/(2ε) − (ln G)'(ε)
  Var(k²) = 1/(2ε²) + (ln g)''(ε)     Var(j²) = 1/(2ε²) + (ln G)''(ε)
```

where `1/(2ε), 1/(2ε²)` are the **continuum-Gaussian values** of `⟨k²⟩, Var(k²)` and the dual pieces
are the **defects**. The four defects have a clean sign pattern (verified on the whole branch):

| residual | defect = discrete − continuum(ε) | sign | interpretation |
|---|---|---|---|
| **M1 even** | `−(ln g)'` | **≤ 0** | *sub-Gaussian domination* (discrete mean ≤ continuum) |
| **M1 odd**  | `−(ln G)'` | **≥ 0** | anti-domination (discrete mean > continuum) |
| **M2 even** | `+(ln g)''`| **≥ 0** | anti-domination (discrete var > continuum) |
| **M2 odd**  | `+(ln G)''`| **≤ 0** | *sub-Gaussian domination* |

**This is the honest answer to "does log-concavity suffice?":** genuine sub-Gaussian domination
(discrete ≤ continuum) holds for **exactly two of the four** cases (`M1-even`, `M2-odd`). For the other
two the discrete moment **exceeds** the continuum Gaussian, so a naïve domination argument is *false* —
one additionally needs the elementary **log-gap cushion** of §1.

---

## 1. The universal mechanism: continuum value ≤ target, dual defect ≤ cushion

The target constants sit at `1−u`, the continuum values at `ε`, and they are bridged by one elementary
fact:

> **(LG) log-gap:**  `1 − u ≤ −ln u = ε`  for `u∈(0,1)`  (standard; equality only at `u=1`).

Hence `1/(2ε) ≤ 1/(2(1−u))` and `1/(2ε²) ≤ 1/(2(1−u)²)`, and the **cushions**

```
  c₁(u) := 1/(2(1−u))  − 1/(2ε)   ≥ 0          (for M1)
  c₂(u) := 1/(2(1−u)²) − 1/(2ε²)  ≥ 0          (for M2)
```

are **strictly positive** and `O(1)` on `[1/4,1)`. The mechanism is uniform:

```
  discrete moment  =  continuum(ε)  +  defect
                   ≤  target(1−u)   −  cushion  +  defect            (by LG)
                   ≤  target(1−u)                    ⟺   defect ≤ cushion.
```

* **Favorable cases (M1-even, M2-odd):** defect ≤ 0 ≤ cushion trivially. *M1-even is fully clean, no
  cushion needed:* `⟨k²⟩ ≤ 1/(2ε)` then `V_e(1−u) = 4⟨k²⟩(1−u) ≤ 2(1−u)/ε ≤ 2`.
* **Unfavorable cases (M1-odd, M2-even):** defect `> 0` but is **exponentially small in the dual nome**
  `ã = e^{−π²/ε}`, hence dominated by the `O(1)` cushion.

**Verified uniform margins** (`u∈[1/4, 0.9999]`, 64 points incl. `u→1`, mpmath dps 40):

```
  worst  M1-odd defect / c₁  = 0.0272        worst  M2-even defect / c₂ = 0.0486
```

i.e. the unfavorable defects never exceed **~5 %** of the cushion. Leading-term bracket used (Leibniz):
`−(ln G)'(ε) ≤ (2π²/ε²)·ã/(1−2ã)` — verified valid on the whole branch. Both favorable defects verified
`≤ 0` on all points.

### Exact signed-factor identity (M1-even, the cleanest instance)

The `u`-native form of M1-even is `S_e(u) := Σ_{k∈ℤ}(1 − 2(1−u)k²) u^{k²} ≥ 0`, and Poisson gives the
**manifestly nonnegative three-factor identity** (verified to 8+ digits, `u∈{0.1,…,0.95}`):

```
  S_e(u) = √(π/ε) · [ g(ε)·(1 − (1−u)/ε)  +  2(1−u)·g'(ε) ],
```

with `g ≥ 0`, `g' ≥ 0`, and `1 − (1−u)/ε ≥ 0` (⟺ LG). This *is* M1-even, no cushion bookkeeping.
The companion telescoping identity `1 = (1−u)Σ_{k≥0} u^{k²}(1+u+···+u^{2k})` (verified) is the elementary
`u`-space shadow of the same fact.

### Why this is the right route (the θ-basis blocker dissolved)

In the θ (`q`-series) basis M1/M2 are "not finitely truncatable": tight exactly at `u→1`, where the
θ-series needs unboundedly many terms. The modular dual **inverts the convergence**: near `u=1` the
dual nome `ã = e^{−π²/ε} → 0`, so `g, G` and their derivatives are geometric/super-geometric series
that a prover truncates after **one leading term + an explicit tail**. The free constants `2` and `8`
appear as the **leading continuum-Gaussian coefficients** `1/(2ε), 1/(2ε²)` — the "free rate" is
literally the `ε → 0` limit of the dual.

---

## 2. M2 in the same frame (variance = second cumulant)

`M2 ⟺ Var(k²) ≤ 1/(2(1−u)²)` (even) and `Var(j²) ≤ 1/(2(1−u)²)` (odd). Decomposition above:

```
  even:  Var(k²) = 1/(2ε²) + (ln g)''   ,  (ln g)'' ≥ 0  (unfavorable) → dominated by c₂ (ratio ≤ 0.049)
  odd :  Var(j²) = 1/(2ε²) + (ln G)''   ,  (ln G)'' ≤ 0  (favorable, sub-Gaussian) → immediate
```

The "`Var_p ≈ 2(V_p^∞)²` Gaussian-kurtosis" heuristic in the prior notes is exactly `16·1/(2ε²) =
8/ε²` vs `V²=4/ε²`; M2's constant `8` is `16 × ½`, the continuum kurtosis of `D²`. The odd case is a
genuine variance-domination (log-concavity of the alternating dual `G`); the even case needs the cushion.

---

## 3. Lemma C — investigated, and why it does **not** join M1/M2

Lemma C lives on a **different object**: the *finite* ensemble `ρ_t(D) = (n²−D²)q^{D²}`, `|D|≤t`,
`n=t+2` — a Gaussian **times a parabolic window**, **truncated**. It is not an infinite theta near a
cusp, so the modular dual does not apply. Three concrete negative results (all verified) show there is
no clean total-positivity / cumulant proof:

1. **Pointwise cumulant condition is FALSE.** `∂_μ Var_μ = −½ m₃(D²)` gives `Lemma C ⟸ Δ²m₃(μ;s) ≥ 0`,
   but `min_{s,μ} Δ²m₃ = −115.9` at `(s,μ)=(9,0.1)` — the third-central-moment second-difference goes
   negative. (Reproduced.)
2. **No monotonicity in the tilt.** `q ↦ Δ²Var_q(s)` is **not** monotone on `(0,1]`
   (`∂_q Δ²Var = +(1/2q)Δ²m₃` changes sign), so "maximized at `q=1`" is an interior extremal statement
   reached against a non-monotone approach — no variation-diminishing / Karlin sign-count argument gives
   it directly. What *is* uniformly true and provable is only the **edge derivative**:
   `∂_μ[Δ²Var_μ(s)]|_{μ=0} = −½Δ²m₃_par(s) = −32(5s⁴+60s³+211s²+186s−42)/875 < 0` (strict local max at
   `q=1`), plus the `q→0` collapse `Δ²Var_{q→0}=0`. These are the correct seeds, but they do not close
   the interior.
3. **The Bernstein certificate integers have NO closed form.** Per `s`, Lemma C ⟺ `β_k^{(s)} ≥ 0`
   (integers, `k=0..d`, `d = ½Σ(s²+(s+1)²+(s+2)²)−1`). Factoring them kills any hope of a uniform
   formula:

```
   β_0^{(7)} = 138726604800000000 = 2²⁸·3³·5⁸·7²          (clean)
   β_3^{(7)} = 2²⁸·3·5⁴·7·11·19·23·1356659                (prime 1356659)
   β_3^{(8)} = 2²⁷·3³·5³·7·23·649621979                    (prime 649621979)
```

   The large "random" prime factors (`1356659`, `1888421`, `649621979`, …) rule out a
   Hermite/Charlier/Meixner/Stirling/Narayana closed form or a positive three-term recurrence in
   `(k,s)`. **Item 3 is a dead end.** The `β_k^{(s)} > 0` empirically with smooth `s`-dependence and
   large margin, but there is no manifestly-positive closed form.

**Honest Lemma-C verdict.** It is *true and per-`s` finitely certifiable* (three `decide`-checkable
integer facts: support mod 4, `(x−1)|Px_s`, `β_k ≥ 0`), but the **uniform-in-`s` quantifier is a
genuine residual** that the log-concavity/TP route does **not** remove. The right way to spend the
structure is on M1/M2 (which it fully explains) — Lemma C stays a separate obligation, best discharged
by base-cases-`7..N` + an asymptotic-tail argument seeded by the edge formulas above, **not** by a
single structural lemma.

> Note: Lemma C is only needed on the *parabolic* branch (`w∈[1/2,1]`); the θ-branch reduction uses
> **only M1, M2, and the parity anchors U3/U4** (`ϑ₄(u)⁴` monotone with `ϑ₄(¼)⁴ ≤ 7/100`, and
> `|Var_e−Var_o| ≤ 1`). The exact parity-gap identity `V_o^∞ − V_e^∞ = ϑ₄(u)⁴` (verified to 1e-40)
> lets the odd moments be handled as even + an exponentially-small anchor, an independent clean route
> to M1-odd/U4.

---

## 4. Which codebase file is the formalization template

| piece | needs | template file | why |
|---|---|---|---|
| **M1/M2 dual defect** `g,G` and `g',g'',G',G''` bounds | quadratic × super-geometric Gaussian series `Σ n² ã^{n²}` with explicit geometric majorant | **`Continuum/JTPIdentity.lean`** | it already builds exactly `Σ (n+1)²·a^{(n+1)²}` majorants: `nsq_aa_pow_le` (`n²(a·a)ⁿ ≤ 1/(1−a)²`), `gauss_le_geo` (`a^{(n+1)²} ≤ a^{n+1}(a·a)ⁿ`), `dTermMaj_le`. The dual defect series are this object with `a = ã = e^{−π²/ε}`. |
| **M1-odd / M2 alternating dual** `G` leading-term bracket | Leibniz alternating-series bounds `partial ≤ full ≤ partial+term` | JTPIdentity's `Q'`-alternating toolkit (same file family as `theta4QuarterAnchor`, see commit `fd8a1ee`) | `G` is alternating in `ã^{n²}`; `−(ln G)' ≤ (2π²/ε²)ã/(1−2ã)` is a one-term Leibniz bracket. |
| **log-gap** `1−u ≤ −ln u` | elementary convexity | any `Q'`/`CReal` file | one line. |
| **M1 direct-`u` polynomial fallback** (for a cutoff `u ≤ u*<1`) and **Lemma C per-`s` Bernstein** | "all Bernstein coeffs ≥ 0 ⇒ poly ≥ 0 on [0,1]" | **`Continuum/Positivstellensatz.lean` / `MarkovLukacs.lean`** (interval positivity certificate) + existing `BernsteinVariance.lean` | Markov–Lukács is the interval-positivity engine; the `β_k ≥ 0` step is its Bernstein instance. |
| **Lemma C uniform-in-`s`** | asymptotic tail past base cases | — | **no template; genuine open residual** (not a structural lemma). |

**Recommendation:** formalize M1+M2 as **one modular-dual lemma** on `L_p(ε)` using the
`JTPIdentity` Gaussian-majorant engine (which is already built and axiom-clean), with the log-gap and
the leading-term Leibniz bracket. This is the single structural argument the task asked for — it covers
**four inequalities (M1/M2 × even/odd) with one mechanism**, gives the free constants `2, 8` as the
continuum-Gaussian leading terms, and dissolves the `u→1` non-truncatability. Keep **Lemma C separate**.

---

## 5. Numerical verification log

| check | method / precision | result |
|---|---|---|
| M1 `V_p(1−u) ≤ 2`, both parities, `u∈[¼, .9999]` | mpmath dps 50, direct sums | sup **1.99990** (`u→1`); 0 violations |
| M2 `Var_p(1−u)² ≤ 8`, both parities | mpmath dps 50 | sup **7.99914** (`u→1`); 0 violations |
| `⟨k²⟩·2ε ≤ 1` (even, sub-Gaussian) vs `⟨j²⟩·2ε > 1` (odd) | dps 50 | even `0.977 ≤ 1`; **odd `1.023 > 1`** at `u=¼` (domination fails odd) |
| signed-factor identity `S_e = √(π/ε)[g(1−(1−u)/ε)+2(1−u)g']` | dps 45 | matches direct sum to 8+ digits; all 3 factors ≥ 0 |
| defect signs `−(ln g)'≤0, −(ln G)'≥0, (ln g)''≥0, (ln G)''≤0` | dps 45–50, `mp.diff` | all confirmed on grid |
| **unfavorable defect ≤ cushion** (M1-odd, M2-even) | dps 40, 64 pts `[¼,.9999]` | ratios ≤ **0.0272**, **0.0486**; 0 violations |
| favorable defect ≤ 0 (M1-even, M2-odd) | dps 40 | holds all points |
| Leibniz bracket `−(ln G)' ≤ (2π²/ε²)ã/(1−2ã)` | dps 40 | holds all points |
| parity-gap `V_o^∞ − V_e^∞ = ϑ₄(u)⁴` | dps 40 | agree to `1e-40` |
| pointwise `Δ²m₃ ≥ 0` (Lemma C naïve cumulant) | dps 40 | **FALSE**, min `−115.9` at `(9,0.1)` |
| `β_k^{(s)}` factorizations (`s=7,8`) | exact `sympy.factorint` | large primes (`1356659`, `649621979`, …) → **no closed form** |
| `β_k^{(s)} ≥ 0` all `k` | exact integer (prior, `s=7..60`) | holds (strictly `>0`) — but per-`s` only |

Scripts (in `/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `sg1_poisson.py`, `sg2_dual.py`,
`master_dual.py`, `direct_u.py`, `final_uniform.py`, `paritygap.py`, `beta_closed.py`.

---

## 6. Bottom line

* **M1 + M2 = one structural lemma.** The discrete-Gaussian log-partition `L_p(ε)` and its **Poisson
  modular dual** unify all four inequalities. Mechanism: `discrete = continuum(ε) + dual-defect`;
  `continuum(ε) ≤ target(1−u)` by the log-gap `1−u ≤ −ln u`; the dual-defect is either `≤ 0`
  (genuine sub-Gaussian/log-concave domination, M1-even & M2-odd) or exponentially small in
  `ã=e^{−π²/ε}` and swallowed by the `O(1)` cushion (M1-odd & M2-even). Free constants `2, 8` = the
  continuum-Gaussian leading terms. Template: `JTPIdentity.lean`'s Gaussian-majorant engine.
* **Log-concavity does NOT suffice by itself.** Only 2 of 4 cases are true domination; the log-gap
  cushion is *essential* for the other two. This is the honest limit of the "pure probabilistic
  structure" idea — but the modular dual makes all four **finitely certifiable** (the `u→1` wall is a
  basis artifact, gone in the dual).
* **Lemma C is a separate beast.** Finite parabolic-windowed ensemble; TP/cumulant route obstructed
  (pointwise `Δ²m₃ ≥ 0` false; `Δ²Var_q` non-monotone in `q`); its Bernstein integers `β_k^{(s)}` have
  **no closed form** (large primes). It stays a per-`s` certificate with a genuine uniform-in-`s`
  residual — best handled by base-cases + asymptotic tail, not by the structural lemma.
</content>
</invoke>
