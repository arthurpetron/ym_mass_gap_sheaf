# Lemma C via a two‑region sign argument — with an explicit rational threshold

**Statement (Lemma C).** For all integers `s ≥ 7` and all `q ∈ (0,1]`,
```
        Δ²Var_q(s)  ≤  Δ²Var_par(s) := 96(s²+6s+7)/175,
```
on the finite tilted parabolic ensemble `ρ_t(D) = (n²−D²) q^{D²}` (`D ≡ t (2)`, `|D| ≤ t`, `n = t+2`),
`Var_q(t) = ⟨D⁴⟩ − ⟨D²⟩²`, `Δ²X(s) = X(s) − 2X(s+1) + X(s+2)`.

**Convention (fixed once).** Put `μ := −ln q ≥ 0`, so `q^{D²} = e^{−μD²}` and `g := D²` is the tilted
statistic with weight `∝ (n²−D²)e^{−μg}`. For this exponential family the cumulant chain is exact:
```
   ∂_μ κ_j(g) = −κ_{j+1}(g),   in particular   ∂_μ Var_q = −m₃,   ∂_μ Δ²Var_μ(s) = −Δ²m₃(μ;s),
```
where `m₃ = κ₃` is the third central moment of `g = D²`. (The "−½" in earlier notes is the
`e^{−μD²/2}` convention; with `q^{D²}` the factor is exactly `1`. Only the **sign** is load‑bearing.)

**Verdict of this route.** The two‑region sign programme is REAL and is verified with zero violations
for `s = 7..80`, but the literal premise in the brief ("`Δ²Var_q ≤ 0` for all `q ≤ q*`") is **false
for even `s`**: there is a genuine, bounded positive bump in the deep tail. The honest, complete
structure is:

| region | `μ`-range | statement | mechanism |
|---|---|---|---|
| **B** (near `q=1`) | `μ ∈ [0, μ*]` | `Δ²m₃ ≥ 0` ⟹ `Δ²Var_μ ≤ Δ²Var_par` | **monotone rise** to the `μ=0` max |
| **A** (odd `s`) | `μ ∈ [μ*, ∞)` | `Δ²Var_μ ≤ 0` | **pure sign** |
| **A/C** (even `s`) | `μ ∈ [μ*, ∞)` | `Δ²Var_μ ≤ 3.356 < Δ²Var_par` | sign, then a **bounded `O(1)` tail bump** |

with an explicit **rational** split `q* = q₀(s)` below. Every number here is `mpmath`(dps 40–50) or
exact `sympy`; the load‑bearing constants are exact rationals.

---

## 1. The two sign curves and the natural scale `E := s²+6s+7`

Define the two zero‑crossings (both are `+ → −` crossings as `μ` increases from `0`):
```
   μ_V(s)  : first μ>0 with Δ²Var_μ(s) = 0     (below it Δ²Var>0, above it Δ²Var≤0)
   μ_m3(s) : first μ>0 with Δ²m₃(μ;s) = 0      (below it Δ²m₃>0, above it Δ²m₃<0)
```
Region A needs `μ* ≥ μ_V` (so `Δ²Var ≤ 0` there); Region B needs `μ* ≤ μ_m3` (so `Δ²m₃ ≥ 0` there).
A valid threshold exists **iff** `μ_V(s) ≤ μ_m3(s)`.

**The clean discovery.** The correct scale is `E = s²+6s+7` — *the same `E` in* `Δ²Var_par = 96E/175`.
In `E`‑units the two curves are nearly flat and are cleanly separated (bisection, dps 40):

| `s` | `μ_V·E` | `μ_m3·E` | `μ_m3/μ_V` |
|----:|--------:|---------:|-----------:|
| 7   | 2.8939  | 4.5657   | 1.5777 |
| 10  | 2.9180  | 4.6097   | 1.5798 |
| 20  | 2.9414  | 4.6512   | 1.5813 |
| 40  | 2.9492  | 4.6648   | 1.5817 |
| 80  | 2.9515  | 4.6688   | 1.5818 |

Both increase monotonically to finite limits. The decisive inequality (`s = 7..80`, all checked):
```
   sup_s (μ_V·E)  = 2.9515  (at s=80, →≈2.952)   <   inf_s (μ_m3·E) = 4.5657  (at s=7).
```
So a **single constant** `c` with `μ*·E = c` and `c ∈ (2.952, 4.566)` separates the regions for **all**
`s ≥ 7` simultaneously — a uniform window of width `≈ 1.6/E`, and `μ_V < μ_m3` holds for every `s`.

### The explicit rational threshold
Take the rational split point
```
        q₀(s) := (2E − 7)/(2E),      E = s²+6s+7        (μ₀ = −ln q₀).
```
Then `μ₀ = −ln(1 − 7/(2E))`, and one checks `μ₀·E ∈ [3.500, 3.564]` for all `s ≥ 7` (it decreases from
`3.564` at `s=7` to `→3.5`), i.e. `μ₀·E ∈ (2.952, 4.566)` with margins `≥ 0.55` above `μ_V·E` and
`≥ 1.0` below `μ_m3·E`. **Verified: `q₀(s)` lies strictly inside the window for every `s = 7..80`.**
Equivalently, region B is `q ∈ [q₀, 1]` and region A is `q ∈ (0, q₀]`. (Any rational `c/E`,
`c ∈ {3, 7/2, 4}`, works identically; `q₀=(2E−7)/(2E)` is the tidiest fully‑rational cut.)

---

## 2. REGION B — monotone rise to the maximum (`q ∈ [q₀,1]`)

**Statement (B).** `Δ²m₃(μ;s) ≥ 0` for `μ ∈ [0, μ₀]`. Hence `Δ²Var_μ(s)` is non‑increasing in `μ` on
`[0,μ₀]` (`∂_μΔ²Var = −Δ²m₃ ≤ 0`), so it rises, as `μ ↓ 0` / `q ↑ 1`, to its endpoint value
```
     Δ²Var_μ(s) ≤ Δ²Var_{μ=0}(s) = Δ²Var_par(s)   for all q ∈ [q₀,1].
```
`Δ²Var_{μ=0} = Δ²Var_par` is exact: at `μ=0` the ensemble is the pure parabola with
`Var_par(t) = 8t(t−1)(t+4)(t+5)/175`, `Δ²Var_par = 96(s²+6s+7)/175`.

**Verification (dps 45, fine grid `μ ∈ (0,μ₀]`, `s = 7..80`):**
```
   min_{s, μ∈(0,μ₀]} Δ²m₃(μ;s) = 209.0   (attained at s=7, μ·E≈3.56);  ZERO violations.
```
The endpoint value `Δ²m₃(μ₀;s)` grows like `s⁴` and is robustly positive:
`s=7 → 230.6, s=20 → 6.35·10³, s=50 → 1.78·10⁵, s=80 → 1.07·10⁶`.

**Exact edge data (all closed‑form, `sympy`, both parities identical):**
```
   Δ²m₃_par(s)   = Δ²m₃(0;s)  = 64(5s⁴+60s³+211s²+186s−42)/875              (>0 ∀s≥1)
   Δ²κ₄_par(s)   = 256(126s⁶+2268s⁵+9445s⁴−22740s³−192967s²−258594s−35574)/336875
   Var_par(t)=8t(t−1)(t+4)(t+5)/175,  m₃_par(t)=32t(t−1)(t+4)(t+5)(t²+4t−15)/2625,
   κ₄_par(t) =64t(t−1)(t+4)(t+5)(27t⁴+216t³−2153t²−10340t+22050)/1010625.
```

**Reduction to a finite rational inequality.** With `R_j(t) := Σ_{|D|≤t,D≡t(2)} (n²−D²)D^{2j} q^{D²}
∈ ℤ[q]` (`n=t+2`),
```
   m₃(t) = ( R₃R₀² − 3R₂R₁R₀ + 2R₁³ ) / R₀³ ,
   Δ²m₃(s) ≥ 0  ⟺  Q_B^{(s)}(q) := Σ_{cyc} ±(numerators)·R₀(·)³  ≥ 0   on  q ∈ [q₀, 1],
```
`Q_B^{(s)} ∈ ℤ[q]` (clear the common denom `R₀(s)³R₀(s+1)³R₀(s+2)³ > 0`), `deg_q Q_B^{(s)} ≈
3(s²+(s+1)²+(s+2)²) ≈ 9s²`. This is one **sign** inequality on the sub‑interval `[q₀,1]` — no Bernstein
list, no `(q−1)` factorisation.

---

## 3. REGION A — sign (odd `s`) and a bounded tail bump (even `s`) (`q ∈ (0,q₀]`)

Because `μ₀ ≥ μ_V(s)`, at the split point `Δ²Var` has already changed sign. What happens for
`μ ≥ μ₀` is **parity‑dependent** — this is the honest correction to the brief.

**Odd `s`: pure sign.** `Δ²Var_μ(s)` has a **single** zero‑crossing `μ_V`; for all `μ ≥ μ_V` it stays
`≤ 0`. Verified: `max_{odd s, μ∈[μ₀, 70/E]} Δ²Var_μ = −0.011 ≤ 0`, and `→ 0⁻` as `μ→∞`. So
```
     Δ²Var_μ(s) ≤ 0 ≤ Δ²Var_par(s)      for all q ∈ (0,q₀], odd s.     (pure sign)
```

**Even `s`: sign, then a bounded bump.** `Δ²Var_μ(s)` has **two** crossings: `μ_V` (`+→−`) and a
second `μ₂` (`−→+`, at `μ₂ ≈ 0.18–0.52`, i.e. `μ₂·E ≈ 12–24`). On `[μ_V, μ₂]` it is `≤ 0`; on
`[μ₂,∞)` it is a small **positive bump** (`→ 0⁺` as `μ→∞`). Verified with **exact rational
arithmetic** (`sympy`, e.g. `s=8, q=3/4`: `Δ²Var = +1.137451…`; `s=10,12,q=3/4`: `+1.11, +1.09`), so
the bump is not a float artifact. Its **global** ceiling over all even `s` and all `μ`:
```
   sup_{even s≥8, μ>0} Δ²Var_μ(s) = 3.3555   (attained near s=36, μ≈0.523).
```
The bump is uniformly `O(1)` and hence `≪ Δ²Var_par(s) ≥ Δ²Var_par(8) = 65.28`. Structurally, as
`s→∞` at fixed `μ` the `n²` factor dominates `(n²−D²)` and the ensemble → the pure theta ensemble
`e^{−μD²}` on the parity class; therefore
```
   Δ²Var_μ(s) → 2·(V_even(μ) − V_odd(μ))   (even s),   ≤ max_μ 2(V_e−V_o) = 3.35546  at μ≈0.523,
```
an `s`‑independent **theta‑variance difference** (verified: `s=40,80,200` all `= 3.3552` at `μ=0.52`).

**Unified region‑A statement (what actually closes Lemma C).** In all cases, on the whole split‑off
side,
```
   max_{s=7..80,  μ ≥ μ₀}  ( Δ²Var_μ(s) − Δ²Var_par(s) )  =  −53.94      (attained at s=7).
```
i.e. on `q ∈ (0,q₀]`, `Δ²Var_μ ≤ Δ²Var_par − 53.9`, with **margin ≥ 53.9 uniformly** — trivial for
odd `s` (`Δ²Var≤0`) and by the `≤3.356 ≪ 65.28` bump bound for even `s`.

**Reduction to finite rational inequalities.** With `N(t)=R₂R₀−R₁²`, `d(t)=R₀²`:
```
   Δ²Var_μ(s) ≤ 0  ⟺  Q_A^{(s)}(q) := −[N(s)d(s+1)d(s+2) − 2N(s+1)d(s)d(s+2) + N(s+2)d(s)d(s+1)] ≥ 0,
```
`Q_A^{(s)} ∈ ℤ[q]`, `deg_q ≈ 2(s²+(s+1)²+(s+2)²) ≈ 6s²` (same degree as the dead `P_s`). For odd `s`
this is the whole story on `(0,q₀]`. For even `s` one instead uses the magnitude form
`175·[N(s)d(s+1)d(s+2)−…] ≤ 96E·d(s)d(s+1)d(s+2)` (a single polynomial `≥0`), which the bump satisfies
with the huge `65.28 − 3.36` margin.

---

## 4. Numerical verification log (all with the rational split `q₀=(2E−7)/(2E)`)

| check | method / precision | result |
|---|---|---|
| `q₀(s)` inside window `μ·E ∈ (2.952, 4.566)` | dps 40 | ✓ **all** `s = 7..80` (`μ₀E ∈ [3.500,3.564]`) |
| `μ_V < μ_m3` (window non‑empty) | bisection dps 40 | ✓ all `s = 7..80`; `sup μ_V·E=2.952 < inf μ_m3·E=4.566` |
| **Region B** `Δ²m₃ ≥ 0` on `(0,μ₀]` | dps 45, 80‑pt grid | `min = 209.0` (s=7); **0 violations** |
| edge `Δ²m₃_par, Δ²κ₄_par` closed forms | exact `sympy` | ✓ (both parities identical) |
| **Region A odd** `Δ²Var ≤ 0` on `[μ₀,70/E]` | dps 45 | `max = −0.011`; **0 violations** |
| **Region A even** bump | exact `sympy` + dps 45 | real; `sup = 3.3555` (s≈36); `< 65.28 ≤ Δ²Var_par` |
| even bump `= 2(V_e−V_o)` theta limit | dps 40 | ✓ `= 3.35546` at `μ≈0.523`, `s→∞` |
| **Lemma C** `Δ²Var − Δ²Var_par` on `μ ≥ μ₀` | dps 45 | `max = −53.94` (s=7); **0 violations** |
| **Lemma C end‑to‑end** (B on `[q₀,1]` + A on `(0,q₀]`) | dps 45, `s=7..80` | holds, **0 violations** |

Scripts: `sr_curves.py` (sign curves + `E`‑scale), `sr_final.py` (rational split + both regions),
`sr_tail.py` / `sr_theta.py` (even bump ceiling + theta limit), `sr_exact.py` (exact‑rational bump),
`sr_cumulants.py` (closed‑form edge cumulants), `sr_convex.py`/`sr_conc.py` (curvature probes).

---

## 5. Can this discharge the `∀ s` quantifier? — honest feasibility vs the dead `β_k` route

The sign route was hoped to (i) give a clean threshold, (ii) replace the opaque `β_k` list by a
lower‑complexity object, and (iii) admit a uniform‑in‑`s` argument. Scorecard:

**Wins (real).**
1. **Explicit rational threshold** `q₀=(2E−7)/(2E)` with the natural `E=s²+6s+7` scale and a wide
   verified window `μ·E ∈ (2.952,4.566)` — this the `β_k` route never had.
2. **Region B is ONE inequality** `Δ²m₃ ≥ 0`, a structurally meaningful cumulant sign, not a growing
   list of mysterious integers. Its edge data are *known closed forms*
   (`Δ²m₃_par = 64(5s⁴+…)/875 > 0`), so the object is transparent.
3. **Region B alone covers the corner's actual need.** In the certificate the tilt used is only
   `μ ≤ 35/(8E) ≈ 4.375/E < inf(μ_m3·E)/E = 4.566/E`, i.e. `Δ²m₃ ≥ 0` holds throughout the range where
   Lemma C is invoked — so for the downstream corner, the monotone Region B is the *entire* proof and
   the even‑`s` bump is irrelevant.
4. **Region A odd `s` is a pure sign** `Δ²Var ≤ 0` (degree `≈6s²`, same as `P_s`, but no `(q−1)`
   factorisation / no Bernstein certificate needed — just one polynomial `≥0`).

**Honest caveats (adversarial).**
1. **The brief's premise is wrong for even `s`.** "`Δ²Var ≤ 0` away from `q=1`" fails on a genuine
   (exact‑rational‑verified) tail bump `≤ 3.356`. Even `s` therefore needs one extra ingredient: a
   uniform `O(1)` upper bound on `Δ²Var` in the deep tail (equivalently the theta inequality
   `2(V_e−V_o) ≤ 4`). It is *true and small*, but it is not a pure sign statement.
2. **The `∀ s` quantifier is NOT eliminated.** Both `Q_A^{(s)}` (`≈6s²`) and `Q_B^{(s)}` (`≈9s²`) are
   integer‑polynomial‑positivity‑on‑an‑interval families of growing degree — the same *kind* of
   residual as `β_k`, and `Q_B` is in fact *higher* degree. Per‑`s` this is decidable; uniformly it is
   not closed here.
3. **The tempting uniform closure for Region B is borderline, not clean.** The first‑order edge budget
   is asymptotically favourable:
   ```
      [Δ²m₃_par · E] / [c · Δ²κ₄_par]  →  275/252 ≈ 1.091 > 1   (c = 7/2),   → 1.294  (c = 2.952).
   ```
   so the leading `μ=0` balance says `Δ²m₃` "should" stay positive across `[0,μ₀]`. But this is only a
   tangent‑at‑`0` heuristic, and it is **not rigorous**: `Δ²m₃(μ)` is neither convex nor concave on
   `[0,μ₀]` (its second derivative `Δ²κ₅` changes sign), so it dips below its `μ=0` tangent, and the
   crude bound `Δ²m₃ ≥ Δ²m₃_par − μ·sup_{[0,μ₀]}|Δ²κ₄|` fails (`sup|Δ²κ₄|` exceeds `Δ²κ₄_par` by ≈30%).
   A rigorous uniform proof of Region B therefore needs the *integral* `∫₀^{μ₀}Δ²κ₄`, i.e. a
   second‑order (curvature) control — a well‑posed but genuinely open estimate. The saving grace is
   that it is now a **single, closed‑form‑driven** target (all `Δ²κ_j_par` are explicit rational
   polynomials in `s`), unlike the `β_k` integers.

**Net verdict.** The sign route is a **genuine structural improvement, not a closure.** It delivers the
explicit rational threshold and reduces the *load‑bearing* half of Lemma C (Region B, = exactly the
corner's needed range) to a single transparent cumulant sign `Δ²m₃ ≥ 0` with known `s⁴` edge value and
a favourable (`275/252`) leading balance. It does **not** by itself kill the `∀ s` quantifier: per‑`s`
it is comparable to `β_k` (and `Q_B` is higher degree), and the even‑`s` tail requires an extra `O(1)`
theta bound. The right way to *finish* is now sharply posed: prove the one uniform inequality
`Δ²m₃(μ;s) ≥ 0 on [0, μ₀]` via a two‑term (curvature) edge estimate using the exact
`Δ²m₃_par ~ 0.366 s⁴`, `Δ²κ₄_par ~ 0.096 s⁶` closed forms — a single polynomial‑family estimate, far
better‑conditioned than searching an opaque `β_k` list, but still an open uniform bound.
