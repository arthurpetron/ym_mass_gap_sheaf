# Poisson/modular proof of the discrete‑Gaussian moment envelopes M1, M2

**Goal.** Prove, as finite Lean‑formalizable inequalities, uniform over `u = w² ∈ [1/4, 1)`, both
parities:

> **M1** `V_p^∞(u)·(1−u) ≤ 2`  and  **M2** `Var_p(u)·(1−u)² ≤ 8`.

Everything below is verified numerically (mpmath, dps 40–60; load‑bearing constants exact rationals).
Scripts: `/Users/darthur/.claude/jobs/1c30fec5/tmp/pm_0{1..7}_*.py`.

Notation throughout: `ε := −ln u > 0`, `v := 1−u`, `x := e^{−π²/ε}`.

---

## 0. Headline

* **M1‑even is UNCONDITIONAL and needs no region split**: `V_e = 2/ε − 4P₁/(ε²P₀) ≤ 2/ε`, then
  `2/ε·(1−u) ≤ 2` because `(1−u) ≤ −ln u`. One sign fact (`P₁≥0`) + one log atom.
* **M1‑odd, M2‑even, M2‑odd** each split `[1/4,1)` at the rational cut `u* = 3/4` into
  * **Region A `[1/4, 3/4]`** — original θ (`q`‑)series, truncated at `N=12` with a rational
    geometric tail; the envelope stays `≤ 1.738 < 2` and `≤ 6.042 < 8` (comfortable margin), so the
    truncated **rational polynomial** inequality closes it.
  * **Region B `[3/4, 1)`** — the Poisson/Jacobi **dual** series; after cancelling `v²` the target
    collapses to a **single‑variable rational inequality in `ε`** on `(0, 7/24]` that holds with a
    ~50× margin (ratios `0.020`, `0.016`).

All four envelopes are certified `≤ cap` on `u∈[1/4, 0.99999]`, both parities, with **zero**
certificate failures and zero true‑cap violations (`pm_07_final.py`).

---

## 1. Deliverable 1 — exact Poisson‑dual expressions (verified to ≤1e‑56)

Define the **dual moments** (`m ∈ ℤ`)
```
even:  P_j = Σ_m (π² m²)^j · e^{−π² m²/ε}            (j=0,1,2)
odd :  Q_j = Σ_m (−1)^m (π² m²)^j · e^{−π² m²/ε}
```
`P_0 = θ₃`‑dual `= 1+2x+2x⁴+…`,  `Q_0 = θ₄`‑dual `= 1−2x+2x⁴−…`.

### Even (`m∈ℤ`, Poisson summation of `x^{2j} e^{−εx²}`)
```
A = Σ_k u^{k²}      = √(π/ε) · P₀
B = Σ_k 4k² u^{k²}  = 4 √(π/ε) · [ P₀/(2ε) − P₁/ε² ]
C = Σ_k 16k⁴ u^{k²} = 16 √(π/ε) · [ 3P₀/(4ε²) − 3P₁/ε³ + P₂/ε⁴ ]
```
### Odd (`j=2k+1` odd, `k(k+1)=(j²−1)/4`, so `u^{k(k+1)}=u^{−1/4}e^{−(ε/4)j²}`; θ₂↔θ₄ dual). All three verified `|series−dual| ≤ 1e‑47` for `u ≤ 0.99` (`pm_08b.py`):
```
a = Σ_{k≥0} u^{k(k+1)}   = u^{−1/4} √(π/ε) · ( Q₀/2 )
b = Σ (2k+1)² u^{k(k+1)} = u^{−1/4} √(π/ε) · ( Q₀/ε  − 2 Q₁/ε² )
c = Σ (2k+1)⁴ u^{k(k+1)} = u^{−1/4} √(π/ε) · ( 6 Q₀/ε² − 24 Q₁/ε³ + 8 Q₂/ε⁴ )
```
(the common `u^{−1/4}√(π/ε)` cancels in `b/a`, `c/a`).
The common `u^{−1/4}·¼√(4π/ε)` cancels in every ratio, giving the clean **unified moment form**
(both parities, `(R₀,R₁,R₂)=(P)` even / `(Q)` odd):
```
        V   = 2/ε  − 4 R₁/(ε² R₀)
        Var = 8/ε² − 32 R₁/(ε³ R₀) + 16 (R₂R₀ − R₁²)/(ε⁴ R₀²)
```
Verified `|series − dual| ≤ 1e‑56` for `A,B,C,a,b,c` and `|V,Var (series) − (dual)| ≤ 1e‑54` at
`u = 0.25,0.5,0.9,0.98,0.999` (`pm_01_duals.py`, `pm_02_structure.py`).

**Leading behaviour (why the constants are `2` and `8`).** As `ε→0`, `x→0` super‑exponentially, so
`R_j→` its `m=0` term and `V→2/ε`, `Var→8/ε²`; then `V(1−u)→2·(1−u)/ε→2` and
`Var(1−u)²→8·((1−u)/ε)²→8`. The free constants are exactly the continuum‑Gaussian
mean `2/ε` and kurtosis `8/ε²`.

### Sign facts (verified)
```
even : R₁ = P₁ ≥ 0,   R₂R₀ − R₁² ≥ 0        (variance of a positive measure)
odd  : R₁ = Q₁ ≤ 0,   R₂R₀ − R₁² ≤ 0        (alternation; corrections have the "wrong" sign)
```
Hence M1‑even is immediate; the other three carry a **positive** dual correction that must be
dominated by an envelope deficit.

---

## 2. The two elementary building blocks

### 2a. Deficit lemmas (exact rational lower bounds; 0 violations over `u∈(0.05,1)`)
```
Def₁ := 2 − 2v/ε  ≥  v²/ε  ≥  u(1−u)
Def₂ := 8 − 8v²/ε² ≥ 4v²/ε ≥ 4u(1−u)
```
from `ε − v ≥ v²/2` (atom A3) and `ε ≤ v/u` (weak form of A2). `V(1−u) ≤ 2 ⟺ corr ≤ Def₁`;
`Var(1−u)² ≤ 8 ⟺ corr ≤ Def₂`, where `corr` is the (positive) dual correction.

### 2b. Rational taming of the transcendentals (verified 0 violations)
```
A1  −ln u ≥ 1−u
A2  −ln u ≤ (1−u²)/(2u)          [proof: f(u)=½(1/u−u)+ln u, f(1)=0, f'=−(1−u)²/(2u²)≤0]
A3  −ln(1−v) ≥ v + v²/2
A4  1 − e^{−ε} ≥ ε − ε²/2
π²  bracket:  986/100 ≤ π² ≤ 987/100
X   monomial exp‑bound:  x = e^{−π²/ε} ≤ X_k(ε) := k!·ε^k / (986/100)^k
    (from π² ≥ 986/100 and e^{−y} ≤ k!/y^k;  verified 0 violations for k=4,6 on ε≤0.292)
```
`A2` + monotonicity give, for `u ≥ 3/4`, `ε ≤ (1−u²)/(2u) ≤ 7/24`, i.e. Region B lives in
`ε ∈ (0, 7/24]` (and `ln(4/3)=0.28768 ≤ 7/24 = 0.29167`, exact‑rational‑checkable).

---

## 3. Deliverable 2 — the two‑region certificate

### 3a. Region A `u ∈ [1/4, 3/4]` (moderate; original q‑series)
For `u ≤ 3/4` truncate at `|k| ≤ N = 12` (odd: `0 ≤ k ≤ 12`). Rational geometric tails (with
`r = u^{2N+3}`):
```
0 ≤ A − A_N ≤ 2 u^{(N+1)²}/(1−r) =: tA,   tB ≤ 8(N+3)² tA,   tC ≤ 32(N+3)⁴ tA
```
(odd analogue with `u^{k(k+1)}`, exponent `(N+1)(N+2)`). Over `[1/4,3/4]`, `tC ≤ 2.5e‑15`.
The one‑sided rational bounds
```
V ≤ (B_N + tB)/A_N ,     Var ≤ ((A_N+tA)(C_N+tC) − B_N²)/A_N²
```
give (verified, 0 violations, both parities)
```
sup V(1−u)   ≤ 1.73803 < 2      (margin 0.26)
sup Var(1−u)² ≤ 6.04149 < 8      (margin 1.96)      attained at the right endpoint u=3/4.
```
These are **rational polynomial inequalities in `u`** of degree `≈ (N+1)² = 169` (Bernstein/`decide`
or `polyrith` closeable). `pm_06_regionA.py`.

### 3b. Region B `u ∈ [3/4, 1)` (near‑1; Poisson dual)

Write `V(1−u) = 2 − Def₁ + corr`, `Var(1−u)² = 8 − Def₂ + corr`. Bound `corr` above by the tail
lemmas (all from geometric domination `m²−1 ≥ 3(m−1)` and Leibniz alternation, with
`G₁(X)=(1+X³)/(1−X³)³`, `G₂(X)=(1+11X³+11X⁶+X⁹)/(1−X³)⁵`, `X = X_k(ε)`):
```
even:  P₀∈[1, 1+2X/(1−X³)],  P₁ ≤ 2·(987/100)·X·G₁,  P₂ ≤ 2·(987/100)²·X·G₂
odd :  Q₀ ≥ 1−2X,            |Q₁| ≤ 2·(987/100)·X,   |Q₂| ≤ 2·(987/100)²·X
```
(verified: 0 validity violations, i.e. these really upper‑bound the true moments on `(0,7/24]`).

**The `v²` cancellation** (this is what makes it finite): dividing `corr ≤ Def` by the common `v²`
(using `Def₁ ≥ v²/ε`, `Def₂ ≥ 4v²/ε`, and for M1‑odd `v ≥ ε(1−ε/2)` from A4) reduces each target to a
**single‑variable rational inequality in `ε`** on `(0, 7/24]`, with `φ:=987/100`, `X_k := k!ε^k/(986/100)^k`:

```
M1‑odd (k=4):   8φ·X₄/(1−2X₄)  ≤  ε²(1 − ε/2)
M2‑both(k=6):   16φ·X₆·G₁·ε/(1−2X₆) + 8φ²·X₆·G₂/(1−2X₆) + 16φ²·X₆²·G₁²/(1−2X₆)²  ≤  ε³
```
Verified on `(0, 7/24]`: **0 violations**, `max(LHS/RHS) = 0.0200` (M1‑odd), `0.0160` (M2). A ~50×
margin. Because these are pure `ε`‑inequalities dominated by their lowest‑degree term
(`8φ²·720·ε⁶/(986/100)⁶ ≈ 0.61 ε⁶ ≤ ε³`), they are `decide`/`nlinarith`‑trivial once `X_k` is
substituted. `pm_05_correct.py`, `pm_07_final.py`.

M1‑even needs neither region: `P₁ ≥ 0 ⇒ V_e ≤ 2/ε`, and `A1 ⇒ 2/ε·(1−u) ≤ 2`.

---

## 4. Deliverable 3 — rationality (done above)

Every `ε = −ln u` and every `x = e^{−π²/ε}` has been replaced by rational functions of `u`/`ε` via
atoms A1–A4, the `π²` bracket, and the monomial bound `x ≤ X_k`. The final inequalities in §3 are
rational (polynomial after clearing denominators) — Region A in `u`, Region B in `ε` with
`ε ∈ (0, 7/24]` supplied by A2. No transcendental survives in the closing step.

---

## 5. Deliverable 4 — full assembled numerical verification

`pm_07_final.py`, grid `u ∈ [1/4, 0.99999]` (incl. `1−10^{−4}, 1−10^{−5}`), both parities,
evaluating the **rational certificates** (not the raw series):

```
Region A certificate failures : 0
Region B certificate failures : 0
true‑cap violations           : 0
log/exp atoms A1..A4          : 0 violations ;  ln(4/3) ≤ 7/24 : True
monomial x ≤ X_k (k=4,6)      : 0 violations
reduced ε‑ineqs on (0,7/24]   : 0 violations, max ratio 0.0200 / 0.0160
⇒ M1 ≤ 2 and M2 ≤ 8 certified on [1/4, 0.99999], both parities.
```
Independent truth check (`pm_02b.py`): `sup V_p(1−u)=1.99687`, `sup Var_p(1−u)²=7.97112` over the
same range — consistent with caps `2, 8` approached only as `u→1`.

---

## 6. Deliverable 5 — honest, adversarial assessment

**Are M1, M2 now finite, Lean‑formalizable inequalities?  Yes — all four.**

* **M1‑even**: essentially trivial. `V_e ≤ 2/ε` (one sign fact `P₁≥0` from the Poisson dual) + atom
  A1. No truncation, no region split. *This one is a few lines.*
* **M1‑odd, M2‑even, M2‑odd**: each = (Region A) a finite rational **polynomial** inequality in `u`
  of degree ≈169, closeable by Bernstein/`decide`; **+** (Region B) a single‑variable rational
  inequality in `ε` on `(0, 7/24]` with a 50× margin, closeable by `nlinarith`. Both are finite and
  decidable.

**Where is the hardest sub‑step?** Not the endgame (rational, wide‑margin) but the **analytic input
that legitimises the dual series**:

1. **The Poisson/Jacobi modular identity** `A = √(π/ε)·P₀` and its two weighted siblings for `B, C`
   (and the θ₂/θ₄ versions for `a, b, c`). This is the one genuine piece of analysis — Poisson
   summation of `x^{2j}e^{−εx²}`, equivalently the Jacobi imaginary transform plus term‑by‑term
   `ε`‑differentiation of a uniformly (on `ε ≥ ε₀ > 0`) convergent theta series. Everything downstream
   is algebra.
2. **The dual tail lemmas** (`P₀≥1`, `|Q₁|≤2π²X`, `P₂ ≤ 2π⁴X·G₂`, …). These are geometric‑series /
   Leibniz‑alternation bounds — the *same* toolkit already in the codebase (the `Q'`
   alternating‑series/Leibniz brackets and `theta4QuarterAnchor`).

Ranking: the **modular identity** is the crux; the tail lemmas are routine; the rational endgame is
trivial.

**Codebase machinery the dual step needs.**
* `JTPIdentity` / `ThetaConv` / `RealTheta` — supply (or are one transform away from) the modular
  identity `A = √(π/ε)P₀`. The weighted duals `B, C` are best obtained as **`ε`‑derivatives** of that
  identity: `B = −4A'(ε)`, `C = 16A''(ε)` (verified), i.e. one needs term‑by‑term differentiability
  of the theta series in `ε` (uniform on compact `ε`‑subsets of `(0,∞)`). If `ThetaConv` only gives
  the unweighted transform, the two extra Poisson instances (for `x²e^{−εx²}`, `x⁴e^{−εx²}`) must be
  added, or derived via that differentiation.
* `CRealExp` / `CRealLog` — atoms A1–A4 and the monomial bound `e^{−π²/ε} ≤ k!ε^k/(986/100)^k` (a
  finite Taylor‑remainder fact `e^y ≥ y^k/k!`), plus the `π²` rational bracket.
* The existing **alternating‑series (Leibniz) toolkit** — the `Q₀ ≥ 1−2X`, `|Q₁| ≤ 2π²X` brackets and
  the even geometric‑tail `G₁,G₂` bounds; identical in spirit to `theta4QuarterAnchor`.
* Rational‑arithmetic tactics (`decide`/`nlinarith`/Bernstein) for the two closing inequalities.

**Adversarial caveats (checked, not fatal).**
* The `v²` cancellation in Region B is *exact* and is what removes the `u→1` blow‑up that made the
  θ‑basis "non‑truncatable". Verified the reduced `ε`‑inequalities carry the full proof (the direct
  end‑to‑end margins shrink to 0 as `u→1`, but the reduced inequality has a *uniform* 50× margin).
* Region A and B **overlap** at `u=3/4` (`ε=ln(4/3)=0.2876 ≤ 7/24`), so there is no gap.
* An earlier coefficient error (dropping the factor‑2 and `G` tail factors in the even M2 bound) was
  caught by a validity check (`corrUB ≥ true corr`) and corrected; the final `corrUB` passes that
  check with 0 violations.
* The cut `u*=3/4`, `N=12`, `k=4/6`, `ε*=7/24` are comfortable but not forced; the margins tolerate
  a range of choices.

**Net.** The two moment envelopes are no longer an opaque `u→1` analytic wall. They are:
`{one modular identity + standard Leibniz/geometric tails}` (both already resembling codebase
lemmas) `+ {rational deficit algebra}`. M1‑even is nearly free; the remaining three are a finite
region‑A polynomial + a wide‑margin single‑variable rational inequality apiece.
