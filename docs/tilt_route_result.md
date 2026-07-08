# Tilt-bound route for the parabolic branch — recommended Lean-formalizable path

**Target inequality** (parabolic branch, `w∈[1/2,1]`, `s≥7`):
```
   Δ²e(s)  ≤  ((1−w)/2w) · Δ²Var_par(s),     Δ²Var_par(s) = 96(s²+6s+7)/175,
```
whence `Δ²V(s)+2 = 12/5 − Δ²e ≥ 0` on the rational region `(1−w)/w ≤ 35/(4K)`, `K=s²+6s+7`.

Objects (all with `n=t+2`, `D≡t (mod 2)`, `|D|≤t`, `a_D := n²−D² ≥ 0`, `P(t)=t(t+4)/5`):
```
   V(t,w) = Σ_D a_D D² w^{D²/2} / Σ_D a_D w^{D²/2},   e(t)=P(t)−V(t,w),   Δ²f(s)=f(s)−2f(s+1)+f(s+2).
```

---

## BOTTOM LINE (recommendation)

**Do NOT formalize `∫₀^λ` or the FTC `dV/dμ=−½Var_μ`.** They are unnecessary. Two things replace them:

1. **A change of variable `v:=√w`** (so `w^{D²/2}=v^{D²}`, `D²∈ℤ`) that removes every transcendental
   except one `CReal.sqrtFrom` — no `exp`, no `log`, no `μ`-tilt at all.

2. **The bound is assembled by the mean-value _inequality_ (not the mean-value _theorem_, not an
   integral):** for the single scalar function `Φ(v') := Δ²V(s; v')` of the real tilt parameter
   `v'∈[v,1]`,
   ```
        Δ²e(s) = Φ(1) − Φ(v)  ≤  (1−v) · sup_{v'∈[v,1]} Φ'(v')  ≤  ((1−v)/v) · Δ²Var_par(s)
                                                                 ≤  ((1−w)/2w) · Δ²Var_par(s).
   ```
   The derivative `Φ'(v')=(1/v')·Δ²Var_{v'}(s)` is an **elementary algebraic derivative of a finite
   rational function**; the uniform bound `Φ'(v')≤(1/v)Δ²Var_par` is **Lemma C** (below) plus
   `Δ²Var_par≥0` and `1/v'≤1/v`; and the mean-value inequality
   `(f'≤M on [a,b]) ⟹ f(b)−f(a)≤M(b−a)` is **constructively valid** and dramatically lighter than any
   integral/FTC-with-error-budget.

**Irreducible crux = Lemma C** (`Δ²Var_{v'}(s) ≤ Δ²Var_par(s)` for all `v'∈(0,1]`), which is *already*
the certificate's single remaining obligation. This route does not add analytic content; it **replaces
the heavy integral assembly with a light MVI assembly**, and reduces the transcendental surface to one
`sqrt`.

A **fully discrete / integration-free EXACT identity for `e`** also exists and is given in §4 (useful as
a cross-check or if a derivative-free representation is wanted), but see §5 for why it does *not* by
itself close `Δ²` — the mixed-sign obstruction — so §1 (MVI) is the recommended assembly.

---

## 0. Why no purely-termwise or purely-discrete-value route can work (the structural fact)

`Δ²e(s)=O(1)` (numerically `∈[0.15, 0.58]` on the whole strip) is a **relative-`O(1/s²)`
cancellation** among individual `e(t)=O(s²)` values. Consequently **any argument that bounds `e(t)`
one window at a time and then differences must fail** — it loses the cancellation. The cancellation
has to be captured *before* differencing, i.e. at the level of the tilt-derivative
`dV/dv' = Var_{v'}/v'`. That derivative-level statement, second-differenced, is exactly Lemma C. This
is the precise reason Lemma C is shared by *every* correct route, and why the assembly is a statement
about `Φ'` (a derivative), realized cheaply by the MVI. It is also why the exact discrete-value
identity of §4, although integration-free, cannot be plugged into Lemma C term-by-term (§5).

---

## 1. RECOMMENDED ROUTE — mean-value inequality in the tilt `v'` (no integration)

Let `v=√w∈[1/√2,1]` for `w∈[1/2,1]`. For `v'∈[v,1]` define the **tilted mean and variance of `D²`**
under the fixed geometry `∝ a_D v'^{D²}`:
```
   Z(v';t)   = Σ_D a_D v'^{D²},
   V(t;v')   = Σ_D a_D D² v'^{D²} / Z,          (so V(t;v)=V(t,w), V(t;1)=P(t))
   Var_{v'}(t) = Σ_D a_D (D²)² v'^{D²}/Z − V(t;v')².
```
Set `Φ(v') := Δ²V(s;v') = V(s;v') − 2V(s+1;v') + V(s+2;v')`, a scalar `C¹` function on `[v,1]`.

**Step 1 (algebraic derivative — no analysis).**
```
   dV(t;v')/dv' = Var_{v'}(t) / v'      ⟹     Φ'(v') = (1/v') · Δ²Var_{v'}(s).
```
This is the quotient-rule derivative of a finite sum of monomials `v'^{D²}`; `1/v'` factors out of `Δ²`
because it is `t`-independent. **Verified:** central-difference vs analytic `< 1.5·10⁻²²`.

**Step 2 (uniform derivative bound — this is where Lemma C enters).** For every `v'∈[v,1]`,
```
   Φ'(v') = (1/v')Δ²Var_{v'}(s)  ≤  (1/v)·Δ²Var_par(s)  =: M.
```
Case `Δ²Var_{v'}≥0`: `(1/v')Δ²Var_{v'} ≤ (1/v')Δ²Var_par ≤ (1/v)Δ²Var_par` (Lemma C, then `1/v'≤1/v`,
`Δ²Var_par≥0`). Case `Δ²Var_{v'}<0`: `(1/v')Δ²Var_{v'} < 0 ≤ (1/v)Δ²Var_par`. **Verified:**
`max_{s=7..60, w, v'∈[v,1]} (Φ'(v') − M) = −1.83 ≤ 0`.

**Step 3 (mean-value inequality — constructively valid, no `∃ξ`, no `∫`).**
```
   Δ²e(s) = Φ(1) − Φ(v)  ≤  M·(1−v)  =  ((1−v)/v)·Δ²Var_par(s).
```
(`e(t)=V(t;1)−V(t;v)` and `Δ²` is linear ⇒ `Δ²e=Φ(1)−Φ(v)`.) The MVI is the standard fact
`Φ'≤M on [v,1] ⟹ Φ(1)−Φ(v)≤M(1−v)`, equivalently `x ↦ Mx−Φ(x)` is non-decreasing (nonneg derivative).

**Step 4 (rational finish — pure algebra).**  `(1−v)/v = (1−√w)/√w ≤ (1−w)/2w` (⟺ `√w≤1`), so
```
   Δ²e(s) ≤ ((1−√w)/√w)Δ²Var_par ≤ ((1−w)/2w)Δ²Var_par = ((1−w)/2w)·96K/175,
```
and `≤ 12/5 ⟺ (1−w)/w ≤ 35/(4K)` — **exactly the existing certificate threshold.** (Using the tighter
`(1−√w)/√w` directly gives a slightly larger parabolic region; either is fine.)

**Verified end-to-end** (`s=7..60`, `w∈[1/2,1]`, fine grid): `Δ²e/[(1−v)/v·Δ²Var_par] ≤ 0.714`;
`Δ²e/[(1−w)/2w·Δ²Var_par] ≤ 0.905`. On the certificate region `max Δ²e = 0.577` vs `12/5` (margin
`1.82`).

---

## 2. Lemma C — the single crux (shared by all routes; already the certificate's obligation)

```
   (C)   Δ²Var_{v'}(s) ≤ Δ²Var_par(s)      for all v'∈(0,1] and all s≥7.
```
`Var_{v'}(s)` is a ratio of finite sums over `|D|≤s`; at `v'=1` it equals `Var_par(s)` exactly. This is
a bounded, explicit, `NO-infinite-theta` inequality — the natural proof is discrete log-concavity /
Karlin sign-variation of the tilted weights `a_D v'^{D²}` (the certificate's stated route). **Verified:**
`Δ²Var_{v'}−Δ²Var_par ≤ 0` throughout, `→0⁻` only as `v'→1`. (`Var_par(t)=8t(t−1)(t+4)(t+5)/175`;
`Δ²Var_par(s)=96(s²+6s+7)/175` exact.)

This route consumes Lemma C in *exactly the same strength* as the integral route (a uniform-in-`v'`
derivative-level bound). It adds nothing beyond it.

---

## 3. Supporting discrete tool — Lipschitz-covariance (independent magnitude check, confirms the constant is sharp)

Under the **fixed untilted ensemble** `⟨·⟩₀ ∝ a_D` (which is `w`-independent!):
```
   e(t) = − Cov₀(D², v^{D²}) / ⟨v^{D²}⟩₀ = Cov₀(D², 1−v^{D²}) / ⟨v^{D²}⟩₀.
```
Since `f(x)=1−v^x` is increasing with `0 ≤ f'(x) = −v^x ln v ≤ −ln v ≤ (1−v)/v`, the elementary
monotone-covariance/Lipschitz bound `Cov(X,f(X)) ≤ (Lip f)·Var(X)` gives the **fully discrete, rational**
```
   Cov₀(D², 1−v^{D²}) ≤ ((1−v)/v) · Var_par(t).      [verified: ratio ≤ 0.862, s=7..60]
```
This bounds `e(t)` (per window), **not** `Δ²e`, so it cannot replace §1 (see §0). Its value: it proves
the *magnitude* independently and shows the constant `(1−v)/v ~ λ/2` is essentially sharp
(`Δ²e/[(λ/2)Δ²Var_par] → 1` as `w→1`), so no materially smaller constant exists — the MVI route is not
lossy.

---

## 4. EXACT integration-free identity for `e` (the "already-integrated" tilt sum)

With `v=√w` and `1−v^{D²}=(1−v)Σ_{i=0}^{D²−1}v^i` (a `telescope_sum` instance), plus the vanishing
parabolic part `Σ_D a_D(D²−P(t))=0` (exact rational identity), swapping the order of summation gives the
**exact, transcendental-free closed form**
```
   e(t) = (1−v)/S0(t) · Σ_{j=0}^{t²−1} v^j · G_t(j),
   G_t(j) := Σ_{D: D²≤j} a_D (P(t)−D²)  ≥ 0,     S0(t)=Σ_D a_D v^{D²}.
```
`G_t(j)≥0` because it is a partial sum of a sequence with total `0` ordered by `D²` (head sums `≤0`).
Companion identity: `Var_par(t) = Σ_{j=0}^{t²−1} G_t(j)/S0⁰(t)`, `S0⁰=Σ_D a_D`. **Verified exact**
(`|e_disc−e| < 10⁻³²`, `s≤60`; `G_t(j)≥0`; both identities exact rationals).

This is the discrete analog of `e=∫_v^1 Var_{v'}/v' dv'` and needs **only** `CReal.sqrtFrom`,
`telescope_sum`, and finite rational algebra — zero analysis. It is the recommended way to *define/represent*
`e` if a derivative-free object is wanted.

---

## 5. Why §4 does not, by itself, close `Δ²` (honest limitation of the pure-discrete route)

`e(t)` and `Var_par(t)` share the numerators `G_t(j)` but carry **different denominators**
`S0(t)` vs `S0⁰(t)` and **different level-weights** `(1−v)v^j` vs `1`. Consequently
`Δ²e = (1−v)Σ_j v^j Δ²[G_t(j)/S0(t)]`, and the per-level second differences `Δ²[G_t(j)/S0(t)]`
**have mixed signs** (verified: roughly half positive, half negative, magnitudes `~10²`), whose near-total
cancellation is precisely the `O(1/s²)` effect of §0. There is **no sign-definite per-level ("discrete
Lemma C") inequality** on this representation. A pure-discrete-value proof of `Δ²g≥0`
(`g=(1−w)/2w·Var_par−e`) therefore does not reduce to Lemma C; it would be a *separate*, uniform-in-`s`
finite-algebra inequality (an SOS on the common-denominator numerator of `Δ²g`, made uniform in `s`) —
research-grade and not recommended. The MVI route of §1 sidesteps this by bounding the *derivative*
`Φ'` (uniformly, via Lemma C) instead of the mixed-sign value.

---

## 6. Lean feasibility & precise lemma list

**Recommended = §1 (MVI in `v'`).** Feasibility: **good.** No integral, no FTC-with-budget, no
`CReal.exp`/`CReal.log` (the codebase treats those as heavy bespoke atoms). Transcendental surface = one
`CReal.sqrtFrom` (present and well-developed). New analytic lemma needed: the **mean-value inequality**
`f'≤M on [a,b] ⟹ f(b)−f(a)≤M(b−a)` for a scalar `Q'`/`CReal`-valued `C¹` function of a rational/real
parameter — constructively valid, far lighter than integration; check whether a "nonneg-derivative ⇒
monotone" lemma already exists (the `ChebOrthoFTCEstimate`/`telescope_sum` machinery is adjacent).

Precise lemma list:

1. **`v=√w` reduction** — `w^{D²/2}=(√w)^{D²}`, integer exponent. (`CReal.sqrtFrom`; trivial.)
2. **Vanishing parabolic part** — `Σ_{|D|≤t} a_D (D²−P(t)) = 0`, `P(t)=t(t+4)/5`. (Finite rational
   identity, both parities. **Verified exact.**)
3. **Exact `Var_par`** — `Var_par(t)=8t(t−1)(t+4)(t+5)/175`, `Δ²Var_par(s)=96(s²+6s+7)/175 ≥ 0`.
   (Finite rational; already in certificate.)
4. **Tilt derivative (algebraic)** — `d/dv'[V(t;v')] = Var_{v'}(t)/v'`, hence
   `Φ'(v')=(1/v')Δ²Var_{v'}(s)`. (Quotient rule on a finite polynomial in `v'`. **Verified numerically.**)
5. **LEMMA C (crux)** — `Δ²Var_{v'}(s) ≤ Δ²Var_par(s)` for all `v'∈(0,1]`, `s≥7`. (Finite ensemble
   inequality; already the certificate's sole obligation. **Verified.**)
6. **Uniform `Φ'` bound** — from 4+5+`Δ²Var_par≥0`+`1/v'≤1/v`: `Φ'(v') ≤ (1/v)Δ²Var_par(s)` on `[v,1]`.
   (**Verified**, margin `≥1.83`.)
7. **Mean-value inequality** — `Δ²e(s)=Φ(1)−Φ(v) ≤ ((1−v)/v)Δ²Var_par(s)`. (Constructive MVI +
   `Δ²e=Φ(1)−Φ(v)` from linearity. **Verified**, ratio `≤0.714`.)
8. **Rational finish** — `(1−√w)/√w ≤ (1−w)/2w`; then `((1−w)/2w)·96K/175 ≤ 12/5 ⟺ (1−w)/w ≤ 35/(4K)`.
   (Elementary rational algebra.)

**Optional / alternative:**
- **§4 exact discrete identity** (`e = (1−v)/S0·Σ_j v^j G_t(j)`, `G_t(j)≥0`) — for a derivative-free
  *representation* of `e`; needs only `telescope_sum`+`sqrtFrom`+algebra. **Verified exact.** Does not
  close `Δ²` alone (§5).
- **§3 Lipschitz-covariance** — independent per-window magnitude bound + constant-sharpness witness.
  Fully discrete/rational. **Verified.**

**Not recommended:** the original `∫₀^λ ½Δ²Var_μ dμ` route. Its assembly is clean on paper but requires
a bespoke constructive integral / FTC-with-error-budget over a `CReal`-parametrized family (heavier than
`ChebOrthoFTCEstimate`) plus a `CReal.exp` tilt — all of which §1 avoids. §1 uses Lemma C at identical
strength.

---

## 7. Verification log (mpmath, dps 35–40; scripts in job tmp `tilt*.py`)

| claim | check | result |
|---|---|---|
| `Σ a_D(D²−P)=0` (both parities) | exact `Fraction` | `=0`, `t=7,8,40,41` |
| exact discrete id `e=(1−v)Σv^jG_t(j)/S0`, `G_t(j)≥0` | dps 40 | `|Δ|<10⁻³²`, `min G=0`, `s≤60` |
| `Var_par=Σ_j G_t(j)/S0⁰` | dps 35 | exact |
| covariance form `e=Cov₀(D²,1−v^{D²})/⟨v^{D²}⟩₀` | dps 35 | `|Δ|<10⁻¹⁵` |
| `d V/dv' = Var_{v'}/v'` (⇒ `Φ'=(1/v')Δ²Var_{v'}`) | central diff | `<1.5·10⁻²²` |
| **Lemma C** `Δ²Var_{v'}≤Δ²Var_par`, `v'∈(0,1]` | dps 35 | `≤0` (`→0⁻` at `v'→1`) |
| **uniform `Φ'≤(1/v)Δ²Var_par`** on `[v,1]` | dps 35 | max diff `−1.83 ≤0` |
| Lipschitz-cov `Cov₀ ≤ (1−v)/v·Var_par` | dps 35 | ratio `≤0.862` |
| `e` convex in `t` (`Δ²e≥0`) | dps 35–40 | `Δ²e∈[0.153,0.577]` |
| **MAIN** `Δ²e ≤ (1−√w)/√w·Δ²Var_par`, `s=7..60`, `w∈[½,1]` | dps 35 | ratio `≤0.714` |
| `Δ²e ≤ (1−w)/2w·Δ²Var_par` (target) | dps 40 | ratio `≤0.905` |
| `Δ²e` on region `(1−w)/w≤35/(4K)` vs `12/5` | dps 40 | `max 0.577`, margin `1.82` |
