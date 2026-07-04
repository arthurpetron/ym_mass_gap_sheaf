# Continuum-floor inequality: `G_odd(w) − G_even(w) ≤ 1` — PROVED with exact slack

## Verdict

**PROVED.** The inequality holds for all `w ∈ (0,1)` because of the closed-form identity

```
    Var_o(j) − Var_e(j)  =  (1/4) · ϑ₄(r)⁴ ,        r = w² ,   ϑ₄(r) = Σ_{n∈ℤ} (−1)ⁿ rⁿ² .
```

Since `0 < ϑ₄(r) < 1` for every `r ∈ (0,1)`, we get `Var_o − Var_e = (1/4)ϑ₄⁴ ∈ (0, 1/4)`, i.e.
`Var_o − Var_e ≤ 1/4`, which is exactly `G_odd − G_even ≤ 1`. In fact, in the cleanest form,

```
    G_odd(w) − G_even(w)  =  ϑ₄(r)⁴  ∈ (0, 1] ,     r = w² ,
```

so the whole target function is literally a fourth power of a Jacobi theta constant:
`→ 1` as `w→0` (ϑ₄→1), `→ 0` as `w→1` (ϑ₄→0), monotone in between. **The bound is tight only in the limit `w→0`.**

Everything below is confirmed numerically to 40–50 digits (`computations/continuum_floor_theta4.py`).

---

## 1. Setup and the reduction (recap)

With `D = 2j` (even) / `D = 2j+1` (odd) and `r = w²`, the discrete Gaussian `w^{D²/2} = r^{D²/4}` gives
`G_even = 4·Var_e`, `G_odd = 4·Var_o`, where `Var_e`, `Var_o` are the variances of `j` under the weights
`rʲ²` (integer-centred) and `r^{(j+1/2)²}` (half-integer-centred). In theta language, with the nome `q = r`,

```
    Var_e = q d/dq log ϑ₃(q) ,     Var_o = q d/dq log ϑ₂(q) ,
    ϑ₃ = Σ q^{n²},   ϑ₂ = Σ q^{(n+1/2)²} = 2q^{1/4}Σ_{n≥0} q^{n(n+1)} .
```

Hence

```
    Var_o − Var_e = q d/dq log(ϑ₂/ϑ₃) = (1/2) d log k / d log q ,     k = (ϑ₂/ϑ₃)² (the elliptic modulus),
```

and the target `Var_o − Var_e ≤ 1/4` is exactly `d log k/d log q ≤ 1/2`, i.e. **`k/√q` decreasing** — the classical monotonicity of the elliptic modulus. The identity below makes this quantitative.

## 2. The identity (the proof)

**Claim.** `q d/dq log(ϑ₂/ϑ₃) = (1/4) ϑ₄⁴`  (equivalently `d log k / d log q = (1/2)ϑ₄⁴`).

**Proof (theta-constant ODEs + Jacobi, E₂ cancels).** Write `δ = q d/dq`. The heat equation for the
Jacobi theta function, evaluated at `z = 0` together with the logarithmic derivatives of the triple-product
representations, gives the three standard theta-constant ODEs (`E₂` = the weight-2 Eisenstein series):

```
    δ log ϑ₂ = (1/12)(E₂ + ϑ₃⁴ + ϑ₄⁴)
    δ log ϑ₃ = (1/12)(E₂ + ϑ₂⁴ − ϑ₄⁴)
    δ log ϑ₄ = (1/12)(E₂ − ϑ₂⁴ − ϑ₃⁴)
```

Subtracting the first two, the (otherwise non-modular) `E₂` **cancels**:

```
    δ log(ϑ₂/ϑ₃) = (1/12)(ϑ₃⁴ − ϑ₂⁴ + 2ϑ₄⁴).
```

Jacobi's identity `ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴` gives `ϑ₃⁴ − ϑ₂⁴ = ϑ₄⁴`, hence
`δ log(ϑ₂/ϑ₃) = (1/12)(3ϑ₄⁴) = (1/4)ϑ₄⁴`.  ∎

(The sibling identities `δ log(ϑ₃/ϑ₄) = (1/4)ϑ₂⁴` and `δ log(ϑ₂/ϑ₄) = (1/4)ϑ₃⁴` were also verified;
they are mutually consistent with Jacobi, since `(1/4)ϑ₂⁴ + (1/4)ϑ₄⁴ = (1/4)ϑ₃⁴`.)

Combining with §1: `Var_o − Var_e = (1/4)ϑ₄⁴`, and `G_odd − G_even = 4(Var_o − Var_e) = ϑ₄⁴`.

## 3. Why `0 < ϑ₄(r) < 1` (fully elementary / constructive)

Jacobi triple product:  `ϑ₄(r) = ∏_{n≥1} (1 − r^{2n})(1 − r^{2n−1})²`.
For `r ∈ (0,1)` every factor lies in `(0,1)`, so the product is a positive number `< 1`.
(Positivity and the `< 1` bound need no cancellation — it is a product of terms in `(0,1)`.) Therefore
`ϑ₄⁴ ∈ (0,1)` and `Var_o − Var_e = (1/4)ϑ₄⁴ ∈ (0, 1/4)`. This step is the only one the final inequality
strictly needs; it is rational/CReal-friendly (finite partial products bracket `ϑ₄` from above/below).

## 4. Exact slack, sign, and tightness

```
    1/4 − (Var_o − Var_e) = (1/4)(1 − ϑ₄(r)⁴)  >  0 ,     r ∈ (0,1),
```

with an explicit **integer** Lambert (divisor) series (verified to 40 digits):

```
    ϑ₄(r)⁴ = 1 + 8 Σ_{n≥1} (−1)ⁿ s(n) rⁿ ,     s(n) = Σ_{d | n, 4∤d} d
           = 1 − 8r + 24r² − 32r³ + 24r⁴ − 48r⁵ + 96r⁶ − ⋯
```

so the slack `= (1/4)(1 − ϑ₄⁴) = 2r − 6r² + 8r³ − 6r⁴ + ⋯`. The slack is `Θ(2r)` as `r→0`
(bound tight: `Var_o − Var_e ↑ 1/4`), and `↑ 1/4` as `r→1` (bound loosest). Because `ϑ₄` is strictly
decreasing on `(0,1)`, `G_odd − G_even = ϑ₄⁴` is strictly decreasing, `1 → 0`.

Worst case (closest to the bound): `r → 0`, where `Var_o − Var_e = 1/4 − 2r + O(r²)`. The inequality is
**never** violated on the open interval and is attained only in the limit.

## 5. Finite-lattice truncation (the real residual, |D| ≤ t)

The `≤ 1` bound is a **`t → ∞` (continuum) statement**; at finite `t` it can fail when the lattice is
shorter than a few correlation lengths (`ξ ≈ 1/√(−log w)`):

| w    | ξ≈1/√(−log w) | smallest t with `G_odd−G_even ≤ 1` | value at t=3 |
|------|---------------|-------------------------------------|--------------|
| 0.2  | ~0.7          | already ≤1 at t=3                   | 0.716        |
| 0.5  | ~1.2          | t=3                                 | 0.137        |
| 0.8  | ~2.1          | t=5 (t=3 gives **1.079 > 1**)       | 1.079        |
| 0.95 | ~4.4          | t=15 (t≤9 give up to **2.39 > 1**)  | 2.017        |

**Rule of thumb:** the bound holds once `t ≳ 3ξ = 3/√(−log w)`; beyond that, convergence to the limit
`ϑ₄⁴` is Gaussian-fast (boundary term `~ t² w^{t²/2}`, e.g. gap-to-limit `< 10⁻³³` by `t = 9` at `w = 0.2`).
So for the mass-gap residual in its intended `t → ∞` regime the bound is safe; a finite-`t` Lean statement
must carry the hypothesis `t ≳ 3/√(−log w)` (or use the closed-form limit plus an explicit tail bound).

## 6. Lean-friendliness — recommended proof skeleton

The bound reduces to two ingredients, in increasing depth:

1. **`0 < ϑ₄(r) < 1`** — trivial: finite truncations of the triple product `∏(1−r^{2n})(1−r^{2n−1})²`
   are products of rationals in `(0,1)`, monotone in the truncation, bracketing `ϑ₄`. (constructive)
2. **The identity `Var_o − Var_e = (1/4)ϑ₄⁴`** — the one non-trivial input. Two routes:
   - *Conceptual:* the three theta-constant ODEs (§2) + Jacobi `ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴`, with `E₂` cancelling
     in the difference. Needs the heat-equation ODEs as lemmas.
   - *Constructive/series:* prove the equivalent **q-series identity** directly —
     `q d/dq log(ϑ₂/ϑ₃) = 1/4 + 2 Σ_{n≥1}[ 2n r^{2n}/(1+r^{2n}) − (2n−1) r^{2n−1}/(1+r^{2n−1}) ]` (log-deriv of
     the triple products) equals `(1/4)ϑ₄⁴ = 1/4 + 2 Σ_{n≥1}(−1)ⁿ s(n) rⁿ`. This is a comparison of two
     explicit Lambert series with **integer** coefficients (a divisor identity), term-checkable and
     CReal-friendly, avoiding `E₂`.

If only the inequality (not the exact slack) is wanted, one may instead aim directly at
`k/√q` **decreasing** ⇔ `Σ_{(n,m)∈ℤ²}[n(n+1) − m²] r^{n(n+1)+m²} ≤ 0`; but no *manifestly-signed*
elementary rearrangement of that lattice sum was found — every attempted involution/product route
reduces back to the same theta identity. **The `(1/4)ϑ₄⁴` identity is the smallest rigorous core**, and it
delivers the bound, the exact slack, and tightness simultaneously.

## 7. Numerical certification

`computations/continuum_floor_theta4.py` (mpmath, 50 dps): the identity `Var_o − Var_e = (1/4)ϑ₄⁴` holds
to `< 10⁻⁵⁰` across `r ∈ {10⁻⁸, 0.01, 0.1, 0.3, 0.5, 0.7, 0.9}`; the theta-constant ODE, the triple-product
positivity, and the integer Lambert series are each independently verified to `< 10⁻⁴⁰`.
