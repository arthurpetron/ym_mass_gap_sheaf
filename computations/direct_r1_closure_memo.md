# Direct uniform closure of R1 — analysis memo

**Residual R1.** Prove `Δ²_t V(t) ≥ −2` for all `t = s ≥ 0` and all `w ∈ [0,1)`, where
`V(t) = ⟨D²⟩` under `ρ_t(D) ∝ (M²−D²) w^{D²/2}`, `D ≡ t (mod 2)`, `|D| ≤ t`, `M = t+2`.
Exactly `V(t) = num_t/den_t`, `den_t = Σ_D (M²−D²) w^{D²/2}`, `num_t = Σ_D D²(M²−D²) w^{D²/2}`.

This memo is the **independent direct hedge** (not the continuum/elliptic-modulus route). Bottom
line: R1 is confirmed true (high-precision, `s ≤ ~300`) and reduced to a **single sharp uniform
envelope with an exact extremiser**, plus several structural simplifications that reshape what a
uniform ∀s proof must do. The residual is not fully closed; the surviving wall is named precisely.

Pilot: `computations/direct_r1_closure_pilot.py`.

---

## 1. Exact three-body representation ⇒ a convexity reformulation

Clearing denominators, `slack_s := den_s den_{s+1} den_{s+2} · (Δ²V(s)+2)` has the **exact
three-body form** (verified symbolically, `s ≤ 5`):

```
slack_s = Σ_{D0,D1,D2} ( D0² + D2² − 2 D1² + 2 ) · c_s(D0) c_{s+1}(D1) c_{s+2}(D2),
c_t(D) = coeffW((t−D)/2) · coeffW((t+D)/2) ≥ 0,   D0≡s, D1≡s+1, D2≡s+2 (mod 2).
```

The mass factors `c` are nonnegative; the kernel `f = D0²+D2²−2D1²+2` changes sign, so this is
*not* termwise nonnegative. Summing out the masses gives the clean equivalent statement

> **R1 ⇔ Δ²V + 2 ≥ 0 ⇔ `U(t) := V(t) + t²` is discretely convex in `t`** (since `Δ²(t²) = 2`).

This is Lean-friendly (a convexity of a single scalar sequence) and is the cleanest way to state
R1 for a future formalization.

## 2. Parity split — the key empirical structure

Numerically (high precision, `s` up to 300), `Δ²V+2` splits sharply by parity:

| parity | behaviour of `min_w (Δ²V+2)` | binding regime |
|--------|------------------------------|----------------|
| **odd `s`** | `≥ 12/7 ≈ 1.714` (min at `w = 1/√2`); comfortable | none |
| **even `s`** | `→ 0⁺` as `w → 0`, else positive | **only `w → 0`** |

- **Odd `s`:** exact worst case is `s=1`, `min_w (Δ²V(1)+2) = 12/7` at `w=1/√2`, i.e.
  `Δ²V(1) ≥ −2/7 > −2`. All larger odd `s` have a *larger* margin (→ the continuum value). So the
  odd family is uniformly bounded away from the floor and is **not** the obstruction.
- **Even `s`:** the constant term of `Δ²V+2` cancels exactly (the odd neighbour has `V(odd) → 1`,
  and `−2·1 + 2 = 0`), leaving the leading behaviour
  `Δ²V + 2 = (C(s)+C(s+2)) w² + O(w⁴)`, `C(t) = 8t(t+4)/(t+2)² ∈ [6,8)`,
  so the leading coefficient is uniformly in `[12,16)` — bounded away from 0. The binding-ness at
  `w→0` is only that the whole quantity → 0; its *shape* is a positive `w²` with a controlled tail.

Consequence: **the entire difficulty of R1 lives in the even family near `w = 0`.**

## 3. Sharp uniform envelope (main result)

All `s` and both parities satisfy a **single manifestly-nonnegative minorant**:

> **`Δ²V(s) + 2  ≥  (144/25) · w²(1 − w²)`  for all `s ≥ 0`, `w ∈ [0,1]`.**

- Manifestly `≥ 0` on `[0,1]`, so it **implies R1** with margin.
- **Sharp:** equality holds only at `(s = 0, w² = 1/6)`; `144/25 = 5.76` is the exact global
  infimum of `(Δ²V+2)/(w²(1−w²))` over all `s, w`. Verified: global inf `= 5.7600003…` attained at
  `s = 0`.
- Exact base cases:
  - `s=0`: `Δ²V(0)+2 = 12w²/(2+3w²)`; ratio to `w²(1−w²)` is minimized at `w²=1/6`, value `144/25`.
  - `s=1`: ratio min `= 48/7 ≈ 6.857` at `w = 1/√2`.
  - `s=2`: ratio min `≈ 7.208` at `w ≈ 0.731`.
- The ratio `g_s := inf_w (Δ²V+2)/(w²(1−w²))` is **monotone increasing in `s`** (interleaved across
  parities): `5.76 (s0) < 6.857 (s1) < 7.208 (s2) < 7.560 (s3) < … → 8`.

## 4. Structural verdict: the binding case is finite small-`s`, not the continuum

The limit `s → ∞` gives ratio `→ 8`, corresponding to the theta statement
`G_odd(w) − G_even(w) ≤ 1` (continuum parity-variance gap; `Φ := 2(1−(G_o−G_e)) ≈ 8 w²(1−w²)` near
the worst `w`). Since `8 > 144/25`, **the continuum is not the extremiser** — the tight obligation
is the *smallest* `s`, and in fact `s = 0`. This is a genuinely useful orientation: a pure
continuum/elliptic route (the parallel team) proves the `s→∞` face but *cannot* certify the sharp
constant; the finite small-`s` cases are strictly tighter and must be handled directly (they are
exact rationals, hence trivially checkable base cases).

This yields the cleanest available **conditional closure**:

> **R1 ⟸ [`g_s = inf_w (Δ²V+2)/(w²(1−w²))` is nondecreasing in `s`] + [`g_0 = 144/25`, `g_1 = 48/7`
> checked exactly].**

## 5. Strategy-by-strategy honest report

**(1) Bernstein-coefficient recursion (the requested main path).** The native-degree Bernstein
certificate exists per `s` (re-confirmed), and for even `s ≥ 4` even the *increment*
`(B_s(w) − B_s(0))/w²` has all-nonnegative native Bernstein coefficients (`s=2` is a lone base
case) — a real sharpening. But **no closed form / stable recursion for the coefficients was found**:
they scale `~s²` and the even/odd chains `(s, s+2)` vs `(s+1)` are coupled by the three-body kernel
(different parity levels), so there is **no single-parity recursion** for `slack_s`. The mediant
recursion `V(t+2)=λ_t V(t)+(1−λ_t)G(t+2)` couples same parity only, so it cannot generate `Δ²V(s)`
(which mixes the even and odd chains). *Obstruction: coupled two-chain structure blocks a
nonnegativity-preserving one-step recursion.*

**(2) Two-regime split.** Realized concretely: even `s` is binding only on `[0, w*]` with leading
coefficient `≥ 12`; odd `s` and the region near `w→1` carry a uniform margin (`≥ 12/7`). The sharp
envelope in §3 is the clean unification of both regimes into one inequality.

**(3) Parity split.** Fully carried out (§2). Even `s`: min at `w=0`, reduces to `B_s(w) ≥ B_s(0)`;
the increment is native-Bernstein-nonnegative for `s≥4`. Odd `s`: interior margin, exact floor
`12/7` at `s=1`. No uniform closed pattern for the even increment coefficients.

**(4) Uniform sufficient condition / lower envelope.** **Succeeded** as the sharp minorant
`(144/25) w²(1−w²)` (§3), with the exact extremiser `(0, 1/6)`. This is the most Lean-actionable
deliverable: a single polynomial inequality with a manifestly-nonnegative RHS.

## 6. Surviving wall (smallest uniform residual)

Everything reduces to one of two equivalent uniform statements, both verified numerically but not
proved ∀s by elementary means:

- **(A)** `Δ²V(s)+2 ≥ (144/25) w²(1−w²)` for all `s` (a polynomial inequality per `s` with the same
  no-closed-form Bernstein obstruction as R1 itself), or
- **(B)** the monotonicity `g_{s} ≤ g_{s+1}` of the interior-minimised ratio (base cases `g_0, g_1`
  are exact rationals). Pointwise monotonicity `Δ²V(s+2;w) ≥ Δ²V(s;w)` **fails**, but only near
  `w→1` where `Δ²V+2` is large (`≥ 1.5`); the interior minimiser near `w = 1/√2` is monotone. A
  region-restricted monotonicity `[0, w_b]` + comfortable-margin on `[w_b, 1]` is the plausible
  route to (B).

Both (A) and (B) are strictly stronger, sharper targets than the raw R1, with an exactly known
extremiser — which is the right shape to hand to a subsequent focused proof or a `CReal`/Lean
certificate that only needs to verify finitely many exact base cases plus one monotonicity lemma.

## Numerical confirmations (all at `mp.dps ≥ 30–50`)
- Three-body form `=` cleared slack, `s ≤ 5` (symbolic, exact).
- `min Δ²V` over all tested `(s,w)` `= −1.9999985` (floor `−2` approached at even `s`, `w→0`).
- Global `inf_{s,w} (Δ²V+2)/(w²(1−w²)) = 5.7600003 = 144/25`, attained at `s=0`, `w²=1/6`.
- `g_s` increasing: `5.76, 6.857, 7.208, 7.560, 7.773, … → 8`.
- Odd-family floor `min_w(Δ²V(1)+2) = 12/7` exact.
