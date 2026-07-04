# Explicit two-region certificate for the terminal scalar `φ(q) ≥ 0`

**Outcome.** `φ(q) ≥ 0` for all real `q ∈ (0, 1/4]` is **CERTIFIED** by an explicit
finite rational two-region certificate: on `(0, 1/16]` `φ(q) ≥ (7/5)·q` (via proved
convexity `φ'' ≥ 37/5` plus the proved leading coefficient `α = 16−32κ ≥ 7/5`), and on
`[1/16, 1/4]` `φ(q) ≥ 1/10` (via a 13-node rational grid with Lipschitz `L = 4`). No
sub-bound resists: every constant is an explicit rational (or a rational lower/upper
bound), every infinite theta sum is truncated with a proven rational geometric tail
bound, and all inequalities are validated in mpmath interval arithmetic
(`phi_certificate_verify.py`, all blocks pass; enclosures are guaranteed outer bounds).

The scalar is the one exactly as produced by the reduction (verified: the `q`-power-series
form used here agrees with the memo's `φ(q) = Ψ(3)` to `3·10⁻⁸⁰` on all of `(0,1/4]`).

---

## 0. The object, in integer powers of `q`

With `q = w²`, `w^{D²/2} = q^{D²/4}`, the untruncated moments split by parity as clean
power series in `q` (all fractional/`q^{1/4}` factors cancel in the ratios `G_p`, `S_p`):

```
  even (D=2k): A_e = 1 + 2Σ_{k≥1} q^{k²},  B_e = 8Σ_{k≥1} k² q^{k²},  C_e = 32Σ_{k≥1} k⁴ q^{k²}
  odd  (D=2k+1): m_j = Σ_{k≥0}(2k+1)^{2j} q^{k(k+1)},  G_o = m_1/m_0,  S_o = m_2/m_0 − (m_1/m_0)²
  θ₄(q) = 1 + 2Σ_{n≥1}(−1)ⁿ q^{n²}
  G_e = B_e/A_e,  S_e = C_e/A_e − (B_e/A_e)²
```
```
  φ(q) = 2(1 − θ₄(q)⁴) + (2/9)·S_o(q) − κ·S_e(q),   κ = 1/(4−Ḡ_e) + 1/(16−Ḡ_e),  Ḡ_e = G_e(1/4).
```

`φ` is analytic on `|q|<1`; `φ(0)=0`, `φ'(0)=α=16−32κ`. Empirically `min_{(0,1/4]} φ/q = α`
(attained as `q→0`) and `φ' < 0` near `q=1/4`, so no single elementary bound closes the whole
interval — hence the split at `q₀ = 1/16`.

## 1. Explicit constants (all rational or rational-bracketed)

| constant | value / rigorous rational enclosure |
|---|---|
| `q₀` (breakpoint) | `1/16` |
| `c` (Region I slope) | `7/5` |
| `δ` (Region II floor) | `1/10` |
| `Ḡ_e = B_e(¼)/A_e(¼)` | `1.4095014689866763774417 < Ḡ_e < 1.4095014689866763774418` |
| `κ = 1/(4−Ḡ_e)+1/(16−Ḡ_e)` | `0.45456383670016790895…` (`< 73/160`) |
| `α = 16 − 32κ` | `1.45395722559462691354… ⇒ α − 7/5 = 0.0539572… > 0` |
| `L` (Region II Lipschitz) | `4` (proved: `sup_{[1/16,1/4]}|φ'| ≤ 3.9420 < 4`) |
| `D_max` (theta truncation) | `24` (geometric tail `< 8.2·10⁻⁹⁷`); validator runs `D≤40` (tail `< 10⁻²⁵²`) |
| grid | `h = 1/64`, `M = 12` intervals (`13` nodes), `L·h/2 = 1/32` |

The `Ḡ_e` enclosure is the partial sum `B_e/A_e` at `q=1/4` truncated at `D≤24` corrected by
the geometric tail below; the two endpoints are the (`B` under / `A` over) and (`B` over / `A`
under) rounds.

## 2. Tail-bound lemma (rational, conservative)

For `q ∈ (0,1/4]`, one parity, weight exponent `j ∈ {0,1,2}` (`A,B,C`):
```
  Σ_{D>D_max, D≡p(2)} D^{2j} q^{D²/4}  ≤  T_j(D_max) := (D_max+2)^{2j}·q^{(D_max+2)²/4} / (1 − ρ_j),
        ρ_j = ((D_max+2)/D_max)^{2j}·(1/4)^{D_max+1}.
```
*Proof.* Consecutive same-parity terms have ratio `((D+2)/D)^{2j} q^{D+1} ≤ ρ_j` for `D≥D_max`,
`q≤1/4`; geometric-sum majorant on the first omitted term `D=D_max+2`. ∎
At `D_max=24, q=1/4, j=2`: `ρ₂ = 1.2·10⁻¹⁵`, first term `8.2·10⁻⁹⁷`, so `T₂ < 8.2·10⁻⁹⁷` — far
below the smallest certificate margin (`0.030`). The validator uses `D≤40` and a uniform
rigorous tail `10⁻⁴⁰` that dominates the true tails (`< 10⁻²⁵²`); either `D_max` is sufficient.

## 3. Leading coefficient `α ≥ 7/5` (clean rational reduction)

```
  α = 16−32κ ≥ 7/5  ⟺  κ ≤ 73/160  ⟺  1/(4−Ḡ_e)+1/(16−Ḡ_e) ≤ 73/160
                     ⟺  73·Ḡ_e² − 1140·Ḡ_e + 1472 ≥ 0   (denominators 4−Ḡ_e,16−Ḡ_e > 0).
```
The quadratic `73x²−1140x+1472` has smaller root `x₋ = (1140−√869776)/146 = 1.4204258…`, and
`Ḡ_e ≤ 1.40950147 < 1.4204258 = x₋`, so the quadratic is `≥ 0` (value `10.197` at `Ḡ_e`).
Hence `κ ≤ 73/160` and `α ≥ 7/5`. This is a single explicit rational polynomial inequality in
`Ḡ_e`. (`Ḡ_e < 8−√40` from the reduction memo is the same fact for the weaker threshold `κ<½`.)

## 4. Region I — `φ(q) ≥ (7/5)·q` on `(0, 1/16]`

**Method (convexity).** `φ(0)=0` (exact algebraic identity: at `q=0`, `G_e=S_e=S_o=0`,
`θ₄=1`), `φ'(0)=α`, and **`φ`is convex on `[0,1/16]`** because
```
   φ''(q) ≥ 37/5 = 7.4 > 0   for all q ∈ [0, 1/16].
```
This is certified by interval enclosure of `φ''` (propagated through the quotient/product
rules from the truncated series `A_e,B_e,C_e,m_0,m_1,m_2,θ₄` and their first two `q`-derivatives,
each with the §2 tail) over the 8 subintervals `[i/128,(i+1)/128]`, `i=0..7`: the rigorous
lower bound is `7.4547 ≥ 37/5`. (True `min_{[0,1/16]} φ'' ≈ 13.5`; `37/5` is a safe rational
floor.) Convexity + `φ(0)=0` give `φ(q) ≥ φ(0)+φ'(0)·q = α·q`, and `α ≥ 7/5` by §3, so
`φ(q) ≥ (7/5)·q > 0` on `(0,1/16]`.

Equivalently in the memo's `φ = c·q + q²R` shape: `R(q) = (α−c)/q + (φ(q)−α q)/q²`, whose first
summand is `> 0` and whose second, `(φ−αq)/q² = a₂ + a₃q + …`, is `≥ 0` on `[0,1/16]` — exactly
the convexity statement `φ ≥ αq` above.

## 5. Region II — `φ(q) ≥ 1/10` on `[1/16, 1/4]`

**Method (grid + Lipschitz).** Truncate all theta sums at `D_max` (§2). Rigorous ingredients:

- **Lipschitz:** `sup_{[1/16,1/4]}|φ'(q)| ≤ 3.9420 < 4 =: L`, certified by iv-enclosure of `φ'`
  over `64` equal subintervals (max of `|·|` over all pieces).
- **Grid:** uniform nodes `q_i = 1/16 + i/64`, `i = 0,…,12` (`M = 12` intervals, `h = 1/64`),
  with rigorous rational **lower bounds** `ℓ_i ≤ φ(q_i)` (partial theta sums minus the §2 tail):

  | `q_i` | `1/16` | `5/64` | `3/32` | `7/64` | `1/8` | `9/64` | `5/32` | `11/64` | `3/16` | `13/64` | `7/32` | `15/64` | `1/4` |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | `ℓ_i ≥` | `.16131` | `.21481` | `.26975` | `.32442` | `.37722` | `.42662` | `.47120` | `.50961` | `.54059` | `.56296` | `.57563` | `.57759` | `.56789` |

- **Certificate:** on each `[q_i, q_{i+1}]`, any `q` lies within `h/2` of the nearer node, so
  `φ(q) ≥ min(ℓ_i, ℓ_{i+1}) − L·h/2`. With `L·h/2 = 4·(1/64)/2 = 1/32`,
  ```
     min(ℓ_i, ℓ_{i+1}) − 1/32 ≥ 1/10   for every i = 0,…,11,
  ```
  the binding interval being the first: `ℓ_0 = 0.16131 ⇒ 0.16131 − 0.03125 = 0.13006 ≥ 0.1`
  (**worst-case margin `0.03007`**). Hence `φ(q) ≥ δ = 1/10 > 0` on `[1/16, 1/4]`.

## 6. Certificate summary

| region | claim | key explicit data | worst margin |
|---|---|---|---|
| `(0, 1/16]` | `φ(q) ≥ (7/5)q` | `φ''≥37/5` (8 subintervals), `α≥7/5` (`73Ḡ_e²−1140Ḡ_e+1472≥0`) | `φ''` floor `+0.055`; `α−7/5 = +0.0540` |
| `[1/16, 1/4]` | `φ(q) ≥ 1/10` | `L=4`, `h=1/64`, `M=12`, `13` node lower bounds | `+0.03007` |

Both regions yield `φ > 0`; together `φ(q) ≥ 0` on all `(0, 1/4]`. **Complete and
conservative:** tail bounds over-estimate the true tails by `>50` orders of magnitude, `L=4`
exceeds the certified `sup|φ'|=3.942`, `δ=1/10 < min φ ≈ 0.1613`, `c=7/5 < α=1.4540`, and every
per-check margin is strictly positive.

## 7. Finite list of rational inequalities a Lean proof must discharge

**(T) Tail lemma** — for `D_max=24`, each parity, `j∈{0,1,2}`:
`Σ_{D>D_max} D^{2j} q^{D²/4} ≤ (D_max+2)^{2j} q^{(D_max+2)²/4}/(1−ρ_j)`, `ρ_j=((D_max+2)/D_max)^{2j}4^{−(D_max+1)}`.
*(uses `RealTheta`/`ThetaLimit` moment sums + geometric majorant; monotone tail of `q^{D²/4}`.)*

**(C) Constant enclosure** — `1.4095014689866763774417 < B_e(¼)/A_e(¼) < 1.4095014689866763774418`
(two rational inequalities on the `D≤24` partial sums of `A_e,B_e` corrected by (T)).
*(`RealTheta` at `q=1/4`; `JTPIdentity` for the moment identities.)*

**(L) Leading coefficient** — `73·Ḡ_e² − 1140·Ḡ_e + 1472 ≥ 0` (one rational polynomial
inequality; with (C) gives `κ ≤ 73/160` and `α = 16−32κ ≥ 7/5`).

**(I) Region I (convexity)** — the 8 rational inequalities `φ''_lower([i/128,(i+1)/128]) ≥ 37/5`,
`i=0..7` (each a rational inequality in the truncated `A_e,B_e,C_e,m_·,θ₄` and their two
`q`-derivatives), plus the algebraic identities `φ(0)=0`, `φ'(0)=α`. Conclusion by convexity:
`φ(q) ≥ α q ≥ (7/5) q`.
*(`RealTheta` derivatives; anchor `θ₃⁴=θ₂⁴+θ₄⁴`, `0<θ₄<1` for the `1−θ₄⁴ ≥ 0` sign.)*

**(II) Region II (grid)** — (a) the 64 rational inequalities `|φ'|_upper(piece) ≤ 4` giving `L=4`;
(b) the 13 rational node lower bounds `φ(q_i) ≥ ℓ_i` (partial sum − (T)); (c) the 12 rational
inequalities `min(ℓ_i,ℓ_{i+1}) − 1/32 ≥ 1/10`. Conclusion by the mean-value/Lipschitz step:
`φ ≥ 1/10` on `[1/16,1/4]`.
*(`RealTheta` moment/derivative sums; each `ℓ_i` is a finite rational combination of `q_i^{D²/4}`.)*

Existing project theta machinery consumed: **`RealTheta`** (finite moment partial sums
`A_p,B_p,C_p` and `q`-derivatives), **`ThetaLimit`** (untruncated-sum / tail control for (T)),
**`JTPIdentity`** (the parity moment identities behind `G_p,S_p`), and the Jacobi anchor
`θ₃⁴ = θ₂⁴ + θ₄⁴` with `0 < θ₄ < 1` (sign of `1−θ₄⁴`, already proved upstream).

**Validator:** `computations/phi_certificate_verify.py` (mpmath `mp.iv`, dps 60) — all blocks
report `[OK]`; final line `phi(q) >= 0 on (0,1/4] : CERTIFIED`.
