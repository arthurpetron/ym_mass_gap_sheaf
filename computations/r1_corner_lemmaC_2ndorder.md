# Lemma C (LC*) — second-order (cumulant) closure: exact forms, verdict, and the honest residual

**Target (LC*).** For all integers `s ≥ 7`,
```
        Δ²Var_q(s) ≤ Δ²Var_par(s) = 96(s²+6s+7)/175,    q ∈ [q₀(s), 1],
```
on the tilted parabolic ensemble `ρ_t(D) = (n²−D²) q^{D²}` (`D ≡ t (2)`, `|D| ≤ t`, `n = t+2`),
`Var_q(t) = ⟨D⁴⟩−⟨D²⟩²`, `g := D²`, `Δ²X(s) := X(s)−2X(s+1)+X(s+2)`, `E := s²+6s+7`,
`q₀ = (2E−7)/(2E)`.

**Bottom line.** The second-order **integral** Taylor argument **closes LC\* analytically with a uniform
positive margin** (≥ 18 % on the corner-needed range, ≥ 48 % on `[q₀,1]`), decisively beating the
first-order / pointwise route (which fails by ~26 %). The load-bearing win is a factor `½` that comes
from integrating, not from pointwise positivity. **However it does NOT reduce LC\* to a decidable
polynomial-in-`s` inequality**: the one constant it needs, `C(s) = sup_{[0,μ₀]} Δ²κ₄`, is a
theta-transcendental interior maximum with **no** elementary closed form and a **divergent** cumulant
regress. So this is a valid *conditional* proof, not a finite Lean certificate. Details, exact forms,
and high-precision verification below. Every constant is exact `sympy`; all floats are `mpmath`
dps 80–90 with mean-subtracted central moments (no catastrophic cancellation).

---

## 1. The exact cumulant backbone (all verified parity-independent, `sympy`)

Convention (fixed once, clean weight-1): `q^{D²} = e^{−μD²}`, `μ = −ln q ≥ 0`. For this exponential
family in the sufficient statistic `g = D²` the cumulant chain is **exact**:
```
   dVar/dμ = −κ₃,   d²Var/dμ² = +κ₄,   d³Var/dμ³ = −κ₅,   …
   ⇒  d(Δ²Var)/dμ = −Δ²m₃ ,   d²(Δ²Var)/dμ² = +Δ²κ₄  =  Δ²Var''_μ .
```
(Verified numerically at `s=12, μ=0.01`: `dΔ²Var/dμ = −4821.92 = −Δ²m₃`, `d²Δ²Var/dμ² = +959970 = +Δ²κ₄`.)

Edge (`μ=0`, pure parabola) closed forms, in `t` and their second differences in `s`:
```
   Var_par(t)  = 8 t(t−1)(t+4)(t+5)/175
   m₃_par(t)   = 32 t(t−1)(t+4)(t+5)(t²+4t−15)/2625
   κ₄_par(t)   = 64 t(t−1)(t+4)(t+5)(27t⁴+216t³−2153t²−10340t+22050)/1010625
   κ₅_par(t)   = −512 t(t−1)(t+4)(t+5)(183t⁶+2196t⁵+18599t⁴+90232t³−178885t²−1343700t+2160375)/65690625

   Δ²Var_par(s) = 96(s²+6s+7)/175
   Δ²m₃_par(s)  = 64(5s⁴+60s³+211s²+186s−42)/875                                            (> 0 ∀s≥1)
   Δ²κ₄_par(s)  = 256(126s⁶+2268s⁵+9445s⁴−22740s³−192967s²−258594s−35574)/336875
   Δ²κ₅_par(s)  = −1024(8235s⁸+197640s⁷+2260370s⁶+15784020s⁵+64621130s⁴
                        +127244040s³+59322125s²−61960290s−5927922)/65690625
```
`Δ²m₃_par` and `Δ²κ₄_par` match the sign-route memo exactly. Leading behaviour:
`Δ²Var_par ~ (96/175)s²`, `Δ²m₃_par ~ (64/175)s⁴`, `Δ²κ₄_par ~ (32256/336875)s⁶`,
`Δ²κ₅_par ~ −(8432640/65690625)s⁸`.

---

## 2. The correct second-order argument: the INTEGRAL form (the `½` is decisive)

Let `F(μ) := Δ²Var_par − Δ²Var_μ`. Then `F(0)=0`, `F'(μ) = −dΔ²Var/dμ = Δ²m₃(μ)`, so
```
   F(μ) = ∫₀^μ Δ²m₃(ν) dν = ∫₀^μ ( Δ²m₃_par − ∫₀^ν Δ²κ₄(σ)dσ ) dν
        = μ·Δ²m₃_par − ∫₀^μ (μ−σ) Δ²κ₄(σ) dσ
        ≥ μ·Δ²m₃_par − (μ²/2)·C(s),         C(s) := sup_{σ∈[0,μ]} Δ²κ₄(σ).
```
Hence, for all `μ ≤ M`,
```
   (★)   Δ²m₃_par(s) ≥ (M/2)·C(s)   ⇒   F(μ) ≥ 0   ⇒   LC*  on  [e^{−M}, 1].
```
This is the exact Taylor-with-Lagrange-remainder `Δ²Var_μ = Δ²Var_par − μΔ²m₃_par + ½μ²Δ²κ₄(ξ)`,
`ξ∈[0,μ]`, packaged so the remainder is controlled by `sup Δ²κ₄`. The **`½` in `(M/2)`** is the whole
game: it is why *second order closes what first order cannot*.

**First-order / pointwise route fails (as the prior agent found).** Proving `Δ²m₃ ≥ 0` pointwise via
`Δ²m₃(μ) ≥ Δ²m₃_par − μ·C` needs `Δ²m₃_par ≥ M·C` — **no `½`**. Numerically this ratio is `0.738 < 1`
(short by ~26 %). The integral form (★) halves the requirement and wins.

**Verification that (★)'s lower bound is genuine** (dps 90): on the corner interval `M=35/(8E)`,
`F(M) ≥ M·Δ²m₃_par − (M²/2)·sup Δ²κ₄` holds at every tested `s` (e.g. `s=7`: `F=56.97 ≥ 27.43`;
`s=300`: `F=5.296·10⁴ ≥ 2.253·10⁴`), and the end-to-end `max_{[q,1]}(Δ²Var−Δ²Var_par) = 0` (machine
zero `~10⁻⁸⁴`, tight only at `q=1`) — LC* itself is TRUE.

---

## 3. Which interval? — the `½`-convention reconciled

The brief's `μ₀ = 35/(4E)` is in the **half-weight** convention (its stated edge slope
`dΔ²Var/dμ|₀ = −½Δ²m₃_par` carries the extra `½`), i.e. `μ_brief = 2·μ_here`. Translating to the
clean weight-1 `μ`:

| interval | `μ·E ≤` | meaning | binding? |
|---|---|---|---|
| `[q₀,1]`, `q₀=(2E−7)/2E` | `3.50–3.56` | LC* as literally stated | subinterval |
| `M = 35/(8E)` | `4.375` | **corner MVI actually invoked** (`= brief 35/(4E)` halved) | **yes** |
| `35/(4E)` (weight-1) | `8.75` | brief number taken literally in weight-1 | **wrong** — exits Region B |

At `μ·E = 8.75` one is past `μ_m₃·E ≈ 4.566`, so `Δ²m₃ < 0` there and (★) *and* Region B both fail
(`INTreq = 0.59`). This is a convention double-count, **not** a real obstruction; the corner never
tilts that far. The binding range is `μ ∈ [0, 35/(8E)]` (`μE ≤ 4.375`), still inside Region B.

---

## 4. VERDICT on (★): closes uniformly (high-precision, s = 7…500, dps 80)

`INTreq(s) := Δ²m₃_par(s) / ((M/2)·sup_{[0,M]}Δ²κ₄)`  (need `≥ 1`):

| interval | min over `s=7..500` | limit `s→∞` | margin |
|---|---|---|---|
| `[q₀,1]` (`μE≤3.56`) | **1.4765** | `2.1824/L` = 1.4765 | **+48 %** |
| corner `M=35/(8E)` (`μE≤4.375`) | **1.1811** | `(110/63)/L` = 1.1811 | **+18 %** |
| pointwise `Δ²m₃_par ≥ M·C` (no `½`) | 0.738 | — | **FAILS −26 %** |

`INTreq(s)` is **monotone decreasing** in `s` to its limit, so the min is the `s→∞` value and no lower
base-case is worse. `sup Δ²κ₄` is attained at an **interior** peak `μ_peak·E ≈ 0.80–1.11` (well inside
`[0,M]`), value `1.478–2.73 ×` the `μ=0` value `Δ²κ₄_par` (ratio `→ L`, below).

**The clean `s`-free tail condition.** With `M = 35/(8E)`, the `s→∞` form of (★) is a single
transcendental theta inequality:
```
   L := lim_{s→∞}  sup_{μ∈[0,M]} Δ²κ₄(μ) / Δ²κ₄_par(s)   ≤   110/63 = 1.746032.
```
The rational ceiling `110/63` is exact:
`2·(64/175) / [ (35/8)·(32256/336875) ] = 110/63`. Verified `L`:
`s=200→1.479678, 500→1.478486, 1000→1.478312, 2000→1.478269` (converging to `L ≈ 1.47827`),
comfortably `< 110/63` (18 % margin). On `[q₀,1]` the ceiling is `2.1824`.

---

## 5. The honest residual — why second order is NOT a finite Lean certificate

(★) is a **valid rigorous proof of LC\*** *contingent on* a uniform bound `Δ²κ₄(μ) ≤ Cbar(s)` on
`[0,M]`. Every other ingredient is a decidable polynomial in `s`. The obstruction is entirely `Cbar`:

1. **`C(s) = sup Δ²κ₄` is a transcendental interior maximum** (peak `μE≈0.8–1.1`, `q`-irrational), not
   an endpoint value and with no elementary closed form. (At the *endpoints* it is exact rational —
   `Δ²κ₄_par` at `μ=0`, and `Δ²κ₄(q₀)` at `q₀` — but both are ~2–3× **below** the interior peak, so
   endpoint data cannot bound it.)

2. **The cumulant regress DIVERGES.** The natural Lean bound
   `C ≤ Δ²κ₄_par + M·sup|Δ²κ₅| + (M²/2)·sup|Δ²κ₆| + …` has each term **larger** than the last
   (verified, corner interval):

   | `s` | `Δ²κ₄_par` | `M·sup|Δ²κ₅|` | `M²/2·sup|Δ²κ₆|` | ratio₁ | ratio₂ |
   |---|---|---|---|---|---|
   | 20  | 1.26e7 | 8.68e7 | 2.86e8 | 6.89 | 3.30 |
   | 120 | 3.30e11| 1.95e12| 6.91e12| 5.90 | 3.55 |
   | 300 | 7.41e13| 4.35e14| 1.55e15| 5.87 | 3.56 |

   The first correction alone is `~5.9 × Δ²κ₄_par`. **Root cause:** at the tilt scale `μ ~ c/s²` (=
   theta scale), *every* cumulant order contributes the **same** order `O(s²)` to `Δ²Var` and `O(s⁶)`
   to `Δ²κ₄`; the ratio `M·Δ²κ_{j+1}/Δ²κ_j ~ Mσ² = O(1)` does **not** shrink. So no *finite* number of
   cumulants yields a finite bound on `C`. Higher Taylor order does not help — it diverges too.

3. **No uniform-constant bound `Cbar = K·Δ²κ₄_par` fits.** The closure window at each `s` is
   `sup/par ≤ K ≤ (allowed) = INTreq·(sup/par)`: `[2.73, 3.37]` at `s=7` but `[1.4785, 1.746]` at
   `s→∞`. A constant `K` would need `K ≥ 2.73` **and** `K ≤ 1.746` — impossible. A valid `Cbar` must
   track the `s`-dependent, transcendentally-determined ratio `2.73 → 1.4785`.

**Conclusion.** Second order **closes the analysis** (uniform 18–48 % margin) but reduces the `∀s`
quantifier only to: *(finite base cases `s=7..N`) + (monotonicity of `INTreq(s)`, empirically clean) +
**one** `s`-free theta-profile sup bound `L ≤ 110/63`.* The theta bound is genuine real analysis
(bounded, provable in principle by estimating the scaling profile `Φ(u)=lim Δ²κ₄(u/E)/(A s⁶)`), **not**
a `decide` check. It is of the same character/difficulty as LC* itself (its scaling limit), so second
order does **not** beat the per-`s` decidable fallback for discharging `∀s`.

---

## 6. Lean-feasibility verdict

* **Decidable / trivially formalizable:** the closed forms `Δ²m₃_par, Δ²κ₄_par, Δ²κ₅_par`; the algebraic
  identity `d(Δ²Var)/dμ=−Δ²m₃`, `d²(Δ²Var)/dμ²=Δ²κ₄`; and — *given any* `Cbar(s)` — the polynomial
  inequality `35·Cbar(s) ≤ 16·E·Δ²m₃_par(s)` (`E=s²+6s+7`), the `M=35/(8E)` form of (★).
* **Blocker (not Lean-closable cheaply):** a Lean-usable `Cbar(s) ≥ sup_{[0,M]}Δ²κ₄`. None exists in
  closed form; the finite-cumulant route diverges; a constant multiple of `Δ²κ₄_par` cannot fit the
  window. Supplying `Cbar` requires formalizing a **theta-function sup estimate** `L ≤ 110/63` — a
  continuum-analysis lemma comparable to the other open continuum walls, **not** a finite check.
* **Net:** the second-order route is a clean *conditional* proof and a sharp restatement (`L ≤ 110/63`),
  but it does **not** collapse LC* to finite decidable pieces. For an *unconditional* Lean theorem the
  genuinely decidable object remains the per-`s` integer-polynomial certificate — either
  `Q_B^{(s)}(q) ≥ 0` on `[q₀,1]` (Region B, `Δ²m₃≥0`, degree `≈9s²`) or the direct Bernstein `P_s`
  (degree `≈6s²`) — each a `decide`-check at fixed `s`, with the `∀s` quantifier still open (finite
  base cases + a uniform-tail argument, whose tail is exactly the `L ≤ 110/63` theta bound above).

**Adversarial summary.** *Does second order actually close it, or fail like first order?* It **closes
the analytic inequality** with an 18 % (corner) / 48 % (`[q₀,1]`) uniform margin — the integral `½`
converts the first-order 26 % failure into a solid win, and this is verified `s=7..500` at dps 80 and
`L` to `s=2000`. But it **does not** produce a finite decidable certificate: the required `sup Δ²κ₄` is
irreducibly theta-transcendental (divergent cumulant regress, `s`-varying peak ratio), so the honest
outcome is a *reduction of `∀s` to one clean `s`-free theta inequality `L ≤ 110/63`*, not a closure.

---

### Verification log
| check | method / precision | result |
|---|---|---|
| closed forms `Δ²Var/m₃/κ₄/κ₅ _par`, parity-independence | exact `sympy`, interpolation `k=1..5` | ✓ both parities identical |
| chain signs `d,d²(Δ²Var)/dμ = −Δ²m₃, +Δ²κ₄` | dps 90 central diff, `s=12` | ✓ 6+ digits |
| (★) integral bound `F(M) ≥ MΔ²m₃_par − M²/2·supΔ²κ₄` | dps 90 quad + grid | ✓ `s=7..300` |
| end-to-end LC* `Δ²Var_q ≤ Δ²Var_par` on `[e^{−M},1]` | dps 90 | `max = 0` (~`10⁻⁸⁴`), tight at `q=1` |
| `INTreq` corner `M=35/(8E)` | dps 80, `s=7..500` | min **1.1811** (`→` limit), all `≥1` |
| `INTreq` on `[q₀,1]` | dps 80 | min **1.4765** |
| pointwise `Δ²m₃_par ≥ M·C` (no `½`) | dps 80 | **0.738**, FAILS |
| `μE=8.75` (brief literal, weight-1) | dps 80 | `INTreq=0.59`, `Δ²m₃<0`: wrong interval |
| `sup Δ²κ₄` interior peak location | dps 90 refine | `μ_peak·E ≈ 0.80–1.11`, inside `[0,M]` |
| `L = lim sup Δ²κ₄/Δ²κ₄_par` | dps 90, `s→2000` | `1.47827 < 110/63 = 1.74603` (18 % margin) |
| cumulant regress divergence | dps 90 | corrections `~5.9×, 3.5×` per step: DIVERGES |

Scripts (in `/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `o2_closedforms.py` (exact cumulants),
`o2_structure.py` (exact-rational interior-peak probe), `o2_decisive.py` (margins `s=7..500`),
`o2_intervals.py` (three-interval / convention test), `o2_final.py` (chain signs, peak, `L`, LC*),
`o2_regress.py` (cumulant-regress divergence).
