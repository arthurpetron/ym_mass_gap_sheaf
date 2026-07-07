# Variance monotonicity `Var_m(cos θ)` of the m-fold fusion — attack result

**Date:** 2026-07-07. **Target:** the VARIANCE MONOTONICITY sub-piece of `singleStep`
via the saddle decomposition `Cdef_m = 4·Var_m(cos θ) + F(μ)`
(`UniformMFoldConcentration.saddle_decomposition`). **Method:** exact character algebra +
high-precision numerics (mpmath dps 30–45, two integration methods, smax-converged) + Lean
`Q'`/`Nat` formalization (LEAN-CORE ONLY: no Mathlib/`ring`, no `native_decide`).

---

## VERDICT UP FRONT (maximally adversarial, honest)

`Var_m(cos θ)` is **monotone decreasing in `m`** — TRUE (overwhelming numerics, zero
violations), and its exact character form `4·Var_m = (r2 + 1) − r1²` is **PROVED**
axiom-clean in Lean. **But this does NOT close the uniform-in-m sub-piece of `singleStep`,
for two independent reasons, BOTH now machine-checked:**

1. **It is insufficient.** The `Cdef` gap splits EXACTLY as
   `Cdef_a − Cdef_b = (4Var_a − 4Var_b) + (F_a − F_b)` (`cdef_gap_decomposition`, PROVED),
   and the `F`-gap is `≥ 0` — **opposite in sign** to the `≤ 0` variance gap. The two
   pieces **nearly cancel** and the residual sign is fixed by the QUANTITATIVE near-Maxwell
   balance, NOT by monotonicity of `Var`. **Concrete refutation** (dps 45, smax-converged):
   at `w = 0.6`, `Var_3 = 0.12231 < Var_2 = 0.16563` (variance monotonicity HOLDS) yet
   `Cdef_3 = 0.016757 > Cdef_2 = 0.015254` (the connected remainder INCREASES). So
   `Var_m ≤ Var_2` ⇏ `Cdef_m ≤ Cdef_2`.
2. **Its own proof reduces to the same wall.** `d/dm Var_m(cos θ) =
   Cov_m((cos θ − μ)², log K_w)` is the third-central-moment / skewness of the fused
   measure, whose uniform sign is exactly the local-CLT core `FusionConvLogConcaveCore`,
   already open — NOT a new independent input.

**Nothing is closed. `VarianceMonotonicityCore` is UNINHABITED. The 4D Yang–Mills mass gap
remains OPEN. Nothing is faked.**

---

## 1. The exact variance structure (PROVED)

SU(2) characters `χ₁ = 2 cos θ`, `χ₂ = 4 cos²θ − 1`, fusion `χ₁² = χ₀ + χ₂`. Under the
fused class-angle measure `p_m(θ) ∝ K_w(θ)^m sin²θ` with `r_k(m) = [c^{⋆m}]_k/[c^{⋆m}]_0`:

    E_m[cos θ] = r1/2 ,   E_m[cos²θ] = (1 + r2)/4 ,
    4·Var_m(cos θ) = (r2 + 1) − r1²        (Lean: `fourVarCosQ r1 r2`).

Equivalently `Var_m(cos θ) = (1 + r2(m) − r1(m)²)/4`. This coincides with the existing
`fourVarQ r2 μ = (r2+1) − 4μ²` under `r1 = 2μ`. Base case (single plaquette, `m = 1`):
`r1(1) = 2w³`, `r2(1) = 3w⁸`, so `4·Var_1 = 1 + 3w⁸ − 4w⁶ = (1−w²)²(1 + 2w² + 3w⁴) ≥ 0`
(sympy-verified factorization; manifestly nonnegative).

## 2. The numerics (mpmath dps 30–45, two methods, smax-converged)

**Var monotonicity — ZERO violations** over `w ∈ {0.6, 0.8, 0.9, 0.97}`, `m = 1…500`
(dense for `m ≤ 40`). Example (`w = 0.8`): `Var_m = 0.1137, 0.0516, 0.0286, 0.0180,
0.0124, …` strictly ↓. The concentration `K_w^m → δ_0` narrows the peak; `Var_m ∼ C(1−w)/m`.

**The near-Maxwell cancellation** (`4·ΔVar := 4(Var_m−Var_2)`, `ΔF := F(μ_m)−F(μ_2)`,
`sum = Cdef_m − Cdef_2`):

| w | m=10: 4·ΔVar | ΔF | sum = Cdef_m−Cdef_2 |
|---|---|---|---|
| 0.6 | −0.5636 | +0.5505 | **−0.0131** |
| 0.9 | −0.05301 | +0.05294 | −6.997e-5 |
| 0.97 | −0.005063 | +0.005063 | −5.42e-7 |

The two `O((1−w)²/m²)` pieces cancel to ~1% (`w=0.6`), ~0.13% (`w=0.9`), ~0.01% (`w=0.97`)
— increasingly perfect as `w→1` (the Maxwell `Var(η)/E[η]² → 2/3` relation). The residual
IS `Cdef`.

**The decisive inversion** (`w = 0.6`, smax = 30/45/60 all identical):

| m | 2 | 3 | 4 | 5 |
|---|---|---|---|---|
| Var_m | 0.16563 | 0.12231 | 0.09093 | 0.06920 |
| Cdef_m | 0.015254 | **0.016757** | 0.013184 | 0.009525 |

`Cdef` peaks at `m = 3`, not `m = 2`: the docs' `sup_m Cdef_m = Cdef_2` is only a deep-UV
(`w ≳ 0.8`) statement, FALSE at strong coupling. (The uniform bound `Cdef_m ≤ 6(1−w)² =
0.96` still holds with huge margin — it is the MONOTONICITY reduction, not the bound, that
fails.)

## 3. The mechanism of the monotonicity (why it is the local-CLT wall)

For the exponential family `dμ_m ∝ K_w^m dλ` in the natural parameter `m` with sufficient
statistic `g = log K_w`:

    d/dm Var_m(cos θ) = Cov_m((cos θ − μ)², g).

Since `cos θ` and `g = log K_w` are both decreasing in `θ ∈ [0,π]`, `g` is an INCREASING
function of `cos θ`; near the concentration point `θ = 0`, `g` is locally LINEAR in `cos θ`
(`g ≈ g₀ − 2β(1−cos θ)`), so `d/dm Var ≈ 2β·E[(cos θ − μ)³]` = `2β ·` (third central
moment). The concentrated measure is left-skewed in `cos θ` (mass at the top `cos θ = 1`,
Maxwell `θ² e^{−mβθ²}`), giving a NEGATIVE third moment ⟹ `Var` decreasing. Making this
rigorous **uniformly in `(m, w)`** is exactly the near-Maxwell / log-concavity control
already tracked as `FusionConvLogConcaveCore` — the SAME open wall, not a new closure.

## 4. Lean deliverable — `YMGap/Continuum/VarianceMonotonicity.lean` (imported in YMGap.lean)

PROVED (axiom-clean `Q'`, `propext`/`Quot.sound` only):
- **`fourVarCosQ r1 r2 := (r2 + 1) − r1²`** — `4·Var_m(cos θ)` in character variables.
- **`cdef_split_generic`** — `r2 − C ≃ ((r2+1) − P) + ((P−1) − C)` (pure abelian algebra,
  reuses `tele_add`/`mid_cancel`); the `P := r1²` instance gives:
- **`cdef_split_r1`** — the EXACT cos-variance split `Cdef = fourVarCosQ r1 r2 + fTermR1 r1 X`
  (`fTermR1 r1 X = (r1² − 1) − 3X = F(μ)`), the `r1`-variable form of `saddle_decomposition`.
- **`sub_add_rearrange`** — `(A+A') − (B+B') ≃ (A−B) + (A'−B')`.
- **`cdef_gap_decomposition`** — THE OBSTRUCTION:
  `Cdef_a − Cdef_b = (4Var_a − 4Var_b) + (F_a − F_b)`, machine-checking that the `F`-gap
  competes with the variance gap.
- **`fourVarCos_nonneg`** — `Var ≥ 0` from Cauchy–Schwarz `r1² ≤ r2 + 1`.

NAMED-OPEN (honest, UNINHABITED):
- **`VarianceMonotonicityCore (r1 r2 : Nat → Q')`** — `Type`, Rule 6a: the skewness /
  local-CLT input that would give `Var_a ≤ Var_b` for `a ≥ b ≥ 2`. UNINHABITED.
- **`varMono_insufficient_for_uniform`**, **`fullFloor_still_needs_singleStep`** — the honest
  non-closure verdict; the continuum floor still rests on `singleStep`.

**Build / gate.** `lake build` GREEN (743 jobs). `YMGapGuard` GREEN: "frontier-guard OK: 5
Clay-frontier types unconditionally uninhabited" — this file inhabits NONE. `#print axioms`
on every load-bearing declaration: `propext` only (`cdef_split_generic`, `cdef_split_r1`,
`sub_add_rearrange`, `cdef_gap_decomposition`, `fourVarCos_nonneg`), `propext`/`Quot.sound`
(`fullFloor_still_needs_singleStep`). No `Classical.*`, no `native_decide`, no `ring`, no
`sorry`.

## 5. Honest final verdict

The variance-monotonicity sub-piece was pursued to the end. **`Var_m(cos θ)` monotone
decreasing is TRUE**, and its exact character identity `4·Var = (r2+1) − r1²` plus the
saddle split are PROVED axiom-clean. **It is NOT a closure of the uniform-in-m sub-piece:**
(i) machine-checked `cdef_gap_decomposition` + the `(w=0.6, m=3)` counterexample show
variance monotonicity is STRICTLY WEAKER than `Cdef_m ≤ Cdef_2` (the `F`-gap must be
controlled jointly, the near-Maxwell cancellation), and (ii) the monotonicity's own proof
is the skewness/local-CLT core, already open. The sub-piece is **the residual, not closed.**
`VarianceMonotonicityCore` UNINHABITED; the channel feedback + true-margin construction of
`singleStep` untouched; **the 4D Yang–Mills mass gap remains OPEN.**
