# R1 — the uniform curvature envelope (one sharp inequality supersedes the case split)

**Outcome.** The whole R1 curvature floor `Δ²V(s) ≥ −2` (both parities, all `w∈[0,1]`, all
windows `s`) is subsumed by a **single sharp uniform inequality**:

```
   Δ²V(s) + 2  ≥  (144/25) · w² · (1 − w²)        for all s, all w ∈ [0,1].
```

Here `V(t) = dmomNfull(w,t)/acNfull(w,t) = ⟨D²⟩_t` is the theta-tilted position variance and
`Δ²V(s) = V(s) − 2V(s+1) + V(s+2)`. Because `(144/25)·w²·(1−w²) ≥ 0` on the physical window, the
envelope implies `FullRangeFloor w s` (R1) OUTRIGHT — no even/odd/regime case split, no
two-region theta/parabolic tail. This is the cleanest statement of R1's remaining analytic content.

## Why 144/25

The ratio `(Δ²V+2)/(w²(1−w²))` normalises out the exact boundary vanishing (`Δ²V+2 → 0⁺` as
`w→0` at even centres, and `→0` as `w→1`). Its global behaviour (validated to `s=200`, high
precision):

| window `s` | inf over `w∈(0,1)` | attained at |
|---|---|---|
| `s=0` | **144/25 = 5.76** (global) | `w² = 1/6` |
| `s=1` | 48/7 ≈ 6.857 | `w = 1/√2` |
| `s=2` | 7.208… | |
| `s→∞` | → **8** (plateau, monotone) | `w ≈ 0.7065` |

So the infimum over ALL `s` and ALL `w` is exactly `144/25`, attained ONLY at the corner `s=0`.
For `s≥1` it jumps to `≥48/7` and rises monotonically to `8`. Hence `144/25` is the **sharp**
uniform constant.

## The binding case `s=0` is an exact perfect square (PROVED in Lean)

At `s=0` everything collapses to closed form:

```
   slack₀(w) = 96·w¹¹ ,        A₀A₁A₂ = 8·w⁹·(3w²+2) ,
   slack₀ − (144/25)·w²·(1−w²)·A₀A₁A₂ = (96/25)·w¹¹·(1 − 6w²)²  ≥ 0 .
```

The envelope is EXACT at `w² = 1/6` (the square vanishes). This is
`R1CurvatureEnvelope.curvatureEnvelope_zero`, proved axiom-clean from the polynomial identity
`slackP 0 = envBoundPoly 0 + sqCertPoly` (a single `decide`) plus `q_mul_self_nonneg`.

## Lean status (`lean/YMGap/Continuum/R1CurvatureEnvelope.lean`, axiom-clean)

PROVED:
  * `envBound_nonneg` — envelope slack `(144/25)w²(1−w²)A₀A₁A₂ ≥ 0` on `0≤w≤1`.
  * `fullRangeFloor_of_curvatureEnvelope` — envelope at `s` ⟹ `FullRangeFloor w s`.
  * `saddleVarianceFloor_of_curvatureEnvelope` — the uniform envelope ⟹ R1 (`SaddleVarianceFloor`),
    superseding the 3-cell (even/odd/regime) case split with ONE inequality family.
  * `regimeGETailBound_of_envelopeTail` — the envelope on `s≥7` ⟹ the standing residual
    `R1RegimeGE.RegimeGETailBound`, wiring the envelope into the existing R1 upper-half assembly.
  * `curvatureEnvelope_zero` — the binding `s=0` case, PROVED via the perfect square above.

NAMED OPEN (`Type`-level, never `sorry`):
  * `UniformCurvatureEnvelope w` — the envelope for all `s` (equivalently `s≥1`; `s=0` PROVED).
    The honest remaining analytic core of R1's upper half — a single sharp saddle inequality with
    a global rational certificate `144/25`, strictly better-posed than the two-region
    (`τ=1/50` theta/parabolic) `RegimeGETailBound` it replaces.

**Validator:** `computations/r1_curvature_envelope_verify.py` — blocks (1) exact rational minima
`144/25`, `48/7`; (2) high-precision uniform floor `≥ 144/25` with plateau `→8`; (3) the `s=0`
perfect-square identity (matching the Lean `slackP`/`envBoundPoly`/`sqCertPoly` definitions).
Final line: `R1 CURVATURE ENVELOPE : VERIFIED`.
