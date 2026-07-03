# Parallel-Loop Floor — Constructive Lean YM (2026-07-03)

> **Clay Yang–Mills mass gap: OPEN.** This records the floor reached by a 9-round
> six-wide parallel workflow loop. Every open input is an explicit, uninhabited,
> honestly-named Type-level object. Nothing here claims the mass gap.

## Headline (verified this snapshot)

| Metric | Value |
|---|---|
| `lake build` | **533/533 jobs green** |
| Modules | 532 |
| Permitted axioms | `propext` (5089) · `Quot.sound` (5) |
| Forbidden axioms (`Classical`/`sorryAx`/`native_decide`) | **0** |
| Code-position `sorry` | **0** |
| Loop commits (`ad93e09..da603bb`) | 9 |
| Head | `da603bb`, `origin/main` |

## What the loop did

Nine rounds of a six-track `research → postulate → review → write → check → commit → push`
workflow (~18 agents/round, ~48 new modules) drove cores ④/③/① from opaque continuum
walls to a machine-checked floor. Consolidated in `YMGap/Rubric/LoopScorecard.lean`
(`loop_proved_line` = 7 re-exported theorems; `LoopOpenFrontier` = the named open cores).

### ④ Bounded continuous functional calculus — **RETIRED**

`WilsonFCHead.wilson_continuous_functional_calculus` is a theorem: the physical Wilson
transfer operator has a bounded continuous functional calculus `f(T)` (discharging
`BoundedTransferCalculusResidual`). The `LoopScorecard` records **Track 4 has no open core**.
Proved en route (all green, axiom-clean):
- `RC_cauchy_schwarz` (RC-valued Cauchy–Schwarz), `RCmul`; `LinearTransferOperator` (`T` rep-lift + scalar-homogeneity); `wilsonLinearTransfer`.
- `binomialTheorem`, `bernsteinVariance`, `quarterBound`; the Bernstein `SpectralUnifCauchy` wrap.
- `fcApply_selfAdjoint_limit` + `fcApply_normBound_limit` (both `ContinuousFCLimitData` fields); `polyApply_psub`; `dischargeBTC_complete`; `continuousFC_retired`; `FinEuclCompletionCoords`; `SpectralDiffBound`.

Honest caveat: `wilson_continuous_functional_calculus` is the **weight-1 tower** existence
witness (physical spectrum `λ_s = w^{C₄(s+1)}`, gap intact) — not a `√μ`-fidelity match to
the interacting `E_Λ` moment functional, which remains a separate input. Remaining structural
data: the `∀x` `img` extension + `termwise` (standard OS/Peter–Weyl finite-resolution).

### ③ `sin(kπ)=0` / OS2-uniform — **one transcendental atom**

All of the surrounding structure is proved: the full signed CReal-angle addition laws
(`PythFull` closed), the `CircleModel` (`repDir_add` direct), `sinPi_eqv_zero` for the
assembled model, the Moore–Osgood interchange (`B2`), the ODE-uniqueness (`leg-A`), and the
Machin `ℤ[i]` identity (`e^{iπ}=−1` by `decide`). The sole residual:

- **Core A — `ArctanTrigLink`** : `tan(arctan x)=x` (`sinC(arctan(1/k)) ≃ (1/k)·cosC(arctan(1/k))`). DiffJTP-scale transcendental; closes ③ and OS2's `sin(kπ)=0`.

### ① Fusion local-CLT — **one analytic core (+ tied plumbing)**

Proved: `saddleFloor_wH` (the worst-coupling margin, *no* local-CLT remainder at `wH`),
`whAllSMargin`, the off-diagonal common-range Gram TP₂ (`lagCorrTP2_common`), general
discrete `cauchy_schwarz`, `csDet_nonneg` (Andréief/Plücker Gram positivity). Round-9
structural finding: the line-sum is a **shift-family** sum of windowed autoconvolutions.

- **Core B — `LineSumLogConcaveCR`** : the SU(2)-fusion antidiagonal **line-sum log-concavity** `S_s·S_{s+2} ≤ S_{s+1}²`. Irreducible on three counts: (i) the strict margin is a *variance* estimate, not positivity; (ii) the moving-window truncation edge; (iii) `r`-aggregation super-modularity (a sum of log-concave sequences need not be log-concave). Equivalent general-`w` wall = `FiniteSMarginWorstcase`.
- Plumbing (sign-tied to Core B): `MovingWindowEdge → EdgeSignMatch`.

### Machine-refutations (Lakatos)

Three over-strong pointwise-TP₂/MLR routes were *refuted*, not papered over, correctly
relocating ① onto the full-Gram/Cauchy–Binet object:
`AdjacentMLR` (`216 ≤ 0`), `ScoutFactoring` (`16 ≤ 0`), `naive_lift_direction_wrong`.

## The frontier, exactly

```
Core A  ArctanTrigLink        tan(arctan x)=x            transcendental (DiffJTP-scale)
Core B  LineSumLogConcaveCR   theta shift-family log-concavity   convolution local-CLT
```

Everything else across ④/③/① is proved and axiom-clean. These two are genuine deep-math
walls — an inverse-trigonometric transcendence and a convolution local-CLT — not
formalization gaps. There is no remaining *closable* residual (the `MovingWindowEdge`
plumbing is sign-tied to Core B); further loop rounds would re-sharpen these two, not close
them. This is the honest floor.

## Path forward

1. **Core B (`LineSumLogConcaveCR`)** — the local-CLT crux, closest to the mass gap. A dedicated single-project attack (discrete Laplace / Cauchy–Binet with the cross-shift super-modularity), genuine multi-session research.
2. **Core A (`ArctanTrigLink`)** — known-constructive but DiffJTP-scale; the constructive inverse-tangent identity.
3. **④ fidelity** — upgrade the weight-1 witness to the interacting `E_Λ` functional (needs constructive Haar integration — see the earlier `HaarClassIntegral` reduction to `cos`-of-a-π-angle).

*The fixed-spacing + reconstruction halves are machine-checked and unconditional; ④ (bounded
continuous FC) is now retired; and the continuum frontier is two named irreducible cores.
The Clay Yang–Mills mass-gap problem remains OPEN.*
