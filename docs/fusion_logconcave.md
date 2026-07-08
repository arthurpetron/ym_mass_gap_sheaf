# FusionConvLogConcaveCore — structural attack: findings & verdict

**Date:** 2026-07-06
**Working tree:** `.../ym_mass_gap_sheaf/lean` (MAIN, no worktree)
**New file:** `YMGap/Continuum/FusionCoreStepRoundK.lean` (imported in `YMGap.lean`)
**Build:** full `lake build` GREEN = **668 jobs** (+1). `YMGapGuard` **OK** (5 Clay-frontier
types unconditionally uninhabited). No `sorry` / `Classical.*` / `native_decide` / custom
`axiom`. All new decls axiom-clean (`propext` / `Quot.sound` only; one is axiom-free).

---

## 1. The exact statement (unchanged, re-confirmed)

`SelfFusionLogConcave.FusionConvLogConcaveCore N w hw0 hw1 : Type` carries two fields:

```
strongCoupling : coeffW w 1 * coeffW w 1 ≤ 3
cauchyBinet    : ∀ s, boxSum w N s * boxSum w N (s+2) ≤ boxSum w N (s+1) * boxSum w N (s+1)
```

where `boxSum w N s = Σ_{a,b≤N} fusionInd a b s · (coeffW w a · coeffW w b)` is the SU(2)
**Clebsch–Gordan fusion** coefficient of `F² = (Σ c_a χ_a)²` at character mode `s`, and
`coeffW w s = (s+1)·w^{s(s+2)}` is the heat-kernel weight. It is the `p = 2` self-fusion
box; the real 4-D bond-moving defect is `p = b^{d−1} = 8`.

## 2. CRITICAL correction of the task premise (already machine-checked in-tree)

The task's proposed route — "m-fold convolution preserves log-concavity, so induct from the
two-body case" — **is mathematically FALSE here and is machine-refuted in the codebase three
separate ways.** SU(2) CG fusion is **not** ordinary convolution and does **not** preserve
log-concavity:

- `SelfFusionLogConcave.boxSum1_logConcave_FALSE_at_one` — at `N=1, w=1`: `20 > 16`.
- `FusionCoreStepRoundA.coreStep2_s0_FALSE_half` — the additive per-step `CoreStep` is FALSE
  at `N=2, w=1/2` (so the naive `core N → core (N+1)` induction is *unsatisfiable* for `N≥2`).
- `FusionCoreStepRoundJ.symMinor_can_be_negative` / `offMinor_wrong_direction` — the
  symmetrised off-diagonal Menon minor is strictly `< 0` at `w=1/2,(m,n)=(0,2)`; a
  summand-wise nonnegativity proof cannot exist.

The genuine content is the **heat-kernel-specific `(r,d)` Gaussian-theta local-CLT**, not a
finite rational inequality and not a generic convolution fact.

## 3. State of the attack: it is already ~20 files / 10 rounds deep

This node has been driven very far. Two equivalent reduction routes both bottom out at ONE
quantitative local-CLT residual:

- **Track B (box / Cauchy–Binet):** `FusionConvLogConcaveCore` ⟸ `UniformBoxLogConcave`
  ⟸ `UniformBoxQuadCertificate` (aggregate `quadDiff ≥ 0`) ⟸ `QuadGershgorinClosure`
  (RoundA/B/C). Cores INHABITED symbolically at `N=0,1,2` and concretely at `N=3,4,5,6`
  (`w=1/2`).
- **Track A (line-sum / autoconvolution):** `S1Dominance` ⟸ `StrandReduction`
  ⟸ `CentralAutoconvReserve` ⟸ `AutoconvBumpBounds` ⟸ **`AutoconvReserveResidual`**
  (RoundD–J): the central-autoconvolution margin
  `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.

**Already proved (pre-existing, load-bearing):**
- The magnitude atom `coeffW_superLogConcave` (factor-4: `c_s·c_{s+2} ≤ ¼·c_{s+1}²`, all `s`,
  `w≤1/2`) — RoundC. This is the real Gaussian decay beyond log-concavity.
- The geometric shift-tail domination `offAuto ≤ (1/15)·H0auto` (all `N,t`) — RoundI.
- The diagonal `(3/4)` Casimir minor reserve `δ_s ≥ (3/4)c_{s+1}²` — RoundJ.
- The whole downstream chain `core ⟹ log-concavity ⟹ peak-lemma ⟹ s=1-dominance`
  (`FusionGenFunction.peak_of_logConcave`, `FusionLogConcave.s1Dominance_of_p2`) — COMPLETE.

**The single open residual** is the CROSS-strand aggregate cancellation of the reserve
(`AutoconvReserveResidual` / `QuadGershgorinClosure` / `LagCorrTP2`) — the heat-kernel
local-CLT. RoundI records that plain (factor-1) log-concavity gives only ≈9/8 < 256/225, so
the strict reserve genuinely requires the magnitude decay, aggregated.

## 4. What I added (RoundK — genuine, proved, axiom-clean)

Not a closure (the residual is genuinely open); a **precise localisation of the wall** plus
consolidation of the exact statement + chain:

- **`coeffW_strandReserve`** — the reserve's *own constant* `256/225 = 1+31/225` discharged on
  a SINGLE strand, all `s`, symbolic `w≤1/2`:
  `(1+31/225)·(c_s·c_{s+2}) ≤ c_{s+1}²`, because `(256/225)·(¼) = 64/225 ≤ 1`. So the
  diagonal / single-strand half of `AutoconvReserveResidual` is TRUE with a uniform ≈3.5×
  margin — **the wall is not on the diagonal; it is exactly the cross-strand aggregation**
  (quantifying RoundJ's `symMinor_can_be_negative`).
- **`fusionMeasure_superLogConcave`** — the two-body (`p=2` fusion measure) factor-`1/16`
  magnitude reserve `(c_a c_{a+2})(c_b c_{b+2}) ≤ (1/16)(c_{a+1}² c_{b+1}²)`. A strong-coupling
  strengthening of `R1LocalCLT.fusionMeasure_logConcave` (which has plain factor 1).
- **`fusionConvLogConcaveCore_of_uniform` / `s1Dominance_all_of_uniform`** — the consolidated
  exact box-core statement and the COMPLETE chain to the excited-suppression datum
  `S1Dominance N w 2` for every `N`, driven by the single Track-B residual
  `UniformBoxLogConcave w` (re-exports of `coreOfUniform` / `s1DominanceOfUniform`).

`#print axioms` (from the build):
```
coeffW_strandReserve                : [propext, Quot.sound]
fusionMeasure_superLogConcave       : [propext, Quot.sound]
fusionConvLogConcaveCore_of_uniform : (no axioms)
s1Dominance_all_of_uniform          : [propext, Quot.sound]
```

## 5. HONEST verdict

**`FusionConvLogConcaveCore` is NOT proved for general `N`, and I did not fake a closure.**
It is genuinely reduced (by 10 prior rounds + this one) to the sharpest possible named
residual: the **cross-strand aggregate cancellation of the central-autoconvolution reserve**
(`AutoconvReserveResidual` / `QuadGershgorinClosure`), i.e. the heat-kernel `(r,d)`
Gaussian-theta local-CLT — inhabited concretely at `N=0..6`, `w=1/2`; open for general `N`.

- The task's convolution-induction route is **provably wrong** (three in-tree refutations).
- The downstream chain (core ⟹ log-concavity ⟹ peak ⟹ `s=1`-dominance) is **complete** — the
  ONLY open link is the log-concavity core itself.
- RoundK proves the **diagonal / single-strand half of the reserve holds with margin** and the
  **two-body magnitude reserve**, pinning the open content to cross-strand aggregation alone.

**Guard/frontier note:** RoundK inhabits **no** guarded Clay-frontier bundle;
`FusionConvLogConcaveCore` is a reduction structure (freely inhabited at concrete `N`), not one
of the 5 guarded types (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`,
`ClayTargetPinned`, `FrontierDAG`), all of which remain unconditionally uninhabited
(`YMGapGuard` OK). This is NOT a 4-D Yang–Mills mass gap; nothing is overclaimed.
