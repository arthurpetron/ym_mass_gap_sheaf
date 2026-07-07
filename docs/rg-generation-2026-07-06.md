# The constructive non-perturbative RG that GENERATES Λ≠0 — the RG-invariant scale scaffold

**Verdict (machine-checked, axiom-clean, maximally adversarial): the constructive RG
carries the essential-singularity KINEMATICS of the RG-invariant scale
`Λ = μ·exp(−1/(2β₀g²))` — it is a concrete irrational CReal, EXACTLY self-similar under
one RG step, and conserved along the matched self-similar flow — but the GENERATION of
the REAL 4D flow's Λ is NOT a genuinely new mechanism: it reduces EXACTLY to the single
per-step defect `singleStep` (`realδ_k ≤ δ_model_k`), the same irreducible
interacting-measure / renormalon core. Λ's positivity is the TRIVIAL red herring; the
real generation is the foundational Clay substrate. The 4D Yang–Mills mass gap remains
OPEN.**

- Deliverable Lean file: `lean/YMGap/Continuum/RGInvariantScaleScaffold.lean` (wired into
  `YMGap.lean`). Full `lake build` **green = 722 jobs**; `YMGapGuard` **frontier-guard
  OK = 5** Clay-frontier types unconditionally uninhabited. Lean-core only (`Q'`/`Nat` +
  the `expNeg`/`CReal` backbone), no Mathlib/`ring`/`native_decide`/`Classical`/`sorry`.
  Axiom gate `⊆ {∅, [propext], [propext, Quot.sound]}` on all 7 load-bearing decls.
- **Committed: nothing** (per instruction).

---

## 1. THE FLOW (task point 1) — the RG-invariant Λ IS constructible as a concrete CReal

`Λ_k = μ_k · exp(−c/(β₀ g_k²))`, `μ_k = 1/a_k` the RG scale. The essential-singularity
factor `exp(−c/(β₀g_k²)) = exp(−c(k+B)/(β₀A)) = condensateCReal k` is already a genuine
irrational CReal in `[0,1]` (`CondensateGeometricErosion`, via `CRealExp.expNeg`), for
SU(2) `β₀ = 22/3`, `A=1`, `B=12`, `c=4`, ratio `ρ = exp(−6/11) = 0.5796`. **YES** — Λ is
a concrete CReal (the exp-on-CReal residual is already discharged).

The NEW content this module supplies — the genuine RG-invariance mechanism, PROVED
unconditionally, axiom-clean `[propext, Quot.sound]`:

- **`condExponent_succ`** — `condExponent (k+1) ≃ condExponent k + condRateExp` (one RG
  step adds the fixed exponent `6/11`). Pure `Q'` algebra.
- **`condensate_selfSimilar_step`** — **the essential-singularity factor is EXACTLY
  self-similar under one block-spin RG step**:
  ```
  condensateCReal (k+1)  ≃  condensateCReal k · ρ ,     ρ = exp(−6/11) ∈ (0,1).
  ```
  Proved via the exponential addition law `expNeg_add_equiv` (`e^{−a}·e^{−b} ≃
  e^{−(a+b)}`) fed the exponent recursion. This is RG self-similarity in mechanism form:
  the condensate scale shrinks by the FIXED irrational ratio `ρ` per step, so
  `Λ = μ·condensate` is conserved iff `μ = 1/a` grows by exactly `1/ρ` per step.

## 2. THE GENERATION vs THE POSITIVITY (task point 2) — the dimensionful invariant, conserved on the matched flow (CONDITIONAL)

- **`rgScaleLambda μ k := μ_k · condensateCReal k`** — the RG-invariant Λ as a CReal.
- **`rgScaleLambda_conserved`** — GIVEN the matched self-similar RG-scale law
  `hmatch : ρ·μ_{k+1} ≃ μ_k`, the dimensionful invariant is CONSERVED
  `rgScaleLambda μ k ≃ rgScaleLambda μ (k+1)` (∀k). This IS dimensional transmutation for
  Λ: `μ_k → ∞` and `exp(−c/β₀g_k²) → 0` at reciprocal rates, product fixed. **OPEN
  binders on `μ`, `hmatch`** — a conditional producer.
- **The positivity is the RED HERRING** (`condensate_factor_nonneg`, reused
  `condensate_creal_nonneg`): `exp(−x) ≥ 0` is FREE, so `Λ ≥ 0` (indeed `> 0` for `μ>0`)
  is trivial. The mass gap is NOT this — it is that the REAL flow's invariant EQUALS a
  nonzero Λ. The matched spacing `hmatch` is the DIAL: it is the ideal `ε ≡ 0`
  self-similar trajectory of `DimensionlessMarginTransmutation`, NOT the real flow.

## 3. THE DEEPEST CHECK (task point 3) — the generation reduces to `singleStep`

The self-similar STEP is proved unconditionally, but it is the step of the already-built
condensate MODEL and holds for the ideal zero-defect trajectory. The real flow's
DEVIATION from this ideal self-similarity is the additive erosion `ε_k`, i.e. exactly
`SingleStepDefectBound.singleStep : realδ_k ≤ δ_model_k` (`RGFlowGapAssembly`). So:

> **the constructive non-perturbative RG generation of the real Λ IS `singleStep`** — the
> same irreducible non-perturbative core (the interacting-measure / fusion-local-CLT
> input, a per-step form of the condensate positivity), NOT a genuinely different
> generation mechanism.

Non-vacuity check (`rgInvariant_mechanism_nonvacuous`, unconditional re-export): a
conserved positive RG-invariant EXISTS in Lean — the dimensionless margin
`(1 − sep N)·∏geomSumC` (the `1/a_N`-rescaled lattice gap) has a positive uniform floor
along the real irrational `e^{−1}` self-similar CReal flow
(`uniformContinuumFloor_concreteE`). So the mechanism is genuine, not a type-theoretic
accident — but it is the DIALED toy; the REAL 4D flow's Λ is the residual.

## 4. THE HONEST FOUNDATIONAL ASSESSMENT (task point 4)

Can the Lean-core library carry the constructive non-perturbative RG (Bałaban) that
generates Λ≠0?

- **The KINEMATICS: YES.** The RG-invariant scale `Λ = μ·exp(−1/(2β₀g²))` is a concrete
  irrational CReal; its essential-singularity factor is EXACTLY self-similar per RG step
  (`condensate_selfSimilar_step`, PROVED axiom-clean); its dimensionful value is conserved
  along the matched self-similar flow (`rgScaleLambda_conserved`); a genuine conserved
  positive invariant exists unconditionally (the dimensionless margin). The exp-on-CReal
  and the whole dimensional-transmutation *plumbing* are constructible in Lean-core.
- **The GENERATION: NO — it is the foundational Clay substrate.** That the REAL 4D
  interacting block-spin flow SITS on this trajectory with a nonzero Λ (real erosion ≤
  model, matched spacing) is NOT derivable from the proved pieces. It reduces to
  `singleStep` — the interacting field integral obeying the renormalon structure. A dialed
  Λ (from the toy self-similar seed) is NOT the real generation. The library carries the
  KINEMATICS with the GENERATION reduced to `singleStep`; the substrate that would close
  it (the non-perturbative interacting measure) is beyond the current Lean-core.

## 5. Maximal-scrutiny audit — did Λ≠0 cascade? NO

| claim | status | evidence |
|---|---|---|
| Λ = μ·exp(−1/2β₀g²) is a concrete CReal | **PROVED (construction)** | `rgScaleLambda`, `condensateCReal` via `CRealExp` |
| essential-singularity factor self-similar per RG step | **PROVED** | `condensate_selfSimilar_step` (via `expNeg_add_equiv`) |
| dimensionful Λ conserved on matched flow | **PROVED (conditional)** | `rgScaleLambda_conserved`, open `μ`/`hmatch` |
| Λ ≥ 0 / > 0 (the positivity) | **TRIVIAL — red herring** | `condensate_factor_nonneg` (`exp` positive, free) |
| a conserved positive invariant EXISTS (mechanism genuine) | **PROVED (unconditional)** | `rgInvariant_mechanism_nonvacuous` (dimensionless margin) |
| **matched spacing `hmatch` for the REAL flow** | **OPEN — the DIAL** | ideal `ε ≡ 0` self-similar trajectory, not derived |
| **the GENERATION (real flow → nonzero Λ)** | **OPEN = `singleStep`** | `SingleStepDefectBound.singleStep` UNINHABITED |
| every binder | **checked** | `rgScaleLambda_conserved` open on `μ`, `hmatch` |
| axiom-clean | **checked** | all 7 decls `⊆ {∅,[propext],[propext,Quot.sound]}` |
| guard reacting | **checked** | `frontier-guard OK: 5 … uninhabited`, 722 jobs |

No guarded bundle (`SingleStepDefectBound`, `TrueMarginRecursion*`, `UniformSpacingFloor`,
`Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) is inhabited. The
STOP-and-audit condition (triggered only on a cascade to a guarded bundle) is NOT met.

## 6. `#print axioms`

```
condRateExp_nonneg               : (none)
rho_nonneg                       : [propext, Quot.sound]
condExponent_succ                : [propext, Quot.sound]
condensate_selfSimilar_step      : [propext, Quot.sound]   ← the RG self-similar step
rgScaleLambda_conserved          : [propext, Quot.sound]   ← Λ conserved (conditional)
condensate_factor_nonneg         : [propext, Quot.sound]   ← positivity red herring
rgInvariant_mechanism_nonvacuous : [propext, Quot.sound]   ← mechanism non-vacuous
```

## 7. HONEST FINAL VERDICT

The constructive non-perturbative RG **carries the essential-singularity kinematics of the
RG-invariant scale `Λ = μ·exp(−1/(2β₀g²))`**: Λ is a concrete irrational CReal, its factor
is EXACTLY self-similar under one block-spin RG step (`condensate_selfSimilar_step`,
PROVED), and its dimensionful value is conserved along the matched self-similar flow
(`rgScaleLambda_conserved`, conditional), with a genuine conserved positive invariant
existing unconditionally. Λ's POSITIVITY is the TRIVIAL red herring (`exp` is positive).

But the **GENERATION** — that the REAL 4D interacting flow HAS this nonzero Λ as its
RG-invariant (the real mass gap) — is NOT a genuinely different mechanism: the matched
spacing is the DIAL (the ideal `ε ≡ 0` self-similar trajectory), and the real flow's
deviation from it is the additive erosion `ε_k = singleStep`. So the constructive RG
generation reduces EXACTLY to `singleStep` — the same irreducible interacting-measure /
renormalon core, the foundational non-perturbative substrate (the interacting field
integral) beyond the current Lean-core library. No guarded bundle is inhabited; nothing is
faked; the 4D Yang–Mills mass gap remains **OPEN**. The next attack is still the
interacting per-step fluctuation bound (`singleStep` / fusion-local-CLT), now confirmed —
by a fifth independent route (the RG-invariant-Λ construction itself) — to be the binding
core.
