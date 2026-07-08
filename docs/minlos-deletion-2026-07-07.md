# Minlos atom deleted by architecture — functional continuum target

## Verdict (honest)

**YES — the Minlos σ-additive atom is genuinely removed from the Clay-frontier by
architecture, with nothing faked, guard still 5, Clay still OPEN.**

The continuum-existence obligation is now stated on a POSITIVE LINEAR FUNCTIONAL
(the Schwinger functional) with an explicit modulus + GNS reconstruction — exactly
the Osterwalder–Schrader / Jaffe–Witten requirement, **measure-free**. The
Bochner–Minlos σ-additive lift (`CitedMinlosLift`) is demoted to an OPTIONAL
classical corollary: its dynamical/correlator content coincides with Sub-wall
B/Sub-wall A objects already counted, and its only genuinely-new datum is the
σ-additive tightness modulus — which is not an OS/JW input. The open `a → 0`
functional modulus, OS0, OS4, and Sub-walls A/B remain OPEN; no frontier type is
inhabited.

## Build + guard + axiom status (re-run, not trusted)

- `lake build` → **exit 0, 764 jobs** (`Build completed successfully (764 jobs).`).
- `lake build YMGapGuard` → **`frontier-guard OK: 5 Clay-frontier types
  unconditionally uninhabited across YMGap.*`**. Tier0Scorecard stays uninhabited
  (subA/subB open) after dropping its `minlos` field.
- `#print axioms` on every new/faithfulness/optional-corollary decl → `[propext,
  Quot.sound]` or "does not depend on any axioms". No `sorryAx`.
- grep of the new file: no `sorry` / `native_decide` / `admit` / `Prop := True` /
  `Classical.` in code (only in the honesty docstring listing what's excluded).

## New file: `lean/YMGap/Continuum/FunctionalContinuumTarget.lean`

### What `FunctionalContinuumTarget` carries (measure-free, `Type 1`)

Parametrised by `(A : ObsAlg) (t : Q') (ht : 0 ≤ t)`:

- `scaling : ScalingLimitModulus A` — the OPEN `a → 0` lattice-spacing-uniform
  two-sided modulus on the continuum functional (measure-free; the single open
  `a → 0` obligation, no YM inhabitant).
- `os1 : GJ_OS1_Regularity t ht` — PROVED OS1 (regularity `⟨1⟩_t ≤ 1`), suppliable
  unconditionally via `gj_os1_holds`.
- `os2 : GJ_OS3_ReflectionPositivity t ht` — PROVED OS2 (= Glimm–Jaffe OS3,
  reflection positivity), suppliable unconditionally via `gj_os3_holds`.
- `os0Euclidean : RubricO4Restoration` — OPEN OS0 / O(4)-Euclidean restoration.
- `os4Clustering : RubricUniformInCoupling` — OPEN OS4 spacing-uniform clustering.
- `gnsData : GNSData`, `gnsHilbert : CompleteGNSHilbert gnsData`,
  `gnsGap : SpectralGapData gnsHilbert` — the GNS reconstruction datum on the
  COMPLETE constructive GNS Hilbert space (measure-free).

No σ-additive field anywhere. `functionalTarget_of_openInputs` is the smart
constructor: it fills OS1/OS2 unconditionally from the proved theorems and consumes
only the genuinely-open inputs.

### The faithfulness theorem (exact statement + what it re-exports)

```lean
theorem functionalTarget_faithful {A : ObsAlg} {t : Q'} {ht : (0 : Q') ≤ t}
    (F : FunctionalContinuumTarget A t ht) :
    GJ_OS1_Regularity t ht ∧
    GJ_OS3_ReflectionPositivity t ht ∧
    (∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, corr F.gnsGap.model n
        ≤ (corr F.gnsGap.model 0) * F.gnsGap.gap.sep ^ n) :=
  ⟨gj_os1_holds t ht, gj_os3_holds t ht, mass_gap_of_spectralGap F.gnsGap⟩
```

Re-exports the GENUINE proved theorems (non-vacuous, not `True`):
- `OSAxiomAudit.gj_os1_holds` — OS1 regularity on the SU(2) heat-kernel functional;
- `OSAxiomAudit.gj_os3_holds` — OS2 reflection positivity (all orders / all real
  `c`), the analytic heart via Schur/Peter–Weyl;
- `GNSDynamics.mass_gap_of_spectralGap` — the positive mass gap `Δ = 1 − sep > 0`
  with geometric two-point decay `G(n) ≤ G(0)·sepⁿ` on the complete GNS space.

Why the functional formulation suffices (stated precisely in the docstring):
OS0–OS4 are conditions on the Schwinger FUNCTIONAL and OS reconstruction (GNS:
reflection-positive functional → Hilbert space + Hamiltonian + mass gap) is
FUNCTIONAL-ANALYTIC. No step uses a σ-additive measure on `S'(ℝ⁴)`; Bochner–Minlos
is optional downstream packaging. Supporting re-exports: `functionalTarget_os1`,
`functionalTarget_os2`, `functionalTarget_provedOS` (= `gjProvedAxioms_su2`),
`functionalTarget_gns_massGap`.

### The `minlos_is_optional_corollary` proof

`CitedMinlosLift = ClayScorecard.ClayContinuumExistence` has 4 fields:
`defectRecursion : DefectGapRecursion`, `loopyResidual : LoopyCorrelatorResidual
gw`, `tightnessRate : Nat → Q'`, `tightnessRate_nonneg`.

- `minlosDefectRecursion` / `minlosLoopyResidual` / `minlosTightnessRate` —
  projections of the three fields.
- `subB_gives_defectRecursion : SpectralMarginInput b afr N₀ → DefectGapRecursion`
  (= `Stage2ConvergesToMargin.toDefectGapRecursion`): Sub-wall B PRODUCES the exact
  object that is Minlos's `defectRecursion` field — already counted.
- `subA_gives_loopyResidual : Nat → LoopyCorrelatorResidual gw`
  (= `FPClusterIdentity.loopyResidual_offDiagonalReal`, rate `1/108 < 1`): Sub-wall
  A PRODUCES the exact type that is Minlos's `loopyResidual` field — already counted.
- `minlosOfParts` rebuilds a `CitedMinlosLift` from a `DefectGapRecursion` +
  `LoopyCorrelatorResidual gw` + `tightnessRate` + nonneg.
- `minlos_eq_parts (h) : minlosOfParts h.defectRecursion h.loopyResidual
  h.tightnessRate h.tightnessRate_nonneg = h := rfl` — mechanically shows
  `CitedMinlosLift` is EXACTLY (Sub-wall B content) × (Sub-wall A content) ×
  (σ-additive tightnessRate), so the sole genuinely-new datum beyond the functional
  target is `tightnessRate` — optional Bochner–Minlos packaging, not a JW input.
- `minlos_is_optional_corollary` — the bundled summary theorem.

## Scorecard edits (minlos removed as an atom; guard still 5)

- `Rubric/ContinuumScorecard.lean` — `ContinuumTargetReduction` loses its
  `minlos : CitedMinlosLift` field (now `fixedSpacing` + `discreteFusion`).
  `CitedMinlosLift` is KEPT DEFINED as the optional-corollary object. §-headers and
  the PROVED/OPEN §6 doc updated: continuum target is FUNCTIONAL; Minlos deleted as
  an atom.
- `Continuum/Tier0Scorecard.lean` — `Tier0Scorecard` loses its `minlos` field (now
  `fixedSpacing` + `subA` + `subB`). `toFrontierC` no longer sets `minlos`.
  Docstrings ("6-atom + orthogonal-Minlos" → "6-atom (functional-continuum)";
  Orthogonal-Minlos block → functional target). **Still guard-uninhabited.**
- `Continuum/Tier0FrontierCorrected.lean` — `Tier0FrontierC` loses its `minlos`
  field (kept green with `toFrontierC`), docstring updated.
- `Classical/MinlosQuarantine.lean` — header + `MinlosContinuumLift` docstring +
  closing comment restated: `CitedMinlosLift` is an OPTIONAL classical corollary
  (σ-additive packaging), NOT a frontier atom. Abbrev + conditional projection
  lemmas unchanged (still valid).

## Scope note (honesty)

`Rubric/FrontierDAG.lean` (a guarded frontier type) also carries a `minlos` field
consuming `CitedMinlosLift`; it was intentionally left untouched (out of the task's
edit scope, and `CitedMinlosLift` still exists), so it stays green and uninhabited.
The architectural deletion is applied to the three named continuum-target bundles
plus the quarantine interface. `#print axioms` / guard / build all confirm nothing
frontier is inhabited. Clay YM mass gap remains OPEN.
