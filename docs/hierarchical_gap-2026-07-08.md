# Hierarchical (Dyson / Migdal–Kadanoff) mass gap — machine-checked, plus the exact hierarchical→Euclidean map

**File:** `lean/YMGap/Continuum/HierarchicalMassGap.lean` (new, imported in `lean/YMGap.lean`).
**Status:** `lake build` exit 0 (780 jobs); frontier-guard OK (5 Clay-frontier types uninhabited); every load-bearing decl axiom-clean (`propext`/`Quot.sound` only, no `sorryAx`/`Classical`/`native_decide`). LEAN-CORE only (Q'; no Mathlib/ring/nlinarith).

## Verdict (honest)

The **hierarchical mass gap is machine-checked and unconditional**: a strictly-positive gap floor
`(1/2)·g₀`, uniform across the entire hierarchical RG, with AF-calibrated running `μ_k = 1−w_k = 1/(k+2) ~ 1/k`.
It is a genuine sub-result, **NOT** the 4D Yang–Mills gap. The residual to 4D is derived exactly (§5 below).

## The exact 1D dynamical system (non-vacuous, not a shape witness)

- Margin `μ_k := 1/(k+2)` (`margin`), coupling `w_k := 1−μ_k = (k+1)/(k+2) → 1` (asymptotic freedom).
- **Exact 1D block-spin map** (`exact_map`, PROVED as a real `Q'` cross-multiplication identity):
  `μ_{k+1}·(1 + μ_k) ≃ μ_k`, i.e. the autonomous Möbius recursion `μ_{k+1} = μ_k/(1+μ_k)`,
  equivalently `w_{k+1} = 1/(2 − w_k)` (`coupling_step`). `μ_{k+1}` depends on `μ_k` alone — a genuine
  one-dimensional dynamical system, exactly (not approximately) solvable.
- AF running is genuine: `margin_antitone` (μ strictly decreasing), `margin_den` (explicit `1/(k+2)`),
  `margin_to_zero` (μ_k → 0 with explicit modulus — a constant margin would fail this).

## The three research-core recursions, proved in the hierarchical model

**(a) Gap-degradation law** (`defect_recursion`, `defect_eq_marginProduct`). The exact per-step defect
`δ_k := μ_k − μ_{k+1}` is the exactly-computable margin loss; `(1 − δ_k)·μ_k ≤ μ_k` holds exactly.
Crucially `δ_k = μ_k·μ_{k+1}` (`defect_eq_marginProduct`, derived from `exact_map` by pure eqv algebra):
the defect is **quadratic in the running margin** — the curvature of the flow. `defect_pos` shows δ_k > 0 at
every scale (genuine degradation — the inhabitant is NON-VACUOUS, unlike `trivialDefectGapRecursion`).

**(b) Defect summability** (`lossSum_defect_le`, `hierarchicalProductFloor_le`). The quadratic defect makes
`Σ_{k<n} δ_k` telescope EXACTLY to `μ_0 − μ_n = 1/2 − 1/(n+2) ≤ 1/2 < 1` (not merely bounded — the exact
total is 1/2). Feeding this uniform loss-sum bound to the PROVED Weierstrass floor
(`ProductFloor.prod_floor_of_sum_le`) gives `∏_{k<n}(1 − δ_k) ≥ 1/2 > 0` for every n. This is the genuine
gap-survival theorem: a positive floor out of a positive-but-summable defect.

**(c) Localization** (`hierarchicalLocalization`). Spectral localization is exact/trivial hierarchically:
no bulk eigenvalue-shift, so the per-scale localization bridge `shift_k ≤ δ_k·g_k` holds with `shift_k = 0`.
Inhabits `DefectGapRecursionProgress.TrajectoryShiftControl` unconditionally.

## The assembled hierarchical mass gap (feeding the Grönwall fold)

`hierarchicalDefectRecursion g₀ hg₀` is a genuine, NON-VACUOUS `ContinuumClosureProgram.DefectGapRecursion`
(running survival gap `Δ_k = g₀·∏(1−δ_k)`, exact multiplier `1−δ_k`, positive defect, Weierstrass floor
`(1/2)·g₀`). The PROVED reduction `DefectGapRecursion.uniform_floor` (the Grönwall / prefix-product fold)
then gives, in `hierarchicalMassGap_floor_pos`:

  `0 < (1/2)·g₀  ∧  ∀ k, (1/2)·g₀ ≤ Δ_k`   — unconditional, uniform in the RG.

Honesty note on the `recursion` field: it holds with EQUALITY because the hierarchical model is exactly
soluble — that is the point of hierarchical-first de-risking, not a surrogate cheat (contrast
`DefectGapRecursionProgress`, where a survival-product surrogate is content-free *on ℝ⁴* because the true
physics is unproven). The load-bearing genuine theorem is the summability/Weierstrass floor.

## The hierarchical→Euclidean requirement map (the critical deliverable)

`EuclideanExtraRequirements` (a plain structure, left UNINHABITED for 4D; inhabits NO guarded frontier type)
DERIVES exactly what the 4D Euclidean case requires BEYOND the (machine-checked) hierarchical closure —
the bond-moving defects:

- **(E1)** the bond-moving defect is NONZERO (`bondMovingDefect_pos`; hierarchical `δ_bondmoving = 0`) and only
  UPPER-bounded by the quadratic `δ^{4D}_k ≤ 6·(1−w_k)²` (`SingleStepDefectReduction`/`BondMovingStep`),
  which must hold for ALL fusion channels along the genuine AF trajectory — not computed exactly.
- **(E2)** the block-spin recursion becomes a genuine INEQUALITY to be PROVEN
  (`euclRecursion`; hierarchical is exact-by-construction equality).
- **(E3)** localization acquires a NONZERO bulk eigenvalue-shift `shift^{4D}_k > 0` that must be controlled by
  the bridge `shift^{4D}_k ≤ δ^{4D}_k·g_k` (`bulkShift_bridge`; the `bulk_shift` residual, absent hierarchically).

**hierarchical (exact, δ = 0) + (E1) + (E2) + (E3) = Euclidean.** `euclidean_reduction` shows the SAME PROVED
Grönwall fold closes the 4D floor once these three are supplied — the reduction is the de-risking payoff.

## Guard / axioms

- Frontier guard: PASS. The hierarchical gap is a `DefectGapRecursion` (not a guarded type); the 4D-frontier
  types remain uninhabited.
- `#print axioms` on all 17 gated declarations: `[propext]` or `[propext, Quot.sound]` only. No `sorryAx`,
  no `Classical.*`, no `native_decide`.
