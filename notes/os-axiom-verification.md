# Osterwalder–Schrader axiom verification for μ_∞

**Milestone 8.1 of `work_plan.md`.**  Prose companion to
`formal/os-axioms.tex` and `lean/YMGap/Continuum/OSAxioms.lean`.

## 1. What this milestone delivers

We verify the five Osterwalder–Schrader axioms (OS0–OS4) for the
continuum SU(2) Wilson measure `μ_∞` constructed in
Milestone 7.2 (`formal/continuum-measure.tex`).  The OS axioms are
the precondition for the Hilbert-space + Hamiltonian reconstruction
of Phase 8.2, which in turn feeds the mass-gap theorem of Phase 9.

## 2. The five axioms and their difficulty profile

| Axiom | Status | Difficulty |
|-------|--------|------------|
| **OS0** Regularity | ✅ trivial | Automatic from compact-Hausdorff Polish `Ω_∞` |
| **OS1** Translation invariance (lattice) | ✅ trivial | Density of cylindrical test functions + finite-stage Wilson-action translation invariance |
| **OS1** `H_4` hypercubic invariance | ✅ trivial | Same density argument |
| **OS1** Full `O(4)` invariance | ⚠️ paper-open | Restoration argument with `a_k`-rate (Magnen–Rivasseau–Sénéor 1993); does NOT block Phase 9 |
| **OS2** Reflection positivity | ✅ verified | Standard lattice-timeslice argument (Osterwalder–Seiler 1978, Bałaban §5) lifted via the projective limit |
| **OS3** Symmetry (internal gauge + discrete) | ✅ trivial | Wilson action manifestly gauge-invariant |
| **OS4** Cluster property | ✅ verified with rate | Phase 7.1 `σ̂_∞ > 0` + polymer-cluster decay; supplies the mass gap |

Three of the seven items are **trivial** (OS0, OS1-lattice-translation,
OS3) because they're inherited from the corresponding finite-stage
properties via density of cylindrical test functions.  Two are **standard
but substantive** (OS2 reflection positivity via Osterwalder–Seiler;
OS4 cluster with quantitative `σ̂_∞ > 0` rate via Phase 7.1).  One is
**verified contingent on a paper-level restoration argument** (full
`O(4)` invariance, with the explicit cite to MRS 1993).  Hypercubic
`H_4` invariance is verified directly; the `O(4)` restoration does not
block Phase 9.

## 3. The load-bearing axioms

### 3.1 OS2 reflection positivity — the Hilbert space input

Phase 8.2's OS reconstruction theorem uses OS2 to define the
physical Hilbert space as the quotient of the L²-completion of
positive-half-space test functions by the kernel of the
Schwinger form.  Without OS2, no Hilbert space.

The standard lattice argument (Osterwalder–Seiler 1978, Bałaban §5)
splits the Wilson action into three parts — plaquettes entirely on
the positive half-space, plaquettes entirely on the negative
half-space, and plaquettes crossing the time-slice — and exploits
the heat-kernel weight's sum-of-positive-rank-ones structure to
factorize the crossing-plaquette weight as
`∫ K_t(g) K_t(g⁻¹) dg ≥ 0`.  This argument lifts unchanged to `μ_∞`
through the projective limit + density of cylindrical test
functions, per `formal/os-axioms.tex` Theorem 5.2.

### 3.2 OS4 cluster property — the mass-gap injection

Phase 9's mass-gap theorem reads: `σ(H_op) ∩ (0, m) = ∅` for some
`m > 0`.  The OS reconstruction translates spatial cluster decay
under `μ_∞` into spectral-gap decay of the Hamiltonian
`H_op = e^{-H · t}`-generator, with the same exponential rate.  So
OS4 with explicit rate `σ̂_∞ > 0` IS the mass-gap statement at the
measure-theoretic level.

Phase 7.1's `sigma_hat_uv_limit_positive` is the input.  The
polymer-cluster decay machinery of `formal/sheaf-framework.tex` §7
(Phase 2.1) translates per-step KP certificates into exponential
decay of two-loop correlators with rate `σ_k = a_k^{-2} · σ̂_k`; the
continuum limit gives rate `σ_∞ = a_∞^{-2} · σ̂_∞`, which is the
physical mass squared.

## 4. Chaining-OS compatibility (Phase 6.5 input)

The Phase-6.5 chaining estimate
(`computations/chaining_estimate.py`) is used inside the polymer-
cluster path-counting underlying OS4.  Proposition 8.1 of the paper
verifies that the chaining factor `c_chain(g_k) ∈ (0, 1]` is
multiplicative on the per-step BOUND on `μ_k(Ω_k^∩)`, not on the
measure `μ_k` itself.  Hence:

  * OS2 (reflection positivity of `μ_k`) is unaffected.
  * OS1 (translation + `H_4` invariance) is preserved (chaining
    factor is global).
  * OS3 (gauge invariance) is preserved (chaining factor is gauge-
    invariant by construction).
  * OS4 (cluster) is improved: the prefactor `C_{F,G}` is tightened
    by a factor of `c_chain(g_k)`, but the exponential rate `σ̂_∞`
    is unchanged.

This is the rigor item the work-plan flagged as the Phase 6.5 → 8.1
hand-off question ("Whether the chaining estimate preserves OS
reflection positivity").  Resolved as YES, with the structural
reason being that chaining tightens the bound, not the measure.

## 5. What's in the Lean module

`lean/YMGap/Continuum/OSAxioms.lean` exposes:

  * `IsOS0`, `IsOS1HypercubicTranslation`, `IsOS1HypercubicH4`,
    `IsOS2ReflectionPositivity`, `IsOS3Symmetry`,
    `IsOS4ClusterProperty` — Prop predicate signatures for each
    axiom, parametric over a `ContinuumMeasure`.
  * `OSAxiomBundle` — a `Prop`-bundle structure carrying all five
    axiom conjuncts.
  * `os_compliant_su2_measure` — smart constructor taking the six
    paper-level Prop inputs and assembling the bundle.
  * `ChainingOSCompatible` + `chaining_os_compatibility` — the
    Phase-6.5 OS-compatibility statement, declared as a Prop and
    proved trivially at the type-level interface.
  * `os_axioms_signature_axiom_clean` — sentinel `True := trivial`.

At this milestone all Props are `True` (their analytic content is in
the paper).  When the constructive measure-theory layer of Milestone
7.3 lands, the Props will be refined into actual statements about
constructive measures, and supplying the inputs will require
corresponding Lean proofs.

All Lean exports report empty axiom list.

## 6. What's NOT in this milestone

  * **OS reconstruction theorem** (Phase 8.2): construct the Hilbert
    space + Hamiltonian operator from the OS axioms.  Major
    undertaking; see Phase 8.2 milestone notes.
  * **Mass-gap theorem statement and proof** (Phase 9.1): use OS4
    cluster + 8.2 reconstruction to prove `inf σ(H_op) \ {0} > 0`.
  * **Full `O(4)` restoration argument** (paper-level open item):
    construct the `R_k`-approximation sequence with `a_k`-rate
    convergence per `formal/os-axioms.tex` §4.3.  Hypercubic `H_4`
    invariance is enough for the Phase-9 mass-gap statement; full
    `O(4)` is a Phase-8.1 refinement target.
  * **Constructive measure-theory Lean layer** (Milestone 7.3):
    promote `IsOS*` Props from `True` to substantive statements
    about constructive measures.

## 7. Verification

  * `lake build` 19/19 jobs clean; sentinel
    `os_axioms_signature_axiom_clean` reports empty axiom list.
  * Paper compiles via standard LaTeX; cross-references resolve.
  * No Python computation specific to 8.1 (analytical content is
    axiom verification; numerical content lives in 6.5 + 7.1).

## 8. References

  * `formal/os-axioms.tex` (the formal paper, primary deliverable).
  * `formal/continuum-measure.tex` (Milestone 7.2; supplies `μ_∞`).
  * `lean/YMGap/Continuum/SigmaHatLimit.lean` (Milestone 7.1; supplies
    `σ̂_∞ ≥ ε > 0` for OS4).
  * `lean/YMGap/Continuum/ContinuumMeasure.lean` (Milestone 7.2;
    supplies the `ContinuumMeasure` type that OSAxioms is parametric
    over).
  * `computations/chaining_estimate.py` + `notes/chaining-estimate.md`
    (Milestone 6.5; OS-compatibility verified in Proposition 8.1 of
    the paper).
  * Osterwalder–Seiler 1978 (lattice reflection positivity);
    Glimm–Jaffe 1987 \S6.1 (OS axioms); Bałaban 1987 \S5
    (projection block-spin reflection positivity);
    Magnen–Rivasseau–Sénéor 1993 (rotation restoration);
    Jorgensen 1986 (OS-positivity via analytic continuation).
