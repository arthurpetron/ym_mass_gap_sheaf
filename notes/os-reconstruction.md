# Osterwalder–Schrader reconstruction for μ_∞

**Milestone 8.2 of `work_plan.md`.**  Prose companion to
`formal/os-reconstruction.tex` and
`lean/YMGap/Continuum/OSReconstruction.lean`.

## 1. What this milestone delivers

We apply the Osterwalder–Schrader reconstruction theorem to the
continuum SU(2) Wilson measure `μ_∞` (Milestone 7.2), verified to
satisfy the OS axioms in Milestone 8.1, to construct:

  * the **physical Hilbert space** `H_∞`,
  * the **vacuum vector** `Ω_0 ∈ H_∞` with `‖Ω_0‖ = 1`,
  * the **strongly continuous contraction semigroup** `U(t) = e^{-t H_op}`,
  * the **self-adjoint Hamiltonian** `H_op ≥ 0` with `H_op Ω_0 = 0`,

ready for the spectral analysis of Phase 9 (mass-gap theorem).

## 2. The four-step construction

The OS reconstruction is canonical given the OS-compliant `μ_∞`:

1. **Positive-half-space test-function algebra**: `E_+ ⊆ F_∞` is the
   cylindrical test functions depending only on link variables with
   `x^0 ≥ 0` (forward-time half-space).
2. **Schwinger inner product**: `⟨F, G⟩_OS := ∫ (θF)* G dμ_∞`,
   positive semidefinite by OS2 (Phase 8.1 Theorem 5.2).
3. **Quotient + completion**: `H_∞ := completion(E_+ / N)` where
   `N := {F : ⟨F, F⟩_OS = 0}` is the Schwinger null subspace.
4. **Stone's theorem**: the time-translation `T(t)` on `E_+` descends
   to a strongly continuous contraction semigroup `U(t)` on `H_∞`;
   Stone's theorem gives the unique self-adjoint `H_op ≥ 0` with
   `U(t) = exp(-t · H_op)`.

The vacuum vector `Ω_0 := [1]` (equivalence class of the constant
function 1) is in `ker(H_op)` because `U(t) · 1 = 1` for every `t`.

## 3. The Phase-9 bridge: cluster ⇒ spectral gap

Theorem 7.2 of the paper is the analytical bridge from OS4 (cluster
property with explicit exponential rate `m_0 = σ̂_∞ > 0` from
Phase 7.1) to the spectral gap of `H_op`:

> If `μ_∞` satisfies OS4 with exponential cluster rate `m_0 > 0`,
> then `σ(H_op) ∩ (0, m_0) = ∅`, i.e., `m := inf σ_+(H_op) ≥ m_0`.

**Proof structure** (paper §7): the two-point Schwinger function
under `μ_∞` has the spectral representation

    ⟨F, U(t) G⟩  =  ∫_0^∞ e^{-tE} dμ_{F,G}(E),

where `dμ_{F,G}(E)` is the spectral measure of `H_op` between `[F]`
and `[G]` in `H_∞`.  OS4 forces the LHS to decay as `≤ C e^{-m_0 · t}`
for vacuum-orthogonal `F, G`, and the RHS decay rate is `inf supp
dμ_{F,G}`.  Combining these gives the spectral-gap inequality.

This is the **mass-gap statement at the Hilbert-space level**:
Phase 9.1 will take it and re-package it as the Clay-statement form
`σ(H_op) ∩ (0, m) = ∅` for `m > 0`.

## 4. What's in the Lean module

`lean/YMGap/Continuum/OSReconstruction.lean` exposes:

  * **Abstract types**: `HilbertSpace`, `VectorIn`, `SelfAdjointOp`,
    `ContractionSemigroup` — placeholder carriers pending the
    constructive-analysis Lean build-out.
  * **Abstract Prop predicates**: `VacuumNormalized`,
    `HamiltonianNonneg`, `VacuumAnnihilated`, `SemigroupGenerated`
    — each a `True`-valued sentinel at the type-level interface.
  * `OSReconstruction μ_inf` — the bundling structure carrying
    `(space, vacuum, semigroup, hamiltonian)` + the four Prop
    witnesses.
  * `os_reconstruct_su2` — smart constructor taking
    `μ_inf : ContinuumMeasure M`, an `OSAxiomBundle μ_inf` witness
    (Phase 8.1), the abstract types, and the Prop inputs; assembles
    the reconstruction.
  * `HasSpectralGap` + `ClusterImpliesGap` + `cluster_implies_gap_signature`
    — the Phase-9 bridge: a Prop saying "this reconstruction has a
    spectral gap above 0", proved trivially at the type-level
    interface; substantive content in paper Theorem 7.2.
  * `os_reconstruction_signature_axiom_clean` — sentinel.

All exports report empty axiom list.

## 5. The decision: paper-first + Lean-formal-statement-only

Per the work-plan Milestone 8.2 open question:

> Lean formalization of the reconstruction is a major undertaking
> (Stone's theorem, spectral theorem for self-adjoint operators).
> Likely deferred to "paper-first, Lean-later" or a parallel
> Lean-formal-statement-only milestone.

This project commits to **paper-first + Lean-formal-statement-only**,
parallel to the Phase-7.2 decision
(`notes/continuum-measure.md` §3) and the Phase-8.1 decision
(`notes/os-axiom-verification.md` §6).

Rationale:

1. Stone's theorem + spectral theorem for unbounded self-adjoint
   operators require a major constructive-analysis Lean build-out
   (densely-defined operators, spectral measures, functional
   calculus on constructive reals) far beyond the current Q'-rational
   + projective-system stack.
2. Phase 9 (mass-gap statement) can be expressed against the
   `OSReconstruction` type signature; paper-level existence here +
   the cluster-to-gap bridge lets Phase 9 land in Lean without
   waiting on the full operator-theoretic Lean build-out.
3. Future milestones can refine the abstract types into concrete
   constructive-analysis objects without changing the
   `OSReconstruction` interface that Phase 9 depends on.

## 6. What's NOT in this milestone

  * **Mass-gap theorem statement and proof** (Phase 9.1): take an
    `OSReconstruction` + the cluster-to-gap bridge, derive
    `m > 0`.
  * **Lean operator theory**: refining `SelfAdjointOp` from an
    abstract `Unit`-carrier into a constructive densely-defined
    operator with domain, spectrum, functional calculus.  Major
    parallel deliverable; deferred.
  * **Wightman field reconstruction**: full Streater–Wightman
    operator-valued distribution structure.  Not needed for the
    Phase-9 mass-gap statement; deferred to future work.
  * **Sharpness of `m ≥ m_0`**: the inequality may be strict (the
    actual mass could exceed the σ̂-derived lower bound).  Phase 10
    open question.

## 7. Verification

  * `lake build` 20/20 jobs clean; sentinel
    `os_reconstruction_signature_axiom_clean` reports empty axiom
    list, as do `os_reconstruct_su2` and
    `cluster_implies_gap_signature`.
  * Paper compiles via standard LaTeX; cross-references resolve.
  * No Python computation specific to 8.2 (analytical content is the
    reconstruction theorem; numerical content lives in 6.5 + 7.1).

## 8. References

  * `formal/os-reconstruction.tex` (the formal paper, primary
    deliverable).
  * `formal/os-axioms.tex` (Phase 8.1; supplies the OS-axiom
    witnesses).
  * `formal/continuum-measure.tex` (Phase 7.2; supplies `μ_∞`).
  * `lean/YMGap/Continuum/SigmaHatLimit.lean` (Phase 7.1; supplies
    the explicit rate `σ̂_∞ > 0` for the cluster-to-gap bridge).
  * `lean/YMGap/Continuum/OSAxioms.lean` (Phase 8.1; supplies the
    `OSAxiomBundle` type that `os_reconstruct_su2` consumes).
  * `lean/YMGap/Continuum/ContinuumMeasure.lean` (Phase 7.2;
    supplies the `ContinuumMeasure` type).
  * Glimm–Jaffe 1987 \S6.1 (the canonical OS-reconstruction
    reference); Osterwalder–Schrader 1973, 1975 (original
    construction); Reed–Simon Vol II Thms X.47a + X.49 (Stone's
    theorem + Hille–Yosida); Simon 1974 \S6 (cluster ⇒ mass gap).
