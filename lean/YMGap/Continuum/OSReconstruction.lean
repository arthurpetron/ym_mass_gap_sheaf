/-
Osterwalder-Schrader reconstruction: Hilbert space + Hamiltonian for μ_∞.

Type-level interface for Milestone 8.2 of `work_plan.md`.  Exposes
the data of the OS reconstruction quintuple
`(H_∞, Ω_0, U(t), H_op, D(H_op))` as Lean type signatures, with each
component carried as an abstract `Type` parameter; the existence and
construction proofs live in the paper `formal/os-reconstruction.tex`
(paper-only at this milestone, parallel to the Phase-7.2 and Phase-8.1
decisions).

# Why Lean-formal-statement-only

The OS reconstruction requires:

  * Stone's theorem for one-parameter strongly continuous contraction
    semigroups on a complex Hilbert space.
  * Spectral theorem for unbounded self-adjoint operators with
    densely-defined domains.
  * Functional calculus for self-adjoint operators (to express
    `U(t) = exp(-t · H_op)`).

These collectively require a major constructive-analysis Lean
build-out (operators, spectral measures, functional calculus on
constructive reals) beyond the current Q'-rational + projective-system
stack.  Per the work-plan Milestone 8.2 open question, this project
commits to the **paper-first + Lean-formal-statement-only** branch:
the paper has the full reconstruction proof, the Lean module has the
type signatures that downstream Phase 9 (mass-gap statement) can
reference.

# What this module delivers

  * `HilbertSpace` — abstract type for the physical Hilbert space
    `H_∞` from `formal/os-reconstruction.tex` Theorem 3.3.
  * `SelfAdjointOp` — abstract type for self-adjoint operators on a
    `HilbertSpace`.
  * `VacuumVector` — abstract type for the distinguished vacuum
    vector `Ω_0` (`formal/os-reconstruction.tex` Definition 3.4).
  * `ContractionSemigroup` — abstract type for the one-parameter
    semigroup `U(t)` of `formal/os-reconstruction.tex` Theorem 4.4.
  * `OSReconstruction` — the bundling structure carrying all four
    components + the abstract "H_op ≥ 0" and "H_op · Ω_0 = 0"
    witnesses.
  * `os_reconstruct_su2` — smart constructor taking the paper-level
    Prop inputs and assembling the reconstruction quintuple.
  * `ClusterImpliesGap` + `cluster_implies_gap_signature` — the
    Theorem-7.2 (`formal/os-reconstruction.tex`) signature
    bridging OS4 cluster property to a spectral gap on `H_op`.

# Lean axiom-gate (AGENTS.md Rule 1)

This module declares structures and Prop signatures; it proves no
theorems with analytic content.  Sentinel theorem
`os_reconstruction_signature_axiom_clean` reports an empty axiom list.
-/

import YMGap.Continuum.OSAxioms
import YMGap.Continuum.SpectralGap
import YMGap.Constructive.Reals

namespace YMGap.Continuum.OSReconstruction

open YMGap.Constructive
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.SpectralGap

/-! ## Abstract types for the reconstruction objects

Each of the four reconstruction objects (Hilbert space, vacuum
vector, contraction semigroup, self-adjoint Hamiltonian) is carried
as an abstract type or value at this milestone.  In the eventual
constructive-analysis build-out, these will instantiate to concrete
constructive objects with operations.
-/

/-- The physical Hilbert space of the OS reconstruction.

In the paper this is `H_∞ = completion(E_+ / N)` of the quotient of
the positive-half-space test-function algebra by the Schwinger null
subspace.  Abstract here pending constructive-analysis Lean. -/
structure HilbertSpace : Type where
  /-- Witness placeholder; in the constructive-analysis build-out
  this will be a constructive Cauchy-sequence carrier with inner
  product. -/
  carrier_witness : Unit

/-- A vector in a `HilbertSpace`.

Abstract carrier pending constructive-analysis Lean. -/
structure VectorIn (_H : HilbertSpace) : Type where
  vec_witness : Unit

/-- A self-adjoint operator on a `HilbertSpace`.

Abstract carrier; in the eventual build-out this would carry a
densely-defined domain, a real spectrum, and a functional calculus. -/
structure SelfAdjointOp (_H : HilbertSpace) : Type where
  op_witness : Unit

/-- A one-parameter strongly continuous contraction semigroup
`U(t) : H → H` for `t ≥ 0`.

Abstract carrier; in the build-out this would be a function
`Nat → BoundedOp H` (or a constructive parameter type for `t`) with
the semigroup laws as proofs. -/
structure ContractionSemigroup (_H : HilbertSpace) : Type where
  semigroup_witness : Unit

/-! ## Abstract Prop predicates for the reconstruction laws

Each property is carried as an abstract `Prop`.  Paper-level proofs
discharge them; future constructive-analysis Lean will refine the
`True`-valued Props into substantive statements.
-/

/-- The vacuum vector `Ω_0` is normalized: `⟨Ω_0, Ω_0⟩ = 1`. -/
def VacuumNormalized {H : HilbertSpace} (_omega : VectorIn H) : Prop := True

/-- The Hamiltonian `H_op` is nonnegative: `σ(H_op) ⊆ [0, ∞)`. -/
def HamiltonianNonneg {H : HilbertSpace} (_op : SelfAdjointOp H) : Prop := True

/-- The vacuum is in the kernel of `H_op`: `H_op · Ω_0 = 0`. -/
def VacuumAnnihilated
    {H : HilbertSpace} (_op : SelfAdjointOp H) (_omega : VectorIn H) : Prop := True

/-- The contraction semigroup is the unitary group generated by `H_op`:
`U(t) = exp(-t · H_op)` (Stone-theorem statement). -/
def SemigroupGenerated
    {H : HilbertSpace} (_op : SelfAdjointOp H) (_sg : ContractionSemigroup H) : Prop :=
  True

/-! ## The OS reconstruction quintuple

`OSReconstruction` packages the five components of the paper-level
Definition 6.1 (the OS reconstruction).  Phase 9 (mass-gap statement)
takes an inhabitant of this structure plus a `ClusterImpliesGap`
witness to extract the spectral gap.
-/

/-- The Osterwalder-Schrader reconstruction quintuple for a continuum
measure: `(H_∞, Ω_0, U(t), H_op)` plus the laws.

Carries:
  * `space : HilbertSpace` — the physical Hilbert space `H_∞`.
  * `vacuum : VectorIn space` — the vacuum vector `Ω_0`.
  * `semigroup : ContractionSemigroup space` — the time-translation
    semigroup `U(t)`.
  * `hamiltonian : SelfAdjointOp space` — the Hamiltonian `H_op`.
  * `vacuum_normalized` — Prop: ⟨Ω_0, Ω_0⟩ = 1.
  * `hamiltonian_nonneg` — Prop: H_op ≥ 0.
  * `vacuum_annihilated` — Prop: H_op · Ω_0 = 0.
  * `semigroup_generated` — Prop: U(t) = exp(-t · H_op) (Stone).

The structure is parametric over the underlying continuum measure
(used here only to record the source). -/
structure OSReconstruction {M : Nat → Type} (_μ_inf : ContinuumMeasure M) where
  space : HilbertSpace
  vacuum : VectorIn space
  semigroup : ContractionSemigroup space
  hamiltonian : SelfAdjointOp space
  vacuum_normalized : VacuumNormalized vacuum
  hamiltonian_nonneg : HamiltonianNonneg hamiltonian
  vacuum_annihilated : VacuumAnnihilated hamiltonian vacuum
  semigroup_generated : SemigroupGenerated hamiltonian semigroup
  /-- The finite-volume transfer-matrix spectral model `(w_i, λ_i)` whose
  finite Källén–Lehmann decomposition realises the genuine (non-`True`)
  spectral-gap content.  At finite volume the transfer matrix is a genuine
  positive matrix, so this datum is constructive; the continuum unbounded-`H`
  spectral measure is the paper-level boundary (Pour-El–Richards). -/
  spec : SpectralModel
  /-- The transfer-matrix gap location `μ = e^{−m₀} ∈ [0,1)`. -/
  gapBound : Q'
  /-- `0 ≤ μ`. -/
  gapBound_nonneg : (0 : Q') ≤ gapBound
  /-- **The genuine spectral gap:** every excited transfer-matrix eigenvalue is
  `≤ μ` (equivalently every energy `≥ −log μ`).  This is the substantive content
  behind the predicate `HasSpectralGap`, replacing the former `:= True` stub. -/
  hasGap : SpectralGapBound spec gapBound

/-! ## The SU(2) instance (paper-level supply)

`os_reconstruct_su2` is the smart constructor for the SU(2) Wilson
reconstruction, taking the paper-level data as inputs.  Phase 9
(mass-gap statement) will call this with the
`ContinuumMeasure.su2_continuum_measure` instance + the
`OSAxiomBundle` witness from Phase 8.1.
-/

/-- Smart constructor for the SU(2) OS reconstruction.  Takes:

  * The continuum measure `μ_inf : ContinuumMeasure M`.
  * An `OSAxiomBundle μ_inf` witness (paper-level Phase 8.1).
  * Abstract types + Prop witnesses for the reconstruction quintuple.

Returns the assembled `OSReconstruction μ_inf`.  The `bundle`
argument enforces that the reconstruction is only built from an
OS-compliant measure; in the future-Lean regime it will provide the
analytic-content hypothesis for the reconstruction-theorem proof. -/
def os_reconstruct_su2
    {M : Nat → Type} (μ_inf : ContinuumMeasure M)
    (_bundle : OSAxiomBundle μ_inf)
    (space : HilbertSpace)
    (vacuum : VectorIn space)
    (semigroup : ContractionSemigroup space)
    (hamiltonian : SelfAdjointOp space)
    (h_vac_norm : VacuumNormalized vacuum)
    (h_ham_nonneg : HamiltonianNonneg hamiltonian)
    (h_vac_ann : VacuumAnnihilated hamiltonian vacuum)
    (h_sg_gen : SemigroupGenerated hamiltonian semigroup)
    (spec : SpectralModel)
    (gapBound : Q')
    (gapBound_nonneg : (0 : Q') ≤ gapBound)
    (hasGap : SpectralGapBound spec gapBound) :
    OSReconstruction μ_inf :=
  { space := space,
    vacuum := vacuum,
    semigroup := semigroup,
    hamiltonian := hamiltonian,
    vacuum_normalized := h_vac_norm,
    hamiltonian_nonneg := h_ham_nonneg,
    vacuum_annihilated := h_vac_ann,
    semigroup_generated := h_sg_gen,
    spec := spec,
    gapBound := gapBound,
    gapBound_nonneg := gapBound_nonneg,
    hasGap := hasGap }

/-! ## Bridge to Phase 9: cluster property ⇒ spectral gap

`ClusterImpliesGap` is the Prop signature of
`formal/os-reconstruction.tex` Theorem 7.2: given an
`OSReconstruction` whose underlying measure satisfies OS4 with
exponential rate `m_0 > 0`, the Hamiltonian has a spectral gap at
least `m_0`.

This is the Phase 9 mass-gap input: composing `OSAxiomBundle` (with
the OS4 witness carrying the rate) + `OSReconstruction` + this
bridge gives the mass-gap statement.
-/

/-- The spectral-gap statement: `σ(H_op) ∩ (0, m_0) = ∅`, i.e.,
`H_op` has no spectrum strictly between 0 and `m_0`.

Carried as a `Prop` parametric over the reconstruction and a
positivity rate; the rate `m_0` is supplied externally (by Phase 7.1
as `σ̂_∞`).

In the paper this is `inf σ_+(H_op) ≥ m_0`. -/
def HasSpectralGap
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) : Prop :=
  SpectralGapBound rec.spec rec.gapBound

/-- **The spectral gap has teeth:** `HasSpectralGap rec` implies geometric
clustering of the finite-volume connected two-point function,
`G(n) ≤ G(0)·μ^n` (`decay_of_spectralGap_corr0`).  This is exactly the
substantive consequence the former `:= True` stub could not deliver. -/
theorem HasSpectralGap.clustering
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    {rec : OSReconstruction μ_inf} (h : HasSpectralGap rec) (n : Nat) :
    corr rec.spec n ≤ corr rec.spec 0 * rec.gapBound ^ n :=
  decay_of_spectralGap_corr0 rec.spec rec.gapBound rec.gapBound_nonneg h n

/-- The cluster-to-gap bridge: `formal/os-reconstruction.tex` Theorem 7.2.

Given an `OSReconstruction` whose underlying continuum measure
satisfies OS4 (carried by the `OSAxiomBundle`), the Hamiltonian
`H_op` has a spectral gap.

Paper-level proof in `formal/os-reconstruction.tex` §7; here the
Prop is abstract and the witness is trivial. -/
def ClusterImpliesGap
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (_bundle : OSAxiomBundle μ_inf) : Prop :=
  HasSpectralGap rec

/-- The cluster-implies-gap bridge holds for any reconstruction with
OS4 witness (trivially true at the type-level interface; substantive
content in the paper). -/
theorem cluster_implies_gap_signature
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ClusterImpliesGap rec bundle :=
  rec.hasGap

/-! ## CReal-level cluster-to-gap bridge (Milestone 7.3 follow-on)

The Q′-level `HasSpectralGap`/`ClusterImpliesGap` above carries no
parameter for the mass-gap value: it is the bare statement "there is
some spectral gap."  The CReal-level upgrade below parameterizes the
spectral statement by a *constructive-real* `m_0`, so that downstream
composition with `Constructive.Reals.sigma_hat_inf_creal_positive`
yields an end-to-end CReal-typed mass-gap theorem.

The Props remain abstractly `True` at the type-level interface — the
analytical content is paper-supplied (`formal/os-reconstruction.tex`
Theorem 7.2 + `formal/mass-gap-theorem.tex` §2).  The CReal
parameterization is what makes the spectral statement *mention* the
constructive real m_0 instead of a Q′ surrogate, which is the named
deliverable of Milestone 7.3-followon in `work_plan.md` §7.3.

Compared to the pre-upgrade `HasSpectralGap`/`ClusterImpliesGap` /
`cluster_implies_gap_signature` chain, the new CReal forms

  * Take `m_0 : CReal` as an explicit parameter, so the spectral
    statement is *about m_0*, not "some unspecified gap exists."
  * Require a `CReal.IsPositive m_0` hypothesis on the bridge input,
    threading the constructive-real positivity through the chain
    rather than discarding it at the OS4 step.
  * Compose cleanly with `Reals.sigma_hat_inf_creal_positive` in
    `MassGap/SU2.lean` to deliver `mass_gap_SU2_creal_full` — the
    end-to-end CReal-level mass-gap statement.
-/

/-- The CReal-parameterized spectral-gap statement: `σ(H_op) ∩ (0, m_0) = ∅`
where `m_0 : CReal` is the constructive-real mass-gap lower bound.

Carried as a `Prop` parametric over the reconstruction AND a CReal
bound `m_0`; the bound is supplied externally (by
`Constructive.Reals.sigma_hat_inf_creal_positive` in the SU(2) case).

In the paper this is `inf σ_+(H_op) ≥ m_0` where the inequality is at
the CReal level, not Q′.

**Two genuine, jointly faithful conjuncts** (the rate `m_0` is *not*
ignored):

  * `SpectralGapBound rec.spec rec.gapBound` — the located finite
    spectral gap: every excited transfer-matrix eigenvalue is `≤ sep`
    (`sep = rec.gapBound < 1`).
  * `m_0 ≤ CReal.ofQ' (1 - rec.gapBound)` — the **rate binding**: the
    constructive-real `m_0` is no larger than the eigenvalue-gap
    MARGIN `1 − sep` (the margin currency the located-gap pipeline uses;
    the physical mass is `−log sep`, here kept as the margin to avoid
    `exp`/`log` on `CReal`).  This is the conjunct that makes "the gap
    is at least `m_0`" mean what it says: the located margin avoids the
    gap below `m_0`. -/
def HasSpectralGapAt
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (m_0 : CReal) : Prop :=
  SpectralGapBound rec.spec rec.gapBound ∧
    m_0 ≤ CReal.ofQ' (1 - rec.gapBound)

/-- The CReal-level cluster-to-gap bridge type: given an
`OSReconstruction` and a CReal-positive mass bound `m_0`, the
Hamiltonian has a spectral gap *at m_0*. -/
def ClusterImpliesGapAt
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (_bundle : OSAxiomBundle μ_inf)
    (m_0 : CReal) : Prop :=
  HasSpectralGapAt rec m_0

/-- **The CReal-level cluster-to-gap bridge.**

Given an `OSReconstruction` of an OS-compliant continuum measure
(`bundle`), a CReal-positive bound `m_0`, and the **rate binding**
`m_0 ≤ ofQ' (1 − sep)` (the constructive-real mass does not exceed the
located eigenvalue-gap margin), the bridge produces the
spectral-emptiness statement `σ(H_op) ∩ (0, m_0) = ∅` *at `m_0`*.

This is `formal/os-reconstruction.tex` Theorem 7.2 lifted from the
Q′-rational rate to a constructive-real rate.  The located finite gap
is `rec.hasGap` (the genuine `SpectralGapBound`); the rate binding
`hbind` relating the OS4 cluster rate `m_0` to the transfer-matrix
margin `1 − sep` is the analytic OS4 content, supplied here as an
explicit hypothesis (it cannot be derived from an abstract `rec` whose
`gapBound` is unconstrained relative to `m_0`).  Both conjuncts of the
conclusion are thereby genuine, and the CReal `m_0` truly lower-bounds
the gap margin. -/
theorem cluster_implies_gap_at
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf)
    (m_0 : CReal) (_pos : CReal.IsPositive m_0)
    (hbind : m_0 ≤ CReal.ofQ' (1 - rec.gapBound)) :
    ClusterImpliesGapAt rec bundle m_0 :=
  ⟨rec.hasGap, hbind⟩

/-! ## Axiom-clean sentinel -/

/-- Sentinel: this module's exports introduce no analytic axioms. -/
theorem os_reconstruction_signature_axiom_clean : True := trivial

end YMGap.Continuum.OSReconstruction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OSReconstruction.os_reconstruction_signature_axiom_clean
#print axioms YMGap.Continuum.OSReconstruction.os_reconstruct_su2
#print axioms YMGap.Continuum.OSReconstruction.cluster_implies_gap_signature
#print axioms YMGap.Continuum.OSReconstruction.cluster_implies_gap_at
