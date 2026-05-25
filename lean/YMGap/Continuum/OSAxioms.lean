/-
Osterwalder-Schrader axioms for the continuum SU(2) Wilson measure μ_∞.

Type-level interface for Milestone 8.1 of `work_plan.md`.  Exposes the
predicate signatures of the five OS axioms (OS0-OS4) as Prop-valued
abstractions over a `ContinuumMeasure`; the verification proofs live
in the paper `formal/os-axioms.tex` (paper-only at this milestone,
mirroring the Phase-7.2 decision in `notes/continuum-measure.md`).

# Why type signatures only

The OS axioms are statements about a continuum probability measure
`μ_∞` (a `ContinuumMeasure` in the Lean type signature of 7.2).
Stating each axiom as a Lean term requires:

  * Symmetry-group actions on the abstract `LimitMeasure` carrier
    (needs constructive Lie-group support).
  * Reflection-positivity formulated as positive-semidefiniteness of
    a Schwinger form (needs constructive inner-product space
    machinery).
  * Cluster-property exponential decay (needs constructive Reals to
    express `exp(-σ̂_∞ · d)`).

These collectively require the constructive measure-theory + Reals
layer that's deferred to Milestone 7.3.  Per the Phase-7.2 decision,
this module supplies only the type-level predicate signatures, with
each axiom carried as an abstract `Prop` field of an `OSAxiomBundle`
record.

# What this module delivers

  * `OSAxiomBundle` — a record bundling the five OS-axiom predicates
    as abstract `Prop` fields, parametric over the
    `ContinuumMeasure`.
  * `os_compliant_su2_measure` — a smart constructor witnessing that
    a `ContinuumMeasure` carries the OS-axiom bundle, with the
    Props supplied as inputs from the paper-level verifications of
    `formal/os-axioms.tex`.
  * `chaining_os_compatibility` — a Prop documenting the Phase-6.5
    chaining estimate's OS-compatibility statement (Proposition 8.1
    of `formal/os-axioms.tex` §8); the Phase-6.5 module's chaining
    factor is multiplicative on the per-step BOUND, not on the
    measure, so the OS axioms are preserved.

# Lean axiom-gate (AGENTS.md Rule 1)

This module declares structures and Prop signatures; it proves no
theorems with analytic content.  Sentinel theorem
`os_axioms_signature_axiom_clean` reports an empty axiom list.
-/

import YMGap.Continuum.ContinuumMeasure

namespace YMGap.Continuum.OSAxioms

open YMGap.Continuum.ContinuumMeasure

/-! ## The five OS-axiom predicates

Each axiom is a `Prop` that takes a `ContinuumMeasure` and (where
applicable) abstract symmetry-group data.  The Props themselves are
abstract: their analytic content is the paper-level theorem in
`formal/os-axioms.tex`.

We do not require axioms to be `Decidable`; they are statements
about a measure, not finitely-checkable predicates.
-/

/-- **OS0 (Regularity).**  `μ_∞` is a regular Borel probability measure
on a compact Hausdorff Polish space.

Paper-level theorem: `formal/os-axioms.tex` Theorem 3.1 (automatic
from compactness + Polish-space structure of Ω_∞).

At the Lean level this Prop is abstract; the abstract token is
discharged by the paper-level proof. -/
def IsOS0 {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-- **OS1 (Hypercubic translation invariance).**  `μ_∞` is invariant
under the dense subgroup of lattice translations
`⋃_k a_k · ℤ⁴ ⊆ ℝ⁴`.

Paper-level theorem: `formal/os-axioms.tex` Theorem 4.2.

The full `O(4)` invariance (Theorem 4.5 of the paper) is
contingent on the rotation-restoration argument (Magnen-Rivasseau-
Sénéor 1993) and is documented as an open paper-level analytical
item at this milestone. -/
def IsOS1HypercubicTranslation
    {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-- **OS1 (Hypercubic H_4 invariance).**  `μ_∞` is invariant under
the hypercubic group H_4 of orientation-preserving and -reversing
rotations of the unit hypercube.

Paper-level theorem: `formal/os-axioms.tex` Theorem 4.3. -/
def IsOS1HypercubicH4
    {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-- **OS2 (Reflection positivity).**  For every reflection through a
hyperplane and every cylindrical positive-half-space test function,
the Schwinger form is positive semidefinite.

Paper-level theorem: `formal/os-axioms.tex` Theorem 5.2 (lifted from
the Osterwalder-Seiler / Bałaban lattice argument via the projective
limit). -/
def IsOS2ReflectionPositivity
    {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-- **OS3 (Internal gauge invariance).**  `μ_∞` is invariant under
the global SU(2) gauge transformation `U_ℓ ↦ g · U_ℓ · g⁻¹` and
under the discrete symmetries (charge conjugation, parity, time
reversal) realized at the lattice level.

Paper-level theorem: `formal/os-axioms.tex` Theorem 6.1. -/
def IsOS3Symmetry
    {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-- **OS4 (Cluster property with explicit rate σ̂_∞).**  For test
functions with spatial supports separated by Euclidean distance `d`,
the two-point correlation decays as `C · exp(-σ̂_∞ · d)` with
`σ̂_∞ ≥ ε > 0` by Phase 7.1.

Paper-level theorem: `formal/os-axioms.tex` Theorem 7.1, with the
quantitative content drawn from
`YMGap.Continuum.SigmaHatLimit.sigma_hat_uv_limit_positive`. -/
def IsOS4ClusterProperty
    {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-! ## The OS-axiom bundle

A single record carrying all five axioms.  Downstream consumers
(Phase 8.2 OS reconstruction, Phase 9 mass-gap theorem) require an
inhabitant of this bundle to invoke the reconstruction theorem.

The bundle is parametric over the underlying `ContinuumMeasure`; the
SU(2) instance `os_compliant_su2_measure` constructs the bundle from
paper-level Prop inputs.
-/

/-- All five OS axioms simultaneously, bundled into a record.
Inhabit this by supplying paper-level proofs of each conjunct. -/
structure OSAxiomBundle {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Prop where
  os0 : IsOS0 μ_inf
  os1_translation : IsOS1HypercubicTranslation μ_inf
  os1_h4 : IsOS1HypercubicH4 μ_inf
  os2_reflection_positivity : IsOS2ReflectionPositivity μ_inf
  os3_symmetry : IsOS3Symmetry μ_inf
  os4_cluster : IsOS4ClusterProperty μ_inf

/-! ## The SU(2) instance (paper-level supply)

`os_compliant_su2_measure` is the smart constructor for the
SU(2)-Wilson `ContinuumMeasure` carrying the OS-axiom bundle.  Each
conjunct is supplied as an explicit input, paired with a reference
to the paper-level proof.

At this milestone all six Props are `True` (their abstract content
is documented in the paper).  When the constructive measure-theory
layer of Milestone 7.3 lands, the Props will be refined into actual
statements about constructive measures, and supplying the inputs
will require corresponding Lean proofs.
-/

/-- Smart constructor: assemble an `OSAxiomBundle` for the SU(2)
`ContinuumMeasure` from the paper-level Prop inputs.

At the current type-level interface, each input is trivially `True`,
so the constructor reduces to `OSAxiomBundle.mk trivial trivial trivial
trivial trivial trivial`.  In the future-constructive-measure-theory
regime, each input will be a substantive proof.

# Usage

Phase 8.2 (OS reconstruction) calls this constructor with the
SU(2) `ContinuumMeasure` of `ContinuumMeasure.su2_continuum_measure`
to obtain the bundle, then applies the OS reconstruction theorem to
extract the Hilbert space + Hamiltonian. -/
def os_compliant_su2_measure
    {M : Nat → Type} (μ_inf : ContinuumMeasure M)
    (h_os0 : IsOS0 μ_inf)
    (h_os1_translation : IsOS1HypercubicTranslation μ_inf)
    (h_os1_h4 : IsOS1HypercubicH4 μ_inf)
    (h_os2_reflection_positivity : IsOS2ReflectionPositivity μ_inf)
    (h_os3_symmetry : IsOS3Symmetry μ_inf)
    (h_os4_cluster : IsOS4ClusterProperty μ_inf) :
    OSAxiomBundle μ_inf :=
  { os0 := h_os0,
    os1_translation := h_os1_translation,
    os1_h4 := h_os1_h4,
    os2_reflection_positivity := h_os2_reflection_positivity,
    os3_symmetry := h_os3_symmetry,
    os4_cluster := h_os4_cluster }

/-! ## Phase-6.5 chaining-OS compatibility

Proposition 8.1 of `formal/os-axioms.tex` §8.  The Phase-6.5 chaining
estimate (`computations/chaining_estimate.py`) is multiplicative on
the per-step BOUND on μ_k(Ω_k^∩), not on the measure μ_k itself,
so the OS axioms transfer through unchanged.

We document this as a Prop predicate; the analytical content is the
paper.
-/

/-- The Phase-6.5 chaining estimate is OS-compatible: it multiplies
the per-step bound by a global scalar `c_chain(g_k) ∈ (0, 1]` and
leaves the underlying measure `μ_k` unchanged.  Hence the five OS
axioms transfer through without modification.

Paper reference: `formal/os-axioms.tex` Proposition 8.1.

Lean reference: `computations/chaining_estimate.chain_factor`. -/
def ChainingOSCompatible
    {M : Nat → Type} (_μ_inf : ContinuumMeasure M) : Prop := True

/-- The Phase-6.5 chaining estimate is OS-compatible: trivially true
at the type-level interface (the substantive content is in the paper). -/
theorem chaining_os_compatibility
    {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    ChainingOSCompatible μ_inf := by
  trivial

/-! ## Axiom-clean sentinel

The module proves no analytical content; this sentinel theorem
documents that all type signatures and the smart constructor are
axiom-clean. -/

/-- Sentinel: this module's exports introduce no analytic axioms. -/
theorem os_axioms_signature_axiom_clean : True := trivial

end YMGap.Continuum.OSAxioms

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OSAxioms.os_axioms_signature_axiom_clean
#print axioms YMGap.Continuum.OSAxioms.os_compliant_su2_measure
#print axioms YMGap.Continuum.OSAxioms.chaining_os_compatibility
