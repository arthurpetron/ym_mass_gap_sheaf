/-
Continuum SU(2) Wilson measure: type-level interface for Milestone 7.2.

This module exposes the data of the projective-limit construction of
the continuum SU(2) Wilson measure `μ_∞` as developed in the paper
`formal/continuum-measure.tex` (Milestone 7.2).

# The decision: paper-only existence

The Daniell--Kolmogorov extension theorem on compact-Hausdorff inverse
systems is the analytical workhorse of Milestone 7.2.  Per the
work-plan's explicit open-question kickoff for 7.2, this project has
committed to the **Lean-paper hybrid**: the existence proof of `μ_∞`
lives in the paper (`formal/continuum-measure.tex` §5), and the Lean
module here provides only the type-level interface that downstream
Phases 8 (OS axioms) and 9 (mass-gap statement) can reference.

# What this module delivers

  * `ProjectiveSystem` — the data of an inverse system of measure
    spaces (Definitions 2.3 and 2.4 of the paper): a sequence of
    "measure-space-like" objects + the coarsening morphisms, abstract
    over the Q' / Reals constructive layer.
  * `is_consistent` — the Kolmogorov consistency predicate
    (Definition 3.1 of the paper).
  * `ContinuumMeasure` — a `ProjectiveSystem` + a `Consistent` witness
    + an abstract "extension exists" token (the paper-level invocation
    of Theorem 4.1, Daniell--Kolmogorov).
  * `su2_continuum_measure` — the SU(2) instance, built abstractly
    from the project's existing inductive-state machinery
    (`YMGap.RG.InductiveState`); the consistency and extension-exists
    fields are abstract handles whose semantics is "see
    `formal/continuum-measure.tex` §3 and §5."

# What this module does NOT do

  * Construct `μ_∞` as a Lean term inhabiting a constructive measure
    theory.  Requires `lean/YMGap/Constructive/Reals.lean` (Bishop-
    style constructive Cauchy reals + measure theory), explicitly NOT
    built at this milestone.  Scoped to Milestone 7.3.
  * Prove the consistency theorem `Tbstar μ_{k+1} = μ_k`.  Lives in
    the paper §3 and depends on closing the analytical sorries
    `[P2.1]` (`domGlue_preserves_KP`) — out of scope here.
  * Prove `μ_∞`-supports Wilson-loop area law (Proposition 6.1 of the
    paper).  Lives in the paper §6 and lifts the Phase-7.1
    `sigma_hat_uv_limit_positive` from Q' partial sums to a
    constructive lower bound on Wilson-loop expectations under `μ_∞`.

# Lean axiom-gate (AGENTS.md Rule 1)

This module declares structures and definitions; it proves no theorems
with analytic content, so the only theorem-level export
(`continuum_measure_signature_axiom_clean`) reports an empty axiom
list.  All type signatures and constructor definitions are axiom-clean
by construction.
-/

import YMGap.Continuum.SigmaHatLimit

namespace YMGap.Continuum.ContinuumMeasure

/-! ## Projective system data

A `ProjectiveSystem` packages the inverse-system data of
`formal/continuum-measure.tex` §2 abstractly: a per-scale "measure
space" type (left abstract as a single carrier type `M`) and a
coarsening map at each scale.

The carrier `M` is intentionally abstract.  In the paper, `M_k` is
`Prob(SU(2)^E_k)`; in the eventual constructive measure-theory build-out
it would be a constructive analogue.  Here we expose only the inverse-
system shape that downstream Phases 8/9 need to refer to.
-/

/-- Inverse-system data: a per-scale measure object and a per-step
coarsening morphism from scale `k+1` down to scale `k`.

This abstracts over the choice of constructive measure-space carrier:
in the eventual Constructive/Reals.lean build-out, `M` instantiates to
the constructive-measure type; in the paper, `M` is
`Prob(SU(2)^E_k)`. -/
structure ProjectiveSystem (M : Nat → Type) where
  /-- The coarsening morphism `μ_{k+1} ↦ μ_k` at each scale. -/
  coarsen : ∀ k, M (k + 1) → M k

/-! ## Kolmogorov consistency

The `is_consistent` predicate captures Definition 3.1 of the paper.
The corresponding theorem (Theorem 3.2: the Wilson-measure family is
consistent) lives in the paper and depends on closing the Phase-2
analytical sorries; this module exposes only the predicate.
-/

/-- A choice of per-scale measure `pick : ∀ k, M k` is
**Kolmogorov-consistent** with a `ProjectiveSystem` iff each
`coarsen` step transforms `pick (k+1)` into `pick k`.

Definition 3.1 of `formal/continuum-measure.tex`. -/
def is_consistent {M : Nat → Type} (sys : ProjectiveSystem M)
    (pick : ∀ k, M k) : Prop :=
  ∀ k, sys.coarsen k (pick (k + 1)) = pick k

/-! ## The continuum-measure record

`ContinuumMeasure` packages: a projective system, a consistent family
of measures, and an abstract "the limit measure exists" token.

The token is an abstract `Type` parameter `LimitMeasure` representing
the constructive-measure carrier of `μ_∞`.  It is supplied externally
(in the eventual 7.3 build-out) and is opaque here.

The pushforward laws `(pi_k)_* μ_∞ = μ_k` (Theorem 4.1 of the paper)
are recorded as a field `pushforward_to_stage`, a per-`k` morphism
`LimitMeasure → M k` together with an axiom-free record of which
`pick k` it agrees with.  At this milestone we expose the morphism
field abstractly; the equality-with-`pick` claim is the paper-level
Daniell--Kolmogorov conclusion.
-/

/-- The continuum-measure interface.

Carries:
  * `sys : ProjectiveSystem M` — the inverse-system data.
  * `pick : ∀ k, M k` — the per-scale measures.
  * `consistent : is_consistent sys pick` — the Kolmogorov consistency
    witness (paper-level proof; here a Prop input).
  * `LimitMeasure : Type` — the constructive-measure carrier of `μ_∞`,
    abstract at this milestone (the paper-level analytical object,
    instantiated by the Daniell--Kolmogorov extension).
  * `limit : LimitMeasure` — the limit measure itself.
  * `pushforward_to_stage : ∀ k, LimitMeasure → M k` — the per-stage
    projection `(pi_k)_*`, abstract here.

The paper-level statement that `pushforward_to_stage k limit = pick k`
for every `k` is **Theorem 4.1** of `formal/continuum-measure.tex` and
the load-bearing claim that the field `consistent` plus the
`LimitMeasure` data witness *is* a continuum measure.  We do not state
that equality as a field here, since stating it constructively
requires decidable equality on `M k` (which is itself a constructive-
measure-theory question deferred to 7.3).

# Naming convention

This is a `structure`, not a `Prop`-valued definition: a
`ContinuumMeasure` is the **data** of an interpretation, not a
property.  The paper's existence theorem (Theorem 4.1 + the SU(2)
instance) is what justifies inhabiting this structure for the
canonical SU(2) Wilson system. -/
structure ContinuumMeasure (M : Nat → Type) where
  sys : ProjectiveSystem M
  pick : ∀ k, M k
  consistent : is_consistent sys pick
  LimitMeasure : Type
  limit : LimitMeasure
  pushforward_to_stage : ∀ k, LimitMeasure → M k

/-! ## The SU(2) instance (type-only)

`su2_continuum_measure` is the SU(2) instance of `ContinuumMeasure`.
At this milestone its `consistent` field is supplied as an abstract
parameter (the paper-level Theorem 3.2), and its `LimitMeasure` /
`limit` / `pushforward_to_stage` fields are likewise abstract.

The construction takes:
  * `M : Nat → Type` — the SU(2) per-scale measure carrier (abstract,
    awaiting Reals.lean).
  * `sys : ProjectiveSystem M` — the abstract block-spin coarsening
    system.
  * `pick : ∀ k, M k` — the per-scale Wilson measures.
  * `consistent : is_consistent sys pick` — paper-level Theorem 3.2.
  * `LimitMeasure : Type`, `limit`, `pushforward_to_stage` — paper-
    level Theorem 4.1.

This is a smart constructor / passthrough, not a definition that
proves anything.  Its purpose is to give downstream Phases 8 and 9
something to refer to syntactically when stating their theorems
against `μ_∞`. -/
def su2_continuum_measure
    (M : Nat → Type)
    (sys : ProjectiveSystem M)
    (pick : ∀ k, M k)
    (consistent : is_consistent sys pick)
    (LimitMeasure : Type)
    (limit : LimitMeasure)
    (pushforward_to_stage : ∀ k, LimitMeasure → M k) :
    ContinuumMeasure M :=
  { sys := sys,
    pick := pick,
    consistent := consistent,
    LimitMeasure := LimitMeasure,
    limit := limit,
    pushforward_to_stage := pushforward_to_stage }

/-! ## Reference to Phase 7.1: σ̂_∞ > 0 lives at the Q' layer

The framework theorem `SigmaHatLimit.sigma_hat_uv_limit_positive` is
the Q'-rational form of σ̂_∞ > 0.  Proposition 6.1 of
`formal/continuum-measure.tex` lifts that to the area-law decay of
Wilson-loop expectations under `μ_∞`.  Stating the lifted form here
would require the constructive-measure layer; we record the
dependency via the import only. -/

/-- A trivial sentinel theorem confirming that the type signatures of
this module are axiom-clean.  Since the module proves no analytical
content, the only theorem-level export reports an empty axiom list.

This is the project-convention way of documenting that the module's
data-level definitions (`ProjectiveSystem`, `ContinuumMeasure`,
`is_consistent`, `su2_continuum_measure`) introduce no analytic
sorries or axiomatic content. -/
theorem continuum_measure_signature_axiom_clean :
    True := trivial

end YMGap.Continuum.ContinuumMeasure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumMeasure.continuum_measure_signature_axiom_clean
#print axioms YMGap.Continuum.ContinuumMeasure.is_consistent
#print axioms YMGap.Continuum.ContinuumMeasure.su2_continuum_measure
