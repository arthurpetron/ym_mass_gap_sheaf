/-
Continuum SU(2) Wilson measure: type-level interface for Milestone 7.2.

This module exposes the data of the projective-limit construction of
the continuum SU(2) Wilson measure `μ_∞` as developed in the paper
`formal/continuum-measure.tex` (Milestone 7.2).

# Track B1: the inverse limit is constructed; the measure theory is not

This module builds the genuine constructive **inverse (projective) limit**
of the system and proves the Daniell--Kolmogorov *projection* law, so `μ_∞`
is now an actual term (`InvLim sys`) rather than an opaque `LimitMeasure`
token.  The hard analytic content remains parametrized/open, cleanly
isolated (see "What this module does NOT do").

# What this module delivers

  * `ProjectiveSystem` — the data of an inverse system: per-scale objects
    `M_k` + the coarsening morphisms, abstract over the constructive
    measure layer.
  * `is_consistent` — the Kolmogorov consistency predicate (Definition 3.1).
  * `InvLim sys` — the **constructive inverse limit**: the type of
    consistent threads.  Genuine (a `Σ`-type), MLTT/HoTT-valid, with the
    projection `InvLim.proj` and the proved law
    `InvLim.coarsen_proj : coarsen k (π_{k+1} t) = π_k t`.
  * `ContinuumMeasure` — `ProjectiveSystem` + `pick` + `consistent`; its
    `limit : InvLim sys` is now *constructed* (`ContinuumMeasure.limit =
    InvLim.ofConsistent consistent`) and the pushforward law
    `ContinuumMeasure.pushforward_limit_eq : π_k(μ_∞) = μ_k` is *proved*
    (axiom-free, `rfl`) — it was previously left unstated.
  * `su2_continuum_measure` — the SU(2) instance from the inverse-system
    data + the consistency witness.

# What this module does NOT do (the remaining open analysis)

  * Construct the carriers `M_k = Prob(SU(2)^{E_k})` themselves — `M`
    stays abstract.  A constructive theory of probability measures on
    compact-group lattice configurations (without Mathlib's `ℝ`) is a
    separate build-out.
  * Prove the Wilson family *is* consistent (`coarsen k μ_{k+1} = μ_k`,
    the RG-transport claim of §3); `consistent` is an input hypothesis.
  * Perform the Daniell--Kolmogorov *extension* — a consistent thread is
    the cylinder data, but turning it into a σ-additive measure on the
    configuration inverse limit, with a convergence modulus, is the open
    analytic content (`formal/continuum-measure.tex` §4--6).  This is the
    thermodynamic + continuum limit — the Clay existence problem.
  * Prove the `μ_∞` Wilson-loop area law (Proposition 6.1), lifting the
    Phase-7.1 `sigma_hat_uv_limit_positive` from `Q'` partial sums.

# Lean axiom-gate (AGENTS.md Rule 1)

The inverse-limit construction and the projection/pushforward laws are
genuine structural (`rfl`) proofs and report an empty axiom list.
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

/-! ## The constructive inverse limit

`InvLim sys` is the genuine inverse (projective) limit of the system: the
type of **consistent threads** `(x_k)_k` with `coarsen k (x_{k+1}) = x_k`.
This is an honest construction — a `Σ`-type with a `Π`-valued
compatibility field, valid in MLTT and its HoTT extension — and it
replaces the previous opaque `LimitMeasure : Type` / `limit` handles with
an actual limit object whose projection-consistency law is *proved*, not
posited.

What it captures and what it does NOT: a thread is exactly the cylinder
data of a continuum measure (a Kolmogorov-consistent family of the
per-scale objects `M_k`).  It does NOT supply the `M_k = Prob(G^{E_k})`
themselves (still abstract over the constructive-measure layer), nor the
Daniell–Kolmogorov *extension* of a consistent family to a σ-additive
measure with a convergence modulus — that is the open analytic content
(`formal/continuum-measure.tex` §4–6). -/

/-- The inverse limit: consistent threads of the projective system. -/
structure InvLim {M : Nat → Type} (sys : ProjectiveSystem M) where
  /-- The thread: a per-scale object. -/
  thread : ∀ k, M k
  /-- Kolmogorov compatibility along the thread. -/
  compat : ∀ k, sys.coarsen k (thread (k + 1)) = thread k

/-- Projection `π_k` to stage `k`. -/
def InvLim.proj {M : Nat → Type} {sys : ProjectiveSystem M}
    (t : InvLim sys) (k : Nat) : M k := t.thread k

/-- **Projection consistency, by construction:** `coarsen k (π_{k+1} t) = π_k t`. -/
theorem InvLim.coarsen_proj {M : Nat → Type} {sys : ProjectiveSystem M}
    (t : InvLim sys) (k : Nat) :
    sys.coarsen k (t.proj (k + 1)) = t.proj k := t.compat k

/-- Universal property (the relevant direction): a Kolmogorov-consistent
family is an element of the inverse limit. -/
def InvLim.ofConsistent {M : Nat → Type} {sys : ProjectiveSystem M}
    {pick : ∀ k, M k} (h : is_consistent sys pick) : InvLim sys :=
  ⟨pick, h⟩

@[simp] theorem InvLim.proj_ofConsistent {M : Nat → Type} {sys : ProjectiveSystem M}
    {pick : ∀ k, M k} (h : is_consistent sys pick) (k : Nat) :
    (InvLim.ofConsistent h).proj k = pick k := rfl

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

/-- The continuum measure `μ_∞` **as a constructed inverse-limit object**:
the consistent thread of the per-scale family `pick`.  This replaces the
previous opaque `limit : LimitMeasure` field — the limit is now an actual
term of `InvLim sys`. -/
def ContinuumMeasure.limit {M : Nat → Type} (μ : ContinuumMeasure M) :
    InvLim μ.sys := InvLim.ofConsistent μ.consistent

/-- The per-stage projection `π_k : μ_∞ ↦ μ_k` (formerly the abstract
`pushforward_to_stage` field). -/
def ContinuumMeasure.pushforward_to_stage {M : Nat → Type}
    (μ : ContinuumMeasure M) (k : Nat) : InvLim μ.sys → M k :=
  fun t => t.proj k

/-- **The Daniell–Kolmogorov pushforward law, now a theorem** (it was
left unstated/deferred in the previous interface as "requires decidable
equality on `M k`"): `π_k(μ_∞) = μ_k` for every scale `k`.  Holds
definitionally for the inverse-limit construction. -/
theorem ContinuumMeasure.pushforward_limit_eq {M : Nat → Type}
    (μ : ContinuumMeasure M) (k : Nat) :
    μ.pushforward_to_stage k μ.limit = μ.pick k := rfl

/-- The projection of `μ_∞` is itself Kolmogorov-consistent (the
inverse-limit thread condition), recovering the inverse-system law at the
limit. -/
theorem ContinuumMeasure.coarsen_pushforward {M : Nat → Type}
    (μ : ContinuumMeasure M) (k : Nat) :
    μ.sys.coarsen k (μ.pushforward_to_stage (k + 1) μ.limit)
      = μ.pushforward_to_stage k μ.limit :=
  InvLim.coarsen_proj μ.limit k

/-! ## The SU(2) instance

`su2_continuum_measure` builds the SU(2) `ContinuumMeasure` from the
inverse-system data plus the consistency witness; the limit object and its
pushforward law are then *constructed/proved* (no longer abstract handles).

The remaining inputs are exactly the open analytic content:
  * `M : Nat → Type` — the SU(2) per-scale measure carrier
    `M_k = Prob(SU(2)^{E_k})`, abstract over the constructive-measure layer.
  * `sys : ProjectiveSystem M` — the block-spin coarsening system.
  * `pick : ∀ k, M k` — the per-scale Wilson measures.
  * `consistent : is_consistent sys pick` — that the Wilson family is
    Kolmogorov-consistent (the paper-level RG-transport claim, `§3`).

Given these, `μ.limit : InvLim sys` is an actual term and
`μ.pushforward_to_stage k μ.limit = μ.pick k` is a theorem
(`ContinuumMeasure.pushforward_limit_eq`). -/
def su2_continuum_measure
    (M : Nat → Type)
    (sys : ProjectiveSystem M)
    (pick : ∀ k, M k)
    (consistent : is_consistent sys pick) :
    ContinuumMeasure M :=
  { sys := sys, pick := pick, consistent := consistent }

/-! ## Reference to Phase 7.1: σ̂_∞ > 0 lives at the Q' layer

The framework theorem `SigmaHatLimit.sigma_hat_uv_limit_positive` is
the Q'-rational form of σ̂_∞ > 0.  Proposition 6.1 of
`formal/continuum-measure.tex` lifts that to the area-law decay of
Wilson-loop expectations under `μ_∞`.  Stating the lifted form here
would require the constructive-measure layer; we record the
dependency via the import only. -/

end YMGap.Continuum.ContinuumMeasure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

The inverse-limit construction and the pushforward law are genuine
`rfl`/structural proofs — axiom-clean. -/

#print axioms YMGap.Continuum.ContinuumMeasure.InvLim.coarsen_proj
#print axioms YMGap.Continuum.ContinuumMeasure.InvLim.proj_ofConsistent
#print axioms YMGap.Continuum.ContinuumMeasure.ContinuumMeasure.pushforward_limit_eq
#print axioms YMGap.Continuum.ContinuumMeasure.ContinuumMeasure.coarsen_pushforward
#print axioms YMGap.Continuum.ContinuumMeasure.is_consistent
#print axioms YMGap.Continuum.ContinuumMeasure.su2_continuum_measure
