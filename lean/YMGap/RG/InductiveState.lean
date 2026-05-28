/-
The inductive state ℐ_k carried across RG steps.  Milestone 2.2.

Mirrors `formal/inductive-state.tex` Definitions 2.1 (state), 3.1
(Valid predicate), and 4.1 (type of the block-spin step).

Constructive contract (`lean/AGENTS.md`):

  - The structure carries data only; no well-formedness is baked in.
  - `Valid` is a `Prop` predicate, decidable when the value type `V`
    has decidable order + equality.  Statement-only — no theorem
    here asserts that any concrete state is `Valid`.
  - `StepType` is a `def` returning a Lean `Type`: the *type* of the
    block-spin pushforward.  No term inhabiting that type is exposed
    here — exhibiting one is Milestone 2.3.
  - Witness-bearing scalars (σ̂, ρ, K) inhabit an abstract value
    type `V`; per AGENTS.md Rule 3, no Mathlib `Real`, no Lean-core
    `Rat` (which costs `Classical.choice` via `Rat.decEq` per
    P1.1's empirical finding).
  - The buffer-glue relation in `Valid` literally states the
    conjectured constants of `sheaf-framework.tex` Proposition 7.1.
    Any concrete instance whose buffer field is constructed via
    `domGlue_preserves_KP` carries that theorem's explicit
    closure-under-glue hypothesis `P_glue` — the analytic content,
    supplied at the concrete Q' instances / paper level per `[P2.1]`.
    `domGlue_preserves_KP` itself is axiom-free (build-verified
    2026-05-28); the obligation is the hypothesis, not a `sorry`.

Scope (the 2.2/2.3 boundary).  Everything here is scale-k-local.
No definition references scale k+1, no statement asserts a sum
over k, no claim presupposes a uniform σ_phys.  The four
conditions of `docs/context.md` §3.3 governing the step appear
documented below but are *not* encoded in `StepType` at this
milestone; refining the type to include them is 2.3's job.

Polymer atlas.  `PolyAtlas` is an abstract `Type` parameter per the
open-question recommendation of `formal/inductive-state.tex` §5.
-/

import YMGap.Sheaf.Site
import YMGap.Sheaf.BoundWitness
import YMGap.Sheaf.Summability
import YMGap.Sheaf.Gluing

namespace YMGap.RG

open YMGap.Sheaf

/-! ## The state package -/

/-- The inductive state at scale `k`.  Fields mirror
`formal/inductive-state.tex` Definition 2.1.

Parameters:
- `V` — the scalar value type for σ̂, g, ρ, K.  In the math paper
  `V = ℝ_{>0}`; here abstract, awaiting `YMGap/Constructive/Reals.lean`.
- `P` — the regime-specific KP predicate, abstract here.
- `PolyAtlas` — the polymer atlas type, deliberately abstract per
  Milestone 2.2's open question. -/
structure InductiveState
    (V : Type) (P : V → V → Prop) (PolyAtlas : Type) where
  /-- The RG scale index. -/
  k : Nat
  /-- The renormalized string tension `σ̂_k = a_k² σ_k` (σ-3 sense). -/
  sigmaHat : V
  /-- The running gauge coupling `g_k`. -/
  g : V
  /-- The small-field KP certificate. -/
  c_sf : KPCertificate V P
  /-- The large-field KP certificate. -/
  c_lf : KPCertificate V P
  /-- The buffer KP certificate.  Well-formedness — both the existence
  of `c_cap.satisfies` at the conjectured constants and the tightness
  of the resulting `K_∩` — is discharged by
  `YMGap.Sheaf.domGlue_preserves_KP` (axiom-free; the analytic content
  is its explicit `P_glue` closure-under-glue hypothesis), per
  `lean/SORRY_LEDGER.md` entry `[P2.1]` (both parts CLOSED). -/
  c_cap : KPCertificate V P
  /-- The polymer atlas.  Representation is the open question of
  Milestone 2.2; here it is an abstract type. -/
  poly_atlas : PolyAtlas

namespace InductiveState

variable {V : Type} {P : V → V → Prop} {PolyAtlas : Type}

/-! ## The scale-k induction hypotheses (Valid predicate)

  Mirrors `formal/inductive-state.tex` Definition 3.1.

  Three named clauses:

  - (V1) `σ̂_k > 0` — the local σ-3 positivity.
  - (V2) The KP predicate `P` holds for each certificate's `(ρ, K)`.
        This is propositionally `P c.rho c.K`, not the proof term
        `c.satisfies`; the predicate is the Prop, and the certificate's
        `satisfies` field is exactly its proof.  V2 is thus redundant
        in the sense that `c : KPCertificate V P` already carries a
        proof of `P c.rho c.K`, but listing it as a `Valid` clause
        makes `Valid` the *self-contained, complete* statement of the
        scale-k induction hypotheses — see the design note below.
  - (V3) The buffer constants relate to the sf and lf constants
        per `sheaf-framework.tex` Proposition 7.1.

  All scale-k-local.  No reference to k+1; no sum over k.

  ## Design note: V2 is included for self-containedness

  Earlier P2.2 iterations omitted V2 from `Valid` on the grounds that
  every `KPCertificate V P` already carries its `satisfies : P ρ K`
  field, so V2 was structurally enforced and would be redundant
  here.  That encoding is correct but it leaks the V2 obligation —
  in particular the `YMGap.Sheaf.domGlue_preserves_KP` analytic
  content for the buffer certificate's V2, exposed as that theorem's
  explicit `P_glue` hypothesis — into a field that `Valid` never
  mentions.  Reasoning in 2.3 / Phase 3
  about how validity degrades across the block-spin step would then
  have to combine `Valid` with `c_*.satisfies` reach-into-field
  proofs.

  Restoring V2 as explicit `Valid` clauses (the predicate `P ρ K`
  itself, not the proof term) makes `Valid` the complete scale-k
  hypothesis statement.  The cost is three trivial conjuncts whose
  proofs are exactly the certificate `satisfies` fields; no
  analytic content is added.  Consistency with `formal/inductive-state.tex`
  Definition 3.1 and the Python `validate()` is also restored. -/

/-- The scale-k induction hypotheses, as a `Prop`.

`Valid` is the complete self-contained statement (V1 ∧ V2 ∧ V3).
Decidable for the V1 and V3 conjuncts when the value type `V` has
decidable equality and order; the V2 conjuncts (the regime
predicates) are decidable only for predicates that are themselves
decidable, which in general they will not be (they encode the KP
inequality, an infinite sum). -/
def Valid
    [LT V] [Zero V] [LE V] [Min V] [Add V]
    (s : InductiveState V P PolyAtlas) : Prop :=
  -- (V1) σ̂_k > 0
  (0 < s.sigmaHat) ∧
  -- (V2) KP predicate holds for each regime
  P s.c_sf.rho s.c_sf.K ∧
  P s.c_lf.rho s.c_lf.K ∧
  P s.c_cap.rho s.c_cap.K ∧
  -- (V3) buffer-glue constants relationship from Proposition 7.1
  (s.c_cap.rho = min s.c_sf.rho s.c_lf.rho) ∧
  (s.c_cap.K ≤ s.c_sf.K + s.c_lf.K)

/-- A `Valid` proof, repackaged as a structure of named proofs.
Equivalent to `Valid` (see `validToWitness` / `witnessToValid`) but
ergonomic for destructuring. -/
structure ValidWitness
    [LT V] [Zero V] [LE V] [Min V] [Add V]
    (s : InductiveState V P PolyAtlas) where
  /-- (V1) `σ̂_k > 0`. -/
  sigmaHat_pos : 0 < s.sigmaHat
  /-- (V2-sf) `P` holds for the small-field certificate. -/
  c_sf_predicate : P s.c_sf.rho s.c_sf.K
  /-- (V2-lf) `P` holds for the large-field certificate. -/
  c_lf_predicate : P s.c_lf.rho s.c_lf.K
  /-- (V2-cap) `P` holds for the buffer certificate.  When this state
  is constructed from concrete sf/lf via `YMGap.Sheaf.domGlue_preserves_KP`,
  this field is supplied by that theorem's explicit `P_glue`
  closure-under-glue hypothesis (axiom-free; the analytic content
  lives in `P_glue`, per `[P2.1]`). -/
  c_cap_predicate : P s.c_cap.rho s.c_cap.K
  /-- (V3-ρ) `ρ_∩ = min(ρ_sf, ρ_lf)`. -/
  buffer_glue_rho : s.c_cap.rho = min s.c_sf.rho s.c_lf.rho
  /-- (V3-K) `K_∩ ≤ K_sf + K_lf`. -/
  buffer_glue_K : s.c_cap.K ≤ s.c_sf.K + s.c_lf.K

/-- Package a `Valid` proof as a `ValidWitness` structure of proofs. -/
def validToWitness
    [LT V] [Zero V] [LE V] [Min V] [Add V]
    {s : InductiveState V P PolyAtlas} (h : Valid s) : ValidWitness s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Project a `ValidWitness` back to a `Valid` proof. -/
def witnessToValid
    [LT V] [Zero V] [LE V] [Min V] [Add V]
    {s : InductiveState V P PolyAtlas} (w : ValidWitness s) : Valid s :=
  ⟨w.sigmaHat_pos,
   w.c_sf_predicate, w.c_lf_predicate, w.c_cap_predicate,
   w.buffer_glue_rho, w.buffer_glue_K⟩

/-- A convenient builder: given an `InductiveState`, prove `Valid` by
combining a `V1` proof, a `V3-ρ` proof, a `V3-K` proof, and using the
certificates' built-in `satisfies` fields for V2.  This is the
intended construction path: V2 is filled by the certificate fields
and the analytic obligation flows in through `c_cap.satisfies`. -/
def Valid.mkFromCertificates
    [LT V] [Zero V] [LE V] [Min V] [Add V]
    {s : InductiveState V P PolyAtlas}
    (sigmaHat_pos : 0 < s.sigmaHat)
    (glue_rho : s.c_cap.rho = min s.c_sf.rho s.c_lf.rho)
    (glue_K : s.c_cap.K ≤ s.c_sf.K + s.c_lf.K) :
    Valid s :=
  ⟨sigmaHat_pos,
   s.c_sf.satisfies, s.c_lf.satisfies, s.c_cap.satisfies,
   glue_rho, glue_K⟩

end InductiveState

/-! ## The type of the block-spin step (the 2.2 → 2.3 handoff)

  Mirrors `formal/inductive-state.tex` Definition 4.1.

  Documented but NOT encoded in this Lean type (encoding them
  requires committing to representations of ε_sf, ε_lf, Δ_∩, η in
  `V`, which is Milestone 2.3's job):

    (S1) ρ_{sf, k+1} ≥ ρ_{sf, k} - ε_sf(b, g_k)
    (S2) ρ_{lf, k+1} ≥ ρ_{lf, k} - ε_lf(b, g_k)
    (S3) K_{∩, k+1}  ≤ K_{∩, k} + Δ_∩(b, g_k)
    (S4) σ̂_{k+1}    ≥ σ̂_k - η(b, g_k)

  The simplest form below is just `state → state`; the four
  conditions become type-level constraints in 2.3's refined
  `StepTypeWithBudget`.  A term inhabiting either form is the
  inductive step and the content of Milestone 2.3 (against concrete
  inputs from 3.1–3.3 and the budget closure of 3.4). -/

/-- The TYPE of the block-spin pushforward, in its 2.2 form.

A term of this type takes an `InductiveState` at one scale to one at
the next.  2.2 exposes only the type; 2.3 refines it with the four
degradation conditions (S1)–(S4) above and produces a term.

`#print axioms StepType` must report an empty axiom dependency set:
the definition is purely type-level and references no theorem. -/
def StepType
    (V : Type) (P : V → V → Prop) (PolyAtlas : Type) : Type :=
  InductiveState V P PolyAtlas → InductiveState V P PolyAtlas

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms InductiveState.Valid
#print axioms InductiveState.validToWitness
#print axioms InductiveState.witnessToValid
#print axioms InductiveState.Valid.mkFromCertificates
#print axioms StepType

end YMGap.RG
