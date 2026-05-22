/-
Domination gluing on the buffer overlap, and the named compatibility
predicate.

The buffer Ω_k^∩ is where the small-field and large-field bounds
must be reconciled.  Context.md §3.1 frames this as a *cocycle*
problem: the two bounds are not restrictions of a single function
to two subsets, they are two distinct upper bounds derived under
two different approximations, and "gluing" them on the overlap is
by domination (pointwise sup), not equality.

This file:

  * defines `domGlue` — the pointwise sup of two sections, which is
    the structural shape of the buffer-overlap glue;
  * proves `domGlue` dominates both input sections;
  * defines `CompatibilityRule` — the named predicate type binding
    sections of 𝒜_k to KP certificates of 𝒮_k, where the analytic
    content of the framework lives (per outline.md §8.5 and
    Definition 5.1 of `formal/sheaf-framework.tex`).

Concrete compatibility predicates for the three regimes appear in
Milestones 3.1–3.3.

Mirror: `formal/sheaf-framework.tex` Sections 5 and 6 (Definitions
5.1, 6.1, Proposition 6.2).
-/

import YMGap.Sheaf.Site
import YMGap.Sheaf.BoundWitness
import YMGap.Sheaf.Summability

namespace YMGap.Sheaf

/-! ## Domination gluing -/

/-- The pointwise sup of two bound-witness sections: the structural
shape of the buffer-overlap glue.

In the math paper, with sections in `ℝ̄≥0`, this is
`s^∩(u) = max(s^sf(u), s^lf(u))`.  Here it is binary `sup` at the
abstract value-type level (typeclass `BoundValues T`). -/
def domGlue {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) : Section Config T :=
  Section.sup sf lf

/-- The domination glue dominates the small-field input section. -/
theorem domGlue_dominates_sf {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) : sf ≤ domGlue sf lf :=
  Section.le_sup_left sf lf

/-- The domination glue dominates the large-field input section. -/
theorem domGlue_dominates_lf {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) : lf ≤ domGlue sf lf :=
  Section.le_sup_right sf lf

/-- Universal property: any section dominating both `sf` and `lf`
also dominates their domination glue. -/
theorem domGlue_le {Config T : Type} [BoundValues T]
    {sf lf u : Section Config T}
    (hsf : sf ≤ u) (hlf : lf ≤ u) : domGlue sf lf ≤ u :=
  Section.sup_le hsf hlf

/-- Σ-form witness: given a small-field section, exhibit a
buffer-overlap section dominating it. -/
def domGlue_witness {Config T : Type} [BoundValues T]
    (sf lf : Section Config T) :
    Σ' g : Section Config T, sf ≤ g ∧ lf ≤ g :=
  ⟨domGlue sf lf, domGlue_dominates_sf sf lf, domGlue_dominates_lf sf lf⟩

/-! ## Compatibility — the named definition

The bound from 𝒜_k(U, X) and the KP datum from 𝒮_k(U, X) are bound
together by a regime-specific predicate.  Concrete predicates are
supplied per regime by Milestones 3.1–3.3.  Here we fix only the
TYPE of compatibility predicates: a binary relation between a
bound-witness section and a KP certificate.

This is the "compatibility condition between 𝒜_k and 𝒮_k" required
as a NAMED DEFINITION by Milestone 2.1 (work_plan.md L191–195) and
`formal/sheaf-framework.tex` Definition 5.1. -/

/-- The type of compatibility rules between bound-witness sections
and KP certificates.  A specific compatibility rule is a binary
predicate; the three regimes (small-field, large-field, overlap)
have their own concrete instances in Milestones 3.1–3.3. -/
def CompatibilityRule (Config T V : Type) [BoundValues T]
    (P : V → V → Prop) : Type :=
  Section Config T → KPCertificate V P → Prop

/-- Given a compatibility rule, the predicate "section `s` is
compatible with KP certificate `c`". -/
def Compatible {Config T V : Type} [BoundValues T] {P : V → V → Prop}
    (rule : CompatibilityRule Config T V P)
    (s : Section Config T) (c : KPCertificate V P) : Prop :=
  rule s c

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms domGlue_dominates_sf
#print axioms domGlue_dominates_lf
#print axioms domGlue_le
#print axioms domGlue_witness

end YMGap.Sheaf
