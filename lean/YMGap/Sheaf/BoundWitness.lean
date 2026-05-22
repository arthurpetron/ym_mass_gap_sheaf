/-
The bound-witness presheaf 𝒜_k (abstract scaffold).

Math statement (formal/sheaf-framework.tex §3, Definition 3.2):

    𝒜_k(U, X) = { f : U → ℝ̄≥0 : f bounds polymer-X activity on U },

a flabby (ℝ̄≥0,≤)-valued presheaf on the configuration site, with
restriction "the bound still holds on the smaller open" and gluing
on overlaps by domination, not equality.

For Milestone 2.1 we lift the value type from ℝ̄≥0 to an abstract
type `T` carrying the algebraic structure flabbiness and domination
gluing actually require: a partial order with a top element `⊤` and
a binary sup `⊔`.  This is the constructive-reads-only fallout of
P1.1: Lean 4 core's `Rat` drags `Classical.choice` through
`Rat.decEq` (per the SU2.lean docstring), and Mathlib's `ℝ` is
strictly worse.  The math paper's ℝ̄≥0 will instantiate this
abstraction once `YMGap/Constructive/Reals.lean` lands; until then
the structural lemmas are proved at the typeclass level, with empty
axiom dependency sets.

Constructive contract (`lean/AGENTS.md`):

  - Statements use `Σ` / structures for witness-bearing claims.
  - Flabbiness is the *domination* form: every section is dominated
    by the restriction of some larger-open section.  The proof is
    one line — the constant-⊤ section.  No excluded middle, no
    decidability of open membership.
  - Mirror: `formal/sheaf-framework.tex` Theorem 3.4.
-/

import YMGap.Sheaf.Site

namespace YMGap.Sheaf

/-! ## Value type for bound witnesses

The bound-witness presheaf has section values in a type `T` with a
partial order, a top element, and a binary sup.  We bundle these
into a single typeclass for ergonomics. -/

/-- The algebraic structure required of the value type for
`𝒜_k`-sections: partial order, top element `⊤`, binary sup `⊔`. -/
class BoundValues (T : Type) where
  /-- The order relation `≤` on bound values. -/
  le         : T → T → Prop
  /-- The top element `⊤` — the trivial bound. -/
  top        : T
  /-- Binary sup `⊔`, used by `Sheaf.Gluing` for the buffer overlap. -/
  sup        : T → T → T
  le_refl    : ∀ x, le x x
  le_trans   : ∀ {x y z}, le x y → le y z → le x z
  le_top     : ∀ x, le x top
  le_sup_left  : ∀ x y, le x (sup x y)
  le_sup_right : ∀ x y, le y (sup x y)
  sup_le     : ∀ {x y z}, le x z → le y z → le (sup x y) z

namespace BoundValues

variable {T : Type} [BoundValues T]

/-- `≤` notation for bound values. -/
instance instLE : LE T := ⟨BoundValues.le⟩

end BoundValues

/-! ## A trivial smoke-test instance

To confirm the typeclass has at least one model (and that
`#print axioms` propagates correctly through typeclass resolution),
we instantiate `BoundValues` at `Unit`. -/

instance : BoundValues Unit where
  le _ _       := True
  top          := ()
  sup _ _      := ()
  le_refl _    := True.intro
  le_trans _ _ := True.intro
  le_top _     := True.intro
  le_sup_left  _ _ := True.intro
  le_sup_right _ _ := True.intro
  sup_le _ _   := True.intro

/-! ## Sections of the bound-witness presheaf

A "section over `(U, X)`" is a function `Config → T`.  Values outside
`U` are irrelevant; we do not enforce them propositionally at this
abstract layer because the admissibility predicate (which fixes
what "bounds polymer-X activity on `U`" means) is the concern of
later milestones (3.1–3.3, regime-by-regime). -/

/-- A section of the bound-witness presheaf at configurations
indexed by `Config`, with values in `T`. -/
def Section (Config T : Type) : Type := Config → T

namespace Section

variable {Config T : Type} [BoundValues T]

/-- Pointwise partial order on sections. -/
instance instLE : LE (Section Config T) := ⟨fun s t => ∀ c, s c ≤ t c⟩

/-- The constant-`⊤` section: the trivial bound everywhere. -/
def triv : Section Config T := fun _ => BoundValues.top

theorem le_triv (s : Section Config T) : s ≤ triv :=
  fun _ => BoundValues.le_top _

/-- Pointwise binary sup of two sections.  Used by `Sheaf.Gluing`
for the buffer-overlap glue. -/
def sup (s t : Section Config T) : Section Config T :=
  fun c => BoundValues.sup (s c) (t c)

theorem le_sup_left (s t : Section Config T) : s ≤ sup s t :=
  fun _ => BoundValues.le_sup_left _ _

theorem le_sup_right (s t : Section Config T) : t ≤ sup s t :=
  fun _ => BoundValues.le_sup_right _ _

theorem sup_le {s t u : Section Config T} (hs : s ≤ u) (ht : t ≤ u) :
    sup s t ≤ u :=
  fun c => BoundValues.sup_le (hs c) (ht c)

end Section

/-! ## Flabbiness of 𝒜_k

Theorem 3.4 of `formal/sheaf-framework.tex`: the bound-witness
presheaf is flabby in the *domination* sense.  Every section over
`(U, X)` is dominated by some section over any larger-open `(V, X)`.

The constructive witness is the constant-⊤ section.  No excluded
middle, no decidable open-membership, no analytic input. -/

/-- **Flabbiness theorem (proposition-level form).** Every section
is dominated by the constant-⊤ section.  Combined with the trivial
fact that the constant-⊤ section restricts to itself, this gives
the domination form of flabbiness referenced by
`formal/sheaf-framework.tex` Theorem 3.4. -/
theorem flabby {Config T : Type} [BoundValues T]
    (s : Section Config T) : s ≤ Section.triv :=
  Section.le_triv s

/-- **Flabbiness theorem (Σ-form witness).** For every section `s`,
exhibit the dominating section `t` together with the domination
proof.  This is the constructive-existence form required by AGENTS.md
Rule 2. -/
def flabbyWitness {Config T : Type} [BoundValues T]
    (s : Section Config T) : Σ' t : Section Config T, s ≤ t :=
  ⟨Section.triv, Section.le_triv s⟩

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms Section.le_triv
#print axioms Section.le_sup_left
#print axioms Section.le_sup_right
#print axioms Section.sup_le
#print axioms flabby
#print axioms flabbyWitness

end YMGap.Sheaf
