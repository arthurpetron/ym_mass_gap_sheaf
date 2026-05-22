/-
The configuration site of the constructive Yang–Mills mass gap
program.  Scaffolds the categorical structure underpinning the
bound-witness and summability-certificate presheaves of Milestone
2.1.

Constructive contract (from `lean/AGENTS.md`):

  - All existence claims return witnesses (`Σ` / structures), never
    propositional `∃`.
  - No `Classical.*`, no Mathlib `ℝ`.
  - The configuration and polymer types, and the inclusion of
    polymers, are *parameters*: this file fixes only the categorical
    structure that is group-independent.

Mirror: `formal/sheaf-framework.tex` Section 2 (Definitions 2.1–2.3)
and `docs/sheaf-framework.md` §1.
-/

namespace YMGap.Sheaf

/-! ## Open subsets of the configuration space

We use the predicate model: an "open" is a `Prop`-valued function
on configurations.  This is enough for Milestone 2.1's scope —
inclusions, the three-element cover, restriction maps — without
committing to a topology on the configuration space.  The cover of
`Definition def:three-cover` (small-field / large-field / buffer)
will be the concrete instance in later milestones.
-/

/-- An "open subset" of a configuration space, encoded as a
membership predicate. -/
abbrev Open (Config : Type) : Type := Config → Prop

namespace Open

variable {Config : Type}

/-- Subset relation: `U ⊆ V` iff every `U`-member is a `V`-member. -/
def Subset (U V : Open Config) : Prop := ∀ c, U c → V c

@[inherit_doc] scoped infixl:50 " ⊆o " => Subset

/-- The full open, containing every configuration. -/
def univ : Open Config := fun _ => True

theorem subset_univ (U : Open Config) : U ⊆o univ := fun _ _ => True.intro

theorem subset_refl (U : Open Config) : U ⊆o U := fun _ h => h

theorem subset_trans {U V W : Open Config}
    (h₁ : U ⊆o V) (h₂ : V ⊆o W) : U ⊆o W :=
  fun c hc => h₂ c (h₁ c hc)

/-- Pointwise intersection of opens. -/
def inter (U V : Open Config) : Open Config := fun c => U c ∧ V c

theorem inter_subset_left (U V : Open Config) : inter U V ⊆o U :=
  fun _ h => h.1

theorem inter_subset_right (U V : Open Config) : inter U V ⊆o V :=
  fun _ h => h.2

end Open

/-! ## Objects and morphisms of the configuration site

Objects are pairs `(U, X)`; morphisms `(U, X) → (U', X')` require
both `U ⊆o U'` (open inclusion) and `X ⊑ X'` (polymer inclusion).
We model polymer inclusion as an abstract predicate `PolySub`,
parametrised by the polymer type.  Concrete polymer representations
(plaquette-set inclusions, connected subgraphs) appear in later
milestones; here only the categorical wiring is fixed.
-/

/-- An object of the configuration site: an open subset of
configurations and a polymer. -/
structure Object (Config Polymer : Type) where
  /-- The open subset `U ⊆ Ω_k`. -/
  open' : Open Config
  /-- The polymer `X`. -/
  poly  : Polymer

/-- A morphism `(U, X) → (U', X')` in the configuration site, given
an abstract polymer-inclusion relation `PolySub`. -/
structure Morphism {Config Polymer : Type} (PolySub : Polymer → Polymer → Prop)
    (a b : Object Config Polymer) where
  /-- The open inclusion `U ⊆o U'`. -/
  open_sub : Open.Subset a.open' b.open'
  /-- The polymer inclusion `X ⊑ X'`. -/
  poly_sub : PolySub a.poly b.poly

namespace Morphism

variable {Config Polymer : Type} {PolySub : Polymer → Polymer → Prop}

/-- Identity morphism, requiring `PolySub` reflexivity. -/
def id (a : Object Config Polymer) (hRefl : PolySub a.poly a.poly) :
    Morphism PolySub a a where
  open_sub := Open.subset_refl a.open'
  poly_sub := hRefl

/-- Composition, requiring `PolySub` transitivity. -/
def comp {a b c : Object Config Polymer}
    (hTrans : ∀ {x y z}, PolySub x y → PolySub y z → PolySub x z)
    (f : Morphism PolySub a b) (g : Morphism PolySub b c) :
    Morphism PolySub a c where
  open_sub := Open.subset_trans f.open_sub g.open_sub
  poly_sub := hTrans f.poly_sub g.poly_sub

end Morphism

/-! ## The three-element cover

The defining covering family of the configuration site:
`{(Ω_k^sf, X), (Ω_k^lf, X), (Ω_k^∩, X)} ⇒ (Ω_k, X)`.  Crucially the
buffer `cap` is a first-class element of the cover (cf.\
`formal/sheaf-framework.tex` Definition 2.2 and the cocycle
observation of `docs/context.md` §3.1). -/

/-- The three-element cover `(Ω_k^sf, Ω_k^lf, Ω_k^∩)` of the
configuration space `Ω_k`.  The data is the three opens; the
covering condition is the `covers` field. -/
structure ThreeCover (Config : Type) where
  /-- The small-field open `Ω_k^sf`. -/
  sf  : Open Config
  /-- The large-field open `Ω_k^lf`. -/
  lf  : Open Config
  /-- The buffer open `Ω_k^∩` (NOT the intersection `sf ∩ lf`). -/
  buf : Open Config
  /-- Every configuration is in at least one of the three regions. -/
  covers : ∀ c : Config, sf c ∨ lf c ∨ buf c

namespace ThreeCover

variable {Config : Type}

/-- Each of the three regions is contained in `Ω_k`. -/
theorem sf_subset_univ (T : ThreeCover Config) :
    Open.Subset T.sf Open.univ := Open.subset_univ T.sf

theorem lf_subset_univ (T : ThreeCover Config) :
    Open.Subset T.lf Open.univ := Open.subset_univ T.lf

theorem buf_subset_univ (T : ThreeCover Config) :
    Open.Subset T.buf Open.univ := Open.subset_univ T.buf

end ThreeCover

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms Open.subset_univ
#print axioms Open.subset_refl
#print axioms Open.subset_trans
#print axioms Open.inter_subset_left
#print axioms Open.inter_subset_right
#print axioms Morphism.id
#print axioms Morphism.comp
#print axioms ThreeCover.sf_subset_univ
#print axioms ThreeCover.lf_subset_univ
#print axioms ThreeCover.buf_subset_univ

end YMGap.Sheaf
