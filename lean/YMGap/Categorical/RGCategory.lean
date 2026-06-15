/-
Plan 1 of the categorical lift: the **RG site as a genuine category**, and the
**observable-functional coarsening as a genuine presheaf** (contravariant
functor).

Per `docs/category-theory-lift-assessment.md` this is the highest-payoff lift:
the research found the coarsening map `ProbFunctional.restrict` is *already*
functorial, so packaging it as a `Functor` is the "functoriality-for-free"
reuse the assessment flagged as real (not decorative).

# What this module delivers

  * `ObsHom.comp` — composition of unital *-homomorphisms of observable
    algebras (the missing piece: `ObservableMeasure` had only `idHom`).
  * `ObsCat : Cat` — the category of observable *-algebras.  `Eq`-Hom (no
    setoid): `ObsHom` equality is structural (`funext` + `Prop`
    proof-irrelevance), NOT CReal-`eqv`, so the assessment's "use `Eq`-Hom
    where the equality is not CReal" applies and the category laws are `rfl`.
  * `restrict_id` / `restrict_comp` — **functoriality of coarsening**, the
    genuine content; both `rfl` (structure η + proof-irrelevance).
  * `obsPresheaf : Presheaf ObsCat TypeCat` — the observable-functional
    presheaf `A ↦ ProbFunctional A`, contravariant via `restrict`.  A bona
    fide functor with proven `map_id`/`map_comp`.
  * `siteCat` — the configuration site of `Sheaf/Site.lean` packaged as a
    `Cat` (thin: morphisms are propositional, so the laws are `rfl`), with the
    three-element cover and the `domGlue` buffer-glue noted as its sheaf data.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (the latter via `funext` in the presheaf
functoriality).  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Categorical.Core
import YMGap.Continuum.ObservableMeasure
import YMGap.Sheaf.Site
import YMGap.Sheaf.Gluing

namespace YMGap.Categorical

open YMGap.Continuum.ObservableMeasure

/-! ## Composition of observable *-homomorphisms -/

/-- Composition of unital *-homomorphisms (`g ∘ f`), the missing categorical
operation: `ObservableMeasure` defined only `idHom`. -/
def ObsHom.comp {A B C : ObsAlg} (f : ObsHom A B) (g : ObsHom B C) : ObsHom A C where
  map := fun a => g.map (f.map a)
  map_one := by
    show g.map (f.map A.one) = C.one
    rw [f.map_one]; exact g.map_one
  map_mul := fun a b => by
    show g.map (f.map (A.mul a b)) = C.mul (g.map (f.map a)) (g.map (f.map b))
    rw [f.map_mul, g.map_mul]
  map_star := fun a => by
    show g.map (f.map (A.star a)) = C.star (g.map (f.map a))
    rw [f.map_star, g.map_star]

/-! ## The category of observable *-algebras -/

/-- **`ObsCat`** — the category of observable *-algebras: objects `ObsAlg`,
morphisms `ObsHom`, identity `idHom`, composition `ObsHom.comp`.  All three
category laws are `rfl` (composition is function composition; the `Prop` hom
fields are proof-irrelevant; `ObsHom` enjoys structure η). -/
def ObsCat : Cat where
  Obj := ObsAlg
  Hom := fun A B => ObsHom A B
  id := ObsHom.idHom
  comp := fun f g => ObsHom.comp f g
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## Functoriality of coarsening (`restrict`) -/

/-- **Coarsening preserves identities.**  Pulling a functional back along the
identity *-hom is the identity: `restrict μ (idHom A) = μ`.  `rfl` (the
restricted `E` is `fun a => μ.E (idHom.map a) = μ.E a`, η-equal to `μ.E`; the
`Prop` fields are proof-irrelevant). -/
theorem restrict_id {A : ObsAlg} (μ : ProbFunctional A) :
    μ.restrict (ObsHom.idHom A) = μ := rfl

/-- **Coarsening preserves composition (contravariantly).**  Pulling back
along `φ` then `ψ` equals pulling back along `g ∘ f`:
`(μ.restrict ψ).restrict φ = μ.restrict (ObsHom.comp φ ψ)`.  `rfl`. -/
theorem restrict_comp {A B C : ObsAlg}
    (φ : ObsHom A B) (ψ : ObsHom B C) (μ : ProbFunctional C) :
    (μ.restrict ψ).restrict φ = μ.restrict (ObsHom.comp φ ψ) := rfl

/-- **The observable-functional presheaf.**  `A ↦ ProbFunctional A`, with a
*-hom `φ : B ⟶ A` (a morphism of `ObsCat.op`) acting by coarsening
`restrict · φ : ProbFunctional A → ProbFunctional B`.  A genuine contravariant
functor: `map_id` is `restrict_id`, `map_comp` is `restrict_comp` (both under
`funext`).  This is the "RG coarsening is a presheaf" statement, now a typed
object rather than an informal claim. -/
def obsPresheaf : Presheaf ObsCat TypeCat where
  obj := fun A => ProbFunctional A
  map := fun φ μ => μ.restrict φ
  map_id := fun A => funext (fun μ => restrict_id μ)
  map_comp := fun f g => funext (fun μ => (restrict_comp g f μ).symm)

/-! ## The configuration site as a category

The `Sheaf/Site.lean` `Object`/`Morphism` data, packaged as a `Cat` once the
polymer-inclusion relation `PolySub` is reflexive and transitive.  The category
is **thin**: a `Morphism` is two `Prop` fields (open inclusion + polymer
inclusion), so any two parallel morphisms are equal by proof-irrelevance and
the category laws are `rfl`.  This realizes the Grothendieck-site objects/
morphisms of Milestone 2.1 as a bona fide category. -/

/-- **`siteCat`** — the configuration site as a category, given reflexivity and
transitivity of the polymer-inclusion relation.  Thin (propositional homs), so
the laws are `rfl`. -/
def siteCat {Config Polymer : Type} (PolySub : Polymer → Polymer → Prop)
    (prefl : ∀ x, PolySub x x)
    (ptrans : ∀ {x y z}, PolySub x y → PolySub y z → PolySub x z) : Cat where
  Obj := YMGap.Sheaf.Object Config Polymer
  -- `Morphism` is `Prop`-valued (both fields are propositions), so we lift it
  -- into `Type` with `PLift` to use it as a `Cat.Hom`.  The category is thin.
  Hom := fun a b => PLift (YMGap.Sheaf.Morphism PolySub a b)
  id := fun a => PLift.up (YMGap.Sheaf.Morphism.id a (prefl a.poly))
  comp := fun f g => PLift.up (YMGap.Sheaf.Morphism.comp ptrans f.down g.down)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

end YMGap.Categorical

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Categorical.ObsHom.comp
#print axioms YMGap.Categorical.ObsCat
#print axioms YMGap.Categorical.restrict_id
#print axioms YMGap.Categorical.restrict_comp
#print axioms YMGap.Categorical.obsPresheaf
#print axioms YMGap.Categorical.siteCat
