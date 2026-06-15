/-
Minimal proof-relevant category theory core — the shared substrate for the
categorical lift of the RG site/sheaf (`Categorical/ObsCat.lean`) and the
codynamic EKF↔YM transfer (`Categorical/CodynCat.lean`).

# Design (per `docs/category-theory-lift-assessment.md`)

This is a deliberately MINIMAL, hand-rolled category theory — NOT Mathlib's
`CategoryTheory` (whose Type-Hom + `Prop` proof-irrelevance design is a
structural mismatch for the project's strictly-constructive / MLTT-HoTT-valid
constraint) and NOT a setoid-Hom (agda-categories) library either, because the
two categories we actually build here — observable *-algebras (`ObsCat`) and
codynamic bound-witness systems (`CodynCat`) — have morphism equality that is
STRUCTURAL (`Eq`, dischargeable by `rfl`/`funext` + `Prop` proof-irrelevance),
NOT CReal-setoid `eqv`.  Per the assessment's "pay setoid cost only where the
equality is genuinely CReal", we use `Eq`-Hom here.  (A setoid-`Hom` variant
would be introduced only for a category whose morphisms are CReal-valued.)

The laws are stated as propositional `Eq` between morphisms; all instances in
this development discharge them by `rfl` (composition is function composition)
or `funext` + proof-irrelevance.

# Axiom-gate (AGENTS.md Rule 1)

`Cat`/`Functor` are pure data + `Eq` laws.  No `Classical.*`, no `sorryAx`.
The instances' law proofs use only `rfl`/`funext` (the latter is constructive
and on the `propext`/`Quot.sound` allow-list's spirit — `funext` reduces to
`Quot.sound`).  See the `#print axioms` blocks in the instance files.
-/

namespace YMGap.Categorical

universe u v u' v'

/-! ## Categories (proof-relevant, Type-Hom, `Eq`-laws) -/

/-- A (small-ish) category: objects in `Type u`, hom-types in `Type v`,
identity and composition, with the three category laws as propositional
equalities.  Composition is in **diagrammatic order** `comp f g : Hom X Z`
for `f : Hom X Y`, `g : Hom Y Z` (i.e. `f` then `g`). -/
structure Cat where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms `X ⟶ Y`. -/
  Hom : Obj → Obj → Type v
  /-- Identity morphism. -/
  id : (X : Obj) → Hom X X
  /-- Composition in diagrammatic order (`f` then `g`). -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity law. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Right identity law. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- Associativity. -/
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
            comp (comp f g) h = comp f (comp g h)

/-- The opposite category: same objects, hom and composition flipped.  Used to
state presheaves as covariant functors `C.op ⟶ TypeCat`. -/
def Cat.op (C : Cat.{u, v}) : Cat.{u, v} where
  Obj := C.Obj
  Hom := fun X Y => C.Hom Y X
  id := fun X => C.id X
  comp := fun f g => C.comp g f
  id_comp := fun f => C.comp_id f
  comp_id := fun f => C.id_comp f
  assoc := fun f g h => (C.assoc h g f).symm

/-! ## Functors -/

/-- A functor `C ⟶ D` (covariant): an object map and a hom map preserving
identities and composition. -/
structure Functor (C : Cat.{u, v}) (D : Cat.{u', v'}) where
  /-- Object component. -/
  obj : C.Obj → D.Obj
  /-- Morphism component. -/
  map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)
  /-- Functoriality: identities preserved. -/
  map_id : ∀ X : C.Obj, map (C.id X) = D.id (obj X)
  /-- Functoriality: composition preserved. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
               map (C.comp f g) = D.comp (map f) (map g)

/-- A **presheaf** on `C`: a contravariant functor, i.e. a covariant functor
out of the opposite category `C.op`. -/
abbrev Presheaf (C : Cat.{u, v}) (D : Cat.{u', v'}) := Functor C.op D

/-! ## The category of types

`TypeCat` — objects are types, morphisms are functions.  The target of
set-valued presheaves (e.g. the observable-functional presheaf). -/

/-- The category of types in a fixed universe: `Hom X Y = X → Y`. -/
def TypeCat : Cat.{u + 1, u} where
  Obj := Type u
  Hom := fun X Y => X → Y
  id := fun _ => fun x => x
  comp := fun f g => fun x => g (f x)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

end YMGap.Categorical
