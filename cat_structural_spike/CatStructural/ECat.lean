/-
CatStructural/ECat.lean

Proof-relevant, setoid-Hom (E-category) framework — self-contained spike.

Design constraints (per docs/category-theory-lift-assessment.md §4 and
lean/AGENTS.md):
  * Mathlib-free, Classical-free.  Only core Lean 4.
  * Setoid-enriched hom-equality (agda-categories discipline): each hom
    type carries its own equivalence relation `eqv`; composition must
    respect it.  No UIP, no equality-on-objects.
  * Data bundled as record fields (measured 3x compile win, ITP'14).
  * Proof-relevant 1-categories only.  No 2-cells, no univalence.
  * Content-bearing witnesses live in `Type`, never `Prop`-`∃` (Rule 8.3).

An `ECat` is a category whose homs are setoids.  This is the faithful
encoding of the MLTT/HoTT discipline in Lean 4 (which has kernel proof
irrelevance for `Prop` but no HoTT mode): nothing below relies on UIP or
on equality of objects.
-/

universe u v

/-- A proof-relevant category with setoid-valued homs (an *E-category*).

    `eqv` is the per-hom-setoid equivalence; all laws are stated at `eqv`,
    never at `Eq`, so no use of UIP or function extensionality is needed. -/
structure ECat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  eqv : {a b : Obj} → Hom a b → Hom a b → Prop
  eqv_refl : ∀ {a b : Obj} (f : Hom a b), eqv f f
  eqv_symm : ∀ {a b : Obj} {f g : Hom a b}, eqv f g → eqv g f
  eqv_trans : ∀ {a b : Obj} {f g h : Hom a b}, eqv f g → eqv g h → eqv f h
  ident : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  comp_congr : ∀ {a b c : Obj} {f f' : Hom a b} {g g' : Hom b c},
      eqv f f' → eqv g g' → eqv (comp f g) (comp f' g')
  ident_comp : ∀ {a b : Obj} (f : Hom a b), eqv (comp (ident a) f) f
  comp_ident : ∀ {a b : Obj} (f : Hom a b), eqv (comp f (ident b)) f
  comp_assoc : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
      eqv (comp (comp f g) h) (comp f (comp g h))

namespace ECat

/-- A functor between E-categories: object map, hom map, congruence with
    respect to the hom setoids, and the functor laws at `eqv`. -/
structure EFunctor (C D : ECat) where
  obj : C.Obj → D.Obj
  map : {a b : C.Obj} → C.Hom a b → D.Hom (obj a) (obj b)
  map_congr : ∀ {a b : C.Obj} {f f' : C.Hom a b},
      C.eqv f f' → D.eqv (map f) (map f')
  map_ident : ∀ (a : C.Obj), D.eqv (map (C.ident a)) (D.ident (obj a))
  map_comp : ∀ {a b c : C.Obj} (f : C.Hom a b) (g : C.Hom b c),
      D.eqv (map (C.comp f g)) (D.comp (map f) (map g))

/-- A natural transformation between E-functors, with naturality stated
    at the codomain's hom setoid. -/
structure ENat {C D : ECat} (F G : EFunctor C D) where
  component : (a : C.Obj) → D.Hom (F.obj a) (G.obj a)
  natural : ∀ {a b : C.Obj} (f : C.Hom a b),
      D.eqv (D.comp (component a) (G.map f))
            (D.comp (F.map f) (component b))

/-- The thin E-category on a preorder: at most one morphism `a ⟶ b`,
    inhabited exactly when `le a b`.  Homs are `PLift`ed so they live in
    `Type` (Rule 8.3); the hom setoid is total, as befits a thin category.

    This is the index shape for both the RG-scale chain (`ℕ`, `≤`) and the
    volume-exhaustion chain. -/
def thin (α : Type u) (le : α → α → Prop)
    (le_refl : ∀ a, le a a)
    (le_trans : ∀ {a b c}, le a b → le b c → le a c) : ECat where
  Obj := α
  Hom a b := PLift (le a b)
  eqv _ _ := True
  eqv_refl _ := True.intro
  eqv_symm _ := True.intro
  eqv_trans _ _ := True.intro
  ident a := ⟨le_refl a⟩
  comp f g := ⟨le_trans f.down g.down⟩
  comp_congr _ _ := True.intro
  ident_comp _ := True.intro
  comp_ident _ := True.intro
  comp_assoc _ _ _ := True.intro

/-- The scale index category ω: natural numbers under `≤`.  A functor out
    of `omegaCat` is a coherent multi-scale ledger. -/
def omegaCat : ECat :=
  thin Nat (· ≤ ·) Nat.le_refl (fun h₁ h₂ => Nat.le_trans h₁ h₂)

end ECat
