/-
CatStructural/DomOver.lean

The categorical domination layer, generically over any `GapSubstrate`.

This is the promotion-shaped form of `DominatedGrowth.lean` +
`VolumeCone.lean`: the SAME objects, morphisms, category laws,
telescoping chain, gap persistence, and uniform-gap cone — but stated
over an abstract substrate `S : GapSubstrate`, with every equality
that was `Eq`-of-`Int` now an `S.eqv` setoid step.  Instantiating
`S` at `Int` recovers the concrete spike; instantiating at the
`Q'`-mirror (`QSpike.lean`) is the dress rehearsal for wiring into
the main tree, where the substrate equality is genuinely a setoid.

The porting discipline (worth recording, since it is exactly what a
CReal instantiation will face): every `rw` on an `Int` equation in
the concrete file becomes a `le_of_eqv`/`ge_of_eqv` link in a
`le_trans` chain, or an `eqv_trans` link in an `eqv` chain.  No law
beyond the `GapSubstrate` record is consumed.

Mathlib-free, Classical-free, sorry-free.
-/

import CatStructural.ECat
import CatStructural.Substrate

namespace CatStructural

variable (S : GapSubstrate)

/-- A nonnegative mass over the substrate `S`. -/
structure MassG where
  val : S.Carrier
  nonneg : S.le S.zero val

variable {S}

/-- A domination morphism over `S`: witness-bearing ratio data with the
    denominator-cleared bound `num·a ≤ den·b`, all at the substrate's
    own order. -/
structure DomG (a b : MassG S) where
  num : S.Carrier
  den : S.Carrier
  num_nonneg : S.le S.zero num
  den_pos : S.lt S.zero den
  bound : S.le (S.mul num a.val) (S.mul den b.val)

namespace DomG

/-- Hom-setoid: two witnesses assert the same ratio, up to the
    SUBSTRATE's `eqv` — over `Q'` this is cross-product equivalence of
    cross-products, not `Eq` of records at any level.  Reducible so
    that `Decidable` synthesis (for the kernel square guard in
    `SquareGuard.lean`) sees through to the substrate's decidable
    `eqv` at reducible instances. -/
@[reducible] def eqv {a b : MassG S} (f g : DomG a b) : Prop :=
  S.eqv (S.mul f.num g.den) (S.mul g.num f.den)

theorem eqv_refl {a b : MassG S} (f : DomG a b) : eqv f f :=
  S.eqv_refl _

theorem eqv_symm {a b : MassG S} {f g : DomG a b}
    (h : eqv f g) : eqv g f :=
  S.eqv_symm h

/-- Transitivity, by cancellation of the positive middle denominator —
    the `Int` proof's `calc` of equalities becomes an `eqv_trans`
    chain. -/
theorem eqv_trans {a b : MassG S} {f g h : DomG a b}
    (h₁ : eqv f g) (h₂ : eqv g h) : eqv f h := by
  apply S.mul_right_cancel_eqv g.den_pos
  -- (f.num·h.den)·g.den ≈ (h.num·f.den)·g.den
  exact S.eqv_trans (S.mul_right_comm_eqv f.num h.den g.den)
    (S.eqv_trans (S.mul_congr h₁ (S.eqv_refl h.den))
      (S.eqv_trans (S.mul_right_comm_eqv g.num f.den h.den)
        (S.eqv_trans (S.mul_congr h₂ (S.eqv_refl f.den))
          (S.mul_right_comm_eqv h.num g.den f.den))))

/-- Identity witness: ratio `1/1`. -/
def ident (a : MassG S) : DomG a a where
  num := S.one
  den := S.one
  num_nonneg := S.zero_le_one
  den_pos := S.zero_lt_one
  bound := S.le_refl _

/-- Composition: ratios multiply; the composite `bound` is the
    telescoped inequality, assembled purely from substrate laws. -/
def comp {a b c : MassG S} (f : DomG a b) (g : DomG b c) : DomG a c where
  num := S.mul g.num f.num
  den := S.mul g.den f.den
  num_nonneg := S.mul_nonneg g.num_nonneg f.num_nonneg
  den_pos := S.mul_pos g.den_pos f.den_pos
  bound := by
    -- (g.num·f.num)·a ≈ g.num·(f.num·a)                 [assoc]
    -- g.num·(f.num·a) ≤ g.num·(f.den·b)                 [f.bound]
    -- g.num·(f.den·b) ≈ f.den·(g.num·b)                 [left-comm]
    -- f.den·(g.num·b) ≤ f.den·(g.den·c)                 [g.bound]
    -- f.den·(g.den·c) ≈ (g.den·f.den)·c                 [left-comm + assoc]
    have h₁ : S.le (S.mul g.num (S.mul f.num a.val))
                   (S.mul g.num (S.mul f.den b.val)) :=
      S.mul_le_mul_left f.bound g.num_nonneg
    have h₂ : S.le (S.mul f.den (S.mul g.num b.val))
                   (S.mul f.den (S.mul g.den c.val)) :=
      S.mul_le_mul_left g.bound (S.le_of_lt f.den_pos)
    have e₃ : S.eqv (S.mul f.den (S.mul g.den c.val))
                    (S.mul (S.mul g.den f.den) c.val) :=
      S.eqv_trans (S.mul_left_comm_eqv f.den g.den c.val)
        (S.eqv_symm (S.mul_assoc_eqv g.den f.den c.val))
    exact S.le_trans (S.le_of_eqv (S.mul_assoc_eqv g.num f.num a.val))
      (S.le_trans h₁
        (S.le_trans (S.le_of_eqv (S.mul_left_comm_eqv g.num f.den b.val))
          (S.le_trans h₂ (S.le_of_eqv e₃))))

theorem comp_congr {a b c : MassG S} {f f' : DomG a b} {g g' : DomG b c}
    (hf : eqv f f') (hg : eqv g g') : eqv (comp f g) (comp f' g') := by
  show S.eqv (S.mul (S.mul g.num f.num) (S.mul g'.den f'.den))
             (S.mul (S.mul g'.num f'.num) (S.mul g.den f.den))
  exact S.eqv_trans (S.mul_interchange_eqv g.num f.num g'.den f'.den)
    (S.eqv_trans (S.mul_congr hg hf)
      (S.eqv_symm (S.mul_interchange_eqv g'.num f'.num g.den f.den)))

theorem ident_comp {a b : MassG S} (f : DomG a b) :
    eqv (comp (ident a) f) f := by
  show S.eqv (S.mul (S.mul f.num S.one) f.den)
             (S.mul f.num (S.mul f.den S.one))
  exact S.eqv_trans
    (S.mul_congr (S.mul_one_eqv f.num) (S.eqv_refl f.den))
    (S.eqv_symm (S.mul_congr (S.eqv_refl f.num) (S.mul_one_eqv f.den)))

theorem comp_ident {a b : MassG S} (f : DomG a b) :
    eqv (comp f (ident b)) f := by
  show S.eqv (S.mul (S.mul S.one f.num) f.den)
             (S.mul f.num (S.mul S.one f.den))
  exact S.eqv_trans
    (S.mul_congr (S.one_mul_eqv f.num) (S.eqv_refl f.den))
    (S.eqv_symm (S.mul_congr (S.eqv_refl f.num) (S.one_mul_eqv f.den)))

theorem comp_assoc {a b c d : MassG S}
    (f : DomG a b) (g : DomG b c) (h : DomG c d) :
    eqv (comp (comp f g) h) (comp f (comp g h)) := by
  show S.eqv
    (S.mul (S.mul h.num (S.mul g.num f.num))
           (S.mul (S.mul h.den g.den) f.den))
    (S.mul (S.mul (S.mul h.num g.num) f.num)
           (S.mul h.den (S.mul g.den f.den)))
  exact S.mul_congr (S.eqv_symm (S.mul_assoc_eqv h.num g.num f.num))
    (S.mul_assoc_eqv h.den g.den f.den)

end DomG

/-- The generic domination E-category over any substrate `S` — one
    definition covering the `Int` spike and the `Q'` instantiation. -/
def DomGrowthOver (S : GapSubstrate) : ECat where
  Obj := MassG S
  Hom := DomG
  eqv := DomG.eqv
  eqv_refl := DomG.eqv_refl
  eqv_symm := DomG.eqv_symm
  eqv_trans := DomG.eqv_trans
  ident := DomG.ident
  comp := DomG.comp
  comp_congr := DomG.comp_congr
  ident_comp := DomG.ident_comp
  comp_ident := DomG.comp_ident
  comp_assoc := DomG.comp_assoc

/-! ## The spine, generically -/

/-- Chain composite of a per-scale ledger over `S`. -/
def chainG (M : Nat → MassG S) (step : ∀ k, DomG (M k) (M (k + 1))) :
    ∀ n, DomG (M 0) (M n)
  | 0 => DomG.ident (M 0)
  | n + 1 => DomG.comp (chainG M step n) (step n)

/-- The telescoped global bound, extracted by projection. -/
theorem chainG_bound (M : Nat → MassG S)
    (step : ∀ k, DomG (M k) (M (k + 1))) (n : Nat) :
    S.le (S.mul (chainG M step n).num (M 0).val)
         (S.mul (chainG M step n).den (M n).val) :=
  (chainG M step n).bound

/-- Gap persistence over any substrate: positive anchor + positive
    composite numerators ⟹ every scale's mass is positive.  The proof
    is substrate-law application to the composite's `bound` projection;
    the constructive content lives in `S.pos_cancel`. -/
theorem gap_persistsG (M : Nat → MassG S)
    (step : ∀ k, DomG (M k) (M (k + 1)))
    (anchor_pos : S.lt S.zero (M 0).val)
    (num_pos : ∀ n, S.lt S.zero (chainG M step n).num) (n : Nat) :
    S.lt S.zero (M n).val :=
  S.pos_cancel (chainG M step n).den_pos
    (S.mul_pos (num_pos n) anchor_pos)
    (chainG_bound M step n)

/-! ## Uniform gap (the volume cone), generically -/

/-- Uniform gap over `S`: pinned apex, unit-ratio legs — where "unit
    ratio" is now `S.eqv` of numerator and denominator, the setoid
    form that `Q'` legs will inhabit. -/
structure UniformGapG (G : Nat → MassG S) where
  apex : MassG S
  apex_pos : S.lt S.zero apex.val
  leg : ∀ L : Nat, DomG apex (G L)
  leg_unit : ∀ L : Nat, S.eqv (leg L).num (leg L).den

namespace UniformGapG

/-- Unit-ratio per-volume comparison between two gap ledgers. -/
structure LedgerHomG (G G' : Nat → MassG S) where
  component : ∀ L : Nat, DomG (G L) (G' L)
  component_unit : ∀ L : Nat, S.eqv (component L).num (component L).den

/-- Transport of a uniform gap along a unit-ratio comparison — proved
    once over the abstract substrate; the `Int` and `Q'` versions are
    instantiations, not re-proofs. -/
def transport {G G' : Nat → MassG S} (η : LedgerHomG G G')
    (U : UniformGapG G) : UniformGapG G' where
  apex := U.apex
  apex_pos := U.apex_pos
  leg L := DomG.comp (U.leg L) (η.component L)
  leg_unit L :=
    S.mul_congr (η.component_unit L) (U.leg_unit L)

/-- The pinned lower bound holds at every volume: `apex ≤ G L`,
    extracted from the unit-ratio leg by substrate cancellation. -/
theorem le_all {G : Nat → MassG S} (U : UniformGapG G) (L : Nat) :
    S.le U.apex.val (G L).val := by
  have step : S.le (S.mul (U.leg L).den U.apex.val)
                   (S.mul (U.leg L).den (G L).val) :=
    S.le_trans
      (S.le_of_eqv (S.mul_congr (S.eqv_symm (U.leg_unit L))
        (S.eqv_refl U.apex.val)))
      (U.leg L).bound
  exact S.le_of_mul_le_mul_left step (U.leg L).den_pos

/-- Every volume's gap is strictly positive under a uniform gap. -/
theorem pos_all {G : Nat → MassG S} (U : UniformGapG G) (L : Nat) :
    S.lt S.zero (G L).val :=
  S.lt_of_lt_of_le U.apex_pos (le_all U L)

end UniformGapG

#print axioms DomG.comp
#print axioms DomGrowthOver
#print axioms chainG_bound
#print axioms gap_persistsG
#print axioms UniformGapG.transport
#print axioms UniformGapG.le_all
#print axioms UniformGapG.pos_all

end CatStructural
