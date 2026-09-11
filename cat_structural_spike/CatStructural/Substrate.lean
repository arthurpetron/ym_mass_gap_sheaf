/-
CatStructural/Substrate.lean

The substrate interface for the categorical gap layer.

`DominatedGrowth.lean` proved the telescoping/persistence layer over
`Int` with `Eq` as hom-setoid equality.  Promotion to the main tree
requires the same layer over `Q'` (and eventually CReal), where the
substrate equality is a genuine setoid (`Q'.eqv`, cross-product), not
`Eq`.  This file extracts the EXACT list of substrate facts the
categorical layer consumes, as a record `GapSubstrate` — data and laws
bundled as record fields, no type classes, no Mathlib.

The law list is minimal-by-construction: every field below is used by
`DomOver.lean`, and `DomOver.lean` uses nothing else.  The two
instantiations in this spike (`IntSubstrate.lean`, `QSpike.lean`)
demonstrate the "≥2 genuine instances" bar of the lift assessment —
and the `Q'`-mirror instance is the one that exercises the setoid
discipline for real (`eqv` ≠ `Eq`).

Note the deliberate absence of trichotomy / total order: `pos_cancel`
and the two cancellation laws are carried as named primitives, because
over constructive reals `¬(m ≤ 0) → 0 < m` is NOT available.  `Q'`
proves them by decidability of `Int` order; a future CReal instance
must supply them from located-ness — the record makes that obligation
explicit instead of burying it in a classical tactic.

Mathlib-free, Classical-free, sorry-free.
-/

namespace CatStructural

/-- An ordered setoid semiring fragment: exactly the substrate facts the
    categorical domination layer consumes.  `eqv` is the semantic
    equality (a setoid, possibly coarser than `Eq`); `le`/`lt` must be
    stated up to `eqv`, which is enforced by the congruence and
    `le_of_eqv` laws below. -/
structure GapSubstrate where
  Carrier : Type
  eqv : Carrier → Carrier → Prop
  le : Carrier → Carrier → Prop
  lt : Carrier → Carrier → Prop
  zero : Carrier
  one : Carrier
  mul : Carrier → Carrier → Carrier
  -- setoid laws
  eqv_refl : ∀ a, eqv a a
  eqv_symm : ∀ {a b}, eqv a b → eqv b a
  eqv_trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
  -- order laws
  le_of_eqv : ∀ {a b}, eqv a b → le a b
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_of_lt : ∀ {a b}, lt a b → le a b
  lt_of_lt_of_le : ∀ {a b c}, lt a b → le b c → lt a c
  -- multiplicative laws (all at `eqv`)
  mul_congr : ∀ {a a' b b'}, eqv a a' → eqv b b' → eqv (mul a b) (mul a' b')
  mul_assoc_eqv : ∀ a b c, eqv (mul (mul a b) c) (mul a (mul b c))
  mul_comm_eqv : ∀ a b, eqv (mul a b) (mul b a)
  one_mul_eqv : ∀ a, eqv (mul one a) a
  -- positivity structure
  zero_lt_one : lt zero one
  mul_nonneg : ∀ {a b}, le zero a → le zero b → le zero (mul a b)
  mul_pos : ∀ {a b}, lt zero a → lt zero b → lt zero (mul a b)
  mul_le_mul_left : ∀ {a b c}, le a b → le zero c → le (mul c a) (mul c b)
  -- cancellation (named primitives: constructive content, see docstring)
  mul_right_cancel_eqv : ∀ {a b c}, lt zero c →
      eqv (mul a c) (mul b c) → eqv a b
  le_of_mul_le_mul_left : ∀ {a b c}, le (mul c a) (mul c b) →
      lt zero c → le a b
  pos_cancel : ∀ {d n m}, lt zero d → lt zero n →
      le n (mul d m) → lt zero m

namespace GapSubstrate

variable (S : GapSubstrate)

/-- `le` is reflexive (from `le_of_eqv` at `eqv_refl`). -/
theorem le_refl (a : S.Carrier) : S.le a a :=
  S.le_of_eqv (S.eqv_refl a)

/-- `0 ≤ 1` (from `0 < 1`). -/
theorem zero_le_one : S.le S.zero S.one :=
  S.le_of_lt S.zero_lt_one

/-- `a·1 ≈ a` (from commutativity and `one_mul`). -/
theorem mul_one_eqv (a : S.Carrier) : S.eqv (S.mul a S.one) a :=
  S.eqv_trans (S.mul_comm_eqv a S.one) (S.one_mul_eqv a)

/-- Right-commutation: `(a·b)·c ≈ (a·c)·b`. -/
theorem mul_right_comm_eqv (a b c : S.Carrier) :
    S.eqv (S.mul (S.mul a b) c) (S.mul (S.mul a c) b) :=
  S.eqv_trans (S.mul_assoc_eqv a b c)
    (S.eqv_trans (S.mul_congr (S.eqv_refl a) (S.mul_comm_eqv b c))
      (S.eqv_symm (S.mul_assoc_eqv a c b)))

/-- Left-commutation: `a·(b·c) ≈ b·(a·c)`. -/
theorem mul_left_comm_eqv (a b c : S.Carrier) :
    S.eqv (S.mul a (S.mul b c)) (S.mul b (S.mul a c)) :=
  S.eqv_trans (S.eqv_symm (S.mul_assoc_eqv a b c))
    (S.eqv_trans (S.mul_congr (S.mul_comm_eqv a b) (S.eqv_refl c))
      (S.mul_assoc_eqv b a c))

/-- Interchange: `(a·b)·(c·d) ≈ (a·c)·(b·d)`. -/
theorem mul_interchange_eqv (a b c d : S.Carrier) :
    S.eqv (S.mul (S.mul a b) (S.mul c d)) (S.mul (S.mul a c) (S.mul b d)) :=
  S.eqv_trans (S.mul_assoc_eqv a b (S.mul c d))
    (S.eqv_trans (S.mul_congr (S.eqv_refl a) (S.mul_left_comm_eqv b c d))
      (S.eqv_symm (S.mul_assoc_eqv a c (S.mul b d))))

/-- `eqv` gives `le` in both directions; this is the reverse one. -/
theorem ge_of_eqv {a b : S.Carrier} (h : S.eqv a b) : S.le b a :=
  S.le_of_eqv (S.eqv_symm h)

end GapSubstrate

end CatStructural
