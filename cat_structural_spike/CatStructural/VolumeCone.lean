/-
CatStructural/VolumeCone.lean

The Clay statement's volume-uniformity clause, categorically.

The official problem description makes the gap's uniformity in the
volume part of the problem: a gap for finite-volume approximations
counts only with control of the T⁴ → ℝ⁴ limit.  Structurally this is a
*cone condition*: with volumes as a thin index category and the
per-volume gap bounds as a functor `G` into `DomGrowth`, a uniform gap
is a cone from the constant functor at a strictly positive mass `Δ` —
one leg `Δ ⟶ G(L)` per volume, natural in `L`.

What the categorical packaging buys, concretely:

1. **Pinning by construction** (AGENTS.md Rule 9.7).  Every leg is a
   morphism out of the SAME object `Δ`.  A "uniform" gap assembled from
   per-volume constants that secretly differ cannot be stated: there is
   no object for the cone's apex.  The failure is a type error, not a
   human-audit catch.

2. **Transport is a theorem, proved once.**  `UniformGap.transport`:
   a unit-ratio natural transformation `G ⟹ G'` (a normalization-
   consistent comparison of two gap ledgers) carries a uniform gap of
   `G` to one of `G'` by composing legs with components.  Every future
   "compare two constructions of the finite-volume theory" step reuses
   this instead of re-proving an ε-chase.

3. **Cofinality is structural.**  A uniform gap only ever needs to be
   established on a cofinal family of volumes (`ofCofinal`) — the
   standard exhaustion argument, stated once at the index-category
   level, with the antitone comparison morphisms doing the work.

Honest scope: this is the `Int`-cleared surrogate level (the same level
as `DominatedGrowth`), organizing bookkeeping that the analytic layer
must feed.  It does not construct the continuum measure and does not
claim to.  Mathlib-free, Classical-free, sorry-free.
-/

import CatStructural.DominatedGrowth

namespace CatStructural

open ECat

/-- A per-volume gap ledger: volumes indexed by `Nat` (an exhaustion
    `L ↦ T⁴_L`), a gap bound `G L` for each, and for `L ≤ L'` a
    witness-bearing comparison `G L' ⟶ G L` — larger volumes dominate
    into smaller ones (the direction in which finite-volume gap bounds
    degrade).  Functoriality at the hom setoid is required, so the
    comparison ratios must be coherent across the exhaustion. -/
structure VolumeLedger where
  G : Nat → Mass
  compare : ∀ {L L' : Nat}, L ≤ L' → Dom (G L') (G L)
  compare_refl : ∀ L, Dom.eqv (compare (Nat.le_refl L)) (Dom.ident (G L))
  compare_trans : ∀ {L L' L'' : Nat} (h₁ : L ≤ L') (h₂ : L' ≤ L''),
      Dom.eqv (compare (Nat.le_trans h₁ h₂))
              (Dom.comp (compare h₂) (compare h₁))

/-- A `VolumeLedger` is exactly a contravariant `EFunctor` from the thin
    volume category `omegaCat` into `DomGrowth` (stated covariantly on
    the opposite ordering via `flip`); this packaging keeps the data
    first-order (finding #5 of the lift assessment). -/
def VolumeLedger.toFunctor (V : VolumeLedger) :
    EFunctor (thin Nat (flip (· ≤ ·)) Nat.le_refl
      (fun h₁ h₂ => Nat.le_trans h₂ h₁)) DomGrowth where
  obj := V.G
  map f := V.compare f.down
  map_congr _ := by
    -- thin domain: any two parallel morphisms have equal `down` proofs,
    -- so the images are literally the same witness.
    exact Dom.eqv_refl _
  map_ident a := V.compare_refl a
  map_comp f g := V.compare_trans g.down f.down

/-- **Uniform gap as a cone.**  A strictly positive apex `Δ` and one
    unit-ratio leg `Δ ⟶ G L` per volume: `1·Δ.val ≤ 1·(G L).val`, i.e.
    the SAME `Δ` bounds every volume's gap from below.  The unit ratio is
    what makes this uniformity rather than mere per-volume positivity:
    a leg with ratio `n_L/d_L` varying in `L` would not inhabit this
    structure. -/
structure UniformGap (V : VolumeLedger) where
  apex : Mass
  apex_pos : 0 < apex.val
  leg : ∀ L : Nat, Dom apex (V.G L)
  leg_unit : ∀ L : Nat, (leg L).num = (leg L).den

namespace UniformGap

/-- A unit-ratio comparison between two ledgers: per-volume morphisms
    `G L ⟶ G' L` asserting `G' L ≥ G L` exactly (components of a natural
    transformation whose naturality is not needed for transport, so it is
    not demanded — no decorative coherence obligations, per the lift
    assessment's cost discipline). -/
structure LedgerHom (V V' : VolumeLedger) where
  component : ∀ L : Nat, Dom (V.G L) (V'.G L)
  component_unit : ∀ L : Nat, (component L).num = (component L).den

/-- **Transport, proved once.**  A uniform gap moves along any unit-ratio
    ledger comparison by composing each leg with the component.  The
    apex — the pinned object — is unchanged; only the legs recompose. -/
def transport {V V' : VolumeLedger} (η : LedgerHom V V')
    (U : UniformGap V) : UniformGap V' where
  apex := U.apex
  apex_pos := U.apex_pos
  leg L := Dom.comp (U.leg L) (η.component L)
  leg_unit L := by
    show (η.component L).num * (U.leg L).num
       = (η.component L).den * (U.leg L).den
    rw [η.component_unit L, U.leg_unit L]

/-- Legs on a cofinal family of volumes extend to all volumes: the
    exhaustion argument.  `cof` selects, for each `L`, a larger volume
    in the family; the leg at `L` is the family leg composed with the
    ledger's comparison morphism back down to `L`.  Unit-ratio legs
    stay unit-ratio when the comparisons are unit-ratio on the selected
    pairs. -/
def ofCofinal (V : VolumeLedger) (apex : Mass) (apex_pos : 0 < apex.val)
    (sel : Nat → Nat) (sel_ge : ∀ L, L ≤ sel L)
    (famLeg : ∀ L, Dom apex (V.G (sel L)))
    (famLeg_unit : ∀ L, (famLeg L).num = (famLeg L).den)
    (compare_unit : ∀ L, (V.compare (sel_ge L)).num
                       = (V.compare (sel_ge L)).den) :
    UniformGap V where
  apex := apex
  apex_pos := apex_pos
  leg L := Dom.comp (famLeg L) (V.compare (sel_ge L))
  leg_unit L := by
    show (V.compare (sel_ge L)).num * (famLeg L).num
       = (V.compare (sel_ge L)).den * (famLeg L).den
    rw [compare_unit L, famLeg_unit L]

/-- The payoff projection: a uniform gap makes every volume's gap bound
    strictly positive with the SAME pinned lower bound — `apex.val ≤
    (G L).val` for all `L`, extracted from the unit-ratio leg by
    cancellation. -/
theorem le_all {V : VolumeLedger} (U : UniformGap V) (L : Nat) :
    U.apex.val ≤ (V.G L).val := by
  have h := (U.leg L).bound
  rw [U.leg_unit L] at h
  exact Int.le_of_mul_le_mul_left h (U.leg L).den_pos

/-- Every volume's gap is strictly positive under a uniform gap. -/
theorem pos_all {V : VolumeLedger} (U : UniformGap V) (L : Nat) :
    0 < (V.G L).val :=
  Int.lt_of_lt_of_le U.apex_pos (le_all U L)

end UniformGap

#print axioms UniformGap.transport
#print axioms UniformGap.ofCofinal
#print axioms UniformGap.le_all
#print axioms UniformGap.pos_all

end CatStructural
