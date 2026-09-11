/-
CatStructural/NaturalityGuard.lean

Naturality as a machine-checked normalization guard.

The campaign's adversarial audit list names "smuggled normalization
errors (character-vs-eigenvalue misidentification, wrong vacuum
renormalization, free-part multiplicity miscounts)" as a standing
failure mode, and the project has hit real instances (the
`EigShiftOrder` vacuum-normalization artifact).  The categorical
observation: a claimed comparison between two ledgers is a natural
transformation, and a normalization inconsistency is precisely a
naturality square that fails to commute in the hom setoid.  Over exact
rationals (here `Int`-cleared) that failure is a *decidable* equation —
so the bug class converts from a human-audit catch into a kernel
`decide` refutation, banked as a theorem per the Lakatos discipline
("machine-refute dead routes and bank the refutations").

Below: two tiny ledgers over the scales 0 → 1.

  * `F` is the reference ledger: masses 12 → 9, step ratio 3/4 (tight).
  * `Gbad` is a doubled copy of `F` with a vacuum-shift error at scale 1:
    masses 24 → 15 (should be 18), honest best step ratio 5/8.
  * `Ggood` is the correctly doubled copy: masses 24 → 18, step 3/4.

The claimed "the ledgers agree up to constant rescaling" transformation
has components `c₀ : 12 ⟶ 24` (ratio 2/1) and, for the shifted ledger, a
component `c₁bad : 9 ⟶ 15` that still *exists* as a slack morphism
(ratio 3/2) — every individual arrow typechecks, exactly the situation
in which a normalization bug survives local inspection.  The naturality
square is where it dies:

  * `square_fails_for_shifted_ledger`: the square for `Gbad` does NOT
    commute (composite ratios 10/8 vs 9/8) — refuted by kernel `decide`.
  * `square_holds_for_correct_ledger`: the square for `Ggood` commutes
    (6/4 = 6/4) — proved by kernel `decide`.

Mathlib-free, Classical-free, sorry-free; no `native_decide`.
-/

import CatStructural.DominatedGrowth

namespace CatStructural
namespace NaturalityGuard

/-! ### The reference ledger F : 12 → 9, ratio 3/4 -/

def f0 : Mass := ⟨12, by decide⟩
def f1 : Mass := ⟨9, by decide⟩

/-- Reference step, tight: 3·12 = 36 = 4·9. -/
def fStep : Dom f0 f1 := ⟨3, 4, by decide, by decide, by decide⟩

/-! ### The vacuum-shifted ledger Gbad : 24 → 15 (should be 18) -/

def g0 : Mass := ⟨24, by decide⟩
def g1bad : Mass := ⟨15, by decide⟩

/-- The shifted ledger's honest step, tight at its wrong masses:
    5·24 = 120 = 8·15.  Locally impeccable — the shift is invisible
    at the level of a single arrow. -/
def gStepBad : Dom g0 g1bad := ⟨5, 8, by decide, by decide, by decide⟩

/-- Claimed rescaling component at scale 0, tight: 2·12 = 24. -/
def c0 : Dom f0 g0 := ⟨2, 1, by decide, by decide, by decide⟩

/-- Component at scale 1 against the shifted mass.  It EXISTS (slack:
    3·9 = 27 ≤ 2·15 = 30) — the bug does not manifest as a missing
    arrow. -/
def c1bad : Dom f1 g1bad := ⟨3, 2, by decide, by decide, by decide⟩

/-- **Banked refutation.**  The naturality square for the shifted ledger
    fails in the hom setoid: composite ratios 10/8 ≠ 9/8, kernel-checked.
    A vacuum-normalization inconsistency between two ledgers is not a
    matter of judgement — it is a decidable inequation, and the kernel
    refutes it. -/
theorem square_fails_for_shifted_ledger :
    ¬ Dom.eqv (Dom.comp c0 gStepBad) (Dom.comp fStep c1bad) := by
  decide

/-! ### The correctly doubled ledger Ggood : 24 → 18, ratio 3/4 -/

def g1good : Mass := ⟨18, by decide⟩

/-- Correct step, tight: 3·24 = 72 = 4·18. -/
def gStepGood : Dom g0 g1good := ⟨3, 4, by decide, by decide, by decide⟩

/-- Component at scale 1 against the correct mass, tight: 2·9 = 18. -/
def c1good : Dom f1 g1good := ⟨2, 1, by decide, by decide, by decide⟩

/-- **Positive control.**  With the correct normalization the square
    commutes: composite ratios 6/4 = 6/4, kernel-checked.  The guard
    fires exactly on the bug, not on the comparison as such. -/
theorem square_holds_for_correct_ledger :
    Dom.eqv (Dom.comp c0 gStepGood) (Dom.comp fStep c1good) := by
  decide

#print axioms square_fails_for_shifted_ledger
#print axioms square_holds_for_correct_ledger

end NaturalityGuard
end CatStructural
