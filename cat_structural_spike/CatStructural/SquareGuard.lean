/-
CatStructural/SquareGuard.lean

Residual (2): NaturalityGuard, promoted from a one-off refutation to
a STANDING kernel guard over ledger comparisons.

`NaturalityGuard.lean` established the mechanism at `Int` with a
single hand-built square.  This file makes it a reusable audit
device over any substrate:

  · `LedgerG` — a per-scale ledger (masses + step dominations), the
    object a comparison relates.
  · `square` — the naturality square at scale `k` for a comparison
    family `c`: `step_F ≫ c_{k+1} ≈ c_k ≫ step_G` in the hom-setoid.
  · `squaresUpTo n` — all squares below `n` commute.  At a reducible
    substrate with decidable `eqv` (both `Int` and the `Q'` mirror),
    this is DECIDABLE via the core bounded-∀ instance, so the entire
    guard is one kernel `decide` per audited comparison:

        example : squaresUpTo F G c 12 := by decide

    and a failed audit is banked as a `¬`-theorem the same way.

The `QS` demos below are the reason the guard lives at the setoid
level: `guard_passes` exhibits a comparison whose squares commute
ONLY up to `eqv` — every composite differs structurally from its
partner (`guard_needs_setoid` kernel-checks the structural
inequality), so an `Eq`-based guard would refute a correct
comparison.  `guard_refutes_shifted` banks the refutation of a
vacuum-shifted ledger (the `EigShiftOrder` class) through the same
standing device.

Audit protocol (for `AGENTS.md`, if promoted): every time two
ledgers are claimed equivalent — two normalizations of the same
transfer data, pre/post retargeting forms, spec vs. computed
trajectories — the claim enters the tree as one `squaresUpTo`
theorem with an explicit bound, and every refuted comparison enters
as its negation.  Mathlib-free, Classical-free, sorry-free.
-/

import CatStructural.Substrate
import CatStructural.DomOver
import CatStructural.QSpike

namespace CatStructural

variable {S : GapSubstrate}

/-- A per-scale ledger over `S`: the domain/codomain data of a
    comparison.  (Steps must exist at every scale; the guard only
    ever *checks* a finite prefix.) -/
structure LedgerG (S : GapSubstrate) where
  M : Nat → MassG S
  step : ∀ k, DomG (M k) (M (k + 1))

namespace SquareGuard

/-- The naturality square at scale `k` for a comparison family `c`
    between ledgers `F` and `G`: the two composites
    `F.step k ≫ c (k+1)` and `c k ≫ G.step k` agree in the
    hom-setoid.  Reducible so `Decidable` synthesis reaches the
    substrate's decidable `eqv`. -/
@[reducible] def square (F G : LedgerG S)
    (c : ∀ k, DomG (F.M k) (G.M k)) (k : Nat) : Prop :=
  DomG.eqv (DomG.comp (F.step k) (c (k + 1)))
           (DomG.comp (c k) (G.step k))

/-- All naturality squares strictly below `n` commute — the standing
    guard proposition, decidable at reducible substrates via the core
    bounded-∀ instance. -/
@[reducible] def squaresUpTo (F G : LedgerG S)
    (c : ∀ k, DomG (F.M k) (G.M k)) (n : Nat) : Prop :=
  ∀ k, k < n → square F G c k

end SquareGuard

namespace SquareGuardDemo

open SquareGuard

/-! ## The guard at work over the setoid substrate

Ledger `F` carries the trajectory `1 → 1/2` in minimal
representations; ledger `G` carries the SAME trajectory in inflated
representations (`2/2 → 2/4`), with steps and comparison components
likewise in mismatched representations.  The squares commute — but
only semantically. -/

/-- Closed tail-step bound for `F` (constant mass `1/2`, unit ratio). -/
theorem fTail_bound :
    qSubstrate.le (QS.mul QS.one ⟨1, 1⟩) (QS.mul QS.one ⟨1, 1⟩) := by decide

/-- Ledger `F`: masses `1, 1/2, 1/2, …`, step ratio `1/2` as `1 / 2`. -/
def F : LedgerG qSubstrate where
  M | 0 => ⟨⟨1, 0⟩, by decide⟩
    | _ + 1 => ⟨⟨1, 1⟩, by decide⟩
  step
    | 0 => ⟨⟨1, 0⟩, ⟨2, 0⟩, by decide, by decide, by decide⟩
    | _ + 1 => ⟨QS.one, QS.one, by decide, by decide, fTail_bound⟩

/-- Closed tail-step bound for `G` (constant mass `2/4`, unit ratio). -/
theorem gTail_bound :
    qSubstrate.le (QS.mul QS.one ⟨2, 3⟩) (QS.mul QS.one ⟨2, 3⟩) := by decide

/-- Ledger `G`: the SAME trajectory in inflated representations —
    masses `2/2, 2/4, 2/4, …`, step ratio `1/2` carried as
    `(2/4) / 1`. -/
def G : LedgerG qSubstrate where
  M | 0 => ⟨⟨2, 1⟩, by decide⟩
    | _ + 1 => ⟨⟨2, 3⟩, by decide⟩
  step
    | 0 => ⟨⟨2, 3⟩, ⟨1, 0⟩, by decide, by decide, by decide⟩
    | _ + 1 => ⟨QS.one, QS.one, by decide, by decide, gTail_bound⟩

/-- Closed tail comparison bound (`1/2 ≤ 2/4`, unit ratio in inflated
    representation `3/3`). -/
theorem cTail_bound :
    qSubstrate.le (QS.mul ⟨3, 2⟩ ⟨1, 1⟩) (QS.mul ⟨3, 2⟩ ⟨2, 3⟩) := by decide

/-- Comparison components: unit ratios in deliberately inflated
    representations (`1/1` at scale 0, `(3/3)/(3/3)` thereafter). -/
def c : ∀ k, DomG (F.M k) (G.M k)
  | 0 => ⟨⟨1, 0⟩, ⟨1, 0⟩, by decide, by decide, by decide⟩
  | _ + 1 => ⟨⟨3, 2⟩, ⟨3, 2⟩, by decide, by decide, cTail_bound⟩

/-- **The standing guard, passing**: both naturality squares below 2
    commute in the hom-setoid — one kernel `decide` for the whole
    audit. -/
theorem guard_passes : squaresUpTo F G c 2 := by decide

/-- The pass is setoid-ONLY: at scale 0 the two composites differ
    structurally in the numerator (`3/3 · 1` vs `2/4 · 1`), so an
    `Eq`-based guard would wrongly refute this correct comparison.
    Kernel-checked. -/
theorem guard_needs_setoid :
    (DomG.comp (F.step 0) (c 1)).num ≠ (DomG.comp (c 0) (G.step 0)).num := by
  decide

/-- Closed tail-step bound for the shifted ledger (constant `5/8`). -/
theorem gsTail_bound :
    qSubstrate.le (QS.mul QS.one ⟨5, 7⟩) (QS.mul QS.one ⟨5, 7⟩) := by decide

/-- A vacuum-shifted variant of `G`: the scale-1 mass is `5/8`
    instead of `2/4`, with step ratio `5/8` (the `EigShiftOrder` bug
    class — every individual arrow is a perfectly valid domination;
    only the comparison square can see the shift). -/
def Gshift : LedgerG qSubstrate where
  M | 0 => ⟨⟨2, 1⟩, by decide⟩
    | _ + 1 => ⟨⟨5, 7⟩, by decide⟩
  step
    | 0 => ⟨⟨5, 7⟩, ⟨1, 0⟩, by decide, by decide, by decide⟩
    | _ + 1 => ⟨QS.one, QS.one, by decide, by decide, gsTail_bound⟩

/-- Closed tail comparison bound toward the shifted ledger
    (`1/2 ≤ 5/8`, unit ratio in inflated representation `3/3`). -/
theorem csTail_bound :
    qSubstrate.le (QS.mul ⟨3, 2⟩ ⟨1, 1⟩) (QS.mul ⟨3, 2⟩ ⟨5, 7⟩) := by decide

/-- Comparison components toward the shifted ledger — each one a
    valid domination on its own. -/
def cshift : ∀ k, DomG (F.M k) (Gshift.M k)
  | 0 => ⟨⟨1, 0⟩, ⟨1, 0⟩, by decide, by decide, by decide⟩
  | _ + 1 => ⟨⟨3, 2⟩, ⟨3, 2⟩, by decide, by decide, csTail_bound⟩

/-- **The standing guard, refuting**: the shifted ledger fails the
    audit at the very first square — banked as a `¬`-theorem per the
    Lakatos discipline, through the same one-line device that passed
    the correct comparison above. -/
theorem guard_refutes_shifted : ¬ squaresUpTo F Gshift cshift 1 := by decide

end SquareGuardDemo

#print axioms SquareGuardDemo.guard_passes
#print axioms SquareGuardDemo.guard_needs_setoid
#print axioms SquareGuardDemo.guard_refutes_shifted

end CatStructural
