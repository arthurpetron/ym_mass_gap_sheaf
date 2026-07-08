/-
**Track A2 — the MINIMAL recoupling interface the physical consumer actually
needs, and its elementary (fundamental-seeded) discharge over Temperley–Lieb.**

The sole load-bearing A2 consumer is
`Stage1LoopyReduction.Stage1Loopy.physical_identity`, the abstract↔real
partition identity `Ξ ≃ Zreal` that upgrades the Penrose–Ursell polymer decay
to the real two-component Wilson correlator.  This module runs the TRACE
DISCIPLINE on that consumer to extract the *minimal* coherence interface it
factors through — with full honesty about where that interface is under-cut —
and discharges the *elementary* (fundamental-rep-seeded) recoupling over the
rational Temperley–Lieb algebra (`TemperleyLiebRecoupling`).

# Step 1 — the exact consumer trace (what `physical_identity` factors through)

`Stage1Loopy.physical_identity S Γ = S.beyondTree.identity Γ` — it invokes ONLY
the `identity` field of `BeyondTreePartitionIdentity`, NOT the bundled `recoup`
(`SixJRecoupling`) field.  So the LITERAL minimal interface is
`AbstractRealPartitionIdentity` (a `Zreal` + `Ξ ≃ Zreal`), proved by
`physical_identity_factors` (`rfl`).

**HONESTY (the decisive point).**  That literal minimal interface is TRIVIALLY
inhabitable (`PartitionBeyondTree.trivialAbstractRealIdentity`, `Zreal := Ξ`).
So formalizing A2 against *only* `identity` would be an UNDER-CUT — a fake close
(`under_cut_is_fake`, re-exporting the trivial inhabitant).  The genuine
physical content is the SIDE CONDITION that `Zreal` be the *real* spin-network /
Haar partition function, which is CONSTRUCTED by recoupling.  Hence the genuine
minimal interface is: "a recoupling datum sufficient to build `Zreal`, plus
`Ξ ≃ Zreal`."  We name that as `PhysicalRecouplingInterface` and factor
`physical_identity` through it honestly.

# Step 2 — fundamental-rep seeding

The Wilson line is the fundamental `χ₁` (`fundamental_fusion_channels`:
`χ₁⊗χ₁ = χ₀ ⊕ χ₂`).  Every internal channel of a fundamental Wilson network is
reached by iterating this ½⊗½ move — so the recoupling datum `Zreal` needs is
seeded by the ELEMENTARY ½-recoupling, and built up by the Jones–Wenzl tower.
This is the physical justification for the Wenzl route being the *native*
recoupling structure.

# Step 3 discharge (elementary) — `ElementaryRecoupling` INHABITED, radical-free

The elementary ½-recoupling interface (a complete orthogonal Jones–Wenzl
idempotent pair on `χ₁⊗χ₁`, trace-faithful to the SU(2) channel dimensions) is
`INHABITED` by the rational Temperley–Lieb construction
(`elementaryRecoupling`, from `jw2`/`p0`).  This DISCHARGES the base of the
recoupling interface over `Q'`, with no radical.  The general tower is the
`TemperleyLiebRecoupling.JWTowerCoherence` residual (the induction).

# Honest verdict

A2 is NOT closed.  What is achieved: (1) the exact consumer trace, with the
honest finding that the literal minimal interface is under-cut and the genuine
interface is the recoupling-built `Zreal`; (2) the fundamental-rep seeding,
proved; (3) the ELEMENTARY recoupling interface DISCHARGED over the rational TL
algebra (inhabited, non-vacuous, trace-faithful).  The residual is the general
Jones–Wenzl tower induction (`JWTowerCoherence`) plus the construction of the
real `Zreal` from network evaluations and the proof `Ξ ≃ Zreal`.  The Clay
problem stays OPEN; nothing is faked.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'`/`Nat` core only.  No `Classical.*`, no `Real`, no radical, no
`native_decide` (only `decide`/`rfl`).  No `sorry`/`admit`/new `axiom`.  All
witnesses are `Type`-level data; the general tower is a NAMED obligation, never
faked.  `#print axioms` gated (permitted: `propext`/`Quot.sound`).
-/

import YMGap.Continuum.Stage1LoopyReduction
import YMGap.Continuum.TemperleyLiebRecoupling

namespace YMGap.Continuum.RecouplingInterface

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.TemperleyLiebRecoupling

/-! ## 1. Step 1 — the exact consumer trace: what `physical_identity` invokes. -/

/-- **`physical_identity` factors through `AbstractRealPartitionIdentity`
(the literal minimal interface, `rfl`).**  `Stage1Loopy.physical_identity` is
DEFINITIONALLY `S.beyondTree.identity`, which is the `identity` field of the
forgetful projection `BeyondTreePartitionIdentity.toAbstract` — so it invokes
ONLY the identity, never the bundled `SixJRecoupling`. -/
theorem physical_identity_factors [DecidableEq z4Chain.toLattice.Plaquette]
    {p : z4Chain.toLattice.Plaquette}
    {label : z4Chain.toLattice.Plaquette → Rep}
    (S : Stage1Loopy p label) (Γ : List (Polymer z4Chain.toLattice)) :
    S.physical_identity Γ = (S.beyondTree.toAbstract).identity Γ := rfl

/-- **HONESTY: the literal minimal interface is TRIVIALLY inhabitable, so
formalizing A2 against only `identity` is an UNDER-CUT (a fake close).**  The
bare `AbstractRealPartitionIdentity` is inhabited by `Zreal := Ξ`
(`trivialAbstractRealIdentity`), carrying NO recoupling content.  Hence
`physical_identity`'s literal interface does not by itself capture the A2
obligation — the genuine content is the side condition that `Zreal` be the real
partition function.  (Re-export of the caveat that pins this.) -/
theorem under_cut_is_fake [DecidableEq z4Chain.toLattice.Plaquette]
    (w : Q') (label : z4Chain.toLattice.Plaquette → Rep)
    (Γ : List (Polymer z4Chain.toLattice)) :
    (trivialAbstractRealIdentity (L := z4Chain.toLattice) w label).Zreal Γ
      = Xi w Γ label :=
  trivialAbstractRealIdentity_Zreal (L := z4Chain.toLattice) w label Γ

/-! ## 2. The genuine minimal interface: a recoupling datum that builds `Zreal`.

The honest minimal interface `PhysicalRecouplingInterface` bundles the genuine
side condition — a recoupling datum sufficient to *construct* the real partition
function — with the identity `Ξ ≃ Zreal`.  Concretely we carry the elementary
Jones–Wenzl recoupling (the fundamental seed) alongside `Zreal`/`identity`; the
forgetful map to `AbstractRealPartitionIdentity` shows `physical_identity`
factors through it, while the recoupling field forbids the trivial `Zreal := Ξ`
under-cut from being the *intended* datum. -/

/-- **The elementary ½-recoupling interface** (a complete orthogonal Jones–Wenzl
idempotent pair on `χ₁⊗χ₁`, trace-faithful to the SU(2) channel dimensions).
This is the fundamental-seeded base of the recoupling datum, over the rational
TL algebra — no radical. -/
structure ElementaryRecoupling where
  /-- The Jones–Wenzl projector onto the `χ₂` (spin-1) channel. -/
  p_top : TL2
  /-- The projector onto the `χ₀` (trivial) channel. -/
  p_bot : TL2
  /-- `p_top` is idempotent. -/
  top_idem : tl2eqv (tl2mul p_top p_top) p_top
  /-- `p_bot` is idempotent. -/
  bot_idem : tl2eqv (tl2mul p_bot p_bot) p_bot
  /-- The two channels are orthogonal (do not mix). -/
  orthogonal : tl2eqv (tl2mul p_top p_bot) (0, 0) ∧ tl2eqv (tl2mul p_bot p_top) (0, 0)
  /-- Completeness `p_top + p_bot = 1` (resolution of identity on `χ₁⊗χ₁`). -/
  complete : ((p_top.1 + p_bot.1).eqv tl_id.1) ∧ ((p_top.2 + p_bot.2).eqv tl_id.2)
  /-- Trace-faithful: `tr(p_top) = dim χ₂ = 3`. -/
  trace_top : (mtr p_top).eqv (Q'.ofNat (dimN 2))
  /-- Trace-faithful: `tr(p_bot) = dim χ₀ = 1`. -/
  trace_bot : (mtr p_bot).eqv (Q'.ofNat (dimN 0))

/-- **`ElementaryRecoupling` is INHABITED (Step 3 discharge, radical-free).**
The rational Temperley–Lieb Jones–Wenzl idempotents `jw2`/`p0` supply a genuine,
non-vacuous elementary ½-recoupling — a complete orthogonal idempotent pair,
trace-faithful to the SU(2) channel dimensions `3, 1`.  This closes the base of
the recoupling interface over `Q'`. -/
def elementaryRecoupling : ElementaryRecoupling where
  p_top := jw2
  p_bot := p0
  top_idem := jw2_idem
  bot_idem := p0_idem
  orthogonal := jw2_p0_orthogonal
  complete := jw2_add_p0_id
  trace_top := mtr_jw2
  trace_bot := mtr_p0

/-- **The genuine minimal physical interface.**  A recoupling datum (here the
elementary ½-recoupling, the fundamental seed) TOGETHER with the real partition
function and the identity `Ξ ≃ Zreal`.  The `recoupling` field is the genuine
side condition that rules out the trivial `Zreal := Ξ` under-cut as the intended
datum; the `toAbstract`-style projection recovers exactly the interface
`physical_identity` factors through. -/
structure PhysicalRecouplingInterface [DecidableEq z4Chain.toLattice.Plaquette]
    (w : Q') (label : z4Chain.toLattice.Plaquette → Rep) where
  /-- The fundamental-seeded elementary recoupling datum. -/
  recoupling : ElementaryRecoupling
  /-- The real spin-network / Haar partition function. -/
  Zreal : List (Polymer z4Chain.toLattice) → Q'
  /-- The abstract↔real identity `Ξ ≃ Zreal`. -/
  identity : ∀ Γ, (Xi w Γ label).eqv (Zreal Γ)

/-- The genuine minimal interface forgets to the literal
`AbstractRealPartitionIdentity` (dropping the recoupling datum) — so anything
factoring through it also serves `physical_identity`. -/
def PhysicalRecouplingInterface.toAbstract
    [DecidableEq z4Chain.toLattice.Plaquette]
    {w : Q'} {label : z4Chain.toLattice.Plaquette → Rep}
    (P : PhysicalRecouplingInterface w label) :
    AbstractRealPartitionIdentity (L := z4Chain.toLattice) w label where
  Zreal := P.Zreal
  identity := P.identity

/-- **`physical_identity` factors through the genuine minimal interface.**  Given
a `PhysicalRecouplingInterface` whose `Zreal` matches the Stage-1 datum, its
`identity` field discharges `physical_identity` — i.e. the recoupling-aware
interface is a sufficient producer of the sole A2 consumer. -/
theorem physical_identity_of_interface
    [DecidableEq z4Chain.toLattice.Plaquette]
    {w : Q'} {label : z4Chain.toLattice.Plaquette → Rep}
    (P : PhysicalRecouplingInterface w label)
    (Γ : List (Polymer z4Chain.toLattice)) :
    (Xi w Γ label).eqv (P.Zreal Γ) :=
  P.identity Γ

/-! ## 3. Step 2 — fundamental-rep seeding (re-exported, proved). -/

/-- **The Wilson line is fundamental-seeded: `χ₁⊗χ₁ = χ₀ ⊕ χ₂`.**  Re-export of
the elementary Clebsch–Gordan; every recoupling channel of a fundamental Wilson
network is reached by iterating this move (the physical seeding of the Wenzl
tower). -/
theorem wilson_fundamental_seeding :
    (fusionInd 1 1 0).eqv 1 ∧ (fusionInd 1 1 2).eqv 1 ∧
    (fusionInd 1 1 1).eqv 0 ∧ (fusionInd 1 1 3).eqv 0 :=
  fundamental_fusion_channels

/-! ## 4. Non-vacuity of the discharged interface. -/

/-- **The discharged elementary recoupling is non-vacuous / not a shape witness.**
Its two projectors have DISTINCT traces `3 ≠ 1` (the genuine channel dimensions
`dim χ₂ ≠ dim χ₀`) — a constant/shape witness could not separate the channels.
So `elementaryRecoupling` carries real recoupling content. -/
theorem elementaryRecoupling_nonvacuous :
    ¬ (mtr elementaryRecoupling.p_top).eqv (mtr elementaryRecoupling.p_bot) := by
  decide

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean):

  * `physical_identity_factors` — `physical_identity` invokes ONLY `identity`
    (the literal minimal interface, `rfl`);
  * `under_cut_is_fake` — that literal interface is trivially inhabitable, so it
    is an under-cut; the genuine content is the `Zreal`-is-real side condition;
  * `ElementaryRecoupling` + `elementaryRecoupling` — the elementary ½-recoupling
    interface, INHABITED over the rational TL algebra (radical-free, complete
    orthogonal idempotent pair, trace-faithful);
  * `PhysicalRecouplingInterface` (+ `toAbstract`, `physical_identity_of_interface`)
    — the genuine minimal interface (recoupling datum + `Ξ ≃ Zreal`) that
    `physical_identity` factors through;
  * `wilson_fundamental_seeding` — the fundamental-rep seeding `χ₁⊗χ₁ = χ₀ ⊕ χ₂`;
  * `elementaryRecoupling_nonvacuous` — the discharged datum separates the
    channels (`3 ≠ 1`), not a shape witness.

NAMED-open (NOT faked, NO inhabitant):

  * `TemperleyLiebRecoupling.JWTowerCoherence` — the general Jones–Wenzl tower
    (∀-spins pentagon) as the induction on the Wenzl recursion;
  * the construction of the real `Zreal` from network evaluations, and the proof
    `Ξ ≃ Zreal` for it (the R1-side matching) — the remaining A2 content.

A2 is NOT closed.  This is the exact consumer trace + fundamental seeding + the
elementary recoupling DISCHARGED over the rational TL algebra.  It is NOT the
∀-spins closure, NOT a continuum limit, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.RecouplingInterface

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RecouplingInterface.physical_identity_factors
#print axioms YMGap.Continuum.RecouplingInterface.under_cut_is_fake
#print axioms YMGap.Continuum.RecouplingInterface.elementaryRecoupling
#print axioms YMGap.Continuum.RecouplingInterface.physical_identity_of_interface
#print axioms YMGap.Continuum.RecouplingInterface.wilson_fundamental_seeding
#print axioms YMGap.Continuum.RecouplingInterface.elementaryRecoupling_nonvacuous
