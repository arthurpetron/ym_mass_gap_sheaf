/-
ARCHIVED (2026-07-03) — superseded r2 Tier-0 capstone. Excluded from the Lake build
(not under the `YMGap` glob) and kept for provenance only; do NOT import.
Superseded by `YMGap/Continuum/Tier0FrontierCorrected.lean` (r3, inhabitable atoms)
and `YMGap/Continuum/Tier0Scorecard.lean` (r4, the 6-atom frontier scorecard),
which re-prove its half-payoffs on the corrected atoms. See docs/continuum-map.md.
-/

/-
The **Tier-0 reduction capstone**: the whole open frontier of the constructive
Yang–Mills mass-gap development, bundled as EXACTLY THREE named Type-level atoms
(plus one orthogonal, separately-listed measure-existence caveat), with the two
honestly-attainable a→0 half-payoffs PROVED as total functions of those atoms.

# What this module records (and what it does NOT claim)

After the long arc of reductions, the OPEN content of the mass-gap program is
carried by three, and only three, named-open Type-level data, each already
isolated (non-vacuous, never `sorry`) in its own module:

  * **A1 — Penrose–Ursell** (`MultiComponentKPProgress.PenroseUrsellDatum p`):
    the signed connecting-cluster domination `offCorr d ≤ connTailPartial p d
    (tailLen d)`.  Count / threshold / tree-graph / geometric decay are GREEN;
    the sole open field is `penrose_ursell`.
  * **A2 — closed-fusion-loop 6j** (`PartitionBeyondTree.BeyondTreePartition
    Identity w label`): the SU(2) Biedenharn–Elliott / Racah recoupling identity
    bundled with the abstract↔real identity.  The `m`-fold single-link star
    FOLDS with no 6j (proved); the sole open field is `recoup.biedenharn_elliott`.
  * **B — s=1 spectral margin / Core B** (`FiniteSMarginWorstcase.CrossRatio
    Monotone w`): the `w²`-monotone cross-ratio `A_s(w)·M_s(wH)² ≤ A_s(wH)·
    M_s(w)²`.  The interior worst case `w = wH` is CLOSED (`SaddleFloor.saddle
    Floor_wH`); the residual is w-monotonicity on `[0, wH]` only.

`A3` (the 4D lattice-animal count `K = 625`) and the `B1`/`B2`/`B3` layers are
CLOSED / discharged upstream and are NOT re-listed as open here.

## The two half-payoffs (PROVED total functions of the three atoms)

  * **A-half (Stage-1, loopy correlator):** `tier0_A_loopy` turns the three
    atoms into a genuine `LoopyCorrelatorResidual gw` at the majorant rate
    `ρ = mayerRho p = 4/9 < 1` — `MultiComponentKPProgress.loopyResidual_
    penroseUrsell p A.a1`, licensed past trees by the beyond-tree/closed-loop
    partition identity `A.a2`.
  * **B-half (Stage-2, spectral margin):** on `0 ≤ w ≤ wH`, `tier0_B_
    finiteSMargin` turns the three atoms into the full `AcNReserveAnalytic.
    FiniteSMargin w` — feeding `A.b` and the PROVED wH θ-tail
    `WHTailCeilingsClose.whAllSMargin` through `finiteSMarginOfCrossRatio` — and
    `tier0_B_reserve` composes on to the autoconvolution log-concavity reserve
    `LeakGeoDecay.AcNDefectReserve w` (the s=1 spectral-margin node).

## The capstone bundle (DELIBERATELY UNINHABITED — the honest boundary)

`Tier0Frontier` bundles the PROVED fixed-spacing rubric line, the three open
atoms, and the SEPARATE, orthogonal measure-existence caveat
`ContinuumScorecard.CitedMinlosLift`.  It is provided with **no inhabitant**.

# HONESTY FLAG — why there is NO `Tier0Atoms → UniformPhysicalCorrelationDecay`

A clean total function from the three atoms to
`UniformCorrelationDecay.UniformPhysicalCorrelationDecay` does **not** hold and
is NOT written here — it would overclaim.  `UniformPhysicalCorrelationDecay`
additionally requires (i) the σ-additive **measure-existence** lift
`ContinuumScorecard.CitedMinlosLift` (= `ClayContinuumExistence`, orthogonal to
gap survival), and (ii) the envelope-assembly glue turning per-spacing loopy
decay + the uniform rate `m₋` into the single continuum bound.  Hence the
correct capstone is the `Tier0Frontier` bundle (three atoms + the separate
`minlos`), with the two conditional half-payoffs PROVED and the full
`→ UniformPhysicalCorrelationDecay` left as the bundle — never a total function
of the three.  This exactly mirrors `ContinuumScorecard.ContinuumTargetReduction`.

Additionally, the pointwise-factoring shortcut for B is REFUTED upstream
(`FiniteSMarginWorstcaseProof.facI_mlr_false`, `scoutFactoring_uninhabited`,
`factoring_is_strict_regression`), so B is NOT mislabeled "nearly closed": its
residual is the genuine uniform-in-`s` theta / local-CLT cross-ratio.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  The three atoms are named
Type-level fields, left uninhabited, never faked.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
This is a genuine REDUCTION + honest bundling — net new closed *physical*
theorems: zero.  The Clay problem stays OPEN.
-/

import YMGap.Continuum.MultiComponentKPProgress
import YMGap.Continuum.PartitionBeyondTree
import YMGap.Continuum.FiniteSMarginWorstcase
import YMGap.Continuum.WHTailCeilingsClose
import YMGap.Rubric.ContinuumScorecard

namespace YMGap.Continuum.Tier0ReductionCapstone

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Rubric
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.LaplaceMarginDeep

variable {L : Lattice}

/-! ## 1. The three open atoms, bundled (Rule 8: witnesses as data, never Prop-∃) -/

/-- **`Tier0Atoms` — the whole OPEN frontier as exactly three named Type-level
data.**

  * `a1` — Stage-1 off-diagonal: the Penrose–Ursell connecting-cluster datum on
    the plaquette `p` of `zChain`.
  * `a2` — Stage-1 closed loop: the beyond-tree 6j / Biedenharn–Elliott partition
    identity at weight `w` and rep-labelling `label` on a lattice `L`.
  * `b`  — Stage-2 spectral margin: the `w²`-monotone cross-ratio at coupling `w`.

Each field is a named-open datum isolated (non-vacuous, never `sorry`) upstream.
`Tier0Atoms` itself is LEFT UNINHABITED — supplying all three WITHOUT `sorry` /
`axiom` is the open content of the mass-gap program. -/
structure Tier0Atoms (p : zChain.toLattice.Plaquette) (w : Q')
    [DecidableEq L.Plaquette] (label : L.Plaquette → Rep) : Type where
  /-- **A1** — the Penrose–Ursell connecting-cluster datum (Stage-1, off-diagonal). -/
  a1 : MultiComponentKPProgress.PenroseUrsellDatum p
  /-- **A2** — the beyond-tree closed-fusion-loop 6j partition identity (Stage-1). -/
  a2 : PartitionBeyondTree.BeyondTreePartitionIdentity (L := L) w label
  /-- **B** — the s=1 spectral-margin cross-ratio monotonicity (Stage-2). -/
  b : FiniteSMarginWorstcase.CrossRatioMonotone w

/-! ## 2. The A-half payoff (Stage-1): a genuine loopy correlator residual. -/

/-- **`tier0_A_loopy` — A-half (PROVED total function of the atoms).**

The three atoms yield a genuine `LoopyCorrelatorResidual gw`: `A.a1` supplies the
Penrose–Ursell datum, from which `loopyResidual_penroseUrsell` builds the loopy
residual at the majorant rate `ρ = mayerRho p = 4/9 < 1`; `A.a2` supplies the
beyond-tree / closed-loop partition identity that licenses this residual past the
acyclic tree case.  (The `graphMass`, `loopyEnvelope`, `loopyCorr`, `loopy_decay`
are exactly `MultiComponentKPProgress.loopyResidual_penroseUrsell p A.a1`.) -/
def tier0_A_loopy {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (A : Tier0Atoms (L := L) p w label) : LoopyCorrelatorResidual gw :=
  MultiComponentKPProgress.loopyResidual_penroseUrsell p A.a1

/-- **`tier0_A_offCorr_decay` — the reduced A-conclusion (PROVED).**  The
off-diagonal correlator carried by the A1 datum decays geometrically at the
majorant rate: `offCorr d ≤ 2·(mayerRho p)^d`, `mayerRho p = 4/9 < 1`. -/
theorem tier0_A_offCorr_decay {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (A : Tier0Atoms (L := L) p w label) (d : Nat) :
    A.a1.offCorr d ≤ Q'.ofNat 2 * (mayerRho p) ^ d :=
  MultiComponentKPProgress.penroseUrsell_offCorr_decay p A.a1 d

/-! ## 3. The B-half payoff (Stage-2): the finite-`s` spectral margin + reserve.

The wH θ-tail `WHTailCeilingsClose.whAllSMargin : WHAllSMargin` is PROVED
upstream, so the B-half is a total function of the atoms plus the coupling window
`0 ≤ w ≤ wH` — no extra open input is smuggled in. -/

/-- **`tier0_B_worstcase` — the `w`-monotone worst-case reduction (PROVED).**  On
`0 ≤ w ≤ wH`, the cross-ratio atom `A.b` discharges the ENTIRE `w`-dependence
algebraically, inhabiting `LaplaceMarginDeep.FiniteSMarginWorstcase w`
(`crossRatioMonotoneToWorstcase`). -/
def tier0_B_worstcase {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (A : Tier0Atoms (L := L) p w label) : FiniteSMarginWorstcase w :=
  FiniteSMarginWorstcase.crossRatioMonotoneToWorstcase hw0 hwWH A.b

/-- **`tier0_B_finiteSMargin` — B-half (PROVED total function of the atoms).**  On
`0 ≤ w ≤ wH`, the atoms yield the full `AcNReserveAnalytic.FiniteSMargin w`: the
cross-ratio atom `A.b` and the PROVED wH θ-tail `WHTailCeilingsClose.whAllSMargin`
are fed through `finiteSMarginOfCrossRatio`.  This collapses the two-parameter
`(w,s)` family to the single wH sequence with the `w`-dependence discharged and
the sole residual factored into the cross-ratio. -/
def tier0_B_finiteSMargin {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (A : Tier0Atoms (L := L) p w label) : FiniteSMargin w :=
  FiniteSMarginWorstcase.finiteSMarginOfCrossRatio hw0 hwWH A.b
    WHTailCeilingsClose.whAllSMargin

/-- **`tier0_B_reserve` — the downstream spectral-margin node (PROVED).**  The
finite-`s` margin composes on to the autoconvolution log-concavity defect reserve
`LeakGeoDecay.AcNDefectReserve w` (`reserveOfFiniteSMargin`), the s=1
spectral-margin object feeding `SymMinorGershgorin` / the asymptotic descent
tower. -/
def tier0_B_reserve {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (A : Tier0Atoms (L := L) p w label) : LeakGeoDecay.AcNDefectReserve w :=
  AcNReserveAnalytic.reserveOfFiniteSMargin hw0 (tier0_B_finiteSMargin hw0 hwWH A)

/-! ## 4. The PROVED fixed-spacing line + the orthogonal Minlos caveat. -/

/-- **The fixed-spacing rubric line is MET (PROVED, UNCONDITIONAL).**  Re-export
of `ClayScorecard.clay_fixed_spacing_met` via `ContinuumScorecard.fixed_spacing_
met`: every fixed-spacing clause (positive gap, geometric clustering,
nontriviality, OS2, positive infinite-volume mass) is a real theorem about
SPECIFIC Yang–Mills objects. -/
theorem tier0_fixedSpacing_met : ClayScorecard.ClayFixedSpacingMet :=
  ContinuumScorecard.fixed_spacing_met

/-! ## 5. The capstone bundle (DELIBERATELY UNINHABITED — the honest boundary). -/

/-- **`Tier0Frontier` — the frontier scorecard.**  Bundles the PROVED
fixed-spacing rubric line, the three OPEN atoms (`Tier0Atoms`), and the SEPARATE,
orthogonal measure-existence caveat `ContinuumScorecard.CitedMinlosLift` (=
`ClayContinuumExistence`, Input B — the cited-classical σ-additive Minlos lift,
non-transferable to this Mathlib-free substrate).

**There is no inhabitant of this structure in this file, by design.**  Supplying
the three atoms AND the Minlos lift WITHOUT `sorry` / `axiom` / `Prop := True` is
exactly the open continuum Yang–Mills mass-gap problem.  Only `fixedSpacing` is
already proved (`tier0_fixedSpacing_met`).  Mirrors
`ContinuumScorecard.ContinuumTargetReduction`. -/
structure Tier0Frontier (p : zChain.toLattice.Plaquette) (w : Q')
    [DecidableEq L.Plaquette] (label : L.Plaquette → Rep) : Type where
  /-- PROVED — the fixed-spacing rubric line (`clay_fixed_spacing_met`). -/
  fixedSpacing : ClayScorecard.ClayFixedSpacingMet
  /-- OPEN — the three named Type-level atoms (A1, A2, B). -/
  atoms : Tier0Atoms (L := L) p w label
  /-- OPEN (ORTHOGONAL) — the cited-classical Minlos σ-additive measure lift. -/
  minlos : ContinuumScorecard.CitedMinlosLift

/-- **The fixed-spacing half of any frontier is the PROVED line** — independent of
the open atoms and the Minlos caveat. -/
theorem tier0_frontier_fixedSpacing_proved {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (F : Tier0Frontier (L := L) p w label) : ClayScorecard.ClayFixedSpacingMet :=
  F.fixedSpacing

/-- **`tier0_frontier_A_loopy` — the A-half payoff from a frontier (PROVED).**
Given a frontier, its atoms yield the loopy correlator residual. -/
def tier0_frontier_A_loopy {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (F : Tier0Frontier (L := L) p w label) : LoopyCorrelatorResidual gw :=
  tier0_A_loopy F.atoms

/-- **`tier0_frontier_B_reserve` — the B-half payoff from a frontier (PROVED).**
On `0 ≤ w ≤ wH`, a frontier's atoms yield the spectral-margin defect reserve. -/
def tier0_frontier_B_reserve {p : zChain.toLattice.Plaquette} {w : Q'}
    [DecidableEq L.Plaquette] {label : L.Plaquette → Rep}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (F : Tier0Frontier (L := L) p w label) : LeakGeoDecay.AcNDefectReserve w :=
  tier0_B_reserve hw0 hwWH F.atoms

/-! ## 6. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean — total functions of the three atoms / the
coupling window / the PROVED wH θ-tail):

  * `tier0_A_loopy`         — three atoms ⟹ `LoopyCorrelatorResidual gw`
                              (majorant `ρ = 4/9`);
  * `tier0_A_offCorr_decay` — the reduced off-diagonal decay `offCorr d ≤ 2·ρ^d`;
  * `tier0_B_worstcase`     — `0 ≤ w ≤ wH` + `A.b` ⟹ `FiniteSMarginWorstcase w`;
  * `tier0_B_finiteSMargin` — + PROVED wH θ-tail ⟹ `FiniteSMargin w`;
  * `tier0_B_reserve`       — ⟹ `LeakGeoDecay.AcNDefectReserve w`
                              (the s=1 spectral-margin node);
  * `tier0_fixedSpacing_met`             — the PROVED fixed-spacing rubric line;
  * `tier0_frontier_fixedSpacing_proved` / `tier0_frontier_A_loopy` /
    `tier0_frontier_B_reserve` — the bundle projections / payoffs.

NAMED-open (NOT faked, NO inhabitant — the SOLE residual set):

  * `Tier0Atoms.a1` — `PenroseUrsellDatum.penrose_ursell` (A1);
  * `Tier0Atoms.a2` — `SixJRecoupling.biedenharn_elliott` inside
    `BeyondTreePartitionIdentity.recoup` (A2);
  * `Tier0Atoms.b`  — `CrossRatioMonotone.cross` (B);
  ⟹ `Tier0Atoms`, and the bundle `Tier0Frontier` [DELIBERATELY UNINHABITED],
     which additionally carries the ORTHOGONAL `CitedMinlosLift` (measure
     existence, Input B).

There is intentionally NO `Tier0Atoms → UniformPhysicalCorrelationDecay`: that
would overclaim (it needs the orthogonal Minlos lift + envelope-assembly glue).
`A3` (the 4D lattice-animal count) and the `B1`/`B2`/`B3` layers are
CLOSED / discharged upstream and are not re-listed.  The Clay problem stays OPEN
— this module is the honest reduction bundle, net new closed physical theorems:
zero. -/

end YMGap.Continuum.Tier0ReductionCapstone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_A_loopy
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_A_offCorr_decay
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_B_worstcase
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_B_finiteSMargin
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_B_reserve
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_fixedSpacing_met
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_frontier_fixedSpacing_proved
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_frontier_A_loopy
#print axioms YMGap.Continuum.Tier0ReductionCapstone.tier0_frontier_B_reserve
