/-
The **Tier-0 reduction capstone, HONESTY-CORRECTED**: the same three-atom a→0
frontier, restated over the CLOSED 4D lattice `z4Chain` on three atoms NONE of
which is provably empty.

# Why a corrected capstone exists (two honesty corrections)

The round-1 `Tier0ReductionCapstone.Tier0Atoms` bundled TWO defective atoms:

  * **a2 was PROVABLY EMPTY.**  Its `PartitionBeyondTree.BeyondTreePartition
    Identity` carries a `SixJRecoupling`, and `SixJRecouplingProgress.
    sixjRecoupling_uninhabited : SixJRecoupling → False` proves that field forces
    `1 ≃ 0` at the unguarded `D = 0` truncation.  So `Tier0Atoms` was itself
    uninhabited and the ENTIRE A-half type-checked only as a total function of a
    structure nothing can inhabit — vacuously true.
  * **a1 was a 1D MISLABEL.**  `MultiComponentKPProgress.PenroseUrsellDatum p`
    is the redundant single-rep 1D artifact (rate `ρ = 4/9`); the genuine 4D
    content is `Stage1LoopyReduction.PenroseUrsellDatumG (z4ClusterCountBound p)
    w4 gr` over the CLOSED count `K = 625` (rate `ρ4 = 15/32 < 1`).

This module re-states the frontier on the three CORRECTED atoms and re-derives
both honestly-attainable half-payoffs on them.  All three are genuinely
INHABITABLE (none provably empty):

  * `a1` — `PenroseUrsellDatumG` is a genuine relaxation, no `D = 0` truncation
    bug (`ofPenroseUrsellDatum` witnesses it is a relaxation, not a re-label).
  * `a2` — `RacahProb` is Defect-1-safe (`guardedRow_satisfiable_at_zero`: the
    guarded all-zero row constraint is SATISFIABLE by the δ-kernel, so the
    `1 ≃ 0` degeneracy is gone) and carries content (`racahProb_not_allZero`).
  * `b`  — `CrossRatioMonotone w` is unchanged (Core B, the s=1 spectral margin).

# The honesty caveat that must be surfaced (the one non-mechanical delta)

The old (empty) `BeyondTreePartitionIdentity` supplied a GLOBAL identity
`Ξ ≃ Zreal` certifying that `loopyCorr = offCorr` IS the physical two-component
Wilson correlator.  `RacahProb` does NOT supply that global partition identity —
it supplies the LOCAL closed-fusion-loop collapse (`tetraAmp`: the `m ≥ 4`
tetrahedron = two PROVED trivalent corners `tripleCharInt = nFoldCharInt_three`
glued by ONE `RacahProb` contraction, `tetraAmp_nonneg`).  So the corrected
capstone closes the VACUITY of a2, but the "offCorr is the physical correlator"
link is now carried by the `tetraAmp` closed-loop collapse rather than a single
`Ξ ≃ Zreal`.  This is a genuine REDUCTION, not a closure, and it is NOT claimed
that `RacahProb` reproduces the exact partition-identity role.  Clay stays OPEN.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  The three atoms are named
Type-level fields, left uninhabited, never faked.  Net new closed *physical*
theorems: zero.
-/

import YMGap.Continuum.Stage1LoopyReduction
import YMGap.Continuum.SixJRecouplingProgress
import YMGap.Continuum.FiniteSMarginWorstcase
import YMGap.Continuum.WHTailCeilingsClose
import YMGap.Rubric.ContinuumScorecard

namespace YMGap.Continuum.Tier0FrontierCorrected

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Rubric

/-! ## 1. The three CORRECTED open atoms (all inhabitable; none provably empty). -/

/-- **`Tier0AtomsC` — the corrected OPEN frontier as exactly three named atoms.**
Signature SIMPLIFIES vs. round 1: `RacahProb` needs no `L`/`w`/`label`/
`DecidableEq`, and `a1` is now 4D-indexed on `z4Chain`.

  * `a1` — the 4D, DEFECT-FREE Penrose–Ursell datum over the CLOSED count
    `z4ClusterCountBound p` at `w4` (rate `ρ4 = 15/32`); a genuine relaxation.
  * `a2` — the guarded doubly-stochastic `(2e+1)(2f+1){6j}²` Racah kernel;
    Defect-1-safe (`guardedRow_satisfiable_at_zero`) and non-vacuous
    (`racahProb_not_allZero`).
  * `b`  — the s=1 spectral-margin cross-ratio monotonicity (Core B), unchanged.

LEFT UNINHABITED — supplying all three WITHOUT `sorry`/`axiom` is the open
content.  Unlike round 1, NO field is a provably-empty obligation. -/
structure Tier0AtomsC (p : z4Chain.toLattice.Plaquette) (w : Q') : Type where
  /-- **A1 (4D, Defect-free)** — the Penrose–Ursell connecting-cluster datum. -/
  a1 : PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr
  /-- **A2 (Defect-1-safe)** — the guarded doubly-stochastic Racah 6j² kernel. -/
  a2 : SixJRecouplingProgress.RacahProb
  /-- **B (unchanged)** — the s=1 spectral-margin cross-ratio monotonicity. -/
  b  : FiniteSMarginWorstcase.CrossRatioMonotone w

/-! ## 2. The A-half payoff, re-proved on the corrected atoms (rests on `a1`). -/

/-- **`tier0C_A_offCorr_decay` — the reduced A-conclusion (PROVED).**  The
off-diagonal correlator carried by the 4D datum `A.a1` decays geometrically at
the GENUINE 4D rate: `offCorr d ≤ 2·(kpRatio (z4ClusterCountBound p) w4 gr)^d`,
`ρ4 = 15/32 < 1`.  Rests on `A.a1` ALONE (exactly as `Stage1Loopy.decay`'s body
uses only `S.ursell`). -/
theorem tier0C_A_offCorr_decay {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (A : Tier0AtomsC p w) (d : Nat) :
    A.a1.offCorr d ≤ Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ d :=
  penroseUrsell_offCorr_decayG (z4ClusterCountBound p) w4_nonneg gr
    (z4_genuine_threshold p) A.a1 d

/-- **`tier0C_A_loopy` — A-half (PROVED total function of the atoms).**  Mirrors
`Stage1Loopy.decay` verbatim with `S.ursell := A.a1`: a genuine
`LoopyCorrelatorResidual w4` at the 4D majorant rate `ρ4 = 15/32 < 1`.  Upgrades
the honest rate from the vacuous 1D `ρ = 4/9` to the genuine 4D `ρ4 = 15/32`
(`stage1_rate_value` / `stage1_rate_lt_one`). -/
def tier0C_A_loopy {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (A : Tier0AtomsC p w) : LoopyCorrelatorResidual w4 where
  graphMass := fun d => d
  loopyEnvelope := fun L => Q'.ofNat 2 * (kpRatio (z4ClusterCountBound p) w4 gr) ^ L
  loopyCorr := fun d => A.a1.offCorr d
  loopy_decay := fun d => tier0C_A_offCorr_decay A d

/-- **`tier0C_A_closedLoop` — a2's corrected load-bearing use (PROVED).**  This
replaces the now-vacuous `Stage1Loopy.physical_identity` (`Ξ ≃ Zreal` from an
EMPTY datum) with the genuine closed-fusion-loop collapse: the `m ≥ 4`
tetrahedron amplitude is nonnegative, realized as two PROVED trivalent corners
(`tripleCharInt = nFoldCharInt_three`) glued by ONE `RacahProb` contraction.
This is the LOCAL closed-loop link, NOT a global `Ξ ≃ Zreal` (see the module
caveat). -/
theorem tier0C_A_closedLoop {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (A : Tier0AtomsC p w) (D : Nat) (a b c d : Rep) :
    (0 : Q') ≤ SixJRecouplingProgress.tetraAmp A.a2 D a b c d :=
  SixJRecouplingProgress.tetraAmp_nonneg A.a2 D a b c d

/-! ## 3. The B-half payoff (ports over VERBATIM — `A.b` is unchanged Core B). -/

/-- **`tier0C_B_worstcase` (PROVED).**  On `0 ≤ w ≤ wH`, the cross-ratio atom
`A.b` discharges the entire `w`-dependence algebraically. -/
def tier0C_B_worstcase {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (A : Tier0AtomsC p w) : FiniteSMarginWorstcase w :=
  FiniteSMarginWorstcase.crossRatioMonotoneToWorstcase hw0 hwWH A.b

/-- **`tier0C_B_finiteSMargin` (PROVED total function of the atoms).**  On
`0 ≤ w ≤ wH`, `A.b` plus the PROVED wH θ-tail `WHTailCeilingsClose.whAllSMargin`
inhabit `AcNReserveAnalytic.FiniteSMargin w` via `finiteSMarginOfCrossRatio`. -/
def tier0C_B_finiteSMargin {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (A : Tier0AtomsC p w) : FiniteSMargin w :=
  FiniteSMarginWorstcase.finiteSMarginOfCrossRatio hw0 hwWH A.b
    WHTailCeilingsClose.whAllSMargin

/-- **`tier0C_B_reserve` — the downstream spectral-margin node (PROVED).**  The
finite-`s` margin composes on to the autoconvolution log-concavity defect reserve
`LeakGeoDecay.AcNDefectReserve w` (`reserveOfFiniteSMargin`). -/
def tier0C_B_reserve {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (A : Tier0AtomsC p w) : LeakGeoDecay.AcNDefectReserve w :=
  AcNReserveAnalytic.reserveOfFiniteSMargin hw0 (tier0C_B_finiteSMargin hw0 hwWH A)

/-! ## 4. The PROVED fixed-spacing line (unchanged, unconditional). -/

/-- **The fixed-spacing rubric line is MET (PROVED, UNCONDITIONAL).** -/
theorem tier0C_fixedSpacing_met : ClayScorecard.ClayFixedSpacingMet :=
  ContinuumScorecard.fixed_spacing_met

/-! ## 5. The corrected capstone bundle (DELIBERATELY UNINHABITED). -/

/-- **`Tier0FrontierC` — the corrected frontier scorecard.**  Bundles the PROVED
fixed-spacing rubric line and the three CORRECTED open atoms (`Tier0AtomsC`, now
genuinely non-vacuous — no provably-empty obligation).

**Minlos is NO LONGER a field (architectural deletion).**  The continuum-existence
requirement is functional (OS0–OS4 on the Schwinger functional + GNS reconstruction,
`Continuum.FunctionalContinuumTarget`, measure-free = the Jaffe–Witten requirement).
The σ-additive Bochner–Minlos lift `ContinuumScorecard.CitedMinlosLift` is thereby an
OPTIONAL classical corollary DOWNSTREAM of the functional target, NOT a frontier
atom (`FunctionalContinuumTarget.minlos_is_optional_corollary`), so it is dropped
from this bundle.

**No inhabitant, by design** — same honest boundary as round 1, but the atoms are
no longer a provably-empty obligation.  Only `fixedSpacing` is proved. -/
structure Tier0FrontierC (p : z4Chain.toLattice.Plaquette) (w : Q') : Type where
  /-- PROVED — the fixed-spacing rubric line (`clay_fixed_spacing_met`). -/
  fixedSpacing : ClayScorecard.ClayFixedSpacingMet
  /-- OPEN — the three corrected Type-level atoms (A1 4D, A2 Racah, B). -/
  atoms : Tier0AtomsC p w

/-- The fixed-spacing half of any corrected frontier is the PROVED line. -/
theorem tier0C_frontier_fixedSpacing_proved {p : z4Chain.toLattice.Plaquette}
    {w : Q'} (F : Tier0FrontierC p w) : ClayScorecard.ClayFixedSpacingMet :=
  F.fixedSpacing

/-- The A-half payoff from a corrected frontier (PROVED). -/
def tier0C_frontier_A_loopy {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (F : Tier0FrontierC p w) : LoopyCorrelatorResidual w4 :=
  tier0C_A_loopy F.atoms

/-- The B-half payoff from a corrected frontier (PROVED). -/
def tier0C_frontier_B_reserve {p : z4Chain.toLattice.Plaquette} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (F : Tier0FrontierC p w) : LeakGeoDecay.AcNDefectReserve w :=
  tier0C_B_reserve hw0 hwWH F.atoms

end YMGap.Continuum.Tier0FrontierCorrected

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_A_offCorr_decay
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_A_loopy
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_A_closedLoop
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_B_worstcase
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_B_finiteSMargin
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_B_reserve
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_fixedSpacing_met
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_frontier_fixedSpacing_proved
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_frontier_A_loopy
#print axioms YMGap.Continuum.Tier0FrontierCorrected.tier0C_frontier_B_reserve
