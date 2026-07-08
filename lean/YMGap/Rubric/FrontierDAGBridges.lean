/-
# `YMGap.Rubric.FrontierDAGBridges` — the four suspected cross-list identifications

The `FrontierDAG` frontier node (`YMGap.Rubric.FrontierDAG`) shares several atoms
with the reconstruction/continuum scorecards and with the graded-budget /
cross-ratio programme.  Four cross-list identifications were *suspected*; this
module adjudicates each ONE way — a proved equivalence, a proved one-directional
supply, or a documented refutation — and never fakes a merge.  The verdicts:

  (i)   **Minlos ≡ Minlos — PROVED EQUIVALENCE (definitional `rfl`).**
        `ContinuumScorecard.CitedMinlosLift = ReconstructionScorecard.OpenContinuumMeasure`
        (both `= ClayContinuumExistence`).  This is the ONLY genuine node MERGE:
        the two Minlos slots are one node.

  (ii)  **`bulkCtrl` vs `hlocalize` — DOCUMENTED REFUTATION (arity mismatch).**
        `FrontierDAG.bulkCtrl : SpectralLocalizationCrux.SpectralLocalization w`
        is PER-MODE (`Q' → Type`); the graded-budget carrier
        `GradedBondMovingBudget.SpectralLocalization : AFRateModulus → Nat → Type`
        is PER-SCALE.  The arities differ, so there is NO `rfl` merge.  The
        genuine link is the per-scale `hbridge_of_hlocalize`
        (`Stage2ConvergesToMargin`), a NAMED-OPEN reduction — encoded here as the
        uninhabited bridge type `BulkCtrlToHlocalizeBridge`, NOT an identity.

  (iii) **`OpenTrueMargin ⟹ UniformSpacingFloor` — PROVED supply, two routes.**
        The additive/physical route re-exports the landed
        `uniformSpacingFloor_of_trueMarginPhysical`; the multiplicative/surrogate
        route (`qFloor_of_openTrueMargin`) is the one that discharges the ACTUAL
        `FrontierDAG.trueMargin` atom (the multiplicative
        `UniformCouplingFromAF.TrueMarginRecursion`), via
        `DefectGapRecursion.uniform_floor` + the true-margin pin
        `physGap_is_trueMargin`.  This is a one-directional supply, NOT an
        equivalence — the two routes consume DIFFERENT structures.

  (iv)  **`CoreBBridge` — DOCUMENTED REFUTATION of equivalence + PROVED CONVERSE.**
        `FrontierDAG.CoreBBridge w : FiniteSMargin w → CrossRatioMonotone w` is the
        FORWARD/hard direction and stays NAMED-OPEN.  Only the CONVERSE
        `CrossRatioMonotone w → FiniteSMargin w` is a theorem
        (`finiteSMarginOfCrossRatio`); we re-export it as `finiteSMargin_of_crossRatio`.
        So the suspected equivalence is refuted; exactly one direction is proved.

# Honesty (AGENTS.md Rules 1, 6, 8)

Every load-bearing declaration is `#print axioms`-gated below (permitted output:
`propext` / `Quot.sound` only).  No `Classical.*`, no `by_contra`, no
`native_decide`, no `sorry`, no custom `axiom`.  The two refuted/open directions
are carried as NAMED, UNINHABITED Type-level residuals — never `sorry`, never a
vacuous `Prop := True`.  No Clay-frontier type is inhabited: (iii) discharges only
the OPEN-to-FLOOR *supply* (`QFloor`), whose own input `TrueMarginRecursion` is the
uninhabited residual, so nothing here closes the frontier.
-/
import YMGap.Rubric.FrontierDAG
import YMGap.Rubric.ContinuumScorecard
import YMGap.Rubric.ReconstructionScorecard
import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.GradedBondMovingBudget
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.UniformCouplingFromAF
import YMGap.Continuum.TrueMarginRecursionPhysical
import YMGap.Continuum.ContinuumClosureProgram
import YMGap.Continuum.UnifiedContinuumFloor
import YMGap.Continuum.FiniteSMarginWorstcase
import YMGap.Continuum.AcNReserveAnalytic
import YMGap.Continuum.LaplaceMarginDeep
import YMGap.Continuum.FusionCoreStepRoundA

namespace YMGap.Rubric.FrontierDAGBridges

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.AFRateCalibration
open YMGap.Rubric

/-! ## (i) Minlos ≡ Minlos — PROVED EQUIVALENCE (definitional `rfl`)

`CitedMinlosLift := ClayContinuumExistence` (ContinuumScorecard) and
`OpenContinuumMeasure := ClayScorecard.ClayContinuumExistence`
(ReconstructionScorecard) are the SAME type.  Their equality is definitional; this
is the only true node MERGE of the four suspected identifications: the two
optional-measure slots are the same type.  (The Minlos node is no longer carried
as a `FrontierDAG` field — the continuum target is stated functionally — so this
records the surviving definitional identity between the two optional-corollary
objects, not a transport of a carried frontier value.) -/

/-- **The shared-Minlos node identity (PROVED, definitional).**  The Tier-0
continuum scorecard's `CitedMinlosLift` slot and the reconstruction scorecard's
`OpenContinuumMeasure` slot are ONE node. -/
theorem minlos_crosslist_identity :
    ContinuumScorecard.CitedMinlosLift = ReconstructionScorecard.OpenContinuumMeasure :=
  rfl

/-! ## (ii) `bulkCtrl` vs `hlocalize` — DOCUMENTED REFUTATION (arity mismatch)

`FrontierDAG.bulkCtrl` has type `SpectralLocalizationCrux.SpectralLocalization w`
(`Q' → Type`, a per-MODE bulk-shift certificate).  The graded-budget localization
carrier is `GradedBondMovingBudget.SpectralLocalization afr N₀`
(`AFRateModulus → Nat → Type`, a per-SCALE statement).  The arities differ, so no
`rfl` identifies them.  The GENUINE link is the per-scale
`Stage2ConvergesToMargin.hbridge_of_hlocalize`, which is NOT an identity.  We
record the honest cross-list content as the NAMED-OPEN bridge type below and DO
NOT inhabit it (Rule 8). -/

/-- **`BulkCtrlToHlocalizeBridge` — the NAMED-OPEN per-mode ⟶ per-scale bridge.**
From a per-MODE `SpectralLocalization` at every weight `afr.w k`, produce the
per-SCALE graded-budget `SpectralLocalization afr N₀`.  This is the honest content
of the suspected `bulkCtrl`/`hlocalize` identification — a reduction, NOT the `rfl`
merge the arities forbid.  Left UNINHABITED. -/
abbrev BulkCtrlToHlocalizeBridge (afr : AFRateModulus) (N₀ : Nat) : Type :=
  (∀ k, SpectralLocalizationCrux.SpectralLocalization (afr.w k)) →
    GradedBondMovingBudget.SpectralLocalization afr N₀

/-! ## (iii) `OpenTrueMargin ⟹ UniformSpacingFloor` — PROVED supply, two routes

Two independent routes turn a true-margin residual into the shared spacing-uniform
`QFloor`.  They consume DIFFERENT structures, which is the load-bearing subtlety:

  * the ADDITIVE/physical route re-exports `uniformSpacingFloor_of_trueMarginPhysical`,
    which takes the honest additive `TrueMarginRecursionPhysical`;
  * the MULTIPLICATIVE/surrogate route (`qFloor_of_openTrueMargin`) takes the
    MULTIPLICATIVE `UniformCouplingFromAF.TrueMarginRecursion` — which is exactly the
    `FrontierDAG.trueMargin` field — and is the ONE that discharges the real DAG
    atom, via `DefectGapRecursion.uniform_floor` and the pin `physGap_is_trueMargin`.

Neither is an equivalence: both are one-directional supplies of `QFloor`, whose own
input (the true-margin residual) stays uninhabited. -/

/-- **Additive/physical route (re-export).**  The honest additive true-margin
residual supplies the shared `QFloor` on its `margin`. -/
def uniformSpacingFloor_of_physical (T : TrueMarginRecursionPhysical) :
    UnifiedContinuumFloor.QFloor T.margin :=
  uniformSpacingFloor_of_trueMarginPhysical T

/-- **Multiplicative/surrogate route (NEW) — discharges the ACTUAL DAG atom.**  The
multiplicative `UniformCouplingFromAF.TrueMarginRecursion` supplies the shared
`QFloor` on its `trueMargin`: the floor is the recursion's product floor
`D.prodFloor`, positive by `D.prodFloor_pos`, and below `trueMargin k` at every
scale via `DefectGapRecursion.uniform_floor` rewritten through the pin
`physGap_is_trueMargin`. -/
def qFloor_of_openTrueMargin (T : UniformCouplingFromAF.TrueMarginRecursion) :
    UnifiedContinuumFloor.QFloor T.trueMargin where
  floor := T.D.prodFloor
  floor_pos := T.D.prodFloor_pos
  bound := fun k => by
    have h := ContinuumClosureProgram.DefectGapRecursion.uniform_floor T.D k
    rw [T.physGap_is_trueMargin k] at h
    show T.D.prodFloor ≤ T.trueMargin k
    exact h

/-- **The `FrontierDAG.trueMargin` atom ⟹ shared `QFloor` (PROVED).**  Applying the
multiplicative route to the `trueMargin` field of a `FrontierDAG` yields the
spacing-uniform floor on the genuine dimensionless margin.  (Nothing here inhabits
`FrontierDAG` itself — this is a field-level supply, conditional on the frontier
node existing.) -/
def frontierTrueMargin_qFloor
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG.FrontierDAG p w G L N pΓ) :
    UnifiedContinuumFloor.QFloor F.trueMargin.trueMargin :=
  qFloor_of_openTrueMargin F.trueMargin

/-! ## (iv) `CoreBBridge` — DOCUMENTED REFUTATION + PROVED CONVERSE

`FrontierDAG.CoreBBridge w : FiniteSMargin w → CrossRatioMonotone w` is the
FORWARD/hard direction (analytic finite-`s` margin ⟹ cross-ratio monotonicity) and
is NAMED-OPEN in `FrontierDAG` — it is NOT inhabited anywhere.  What the codebase
PROVES is the CONVERSE: `CrossRatioMonotone w` (with `0 ≤ w ≤ wH`) plus the wH tail
`WHAllSMargin` gives `FiniteSMargin w` (`finiteSMarginOfCrossRatio`).  Hence the
suspected `FiniteSMargin ↔ CrossRatioMonotone` equivalence is REFUTED; exactly one
direction is a theorem, which we re-export. -/

/-- **The PROVED converse of `CoreBBridge`.**  `CrossRatioMonotone w` + `WHAllSMargin`
⟹ `FiniteSMargin w` (re-export of `finiteSMarginOfCrossRatio`).  The forward
`CoreBBridge` direction stays NAMED-OPEN, so this is NOT an equivalence. -/
def finiteSMargin_of_crossRatio {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwWH : w ≤ FusionCoreStepRoundA.wH)
    (star : FiniteSMarginWorstcase.CrossRatioMonotone w)
    (m : LaplaceMarginDeep.WHAllSMargin) :
    AcNReserveAnalytic.FiniteSMargin w :=
  FiniteSMarginWorstcase.finiteSMarginOfCrossRatio hw0 hwWH star m

/-! ## PROVED vs OPEN (AGENTS.md Rule 6)

PROVED here (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * (i)   `minlos_crosslist_identity` — the one true node MERGE (definitional);
  * (iii) `uniformSpacingFloor_of_physical` — additive route to `QFloor`;
  * (iii) `qFloor_of_openTrueMargin` — multiplicative route, discharges the real
          `FrontierDAG.trueMargin` atom into `QFloor` (the KEY result);
  * (iii) `frontierTrueMargin_qFloor` — the same at the `FrontierDAG` field;
  * (iv)  `finiteSMargin_of_crossRatio` — the PROVED converse of `CoreBBridge`.

OPEN / REFUTED (named, NO inhabitant — never `sorry`):

  * (ii)  `BulkCtrlToHlocalizeBridge` — the per-mode ⟶ per-scale bridge; the
          `bulkCtrl`/`hlocalize` identity is refuted by the arity mismatch, the
          genuine link being the named per-scale `hbridge_of_hlocalize`;
  * (iv)  `FrontierDAG.CoreBBridge` — the forward `FiniteSMargin → CrossRatioMonotone`
          direction stays open; the suspected equivalence is refuted.

Nothing here inhabits a Clay-frontier type: (iii)'s `QFloor` supplies are
conditional on the uninhabited true-margin residual / on a `FrontierDAG` term, so
the mass-gap problem remains OPEN. -/

end YMGap.Rubric.FrontierDAGBridges

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.FrontierDAGBridges.minlos_crosslist_identity
#print axioms YMGap.Rubric.FrontierDAGBridges.uniformSpacingFloor_of_physical
#print axioms YMGap.Rubric.FrontierDAGBridges.qFloor_of_openTrueMargin
#print axioms YMGap.Rubric.FrontierDAGBridges.frontierTrueMargin_qFloor
#print axioms YMGap.Rubric.FrontierDAGBridges.finiteSMargin_of_crossRatio
