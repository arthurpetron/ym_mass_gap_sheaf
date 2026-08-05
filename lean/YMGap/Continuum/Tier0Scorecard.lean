/-
The **Tier-0 scorecard** — the sharpened a→0 gap-survival frontier as a
machine-checked **6-atom (functional-continuum)** enumeration.  Supersedes the
3-atom `Tier0FrontierCorrected.Tier0FrontierC` by REFINING its single loopy atom
`a1` into three geometry atoms (T′)+(D1)+(D2), keeping the closed-fusion 6j atom
as the genuinely-nonlinear `SixJPentagon` residual, and refining its Core-B atom
`b` into the pinned `SpectralMarginInput` (three Balaban-RG sub-atoms).

# The picture recorded (read first)

  Sub-wall A (loopy geometry) — 4 OPEN atoms
    (T′)  `Ursell4DProgress.TreeGraphBound.tree_graph`  — spanning-tree inequality
    (D1)  `Ursell4DProgress.BridgeDecomposition.decompose` — Mayer–Ursell expansion
    (D2)  `Ursell4DProgress.SepLatticeZ4`  — the plaquette metric refining `z4Chain`
    (A2)  `PentagonRelation.PentagonNumericCore` — the fractional-6j associator
          (`SixJPentagon` was a channel-mismatch BUG, REFUTED; the genuine
          Biedenharn–Elliott pentagon is LINEAR in the signed irrational `{6j}`,
          not `Q'`-representable).  Carried alongside a Level-1 `RacahProb` coarse
          surrogate used only for the frontierC coarsening.

  Sub-wall B (Balaban RG) — 3 OPEN atoms, all inside ONE
    `AsymptoticSpectralLoc.SpectralMarginInput b afr N₀`
      · `sl.hlocalize` = Core B (the p≥2 SU(2)-fusion local-CLT)
      · `hbridge`      = the pinned trajectory-shift control (`g_k ≠ 1`)
      · `hadd`         = the located-2nd-eigenvalue ↔ physical-margin dictionary

  Continuum existence — FUNCTIONAL (`Continuum.FunctionalContinuumTarget`: OS0–OS4
  on the Schwinger functional + GNS reconstruction, measure-free).  The σ-additive
  `ContinuumScorecard.CitedMinlosLift` (= `ClayContinuumExistence`) is NO LONGER an
  atom — an OPTIONAL classical corollary downstream of the functional target
  (`FunctionalContinuumTarget.minlos_is_optional_corollary`).

# What is PROVED here (each `#print axioms`-gated, permitted `propext`/`Quot.sound`)

  * `fixedSpacing_met` — the entire fixed-spacing rubric line, UNCONDITIONAL
    (`ContinuumScorecard.fixed_spacing_met`).
  * `subA_offCorr_decompose` / `subA_tree_graph` — the load-bearing (D1)/(T′)
    projections of Sub-wall A.
  * `subB_prodFloor_pos` / `subB_physGap_pos` — the assembled Stage-2 floor
    (the three-floor collapse `Stage2ConvergesToMargin.stage2_*` fired from the
    single `SpectralMarginInput`, `recursion` DISCHARGED not assumed).
  * `a2_racah` / `a2_tetra_nonneg` — the Level-1 A2 surrogate is non-empty:
    `RacahInhabit.racahRP` inhabits `RacahProb` (the coarse `SubWallA.a2Racah`
    slot) and the tetrahedron amplitude is concretely nonnegative.
  * `pentagon_to_racah` — a retained (NO-LONGER-USED) fact about the REFUTED buggy
    `SixJPentagon`: dropping its pentagon field yields a `RacahProb`.
  * `toFrontierC` — the supersession bridge: a `Tier0Scorecard` coarsens to a
    `Tier0FrontierCorrected.Tier0FrontierC`, discharging its coarse a2 slot from
    the scorecard's OWN Level-1 `SubWallA.a2Racah` surrogate (the genuine Level-2
    content `SubWallA.a2Pentagon : PentagonNumericCore` is non-stochastic — constant
    `1/4` — so it admits NO total map to `RacahProb`).  It consumes the coarse
    `a1`/`b` as explicit inputs precisely BECAUSE Sub-wall A refines `a1` into
    (T′)+(D1)+(D2) and Sub-wall B refines `b` into the pinned `SpectralMarginInput`
    — the finer enumeration does not hand back the coarse atoms for free.  This
    records the strict refinement mechanically.

# DELIBERATELY UNINHABITED bundle

`Tier0Scorecard` has NO inhabitant, by design (mirrors `Tier0FrontierC` /
`ClayTarget` / `ContinuumScorecard.ContinuumTargetReduction`).  Only `fixedSpacing`
is proved; supplying `subA` (four open atoms) and `subB` (three open atoms) —
together with the open `a → 0` functional modulus of `FunctionalContinuumTarget` —
WITHOUT `sorry`/`axiom` is the open continuum Clay problem.  (The σ-additive Minlos
lift is NOT among these — it is an optional classical corollary, not an atom.)

# Coupling note (Sub-wall A geometry atoms are coupled)

`TreeGraphBound`'s first argument is a `SepLattice`, and `SepLatticeZ4` IS the open
(D2) field; so `tTree` is phrased over `d2Sep.val` — the two A-geometry atoms
(T′) and (D2) are genuinely coupled, as flagged.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat`.  No `Classical.*`, no `Real`, no `native_decide`,
no `by_contra`, no `sorry` / `admit` / new `axiom`.  Every open atom is a NAMED
Type-level field, uninhabited, never faked.  Net new closed physics: zero — this
is a sharper HONEST enumeration of the same OPEN frontier.  Clay YM mass gap OPEN.
-/

import YMGap.Continuum.Tier0FrontierCorrected
import YMGap.Continuum.Ursell4DProgress
import YMGap.Continuum.RacahInhabit
import YMGap.Continuum.Stage2ConvergesToMargin
import YMGap.Continuum.PentagonRelation

namespace YMGap.Continuum.Tier0Scorecard

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.SixJRecouplingProgress
open YMGap.Continuum.AFRateCalibration
open YMGap.Rubric

/-! ## 1. The REFUTED buggy carrier `SixJPentagon` (retained for the record). -/

/-- **`SixJPentagon` — the REFUTED buggy A2 carrier (retained, NO LONGER a field
of `SubWallA`).**

Originally advertised as "the genuine cubic A2 residual".  A close reading of the
actual field shows this is FALSE: the `pentagon` field is a channel-mismatch BUG —
its third internal factor `P.racahProb (mk6 a b c d x e)` puts the LEFT index `e`
into the RIGHT (`f`) slot, which together with `RacahProb.rowStoch`/`support`
forces `1 ≃ 0`.  So `SixJPentagon` is PROVABLY UNINHABITED for the WRONG reason (a
bug, not open physics); see `SixJPentagonRefutation.sixJPentagon_uninhabited`.

Moreover the genuine Biedenharn–Elliott pentagon is LINEAR in the SIGNED
(irrational) Wigner `{6j}` (e.g. `{1 1 1; ½ ½ ½} = −1/3`), so it is NOT
`Q'`-representable and this cubic squared field can never be corrected in place.
The A2 slot of `SubWallA` is therefore REPOINTED to the correctly-specified
`PentagonRelation.PentagonNumericCore` (the fractional associator, non-empty as a
spec via `numericShapeWitness`, physical associator OPEN, refuted for every
permutation surrogate).  This structure is kept ONLY so the refutation module has
a standalone target; it is no longer used by `SubWallA`. -/
structure SixJPentagon : Type where
  /-- The rational dim-absorbed 6j-square kernel underlying the pentagon. -/
  P : SixJRecouplingProgress.RacahProb
  /-- **The Biedenharn–Elliott pentagon** — a guarded CUBIC closure of `P`
  (nonlinear in the kernel).  LEFT UNINHABITED, never proved. -/
  pentagon : ∀ (a b c d e f : Rep) (D : Nat), a + b + c + d + e + f < D →
    (P.racahProb (mk6 a b c d e f) * P.racahProb (mk6 a b c d e f)).eqv
      (finSum (fun x =>
        P.racahProb (mk6 a b c d e x) *
          (P.racahProb (mk6 a b c d x f) * P.racahProb (mk6 a b c d x e))) D)

/-! ## 2. Sub-wall A — the loopy-geometry atoms (OPEN; (T′) coupled to (D2)). -/

/-- **`SubWallA` — the loopy-geometry sub-wall.**

  * `d2Sep`     — (D2) the `SepLattice` metric refining `z4Chain` (inhabited DATA,
                  carried only to type `tTree`);
  * `tTree`     — (T′) the spanning-tree inequality, phrased over `d2Sep.val`
                  (the (T′)/(D2) coupling made explicit) — GENUINELY OPEN;
  * `d1Mayer`   — (D1) the absolute Mayer–Ursell connecting-cluster expansion —
                  GENUINELY OPEN;
  * `a2Racah`   — (A2, Level-1) the coarse doubly-stochastic Racah 6j² surrogate,
                  carried only to discharge the coarse `Tier0FrontierC` a2 slot;
  * `a2Pentagon`— (A2, Level-2) the genuine fractional-6j associator
                  `PentagonRelation.PentagonNumericCore` (physical associator OPEN).

LEFT UNINHABITED.  The genuine open blockers are `tTree` and `d1Mayer` (and, at the
scorecard level, `subB`); `d2Sep` is inhabited DATA and `a2Racah` is an inhabited
Level-1 surrogate, while the `a2Pentagon` SPEC is inhabitable (`numericShapeWitness`
/ `SixJKernel.racahKernelCore`) yet its PHYSICAL associator stays open.  Supplying
every field as the genuine physical object WITHOUT `sorry`/`axiom` is the open
A-half. -/
structure SubWallA (p : z4Chain.toLattice.Plaquette) (w : Q') : Type 1 where
  /-- **(D2)** — the plaquette-graph `SepLattice` metric refining `z4Chain`
  (inhabited DATA, carried only to type `tTree`). -/
  d2Sep : Ursell4DProgress.SepLatticeZ4
  /-- **(T′)** — the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree
  inequality, over the (D2) lattice `d2Sep.val` (the coupled atom).  GENUINELY OPEN. -/
  tTree : Ursell4DProgress.TreeGraphBound d2Sep.val w4 gr
  /-- **(D1)** — the absolute Mayer–Ursell connecting-cluster expansion over the
  CLOSED 4D count `z4ClusterCountBound p`.  GENUINELY OPEN. -/
  d1Mayer : Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr
  /-- **(A2, Level-1 coarse)** — the doubly-stochastic Racah 6j² kernel, a
  permutation-satisfiable surrogate (`RacahInhabit.racahRP`), carried ONLY to
  discharge the coarse `Tier0FrontierC` a2 slot via `toFrontierC`.  It is NOT what
  keeps `SubWallA` open. -/
  a2Racah : SixJRecouplingProgress.RacahProb
  /-- **(A2, Level-2 genuine)** — the fractional-6j associator numeric core
  `PentagonRelation.PentagonNumericCore`, pinned to `1/4` at the smallest
  tetrahedron and refuted for every permutation surrogate.  Its minimal SPEC is
  inhabitable (`numericShapeWitness` / `SixJKernel.racahKernelCore`); the PHYSICAL
  associator (full nonlinear Biedenharn–Elliott pentagon + two-sided stochasticity)
  is the genuine OPEN obligation.  REPOINTED here from the refuted buggy
  `SixJPentagon`. -/
  a2Pentagon : PentagonRelation.PentagonNumericCore

/-! ## 3. The scorecard bundle (DELIBERATELY UNINHABITED). -/

/-- **`Tier0Scorecard` — the 6-atom (functional-continuum) frontier.**  Bundles the
PROVED fixed-spacing rubric line, Sub-wall A (four open loopy-geometry atoms), and
Sub-wall B (the single `SpectralMarginInput` carrying the three Balaban-RG open
atoms `sl.hlocalize`/`hbridge`/`hadd`).

**Minlos is NO LONGER a field (architectural deletion).**  Continuum existence is
now the FUNCTIONAL target (`Continuum.FunctionalContinuumTarget`: OS0–OS4 on the
Schwinger functional + GNS reconstruction, measure-free = the Jaffe–Witten
requirement).  The σ-additive Bochner–Minlos lift
`ContinuumScorecard.CitedMinlosLift` is thereby an OPTIONAL classical corollary
DOWNSTREAM of the functional target, NOT a frontier atom
(`FunctionalContinuumTarget.minlos_is_optional_corollary`): its dynamical content is
Sub-wall B's `DefectGapRecursion` and its correlator content is Sub-wall A's
`LoopyCorrelatorResidual`, both already counted here, and its ONLY genuinely-new
datum is the σ-additive `tightnessRate` — not an OS input.  It is dropped from this
bundle.

**No inhabitant, by design.**  Only `fixedSpacing` is proved. -/
structure Tier0Scorecard (p : z4Chain.toLattice.Plaquette) (w : Q')
    (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type 1 where
  /-- PROVED — the fixed-spacing rubric line (`ClayFixedSpacingMet`). -/
  fixedSpacing : ClayScorecard.ClayFixedSpacingMet
  /-- OPEN ×4 — Sub-wall A ((T′), (D1), (D2), pentagon). -/
  subA : SubWallA p w
  /-- OPEN ×3 — Sub-wall B (`hlocalize`, `hbridge`, `hadd`) in one input. -/
  subB : AsymptoticSpectralLoc.SpectralMarginInput b afr N₀

/-! ## 4. The PROVED fixed-spacing line (unconditional). -/

/-- **The fixed-spacing rubric line is MET (PROVED, UNCONDITIONAL).** -/
theorem fixedSpacing_met : ClayScorecard.ClayFixedSpacingMet :=
  ContinuumScorecard.fixed_spacing_met

/-! ## 5. Sub-wall A load-bearing projections (PROVED). -/

/-- **(D1) projection (PROVED).**  The off-diagonal correlator carried by the
Mayer–Ursell atom is dominated by its bridge-Ursell tail. -/
theorem subA_offCorr_decompose {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) (d : Nat) :
    F.subA.d1Mayer.offCorr d ≤
      finSum (fun m => F.subA.d1Mayer.bridgeTerm (d + m)) (F.subA.d1Mayer.tailLen d) :=
  F.subA.d1Mayer.decompose d

/-- **(T′) projection (PROVED).**  The truncated Ursell weight of a connecting
cluster is bounded by the tree-graph weight `eSurrogate^{size Y}`, over the coupled
(D2) lattice `d2Sep.val`. -/
theorem subA_tree_graph {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) (Y : Polymer F.subA.d2Sep.val.toLattice) :
    F.subA.tTree.phiT Y ≤ eSurrogate ^ (Polymer.size Y) :=
  F.subA.tTree.tree_graph Y

/-! ## 6. Sub-wall B assembled floor (PROVED — the Stage-2 three-floor collapse). -/

/-- **Sub-wall B floor, strict positivity (PROVED).**  The single
`SpectralMarginInput` fires `Stage2ConvergesToMargin.stage2_*`: the defect-gap
recursion's uniform product floor is strictly positive, with `recursion`
DISCHARGED (not assumed) via `margin_recursion_of_eigShift`. -/
theorem subB_prodFloor_pos {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) :
    (0 : Q') < (Stage2ConvergesToMargin.toDefectGapRecursion F.subB).prodFloor :=
  Stage2ConvergesToMargin.stage2_prodFloor_pos F.subB

/-- **Sub-wall B per-scale gap positivity (PROVED).**  The physical gap of the
`SpectralMarginInput`-derived defect-gap recursion is strictly positive at every
scale `k`. -/
theorem subB_physGap_pos {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) (k : Nat) :
    (0 : Q') < (Stage2ConvergesToMargin.toDefectGapRecursion F.subB).physGap k :=
  Stage2ConvergesToMargin.defectGap_physGap_pos F.subB k

/-! ## 7. Level-1 A2 slot inhabited + retained refuted-carrier domination. -/

/-- **The Level-1 A2 surrogate is inhabited (PROVED inhabitation).**
`RacahInhabit.racahRP` inhabits `RacahProb`, so the coarse Level-1 A2 surrogate
(`SubWallA.a2Racah`, consumed by `toFrontierC`) is genuinely non-empty.  This is
the permutation-satisfiable shadow; the genuine Level-2 content is the fractional
`PentagonRelation.PentagonNumericCore` (`SubWallA.a2Pentagon`), refuted for every
such permutation surrogate (`PentagonRelation.racahRP_fails_numeric`). -/
def a2_racah : SixJRecouplingProgress.RacahProb := RacahInhabit.racahRP

/-- **A2 tetrahedron amplitude nonnegative (PROVED).**  With the `racahRP` witness,
the closed 4-valent fusion loop `tetraAmp` is a concrete nonnegative `Q'`. -/
theorem a2_tetra_nonneg (D : Nat) (a b c d : Rep) :
    (0 : Q') ≤ SixJRecouplingProgress.tetraAmp RacahInhabit.racahRP D a b c d :=
  RacahInhabit.tetraAmp_racahRP_nonneg D a b c d

/-- **Atom-level domination of the REFUTED carrier (retained, NO LONGER USED).**
Every `SixJPentagon` yields a `RacahProb` by dropping its (buggy) pentagon field.
Kept only for the record; `toFrontierC` now discharges the coarse `Tier0FrontierC`
a2 slot directly from the Level-1 `SubWallA.a2Racah` surrogate, since the A2 slot
is repointed to `PentagonRelation.PentagonNumericCore` (which — being
non-stochastic, constant `1/4` — admits NO total map to `RacahProb`). -/
def pentagon_to_racah (S : SixJPentagon) : SixJRecouplingProgress.RacahProb :=
  S.P

/-! ## 8. The supersession bridge to the coarser `Tier0FrontierC`. -/

/-- **`toFrontierC` — the supersession coarsening (PROVED, TOTAL in `F`).**  A
`Tier0Scorecard` coarsens to a `Tier0FrontierCorrected.Tier0FrontierC`:

  * `fixedSpacing` transports verbatim (neither bundle carries a `minlos` field
    any longer — continuum existence is the functional target);
  * the coarse a2 slot is discharged from the scorecard's OWN Level-1 surrogate
    `F.subA.a2Racah` (the genuine `F.subA.a2Pentagon : PentagonNumericCore` is
    non-stochastic, constant `1/4`, and admits no total map to `RacahProb`, so the
    coarse slot uses the Level-1 face);
  * the coarse `a1` and `b` are consumed as EXPLICIT inputs, precisely because
    Sub-wall A refines `a1` into (T′)+(D1)+(D2) and Sub-wall B refines `b` into the
    pinned `SpectralMarginInput` — the finer enumeration does not hand back the
    coarse loopy datum / cross-ratio atom for free.

This records mechanically that `Tier0Scorecard` is the STRICTLY FINER enumeration
dominating `Tier0FrontierC` at the atom level. -/
def toFrontierC {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀)
    (a1 : PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr)
    (bcr : FiniteSMarginWorstcase.CrossRatioMonotone w) :
    Tier0FrontierCorrected.Tier0FrontierC p w where
  fixedSpacing := F.fixedSpacing
  atoms :=
    { a1 := a1
      a2 := F.subA.a2Racah
      b := bcr }

/-- The fixed-spacing half of any scorecard is the PROVED line. -/
theorem scorecard_fixedSpacing_proved {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) : ClayScorecard.ClayFixedSpacingMet :=
  F.fixedSpacing

/-! ## 9. Documentation: PROVED vs OPEN (AGENTS.md Rule 6)

PROVED here (axiom-clean):
  * `fixedSpacing_met` / `scorecard_fixedSpacing_proved` — the fixed-spacing line;
  * `subA_offCorr_decompose` / `subA_tree_graph` — the (D1)/(T′) projections;
  * `subB_prodFloor_pos` / `subB_physGap_pos` — the Stage-2 three-floor collapse
    from ONE `SpectralMarginInput` (`recursion` DISCHARGED);
  * `a2_racah` / `a2_tetra_nonneg` — the Level-1 A2 surrogate inhabited via `racahRP`;
  * `pentagon_to_racah` — a retained fact about the REFUTED buggy `SixJPentagon`;
  * `toFrontierC` — the supersession coarsening onto `Tier0FrontierC` (coarse a2
    discharged from the Level-1 `a2Racah`).

OPEN (NAMED, NO inhabitant — the sharpened frontier):
  Sub-wall A: (T′) `TreeGraphBound.tree_graph`, (D1) `BridgeDecomposition.decompose`,
              (D2) `SepLatticeZ4` (inhabited DATA), (A2)
              `PentagonRelation.PentagonNumericCore` — the fractional-6j associator
              (physical associator open; `SixJPentagon` was a refuted
              channel-mismatch bug);
  Sub-wall B: `SpectralMarginInput` = `sl.hlocalize` (per-scale) + `hbridge` +
              `hadd`.  The canonical per-mode `FrontierDAG.bulkCtrl` is now the
              finite re-based `CanonicalBulkControl`; the cross-arity bridge to
              `hlocalize` remains named-open in `FrontierDAGBridges`;
  Continuum existence: FUNCTIONAL (`Continuum.FunctionalContinuumTarget`, OS0–OS4 +
    GNS, measure-free) — the σ-additive `ContinuumScorecard.CitedMinlosLift` is an
    OPTIONAL classical corollary, NOT an atom.

  ⟹ `Tier0Scorecard`  [DELIBERATELY UNINHABITED — the open continuum Clay problem].

This is a genuine REDUCTION (a finer honest enumeration), NOT a closure.  The Clay
Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.Tier0Scorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Tier0Scorecard.fixedSpacing_met
#print axioms YMGap.Continuum.Tier0Scorecard.subA_offCorr_decompose
#print axioms YMGap.Continuum.Tier0Scorecard.subA_tree_graph
#print axioms YMGap.Continuum.Tier0Scorecard.subB_prodFloor_pos
#print axioms YMGap.Continuum.Tier0Scorecard.subB_physGap_pos
#print axioms YMGap.Continuum.Tier0Scorecard.a2_racah
#print axioms YMGap.Continuum.Tier0Scorecard.a2_tetra_nonneg
#print axioms YMGap.Continuum.Tier0Scorecard.pentagon_to_racah
#print axioms YMGap.Continuum.Tier0Scorecard.toFrontierC
#print axioms YMGap.Continuum.Tier0Scorecard.scorecard_fixedSpacing_proved
