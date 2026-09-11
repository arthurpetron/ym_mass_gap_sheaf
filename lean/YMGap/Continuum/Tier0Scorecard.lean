/-
The historical Tier-0 surrogate census.

This file preserves an earlier decomposition of a functional-continuum route
into `SubWallA` and `SpectralMarginInput`.  It is useful dependency bookkeeping,
but it is not an exact or exhaustive atomization of the Clay frontier.

In `SubWallA`, `tTree` and `d1Mayer` carry substantive loopy-geometry estimates.
By contrast, `d2Sep : SepLatticeZ4` is inhabited metric data, not an open
mathematical theorem.  The Level-1 `a2Racah` surrogate is also inhabited, and
`a2Pentagon : PentagonNumericCore` carries only the minimal numeric shape already
inhabited by `numericShapeWitness`; it is not a formalization of the physical
signed Biedenharn--Elliott associator.  The old `SixJPentagon` carrier is retained
solely to document its channel-mismatch refutation.

`SpectralMarginInput` packages a separate historical RG/localization route.  The
projection theorems below are conditional on a supplied scorecard; they do not
construct that input or identify its scalar `physGap` with the spectral edge of
a canonical continuum Hamiltonian.  Likewise, `fixedSpacing_met` imports the
legacy finite/scalar scorecard, not a physical fixed-spacing Yang--Mills theorem.

The ordinary-GNS `FunctionalContinuumTarget` associated with this older route is
not the reflected positive-time OS reconstruction.  The current canonical path
also requires a pinned global group/action, a genuine two-parameter Schwinger
limit, reflected carrier, full continuous-time semigroup, generator, and
physical spectral and interaction pins.  A sigma-additive Minlos lift is an
optional downstream corollary, not a substitute for those data.

No `Tier0Scorecard` term is constructed here.  This should be read only as the
status of the fields encoded by this legacy bundle: its uninhabited status is
not an exact proof that a fixed number of independent Clay obligations remains.

Mathlib-free; pure `Q'` / `Nat`; no `Classical.*`, `Real`, `native_decide`,
`by_contra`, `sorry`, `admit`, or new axiom.  Clay Yang--Mills mass gap remains
open.
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
The A2 slot of `SubWallA` is therefore repointed to
`PentagonRelation.PentagonNumericCore`, a minimal numeric-shape specification
inhabited by `numericShapeWitness`.  That specification is not the physical
signed associator.  This structure is kept only so the refutation module has a
standalone target; it is no longer used by `SubWallA`. -/
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

/-! ## 2. Sub-wall A — historical loopy-geometry fields -/

/-- **`SubWallA` — the loopy-geometry sub-wall.**

  * `d2Sep`     — (D2) the `SepLattice` metric refining `z4Chain` (inhabited DATA,
                  carried only to type `tTree`);
  * `tTree`     — (T′) the spanning-tree inequality, phrased over `d2Sep.val`
                  (the (T′)/(D2) coupling made explicit) — GENUINELY OPEN;
  * `d1Mayer`   — (D1) the absolute Mayer–Ursell connecting-cluster expansion —
                  GENUINELY OPEN;
  * `a2Racah`   — (A2, Level-1) the coarse doubly-stochastic Racah 6j² surrogate,
                  carried only to discharge the coarse `Tier0FrontierC` a2 slot;
  * `a2Pentagon`— (A2, Level-2) the inhabited minimal numeric-shape structure
                  `PentagonRelation.PentagonNumericCore`, not the physical
                  fractional-6j associator.

No term is constructed here.  Within this structure, the substantive unsupplied
estimates are `tTree` and `d1Mayer`; `d2Sep`, `a2Racah`, and the minimal
`a2Pentagon` specification have inhabitants.  The physical associator remains a
separate unformalized obligation rather than a field discharged by this bundle. -/
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
  /-- **(A2, Level-2 numeric shape)** — a minimal fractional-6j numeric core
  `PentagonRelation.PentagonNumericCore`, pinned to `1/4` at the smallest
  tetrahedron and refuted for every permutation surrogate.  Its minimal SPEC is
  inhabitable (`numericShapeWitness` / `SixJKernel.racahKernelCore`); the PHYSICAL
  associator (full signed Biedenharn–Elliott identity and its analytic role) is
  not encoded by this field.  Repointed here from the refuted buggy
  `SixJPentagon`. -/
  a2Pentagon : PentagonRelation.PentagonNumericCore

/-! ## 3. The legacy scorecard bundle -/

/-- **`Tier0Scorecard` — a historical functional-continuum census.**  Bundles the
proved fixed-spacing surrogate line, `SubWallA`, and one `SpectralMarginInput`.
The field grouping is useful for this reduction route but is neither an exact
count of independent open obligations nor an exhaustive Clay frontier.

**Minlos is NO LONGER a field (architectural deletion).**  This historical
frontier uses `Continuum.FunctionalContinuumTarget`: its OS0--OS4 predicates on
a Schwinger functional plus ordinary GNS data.  It is a legacy surrogate, not
the standard reflected positive-time Jaffe--Wightman reconstruction.  The
sigma-additive Bochner--Minlos lift
`ContinuumScorecard.CitedMinlosLift` is thereby an OPTIONAL classical corollary
DOWNSTREAM of the functional target, NOT a frontier atom
(`FunctionalContinuumTarget.minlos_is_optional_corollary`): its dynamical content is
Sub-wall B's `DefectGapRecursion` and its correlator content is Sub-wall A's
`LoopyCorrelatorResidual`, both already counted here, and its ONLY genuinely-new
datum is the σ-additive `tightnessRate` — not an OS input.  It is dropped from this
bundle.

No inhabitant is constructed in this file.  That fact records the status of this
particular bundle only. -/
structure Tier0Scorecard (p : z4Chain.toLattice.Plaquette) (w : Q')
    (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type 1 where
  /-- PROVED — the legacy fixed-spacing surrogate conjunction. -/
  fixedSpacing : ClayScorecard.ClayFixedSpacingMet
  /-- Historical Sub-wall A; `d2Sep` and both A2 shape slots are inhabitable. -/
  subA : SubWallA p w
  /-- Historical Sub-wall B package (`hlocalize`, `hbridge`, `hadd`). -/
  subB : AsymptoticSpectralLoc.SpectralMarginInput b afr N₀

/-! ## 4. The proved fixed-spacing surrogate line -/

/-- **The legacy fixed-spacing surrogate conjunction is proved.** -/
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

/-- **Sub-wall B per-scale scalar positivity (PROVED conditionally on `F`).**
The field named `physGap` in the `SpectralMarginInput`-derived recursion is
strictly positive at every scale.  This theorem does not identify that scalar
with a canonical Hamiltonian spectral gap. -/
theorem subB_physGap_pos {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) (k : Nat) :
    (0 : Q') < (Stage2ConvergesToMargin.toDefectGapRecursion F.subB).physGap k :=
  Stage2ConvergesToMargin.defectGap_physGap_pos F.subB k

/-! ## 7. Level-1 A2 slot inhabited + retained refuted-carrier domination. -/

/-- **The Level-1 A2 surrogate is inhabited (PROVED inhabitation).**
`RacahInhabit.racahRP` inhabits `RacahProb`, so the coarse Level-1 A2 surrogate
(`SubWallA.a2Racah`, consumed by `toFrontierC`) is genuinely non-empty.  The
separate Level-2 field `PentagonRelation.PentagonNumericCore` is only an inhabited
numeric-shape specification; `PentagonRelation.racahRP_fails_numeric` shows that
this particular permutation surrogate does not meet that shape.  Neither field
is the physical signed associator. -/
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

/-! ## 8. Compatibility projection to the older `Tier0FrontierC` -/

/-- **`toFrontierC` — a compatibility projection (PROVED, TOTAL in `F`).**  A
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

This records a total map after the two older coarse inputs are supplied.  It does
not establish that either bundle is an exact frontier, nor that the displayed
fields are independent physical atoms. -/
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

/-- The fixed-spacing field of any supplied scorecard is the proved legacy
surrogate conjunction. -/
theorem scorecard_fixedSpacing_proved {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (F : Tier0Scorecard p w b afr N₀) : ClayScorecard.ClayFixedSpacingMet :=
  F.fixedSpacing

/-! ## 9. Documentation: proved projections and unsupplied legacy packages

PROVED here (axiom-clean):
  * `fixedSpacing_met` / `scorecard_fixedSpacing_proved` — the legacy
    fixed-spacing surrogate conjunction;
  * `subA_offCorr_decompose` / `subA_tree_graph` — projections from a supplied
    (D1)/(T′) package;
  * `subB_prodFloor_pos` / `subB_physGap_pos` — the Stage-2 three-floor collapse
    conditional on a supplied `SpectralMarginInput`;
  * `a2_racah` / `a2_tetra_nonneg` — the Level-1 A2 surrogate inhabited via `racahRP`;
  * `pentagon_to_racah` — a retained fact about the REFUTED buggy `SixJPentagon`;
  * `toFrontierC` — a compatibility map onto `Tier0FrontierC` (coarse a2
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

  ⟹ no `Tier0Scorecard` constructor is supplied here.  This is not equivalent to
     an exact census of the open continuum Clay problem.

This module preserves a useful historical reduction interface, not a closure and
not an exhaustive frontier.  The Clay Yang--Mills mass gap remains open. -/

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
