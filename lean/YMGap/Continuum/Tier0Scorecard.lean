/-
The **Tier-0 scorecard** — the sharpened a→0 gap-survival frontier as a
machine-checked **6-atom + orthogonal-Minlos** enumeration.  Supersedes the
3-atom `Tier0FrontierCorrected.Tier0FrontierC` by REFINING its single loopy atom
`a1` into three geometry atoms (T′)+(D1)+(D2), keeping the closed-fusion 6j atom
as the genuinely-nonlinear `SixJPentagon` residual, and refining its Core-B atom
`b` into the pinned `SpectralMarginInput` (three Balaban-RG sub-atoms).

# The picture recorded (read first)

  Sub-wall A (loopy geometry) — 4 OPEN atoms
    (T′)  `Ursell4DProgress.TreeGraphBound.tree_graph`  — spanning-tree inequality
    (D1)  `Ursell4DProgress.BridgeDecomposition.decompose` — Mayer–Ursell expansion
    (D2)  `Ursell4DProgress.SepLatticeZ4`  — the plaquette metric refining `z4Chain`
    (A2)  `SixJPentagon`  — the Biedenharn–Elliott pentagon, NONLINEAR in the kernel

  Sub-wall B (Balaban RG) — 3 OPEN atoms, all inside ONE
    `AsymptoticSpectralLoc.SpectralMarginInput b afr N₀`
      · `sl.hlocalize` = Core B (the p≥2 SU(2)-fusion local-CLT)
      · `hbridge`      = the pinned trajectory-shift control (`g_k ≠ 1`)
      · `hadd`         = the located-2nd-eigenvalue ↔ physical-margin dictionary

  Orthogonal — `ContinuumScorecard.CitedMinlosLift` (= `ClayContinuumExistence`).

# What is PROVED here (each `#print axioms`-gated, permitted `propext`/`Quot.sound`)

  * `fixedSpacing_met` — the entire fixed-spacing rubric line, UNCONDITIONAL
    (`ContinuumScorecard.fixed_spacing_met`).
  * `subA_offCorr_decompose` / `subA_tree_graph` — the load-bearing (D1)/(T′)
    projections of Sub-wall A.
  * `subB_prodFloor_pos` / `subB_physGap_pos` — the assembled Stage-2 floor
    (the three-floor collapse `Stage2ConvergesToMargin.stage2_*` fired from the
    single `SpectralMarginInput`, `recursion` DISCHARGED not assumed).
  * `a2_racah` / `a2_tetra_nonneg` — the A2 vacuity is CLOSED: `RacahInhabit.racahRP`
    inhabits `RacahProb`, so the coarse a2 slot is genuinely non-empty and the
    tetrahedron amplitude is concretely nonnegative.
  * `pentagon_to_racah` — the atom-level DOMINATION: every `SixJPentagon` carries a
    `RacahProb` (drop the pentagon), so the finer A2 atom refines the coarse one.
  * `toFrontierC` — the supersession bridge: a `Tier0Scorecard` coarsens to a
    `Tier0FrontierCorrected.Tier0FrontierC`, discharging its a2 slot from the
    scorecard's OWN pentagon kernel.  It consumes the coarse `a1`/`b` as explicit
    inputs precisely BECAUSE Sub-wall A refines `a1` into (T′)+(D1)+(D2) and
    Sub-wall B refines `b` into the pinned `SpectralMarginInput` — the finer
    enumeration does not hand back the coarse atoms for free.  This records the
    strict refinement mechanically.

# DELIBERATELY UNINHABITED bundle

`Tier0Scorecard` has NO inhabitant, by design (mirrors `Tier0FrontierC` /
`ClayTarget` / `ContinuumScorecard.ContinuumTargetReduction`).  Only `fixedSpacing`
is proved; supplying `subA` (four open atoms), `subB` (three open atoms), and
`minlos` WITHOUT `sorry`/`axiom` is the open continuum Clay problem.

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

/-! ## 1. The ONE genuinely-new Type: the 6j pentagon residual (A2). -/

/-- **`SixJPentagon` (NEW — the genuine A2 residual).**  Carries a rational Racah
kernel `P : RacahProb` (dim-absorbed `(2e+1)(2f+1)·{6j}²`) that ADDITIONALLY closes
a Biedenharn–Elliott-type pentagon relation — a CUBIC (nonlinear-in-the-kernel)
identity, guarded by a largeness bound `< D` to avoid the `D = 0` truncation
degeneracy that killed the buggy `SixJRecoupling`.

This is strictly stronger than `RacahProb`: the doubly-stochastic
`RacahInhabit.racahRP` permutation surrogate inhabits `RacahProb` but is a 0/1
matrix and does NOT close the cubic pentagon, so it does NOT lift to a
`SixJPentagon`.  The faithful fractional Wigner-6j is what closes the pentagon, and
extracting it from the squared kernel `P` is nonlinear — hence this is LEFT
UNINHABITED, never proved.  (The wiring below is the pentagon's structural shape —
a two-kernel product equal to an internal sum of three-kernel products — carrying
the genuine nonlinearity, not an assertion of the textbook index assignment.) -/
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

/-! ## 2. Sub-wall A — the four loopy-geometry atoms (all OPEN; (T′) coupled to (D2)). -/

/-- **`SubWallA` — the loopy-geometry sub-wall (4 OPEN atoms).**

  * `d2Sep`     — (D2) the `SepLattice` metric refining `z4Chain`;
  * `tTree`     — (T′) the spanning-tree inequality, phrased over `d2Sep.val`
                  (the (T′)/(D2) coupling made explicit);
  * `d1Mayer`   — (D1) the absolute Mayer–Ursell connecting-cluster expansion;
  * `a2Pentagon`— (A2) the nonlinear 6j pentagon residual.

LEFT UNINHABITED — supplying all four WITHOUT `sorry`/`axiom` is the open A-half. -/
structure SubWallA (p : z4Chain.toLattice.Plaquette) (w : Q') : Type 1 where
  /-- **(D2)** — the plaquette-graph `SepLattice` metric refining `z4Chain`. -/
  d2Sep : Ursell4DProgress.SepLatticeZ4
  /-- **(T′)** — the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree
  inequality, over the (D2) lattice `d2Sep.val` (the coupled atom). -/
  tTree : Ursell4DProgress.TreeGraphBound d2Sep.val w4 gr
  /-- **(D1)** — the absolute Mayer–Ursell connecting-cluster expansion over the
  CLOSED 4D count `z4ClusterCountBound p`. -/
  d1Mayer : Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr
  /-- **(A2)** — the nonlinear 6j Biedenharn–Elliott pentagon residual. -/
  a2Pentagon : SixJPentagon

/-! ## 3. The scorecard bundle (DELIBERATELY UNINHABITED). -/

/-- **`Tier0Scorecard` — the 6-atom + orthogonal-Minlos frontier.**  Bundles the
PROVED fixed-spacing rubric line, Sub-wall A (four open loopy-geometry atoms),
Sub-wall B (the single `SpectralMarginInput` carrying the three Balaban-RG open
atoms `sl.hlocalize`/`hbridge`/`hadd`), and the orthogonal cited-classical Minlos
lift.

**No inhabitant, by design.**  Only `fixedSpacing` is proved. -/
structure Tier0Scorecard (p : z4Chain.toLattice.Plaquette) (w : Q')
    (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type 1 where
  /-- PROVED — the fixed-spacing rubric line (`ClayFixedSpacingMet`). -/
  fixedSpacing : ClayScorecard.ClayFixedSpacingMet
  /-- OPEN ×4 — Sub-wall A ((T′), (D1), (D2), pentagon). -/
  subA : SubWallA p w
  /-- OPEN ×3 — Sub-wall B (`hlocalize`, `hbridge`, `hadd`) in one input. -/
  subB : AsymptoticSpectralLoc.SpectralMarginInput b afr N₀
  /-- OPEN (ORTHOGONAL) — the cited-classical Minlos σ-additive measure lift. -/
  minlos : ContinuumScorecard.CitedMinlosLift

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

/-! ## 7. A2 vacuity CLOSED + atom-level domination. -/

/-- **A2 vacuity CLOSED (PROVED inhabitation).**  `RacahInhabit.racahRP` inhabits
`RacahProb`, so the coarse A2 slot is genuinely non-empty (the buggy
`SixJRecoupling` was provably empty; this is not).  The pentagon of `SixJPentagon`
is the genuinely-stronger residual on TOP of this inhabited base. -/
def a2_racah : SixJRecouplingProgress.RacahProb := RacahInhabit.racahRP

/-- **A2 tetrahedron amplitude nonnegative (PROVED).**  With the `racahRP` witness,
the closed 4-valent fusion loop `tetraAmp` is a concrete nonnegative `Q'`. -/
theorem a2_tetra_nonneg (D : Nat) (a b c d : Rep) :
    (0 : Q') ≤ SixJRecouplingProgress.tetraAmp RacahInhabit.racahRP D a b c d :=
  RacahInhabit.tetraAmp_racahRP_nonneg D a b c d

/-- **Atom-level DOMINATION (PROVED).**  Every `SixJPentagon` yields a `RacahProb`
by dropping the pentagon — so the finer A2 atom refines (mechanically dominates)
the coarse `Tier0FrontierC` A2 atom `RacahProb`. -/
def pentagon_to_racah (S : SixJPentagon) : SixJRecouplingProgress.RacahProb :=
  S.P

/-! ## 8. The supersession bridge to the coarser `Tier0FrontierC`. -/

/-- **`toFrontierC` — the supersession coarsening (PROVED, TOTAL in `F`).**  A
`Tier0Scorecard` coarsens to a `Tier0FrontierCorrected.Tier0FrontierC`:

  * `fixedSpacing` / `minlos` transport verbatim;
  * the coarse a2 slot is discharged from the scorecard's OWN pentagon kernel
    (`F.subA.a2Pentagon.P`, via `pentagon_to_racah`);
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
      a2 := pentagon_to_racah F.subA.a2Pentagon
      b := bcr }
  minlos := F.minlos

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
  * `a2_racah` / `a2_tetra_nonneg` — A2 vacuity CLOSED via `racahRP`;
  * `pentagon_to_racah` — atom-level domination of the coarse A2 atom;
  * `toFrontierC` — the supersession coarsening onto `Tier0FrontierC`.

OPEN (NAMED, NO inhabitant — the sharpened 6-atom + orthogonal frontier):
  Sub-wall A: (T′) `TreeGraphBound.tree_graph`, (D1) `BridgeDecomposition.decompose`,
              (D2) `SepLatticeZ4`, (A2) `SixJPentagon` (nonlinear pentagon);
  Sub-wall B: `SpectralMarginInput` = `sl.hlocalize` (Core B) + `hbridge` + `hadd`;
  Orthogonal: `ContinuumScorecard.CitedMinlosLift`.

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
