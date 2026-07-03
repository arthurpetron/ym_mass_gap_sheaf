/-
# `FrontierDAG` — the whole open Yang–Mills mass-gap frontier as ONE product node

This module bundles the canonical *open* atoms of the continuum programme into a
single deliberately-uninhabited product `structure`, together with the clean
total coarsening onto the loopy-geometry sub-wall and the recorded cross-list
identity shared with the reconstruction scorecard.

The point of the node is bookkeeping-with-teeth: it is a FAITHFUL Type-level
inventory (no `Prop := True` slots, no `sorry`, no `axiom`) whose every field is a
genuine named residual carried elsewhere in the development, and it is
DELIBERATELY UNINHABITED — its `minlos` field is the guard-protected
`ClayContinuumExistence`, so a total inhabitant of `FrontierDAG` would inhabit a
Clay-frontier type and close the problem.

Two coarsenings are PROVED here:

  * `toSubWallA` — a clean, total re-bundle onto `Tier0Scorecard.SubWallA`
    (the Bucket-1 loopy-geometry four-atom sub-wall), analogous to
    `Tier0Scorecard.toFrontierC`;
  * `minlosAsContinuum` — the SHARED cross-list identity: the single `minlos`
    value serves BOTH the Tier-0 scorecard's Minlos slot AND the reconstruction
    scorecard's `OpenContinuumMeasure` slot (definitional; `CitedMinlosLift =
    ClayContinuumExistence = OpenContinuumMeasure`).

Two honest reductions are recorded (NAMED, uninhabited — never faked):

  * `CoreBBridge` — the missing bridge lemma `FiniteSMargin w →
    CrossRatioMonotone w` that would let `coreB` plug into the coarse
    `Tier0AtomsC.b` cross-ratio atom;
  * the `charDiag` character-diagonalization node is DEMOTED (not carried as a
    field): it is dischargeable-conditionally (a proved constructor exists given
    the Schur identities), hence not an unconditional frontier atom.
-/
import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.Ursell4DProgress
import YMGap.Continuum.Tier0Scorecard
import YMGap.Continuum.AcNReserveAnalytic
import YMGap.Continuum.PinnedBridgeProgress
import YMGap.Continuum.UniformCouplingFromAF
import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.O4RestorationProgress
import YMGap.Continuum.ClusterCount4DProgress
import YMGap.Continuum.Stage1LoopyReduction
import YMGap.Continuum.GenuineKP
import YMGap.Continuum.SepLatticeZ4Close
import YMGap.Continuum.FiniteSMarginWorstcase
import YMGap.Rubric.ContinuumScorecard
import YMGap.Rubric.ReconstructionScorecard

namespace YMGap.Rubric.FrontierDAG

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.GenuineKP
open YMGap.Rubric

/-! ## 1. The frontier product node (DELIBERATELY UNINHABITED) -/

/-- **`FrontierDAG` — the whole open frontier as a single product node.**

Every field is a genuine, elsewhere-named open residual of the continuum
programme.  Uninhabited by design: the `minlos` field is
`ContinuumScorecard.CitedMinlosLift = ClayContinuumExistence`, a guard-protected
Clay-frontier type; a total inhabitant of `FrontierDAG` would inhabit it and
close the mass-gap problem.  The single `d2Sep` slot is inhabited DATA (the
`SepLatticeZ4` metric, needed only to *type* `tTree`); it is NOT what keeps the
product open.

Buckets:

* **Bucket 1 — a→0 gap-survival / Tier-0 cluster:** `bulkCtrl`, `d2Sep`,
  `tTree`, `d1Mayer`, `a2Pentagon`, `coreB`.
* **Shared:** `minlos` (also appears in the reconstruction scorecard).
* **Bucket 2 — reconstruction frontier:** `edgeShift`, `trueMargin`,
  `boundedH`, `o4`.

(The character-diagonalization node `charDiag` is DEMOTED — see `CoreBBridge`'s
neighbourhood below — because it is dischargeable-conditionally and hence not an
unconditional frontier atom.) -/
structure FrontierDAG
    (p : z4Chain.toLattice.Plaquette) (w : Q')
    {D : GNSData} (G : SpectralGapData D.gnsComplete)
    (L : AdditiveTransferOperator D) (N pΓ : Nat) : Type 1 where
  -- ── BUCKET 1 : a→0 gap-survival / Tier-0 cluster ────────────────────────
  /-- The bond-moved spectral-localization certificate (open `bulk_shift`). -/
  bulkCtrl : SpectralLocalizationCrux.SpectralLocalization w
  /-- (D2) the plaquette-graph `SepLattice` metric refining `z4Chain` — inhabited
  DATA, carried only to type `tTree`. -/
  d2Sep : Ursell4DProgress.SepLatticeZ4
  /-- (T′) the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality
  over the (D2) lattice `d2Sep.val`. -/
  tTree : Ursell4DProgress.TreeGraphBound d2Sep.val w4 gr
  /-- (D1) the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED
  4D count `z4ClusterCountBound p`. -/
  d1Mayer : Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr
  /-- (A2) the nonlinear 6j Biedenharn–Elliott pentagon residual. -/
  a2Pentagon : Tier0Scorecard.SixJPentagon
  /-- (Core B) the finite-`s` central-autoconvolution theta-floor margin. -/
  coreB : AcNReserveAnalytic.FiniteSMargin w
  -- ── SHARED cross-list node ──────────────────────────────────────────────
  /-- The cited-classical Minlos σ-additive continuum-measure lift.  THE
  guard-protected field: `= ClayContinuumExistence`. -/
  minlos : ContinuumScorecard.CitedMinlosLift
  -- ── BUCKET 2 : reconstruction frontier ──────────────────────────────────
  /-- The pinned edge-shift residual (`hId`/`hLin`; open `bulk_shift` per scale). -/
  edgeShift : PinnedBridgeProgress.EdgeShiftResidual N pΓ
  /-- The genuine dimensionless physical margin recursion `Δ_k = m_lat(a_k)/a_k`. -/
  trueMargin : UniformCouplingFromAF.TrueMarginRecursion
  /-- Residual B — the bounded self-adjoint additive Hamiltonian with `e^{−H}=T`. -/
  boundedH : BoundedFunctionalCalculusResidual G L
  /-- The physical `O(4)` isotropization running (`betaDrop`-sign / anisotropy). -/
  o4 : O4RestorationProgress.CouplingRunning

/-! ## 2. Bucket-1 coarsening — TOTAL, PROVED (à la `Tier0Scorecard.toFrontierC`)

A pure field re-bundle onto the loopy-geometry sub-wall.  Clean and total: the
four sub-wall atoms `d2Sep`/`tTree`/`d1Mayer`/`a2Pentagon` are carried verbatim,
and the dependent typing (`tTree` over `d2Sep.val`) transports because `d2Sep` is
re-supplied first. -/

/-- **`toSubWallA` — the clean Bucket-1 coarsening (PROVED, TOTAL).**  A
`FrontierDAG` coarsens to the four-atom loopy-geometry sub-wall
`Tier0Scorecard.SubWallA p w`.  (It CANNOT total-map to the full
`Tier0Scorecard`, which additionally needs a `SpectralMarginInput` Sub-wall B and
the separately-proved fixed-spacing line — data `FrontierDAG` does not carry.) -/
def toSubWallA
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG p w G L N pΓ) : Tier0Scorecard.SubWallA p w where
  d2Sep := F.d2Sep
  tTree := F.tTree
  d1Mayer := F.d1Mayer
  a2Pentagon := F.a2Pentagon

/-! ## 3. The SHARED cross-list identity — TOTAL, PROVED (definitional)

`ContinuumScorecard.CitedMinlosLift = ClayContinuumExistence =
ReconstructionScorecard.OpenContinuumMeasure`.  A single `minlos` value is the
canonical node that appears in BOTH the Tier-0 scorecard and the reconstruction
scorecard; no bridge proof is needed, only the recorded definitional identity. -/

/-- **`minlosAsContinuum` — the shared-node identity (PROVED, definitional).**
The `minlos` field of a `FrontierDAG` is, verbatim, the reconstruction
scorecard's `OpenContinuumMeasure` slot. -/
def minlosAsContinuum
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG p w G L N pΓ) :
    ReconstructionScorecard.OpenContinuumMeasure :=
  F.minlos

/-! ## 4. Bucket-2 field projections (TOTAL, PROVED)

The three parameter-free reconstruction atoms carried by `FrontierDAG` project to
the reconstruction scorecard's OPEN abbreviations verbatim (definitional).  A
TOTAL map to `FullReconstructionTarget` is NOT possible — that structure also
requires a proved line and the two Schur identities, which `FrontierDAG` does not
carry — so we expose the atoms individually instead. -/

/-- The `trueMargin` field IS the reconstruction scorecard's `OpenTrueMargin`. -/
def trueMarginAtom
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG p w G L N pΓ) :
    ReconstructionScorecard.OpenTrueMargin :=
  F.trueMargin

/-- The `o4` field IS the reconstruction scorecard's `OpenO4PhysicalRunning`. -/
def o4Atom
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG p w G L N pΓ) :
    ReconstructionScorecard.OpenO4PhysicalRunning :=
  F.o4

/-- The `boundedH` field IS the reconstruction scorecard's
`OpenBoundedHamiltonian G L`. -/
def boundedHAtom
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG p w G L N pΓ) :
    ReconstructionScorecard.OpenBoundedHamiltonian G L :=
  F.boundedH

/-! ## 5. Honest NAMED residual — the `coreB` cross-list bridge

`coreB : FiniteSMargin w` and the coarse `Tier0AtomsC.b : CrossRatioMonotone w`
are two faces of the same "Core B / s = 1 spectral margin", but a bridge lemma is
NEEDED before `coreB` plugs into `Tier0AtomsC.b`.  We NAME it as a Type-level
residual and do NOT inhabit it (Rule 8: named-open, never `sorry`). -/

/-- **`CoreBBridge w` — the missing Core-B cross-list bridge (NAMED-OPEN).**  A
function turning the analytic finite-`s` theta-floor margin into the cross-ratio
monotonicity atom.  Left UNINHABITED here; supplying it (without `sorry`) is what
would let a `FrontierDAG.coreB` discharge the coarse `Tier0AtomsC.b` atom. -/
abbrev CoreBBridge (w : Q') : Type :=
  AcNReserveAnalytic.FiniteSMargin w → FiniteSMarginWorstcase.CrossRatioMonotone w

/-- **Bridge consumer (PROVED, TOTAL in its inputs).**  GIVEN a `CoreBBridge`,
the `coreB` field of a `FrontierDAG` yields the coarse cross-ratio atom.  This
records exactly the reduction: `coreB` closes `Tier0AtomsC.b` IFF `CoreBBridge`
is inhabited (which this module does not do). -/
def coreBToCrossRatio
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (br : CoreBBridge w) (F : FrontierDAG p w G L N pΓ) :
    FiniteSMarginWorstcase.CrossRatioMonotone w :=
  br F.coreB

/-! ## 6. Interface non-vacuity witnesses (the DATA slots are real)

`FrontierDAG` is uninhabited as a WHOLE (its `minlos` field is guard-protected),
but its interface is faithful: the data-carrying slots have genuine witnesses.
These certify the product is non-vacuous as a type former (Rule: faithful +
non-vacuous statement layer), NOT that the frontier itself is closed. -/

/-- The `d2Sep` (D2) slot is genuinely inhabited DATA — the plaquette-graph
`SepLattice` metric constructed in `SepLatticeZ4Close`. -/
def d2Sep_witness : Ursell4DProgress.SepLatticeZ4 :=
  SepLatticeZ4Close.SepLatticeZ4_witness

/-- The `bulkCtrl` slot's interface is non-vacuous: the UNPERTURBED spectrum is a
`SpectralLocalization` on any near-continuum weight (this is NOT the bond-moved
certificate; it only certifies the interface is real). -/
def bulkCtrl_interface_witness (w : Q')
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112) :
    SpectralLocalizationCrux.SpectralLocalization w :=
  SpectralLocalizationCrux.trivialLocalization w hnc

/-! ## 7. PROVED vs OPEN (AGENTS.md Rule 6)

PROVED here (axiom-clean, `[propext, Quot.sound]`):

  * `toSubWallA` — the TOTAL Bucket-1 coarsening onto `Tier0Scorecard.SubWallA`;
  * `minlosAsContinuum` — the shared Tier-0 ↔ reconstruction Minlos identity;
  * `trueMarginAtom` / `o4Atom` / `boundedHAtom` — the Bucket-2 field
    projections onto the reconstruction scorecard's OPEN abbreviations;
  * `coreBToCrossRatio` — the Core-B reduction, TOTAL in a `CoreBBridge`;
  * `d2Sep_witness` / `bulkCtrl_interface_witness` — interface non-vacuity.

OPEN (deliberately uninhabited — NO inhabitant provided, never `sorry`):

  * `FrontierDAG` itself — guard-protected via `minlos = ClayContinuumExistence`;
  * `CoreBBridge` — the missing Core-B cross-list bridge lemma.

DEMOTED (not carried as a field): the character-diagonalization node
`CharacterDiagResolution` is dischargeable-conditionally (a proved constructor
exists given the two Schur identities), hence not an unconditional frontier atom.
-/

end YMGap.Rubric.FrontierDAG
