/-
# `FrontierDAG` — the whole open Yang–Mills mass-gap frontier as ONE product node

This module bundles the canonical *open* atoms of the continuum programme into a
single deliberately-uninhabited product `structure`, together with the clean
total coarsening onto the loopy-geometry sub-wall and the recorded cross-list
identity shared with the reconstruction scorecard.

The point of the node is bookkeeping-with-teeth: it is a FAITHFUL Type-level
inventory (no `Prop := True` slots, no `sorry`, no `axiom`) whose every field is a
genuine named residual carried elsewhere in the development, and it is
DELIBERATELY UNINHABITED — its remaining open atoms (`bulkCtrl`'s finite
re-based fusion shift, `tTree`, `d1Mayer`, the `a2Pentagon` physical associator,
`edgeShift`, `trueMargin`, `boundedH`, `o4`) are open Clay-frontier residuals,
so a total inhabitant of `FrontierDAG` would close the problem.  The canonical
`coreB` field is now physically discharged on `0 <= w <= 1/2`; the separate
cross-list `CoreBBridge` below remains open.

One coarsening is PROVED here:

  * `toSubWallA` — a clean, total re-bundle onto `Tier0Scorecard.SubWallA`
    (the Bucket-1 loopy-geometry four-atom sub-wall), analogous to
    `Tier0Scorecard.toFrontierC`.

(The σ-additive Minlos measure lift is NO LONGER carried as a frontier node: the
continuum target is now stated functionally — `Continuum/FunctionalContinuumTarget`
— so `ContinuumScorecard.CitedMinlosLift` is an optional classical corollary, not a
frontier atom.  The type-level identity with the reconstruction scorecard's
`OpenContinuumMeasure` is still recorded in `FrontierDAGBridges`.)

Two honest reductions are recorded (NAMED, uninhabited — never faked):

  * `CoreBBridge` — the missing bridge lemma `FiniteSMargin w →
    CrossRatioMonotone w` that would let `coreB` plug into the coarse
    `Tier0AtomsC.b` cross-ratio atom;
  * the `charDiag` character-diagonalization node is DEMOTED (not carried as a
    field): it is dischargeable-conditionally (a proved constructor exists given
    the Schur identities), hence not an unconditional frontier atom.
-/
import YMGap.Continuum.RebasedBulkLocalizationBridge
import YMGap.Continuum.Ursell4DProgress
import YMGap.Continuum.Tier0Scorecard
import YMGap.Continuum.PentagonRelation
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
import YMGap.Continuum.FrontierCoreBPhysicalDischarge
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

Every field is a genuine, elsewhere-named continuum obligation or datum.
Uninhabited by design: its remaining open atoms (`bulkCtrl`'s bond-moved
`bulk_shift`, `tTree`, `d1Mayer`, the `a2Pentagon` physical associator,
`edgeShift`, `trueMargin`, `boundedH`, `o4`) are frontier residuals, so a total
inhabitant of `FrontierDAG` would close the mass-gap problem.  The `coreB` field
is physically inhabited on `0 <= w <= 1/2`.  The single `d2Sep` slot is
inhabited DATA (the `SepLatticeZ4` metric, needed only to *type* `tTree`); it is
NOT what keeps the product open.

Buckets:

* **Bucket 1 — a→0 gap-survival / Tier-0 cluster:** `bulkCtrl`, `d2Sep`,
  `tTree`, `d1Mayer`, `a2Racah`, `a2Pentagon`, `coreB`.
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
  /-- **The reviewed canonical bond-moved fusion control (OPEN analytic field).**

  Historical field type, preserved verbatim for Rule-9 review:

  ```text
  bulkCtrl : SpectralLocalizationCrux.SpectralLocalization w
  ```

  Its intended physical `pΓ >= 2` pin compared `fusionEig` with the bare `p=1`
  rate and is exactly refuted by
  `RebasedBulkLocalizationBridge.bareFusionShift_two_not_le`.  The replacement
  pins the actual spectrum to the SAME cutoff `N`, weight `w`, and bond-moving
  exponent `pΓ` already used by `edgeShift`; requires `1 <= N`, `0 < pΓ`, the
  physical/near-continuum windows, and an effective weight in `[0,1]`; and leaves
  only the corrected finite family `s <= 2*N` as its analytic field.  Above that
  window the fusion tail vanishes by theorem.  This is a reviewed physical
  strengthening in specificity, not an inhabitant: the genuine finite
  saddle-to-exp certificate remains OPEN for `pΓ >= 2`. -/
  bulkCtrl : RebasedBulkLocalizationBridge.CanonicalBulkControl N w pΓ
  /-- (D2) the plaquette-graph `SepLattice` metric refining `z4Chain` — inhabited
  DATA, carried only to type `tTree`. -/
  d2Sep : Ursell4DProgress.SepLatticeZ4
  /-- (T′) the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality
  over the (D2) lattice `d2Sep.val`. -/
  tTree : Ursell4DProgress.TreeGraphBound d2Sep.val w4 gr
  /-- (D1) the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED
  4D count `z4ClusterCountBound p`. -/
  d1Mayer : Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr
  /-- (A2, Level-1) the coarse doubly-stochastic Racah 6j² surrogate, carried only
  to discharge the coarse `Tier0FrontierC` a2 slot; permutation-satisfiable
  (`RacahInhabit.racahRP`). -/
  a2Racah : SixJRecouplingProgress.RacahProb
  /-- (A2, Level-2) the genuine fractional-6j associator numeric core
  `PentagonRelation.PentagonNumericCore` (physical associator OPEN).  REPOINTED
  from the refuted buggy `Tier0Scorecard.SixJPentagon`. -/
  a2Pentagon : PentagonRelation.PentagonNumericCore
  /-- (Core B) the finite-`s` central-autoconvolution theta-floor margin. -/
  coreB : AcNReserveAnalytic.FiniteSMargin w
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
sub-wall atoms `d2Sep`/`tTree`/`d1Mayer`/`a2Racah`/`a2Pentagon` are carried
verbatim, and the dependent typing (`tTree` over `d2Sep.val`) transports because
`d2Sep` is re-supplied first. -/

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
  a2Racah := F.a2Racah
  a2Pentagon := F.a2Pentagon

/-! ## 3. The Minlos node is REMOVED (functional restatement)

The σ-additive Minlos continuum-measure lift is no longer a frontier node of the
DAG: the continuum target is stated functionally
(`Continuum/FunctionalContinuumTarget`), so `ContinuumScorecard.CitedMinlosLift`
is an optional classical corollary, not a carried open atom.  The type-level
identity `CitedMinlosLift = ReconstructionScorecard.OpenContinuumMeasure` (the two
optional-measure slots are the same type) is still recorded, definitionally, in
`FrontierDAGBridges.minlos_crosslist_identity`. -/

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

/-! ## 5a. Canonical `bulkCtrl` consumer -/

/-- **The canonical field delivers the corrected physical localization output.**
Every mode that is bulk at the field's effective weight lies below the original
`s = 1` heat-kernel gap edge.  The spectrum and exponent are definitionally the
same `N`, `w`, and `pΓ` carried by the enclosing `FrontierDAG`. -/
theorem bulkCtrl_bulk_below_gapEdge
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pΓ : Nat}
    (F : FrontierDAG p w G L N pΓ) (s : Nat)
    (hbulk : BulkModeCrux.q12 <= Q'.ofNat (RGTransport.c4 s) *
      ((1 : Q') - F.bulkCtrl.weff)) :
    FusionKernelStatement.fusionEig N w pΓ s (F.bulkCtrl.denomPos s)
      <= SpectralLocalizationCrux.eigA w 1 :=
  F.bulkCtrl.bulk_below_gapEdge s hbulk

/-! ## 6. Interface non-vacuity witnesses (the DATA slots are real)

`FrontierDAG` is uninhabited as a WHOLE (its remaining open atoms include the
finite physical analytic field inside the now-repointed `bulkCtrl`, `tTree`, `d1Mayer`, the
physical `a2Pentagon`,
`edgeShift`, `trueMargin`, `boundedH`, and `o4`), but its interface is faithful
and the physical `coreB` field is now closed on the certified half interval.
These certify the product is non-vacuous as a type former (Rule: faithful +
non-vacuous statement layer), NOT that the frontier itself is closed. -/

/-- The `d2Sep` (D2) slot is genuinely inhabited DATA — the plaquette-graph
`SepLattice` metric constructed in `SepLatticeZ4Close`. -/
def d2Sep_witness : Ursell4DProgress.SepLatticeZ4 :=
  SepLatticeZ4Close.SepLatticeZ4_witness

/-- The canonical `FrontierDAG.coreB` field is physically inhabited throughout
the complete certified interval `0 <= w <= 1/2`.  This is the field itself,
not the separate forward `CoreBBridge` into the coarse cross-ratio atom. -/
def coreB_physical_witness {w : Q'}
    (hw0 : (0 : Q') <= w) (hwH : w <= FusionCoreStepRoundA.wH) :
    AcNReserveAnalytic.FiniteSMargin w :=
  FrontierCoreBPhysicalDischarge.finiteSMargin_physical hw0 hwH

/-- The repointed `bulkCtrl` interface is non-vacuous: at `pΓ = 1` the actual
fusion spectrum is the unperturbed heat-kernel spectrum and the canonical finite
carrier is inhabited.  This is NOT the genuine `pΓ >= 2` discharge. -/
def bulkCtrl_interface_witness (N : Nat) (w : Q')
    (hN : 1 <= N) (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (hnc : (1 : Q') - w <= SpectralLocalizationCrux.q112) :
    RebasedBulkLocalizationBridge.CanonicalBulkControl N w 1 :=
  RebasedBulkLocalizationBridge.canonicalBulkControl_p1 N w hN hw0 hw1 hnc

/-! ## 7. PROVED vs OPEN (AGENTS.md Rule 6)

PROVED here (axiom-clean, `[propext, Quot.sound]`):

  * `toSubWallA` — the TOTAL Bucket-1 coarsening onto `Tier0Scorecard.SubWallA`;
  * `trueMarginAtom` / `o4Atom` / `boundedHAtom` — the Bucket-2 field
    projections onto the reconstruction scorecard's OPEN abbreviations;
  * `coreBToCrossRatio` — the Core-B reduction, TOTAL in a `CoreBBridge`;
  * `coreB_physical_witness` — the actual `coreB` field throughout
    `0 <= w <= 1/2`;
  * `bulkCtrl_bulk_below_gapEdge` — the corrected canonical field consumer;
  * `d2Sep_witness` / `bulkCtrl_interface_witness` — interface non-vacuity.

The old physical `p=2` pin of `bulkCtrl` is separately kernel-refuted.  The
canonical field has now been reviewed and repointed to the exact finite re-based
fusion carrier; the finite-to-all-mode compiler and corrected bulk-to-gap
consumer are proved in `RebasedBulkLocalizationBridge`.  This statement repair
does not inhabit the remaining finite analytic field.

OPEN (deliberately uninhabited — NO inhabitant provided, never `sorry`):

  * `FrontierDAG` itself — guard-protected via its remaining open atoms
    (the finite saddle-to-exp field inside `bulkCtrl`, `tTree`, `d1Mayer`, the physical
    `a2Pentagon`,
    `edgeShift`, `trueMargin`, `boundedH`, `o4`);
  * `CoreBBridge` — the missing Core-B cross-list bridge lemma.

DEMOTED (not carried as a field): the character-diagonalization node
`CharacterDiagResolution` is dischargeable-conditionally (a proved constructor
exists given the two Schur identities), hence not an unconditional frontier atom.
-/

end YMGap.Rubric.FrontierDAG

#print axioms YMGap.Rubric.FrontierDAG.coreB_physical_witness
#print axioms YMGap.Rubric.FrontierDAG.bulkCtrl_bulk_below_gapEdge
#print axioms YMGap.Rubric.FrontierDAG.bulkCtrl_interface_witness
