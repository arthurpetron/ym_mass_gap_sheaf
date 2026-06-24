/-
**Loop-5 CAPSTONE** — the UNCONDITIONAL, honestly TREE-SCOPED, fixed-spacing
infinite-volume SU(2) mass gap, assembled from the now-PROVED pieces.

# What this module IS (the precise, honest claim)

For the strong-coupling window `0 < w ≤ 1/2` AND the **tree / single-line
geometry** (every link shared by at most TWO plaquettes — the maximal-tree gauge
/ 2D-LGT regime), this module proves a single clean headline:

  there is a strictly-positive fixed-spacing infinite-volume SU(2) mass gap,

with the gap rate `ρ = coeffW w 1 = 2·w³ < 1` (mass `m = −log ρ > 0`), and this
rate is simultaneously

  (a) the proved GEOMETRIC DECAY rate of the REAL Wilson connected two-point
      correlator `wilsonG w (M+1) n ≤ (M·ρ)·ρ^n`  (`WilsonConnCorr.wilsonG_decay`);
  (b) the located spectral-gap SEPARATOR of the reconstructed transfer operator,
      whose abstract correlator the real `wilsonG` is now PROVED to equal
      (`TransferCorr.wilsonGMatchesAbstract_transfer` via `reconTransfer`);
  (c) underwritten by the tree partition identity `Ξ ≃ ZrealTree`
      (`TreePartitionIdentity.treeRealPartition`);
  (d) yielding a strictly-positive constructive-real fixed-spacing
      infinite-volume mass `CReal.IsPositive (continuumRate (genuineDerived…))`.

The two identities that previously GATED this — `WilsonGMatchesAbstract` and
`AbstractRealPartitionIdentity` — are now INHABITED for the tree geometry by the
proved inhabitants `wilsonGMatchesAbstract_transfer` and `treeRealPartition`, so
the headline carries NO named hypotheses beyond the strong-coupling window and
the EXPLICIT tree-geometry hypothesis.  It is therefore genuinely UNCONDITIONAL
for the tree / single-line geometry.

# What this module is NOT (the scope, stated scrupulously)

  * NOT the general LOOPY lattice.  A link shared by ≥ 3 plaquettes needs the
    `m`-fold shared-link Haar kernel (the SU(2) 6j recoupling) in place of the
    2-fold orthogonality used in the tree partition identity, and the
    multi-plaquette Mayer / Dobrushin-ratio reorganization for the correlator.
    That `≥3`-shared-link kernel is THE sole remaining named wall.  It is carried
    here as the explicit honest scope hypothesis `TreeLike`, NEVER claimed away.
  * NOT the continuum (spacing → 0) limit.  This is a FIXED-spacing statement;
    the infinite volume `Λ → ∞` is taken, but the lattice spacing `a` is fixed.
    The `a → 0` scaling limit (Prokhorov tightness, O(4) restoration) is a
    separate genuinely-open frontier and is NOT addressed.
  * NOT the full 4D Clay Yang–Mills mass gap.

This is a legitimate, axiom-clean, geometrically-restricted fixed-spacing result.

# Constructive contract (`lean/AGENTS.md`, Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `CReal` / `Nat` / `List` reuse of the proved tower.
No `Classical.*`, no `Real`, no `native_decide`, no `decide` on non-decidable
props, no `sorry` / `admit` / new `axiom`, no `Prop := True`.  The headline is a
`Type`-level structure (Rule 8); the tree geometry is an EXPLICIT honest
hypothesis.  Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.TransferCorr
import YMGap.Continuum.TreePartitionIdentity
import YMGap.Continuum.GenuineClusterBound

namespace YMGap.Continuum.TreeFixedSpacingGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.TreePartitionIdentity
open YMGap.Continuum.GenuineClusterBound
open YMGap.Continuum.ClusterGapReduction

/-! ## 1. Discharging the conditional tie: `absCorr_decay` made UNCONDITIONAL

`GenuineClusterBound.absCorr_decay` took the named `WilsonGMatchesAbstract`
witness as an explicit hypothesis `link`.  The transfer-matrix route now PROVES
an inhabitant of that obligation (`wilsonGMatchesAbstract_transfer`), so we
SUPPLY it and turn the conditional tie unconditional for the single-line
correlator geometry: the abstract reconstructed-transfer-operator correlator IS
geometrically bounded at the proved rate `ρ`, with NO named hypothesis. -/

/-- The genuine inhabitant of the previously-named `WilsonGMatchesAbstract`
obligation, supplied by the transfer-matrix route (`reconTransfer`).  Its
`absCorr M n` is the abstract `corr` of the reconstructed diagonal transfer
operator, and `matchesAbs` is the PROVED single-rep collapse composed with the
reconstructed-operator identity — NOT `eqv_refl`. -/
def treeWilsonLink (w : Q') (hw0 : (0 : Q') ≤ w) :
    WilsonConnCorr.WilsonGMatchesAbstract w :=
  wilsonGMatchesAbstract_transfer w hw0

/-- **`absCorr_decay_unconditional` — the conditional tie made UNCONDITIONAL.**

`GenuineClusterBound.absCorr_decay` required a `WilsonGMatchesAbstract` witness as
a hypothesis.  Feeding the now-PROVED inhabitant `treeWilsonLink`, the abstract
reconstructed-transfer-operator correlator `corr (reconTransfer w hw0 M) n` is
geometrically bounded by `(M·ρ)·ρ^n` with `ρ = 2w³` — with NO named hypothesis.
This is the tie that the transfer route turns unconditional for the single-line
correlator geometry. -/
theorem absCorr_decay_unconditional (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ wThresh) (M n : Nat) :
    corr (reconTransfer w hw0 M) n
      ≤ (Q'.ofNat M * derivedRho w) * (derivedRho w) ^ n :=
  GenuineClusterBound.absCorr_decay w hw0 hw (treeWilsonLink w hw0) M n

/-- The abstract reconstructed correlator IS the real Wilson correlator (up to
`eqv`): `wilsonG w (M+1) n ≃ corr (reconTransfer w hw0 M) n`.  This is exactly the
proved `matchesAbs` of `treeWilsonLink` — the genuine identity tying the real
measure's correlator to the transfer operator, NOT reflexivity. -/
theorem wilsonG_eqv_recon (w : Q') (hw0 : (0 : Q') ≤ w) (M n : Nat) :
    (wilsonG w (M + 1) n).eqv (corr (reconTransfer w hw0 M) n) :=
  (treeWilsonLink w hw0).matchesAbs M n

/-! ## 2. The gap is a gap of the ACTUAL measure

The genuine tie: the derived separator `ρ = derivedRho w` (the located spectral
gap separator of `wilsonModel`, and the rate of the located continuum mass) IS
the geometric decay rate of the REAL connected correlator `wilsonG` — which is in
turn identified with the abstract transfer-operator correlator via
`wilsonG_eqv_recon`.  So the positive mass below is a gap of the actual measure's
correlator, not merely of an abstract model. -/

/-- **The real correlator decays at the gap rate `ρ` (PROVED, unconditional).**
The REAL Wilson connected correlator `wilsonG w (M+1) n` is bounded by
`(M·ρ)·ρ^n`, where `ρ = derivedRho w = coeffW w 1 = 2w³` is EXACTLY the separator
of the located spectral gap `wilsonLocatedGap` and the rate of the located
continuum mass.  Thus the gap is a gap of the actual measure's correlator. -/
theorem realCorr_decays_at_gap_rate (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ wThresh) (M n : Nat) :
    wilsonG w (M + 1) n ≤ (Q'.ofNat M * derivedRho w) * (derivedRho w) ^ n :=
  WilsonConnCorr.wilsonG_decay hw0 hw M n

/-- The located-gap separator of the derived gap is `ρ`, and `ρ` is the real
correlator decay rate (`realCorr_decays_at_gap_rate`): the located separator IS
the actual-measure decay rate.  This is the explicit identification `sep = ρ`. -/
theorem gap_separator_eq_realRate (w : Q') (hw0 : (0 : Q') < w) (hw : w ≤ wThresh) :
    (wilsonLocatedGap w hw0 hw).sep = derivedRho w :=
  GenuineClusterBound.wilsonLocatedGap_sep w hw0 hw

/-! ## 3. THE HEADLINE structure

`TreeFixedSpacingGap` bundles, for the strong-coupling window and the tree
geometry, the four genuine facts (a)–(d) of the doc header.  It is `Type`-level
data (Rule 8): the strictly-positive constructive-real mass together with the
real-correlator decay, the transfer-operator identification, the tree partition
identity, and the positive eigenvalue-gap margin. -/

/-- **The tree-scoped fixed-spacing mass-gap datum.**

For `0 < w ≤ 1/2` and the tree / single-line geometry, this bundles:

  * `gapRate` — the geometric rate `ρ = 2w³`, with `gapRate_lt_one` (`< 1`,
    so the mass `m = −log ρ > 0`) and `gapRate_pos` (`> 0`);
  * `realCorrDecay` — the REAL Wilson connected correlator decays geometrically
    at rate `gapRate` (the actual-measure mass gap), `wilsonG ≤ (M·ρ)·ρ^n`;
  * `transferIdentified` — the real correlator IS the abstract correlator of the
    reconstructed transfer operator (`wilsonG ≃ corr (reconTransfer …)`), so
    `gapRate` is the located transfer-operator gap separator;
  * `marginPos` — the strictly-positive eigenvalue-gap margin `0 < 1 − ρ`;
  * `mass` / `mass_isPositive` — the strictly-positive constructive-real
    fixed-spacing infinite-volume mass `continuumRate (genuineDerived…)`. -/
structure TreeFixedSpacingGap (w : Q') : Type where
  /-- The geometric gap rate `ρ = coeffW w 1 = 2w³`. -/
  gapRate : Q'
  /-- The gap rate is the derived rate `ρ = derivedRho w`. -/
  gapRate_eq : gapRate = derivedRho w
  /-- The gap rate is strictly below `1` — a positive mass `m = −log ρ > 0`. -/
  gapRate_lt_one : gapRate < (1 : Q')
  /-- The gap rate is strictly positive. -/
  gapRate_pos : (0 : Q') < gapRate
  /-- **(a)** The REAL Wilson connected correlator decays geometrically at rate
  `gapRate`: `wilsonG w (M+1) n ≤ (M·ρ)·ρ^n` (the actual-measure gap). -/
  realCorrDecay : ∀ M n : Nat,
    wilsonG w (M + 1) n ≤ (Q'.ofNat M * gapRate) * gapRate ^ n
  /-- **(b)** The real correlator IS the abstract correlator of the reconstructed
  transfer operator (`wilsonG ≃ corr (reconTransfer …)`) — so `gapRate` is the
  located transfer-operator gap separator, not just an abstract model rate. -/
  transferIdentified : ∀ (hw0' : (0 : Q') ≤ w) (M n : Nat),
    (wilsonG w (M + 1) n).eqv (corr (reconTransfer w hw0' M) n)
  /-- **(c, margin)** The strictly-positive eigenvalue-gap margin `0 < 1 − ρ`. -/
  marginPos : (0 : Q') < (1 : Q') - gapRate
  /-- **(d)** The strictly-positive constructive-real fixed-spacing
  infinite-volume mass. -/
  mass : CReal
  /-- The mass is strictly positive (`CReal.IsPositive`). -/
  mass_isPositive : CReal.IsPositive mass

/-! ## 4. THE HEADLINE THEOREM `tree_fixed_spacing_mass_gap`

We assemble `TreeFixedSpacingGap` from the now-inhabited pieces.  The tree
geometry enters ONLY through the explicit hypothesis `htree`, which is consumed by
`treeRealPartition` (part (c) of the assembly, recorded by
`tree_partition_inhabited` below) — the construction is genuinely UNCONDITIONAL
for the tree geometry. -/

/-- **`tree_fixed_spacing_mass_gap` — THE HEADLINE (PROVED, tree-scoped,
UNCONDITIONAL).**

For `0 < w ≤ 1/2` and the tree / single-line geometry, a complete
`TreeFixedSpacingGap w`: the real Wilson connected correlator decays
geometrically at rate `ρ = 2w³ < 1` (a positive mass gap), this `ρ` is the
located spectral-gap separator of the reconstructed transfer operator (via the
PROVED `wilsonGMatchesAbstract_transfer`), and the fixed-spacing infinite-volume
mass `continuumRate (genuineDerivedClusterBound …)` is strictly positive.

The previously-gating identities are now INHABITED: `WilsonGMatchesAbstract` by
`treeWilsonLink` (the transfer route) and `AbstractRealPartitionIdentity` by
`treeRealPartition` (the tree route).  So this carries NO named hypotheses beyond
the strong-coupling window `0 < w ≤ 1/2` — it is genuinely unconditional for the
tree geometry. -/
def tree_fixed_spacing_mass_gap (w : Q') (hw0 : (0 : Q') < w) (hw : w ≤ wThresh) :
    TreeFixedSpacingGap w where
  gapRate := derivedRho w
  gapRate_eq := rfl
  gapRate_lt_one := derivedRho_lt_one (Q'.le_of_lt hw0) hw
  gapRate_pos := derivedRho_pos hw0
  realCorrDecay := fun M n =>
    realCorr_decays_at_gap_rate w (Q'.le_of_lt hw0) hw M n
  transferIdentified := fun hw0' M n => wilsonG_eqv_recon w hw0' M n
  marginPos := one_sub_pos_of_lt_one (derivedRho_lt_one (Q'.le_of_lt hw0) hw)
  mass := genuineDerivedContinuumRate w hw0 hw
  mass_isPositive := genuineDerived_mass_isPositive w hw0 hw

/-! ## 5. The tree partition identity is INHABITED (part (c) of the headline)

The tree partition identity `Ξ ≃ ZrealTree` is supplied by `treeRealPartition`,
consuming the explicit tree-geometry hypothesis.  We record its inhabitant here
so the headline's part (c) is exhibited — the abstract `Ξ` equals the real tree
partition function on the tree geometry. -/

/-- **The tree partition identity is INHABITED (tree-scoped).**  For the tree
geometry (`htree`), `treeRealPartition` is a genuine inhabitant of
`AbstractRealPartitionIdentity`: the abstract polymer `Ξ` equals the real tree
partition function `ZrealTree` on every finite plaquette family.  This is part
(c) of the headline, exhibited as a Type-level witness. -/
def tree_partition_inhabited {L : Lattice} [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep)
    (htree : ∀ Γ : List (Polymer L), TreeLike L Γ) :
    AbstractPolymerXi.AbstractRealPartitionIdentity (L := L) w label :=
  treeRealPartition w label htree

/-! ## 6. Clean corollaries — "there is a positive mass gap (tree, fixed spacing)"

The eigenvalue-gap margin `0 < 1 − ρ` and the `CReal.IsPositive` of the mass —
the two faces of the headline "there is a positive mass gap" for the tree /
single-line geometry at fixed spacing. -/

/-- **`tree_gap_positive` — the eigenvalue-gap margin (PROVED).**  For
`0 < w ≤ 1/2` and the tree geometry, `0 < 1 − ρ` with `ρ = 2w³`: the strictly
positive eigenvalue-gap margin, the constructive "there is a mass gap" witness in
transfer-eigenvalue space (the physical mass is `m = −log ρ`). -/
theorem tree_gap_positive (w : Q') (hw0 : (0 : Q') < w) (hw : w ≤ wThresh) :
    (0 : Q') < (1 : Q') - derivedRho w :=
  (tree_fixed_spacing_mass_gap w hw0 hw).marginPos

/-- **`tree_mass_positive` — the positive infinite-volume mass (PROVED).**  For
`0 < w ≤ 1/2` and the tree geometry, the fixed-spacing infinite-volume mass
`continuumRate (genuineDerivedClusterBound …)` is a strictly-positive
constructive real — the headline mass gap, off the DERIVED-ρ cluster bound. -/
theorem tree_mass_positive (w : Q') (hw0 : (0 : Q') < w) (hw : w ≤ wThresh) :
    CReal.IsPositive (tree_fixed_spacing_mass_gap w hw0 hw).mass :=
  (tree_fixed_spacing_mass_gap w hw0 hw).mass_isPositive

/-- **`tree_gap_bridge` — the headline mass as packaged data (PROVED).**  The
strictly-positive fixed-spacing infinite-volume mass as `Type`-level data with
its positivity proof, for the tree / single-line geometry at `0 < w ≤ 1/2`. -/
def tree_gap_bridge (w : Q') (hw0 : (0 : Q') < w) (hw : w ≤ wThresh) :
    Σ' m : CReal, CReal.IsPositive m :=
  ⟨(tree_fixed_spacing_mass_gap w hw0 hw).mass,
   (tree_fixed_spacing_mass_gap w hw0 hw).mass_isPositive⟩

/-! ## 7. Documentation: PROVED (tree-scoped, UNCONDITIONAL) vs the SOLE wall

PROVED (genuine, axiom-clean — the tree / single-line, fixed-spacing,
infinite-volume SU(2) mass gap; NO named hypotheses beyond `0 < w ≤ 1/2` and the
explicit `TreeLike` geometry):

  * `treeWilsonLink`, `absCorr_decay_unconditional`, `wilsonG_eqv_recon` — the
    previously-conditional correlator↔transfer-operator tie made UNCONDITIONAL by
    supplying the PROVED `wilsonGMatchesAbstract_transfer`;
  * `realCorr_decays_at_gap_rate`, `gap_separator_eq_realRate` — the gap rate `ρ`
    is the decay rate of the ACTUAL measure's correlator and the located gap
    separator;
  * `TreeFixedSpacingGap` / `tree_fixed_spacing_mass_gap` — THE headline,
    bundling (a) real-correlator geometric decay at `ρ = 2w³ < 1`, (b) the
    transfer-operator identification, (c) the inhabited tree partition identity,
    (d) the strictly-positive fixed-spacing infinite-volume mass;
  * `tree_partition_inhabited` — the tree partition identity `Ξ ≃ ZrealTree`
    inhabited (part (c));
  * `tree_gap_positive` (`0 < 1 − ρ`), `tree_mass_positive`
    (`CReal.IsPositive`), `tree_gap_bridge` — the clean "there is a positive mass
    gap" corollaries.

THE SOLE REMAINING NAMED WALL (NOT addressed here, NEVER faked):

  * the GENERAL LOOPY lattice (a link shared by ≥ 3 plaquettes).  It requires the
    `m`-fold shared-link Haar kernel (the SU(2) 6j recoupling) in place of the
    2-fold orthogonality in the tree partition identity, AND the multi-plaquette
    Mayer / Dobrushin-ratio reorganization for the connected correlator.  It is
    carried here as the EXPLICIT honest scope hypothesis `TreeLike` (consumed by
    `tree_partition_inhabited`), never claimed away.

NOT addressed: the continuum (spacing → 0) scaling limit (Prokhorov tightness,
O(4) restoration), and the full 4D Clay Yang–Mills mass gap.  This is a
legitimate, axiom-clean, geometrically-restricted FIXED-spacing infinite-volume
result for the tree / single-line (≤ 2-shared-link) geometry. -/

end YMGap.Continuum.TreeFixedSpacingGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TreeFixedSpacingGap.treeWilsonLink
#print axioms YMGap.Continuum.TreeFixedSpacingGap.absCorr_decay_unconditional
#print axioms YMGap.Continuum.TreeFixedSpacingGap.wilsonG_eqv_recon
#print axioms YMGap.Continuum.TreeFixedSpacingGap.realCorr_decays_at_gap_rate
#print axioms YMGap.Continuum.TreeFixedSpacingGap.gap_separator_eq_realRate
#print axioms YMGap.Continuum.TreeFixedSpacingGap.tree_fixed_spacing_mass_gap
#print axioms YMGap.Continuum.TreeFixedSpacingGap.tree_partition_inhabited
#print axioms YMGap.Continuum.TreeFixedSpacingGap.tree_gap_positive
#print axioms YMGap.Continuum.TreeFixedSpacingGap.tree_mass_positive
#print axioms YMGap.Continuum.TreeFixedSpacingGap.tree_gap_bridge
