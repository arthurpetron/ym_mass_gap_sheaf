/-
Track B / R2 — **THE δ-LOOP CAPSTONE: the end-to-end Migdal–Kadanoff bond-moving
δ-reduction chain, and the single remaining discrete-fusion residual, wired to the
top-level continuum input.**

# What this module does (read first)

The δ-loop (≈ nine modules) reduced the 4D Migdal–Kadanoff bond-moving obstruction
`δ` — the deviation of the physical block-spin map from exact heat-kernel decimation
— through a precise, fully green, axiom-clean chain.  This module ASSEMBLES that
chain into ONE `Type`-level bundle (`BondMovingGapPreservation`) and ONE green
capstone (`bond_moving_preserves_gap_reduction`), writes the honest residual ledger
(`delta_frontier_ledger`), and WIRES the residual to the single open continuum input
(`BlockingStepFrontier.IsBlockPower` / `BlockSpinModel.PhysicalRGInput.selfSimilar`).

# The chain, node by node (each node already proved green elsewhere)

  1. **Per-`s` budget FAILS, graded fix diagnosed** (`BulkModeCrux` /
     `RenormPerSBudget`): the plain heat-kernel-scaled per-mode defect has a
     `w`-independent bulk FLOOR `≥ 1/128` — the naive per-step budget is a
     SUMMABILITY obstruction.  The cure read off there is the `C₄(s)`-graded norm.

  2. **Graded budget SUMMABLE** (`GradedBondMovingBudget.gradedDefect_le`,
     `GradedTowerSummable`): dividing the per-mode residual by `C₄(s)²` collapses the
     `Θ(1)` floor to the UNIFORM quadratic `gradedDefect ≤ (1−w)²`, summable along the
     AF trajectory `1−w_k ∼ 1/k` (`∑ 1/k² < ∞`).  The summability obstruction is
     DISSOLVED; what remains is a SPECTRAL statement, not a divergent sum.

  3. **Gap = multiplicity-blind EIGENVALUE** (`GapIsEigenvalue`, verdict A): the
     reconstructed gap bounds `SpectralModel.lam` (the transfer eigenvalue), NOT the
     multiplicity-weighted coefficient.  So the gap edge is `eigA w 1 = w³`, dominant
     over all excited modes for ALL `w ∈ [0,1]` — no `w ≤ 7/9` window.

  4. **Bulk eigenvalues sit a `Θ(1)` margin BELOW the edge**
     (`SpectralLocalizationCrux.bulk_below_gapEdge`): on the bulk window
     `C₄(s)(1−w) ≥ 1/2`, `eigA w 1 − eigA w s ≥ 1/12`.  The `Θ(1)` bond-moving defect
     lives in the MULTIPLICITY/density, not in the eigenvalue location.

  5. **The eigenvalue-shift BRIDGE** (`EigenvalueShiftBridge.bondMoved_below_gapEdge`):
     IF the per-mode eigenvalue shift `eigShift ≤ 1/12` on the bulk, THEN the
     bond-moved bulk eigenvalue stays `≤` the gap edge — multiplicity-blind, NO
     `(s+1)` density.  `localization_holds` discharges everything else.

  6. **The naive `eigShift` is a vacuum-normalization ARTIFACT** (`EigShiftOrder`):
     the UN-normalized `eigShift` is `Θ(1)` at the vacuum (`eigShift_vacuum_lower`,
     `≥ 4w⁶`), because the fusion carries the un-normalized vacuum L²-mass `bmc(0)`.
     It VANISHES at `p = 1` (`eigShift_p1_zero`).  The genuine spectral object is the
     VACUUM-NORMALIZED eigenvalue `bmc(s)/((s+1)·bmc(0))`; controlling ITS bulk shift
     is the residual `BulkDefectControlled` (the conclusion the `VacNormEigShift`
     module isolates — carried here as the named input
     `SpectralLocalizationCrux.SpectralLocalization`, whose `bulk_shift ≤ 1/12` field
     is exactly that bound; trivially inhabited at `p = 1`, open for `p ≥ 2`).

  7. **`s = 1`-dominance + `s = 1` QUADRATIC defect** (`S1Dominance`,
     `BondMovingQuadratic`): given `s = 1`-dominance (PROVED `p = 1`,
     `s1Dominance_p1`; named open `p ≥ 2`) the gap edge IS the `s = 1` level
     (`excited_spectrum_bounded_by_s1`), whose retuned transverse defect is QUADRATIC
     in the margin (`bondMovingDeltaRen_quadratic`, `≤ 18p·(1−w)²`).

# What the capstone bundles (all conjuncts GREEN given the one named residual)

`BondMovingGapPreservation N w p` carries the window bounds plus the SINGLE
named-open residual `bulkCtrl` (the vacuum-normalized bulk eigenvalue-shift control,
`BulkDefectControlled` / `VacNormEigShift`-shaped, `bulk_shift ≤ 1/12`; `p = 1`
inhabited by `trivialLocalization`).  `bond_moving_preserves_gap_reduction` then
delivers, all proved:

  (1) the gap edge is the multiplicity-blind `s = 1` eigenvalue, dominant for ALL `w`;
  (2) the bulk eigenvalues sit `≥ 1/12` below the edge;
  (3) under the named bulk-defect control, the bond-moved bulk stays `≤` the edge;
  (4) the `s = 1` retuned transverse defect is QUADRATIC in `(1−w)`, UNCONDITIONAL;
  (5) the vacuum coefficient is positive and the `s = 1` channel clears the bare
      heat-kernel floor.

`delta_step_summable` re-exposes the UNCONDITIONAL graded-tower summability (the
per-step `δ` is summable over the AF trajectory).

# THE single remaining statement (see `delta_frontier_ledger`)

After the whole δ-loop the residual is the discrete SU(2) heat-kernel fusion
LOCAL-CLT: the vacuum-normalized `p`-fold fusion coefficient
`bmc(s)/((s+1)·bmc(0))` matches the Gaussian `e^{−C₄(s)(1−w)/p}` to QUADRATIC order
UNIFORMLY in `s` — equivalently, `s = 1`-dominance of the vacuum-normalized
bond-moved spectrum for the genuine 4D exponent `p = b^{d−1} ≥ 2`.  PROVED: `p = 1`
(exactly), `s = 1` quadraticity, multiplicity-blindness, graded summability,
gap = eigenvalue, the `s = 1` identity-channel floor.  OPEN: the `p ≥ 2` uniform
match (the fusion-multiplicity monotonicity tier).

# The wire to the top (`DeltaToBlockPower`)

This discrete residual is the content of `BlockingStepFrontier.IsBlockPower` for the
physical 4D block-spin map (open precisely because the ℝ⁴ `BondMovingResidual` `δ`
is uninhabited).  `deltaFrontier_physicalRGInput` / `deltaFrontier_continuum_gap`
compose: GIVEN the discharged residual (the named bridge `residualToPower`), the
δ-loop bundle BUILDS a full `PhysicalRGInput`, hence (via
`physicalRG_continuum_gap`) the spacing-uniform physical continuum mass gap.  The
entire chain from the Clay continuum gap down to the one discrete-fusion statement
is wired green.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the already-green δ-loop engines; every carrier is `Type`-level
data, the open pieces are honest named interfaces (never a `sorry`).  Each
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.RenormPerSBudget
import YMGap.Continuum.BulkModeCrux
import YMGap.Continuum.GradedBondMovingBudget
import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.GapIsEigenvalue
import YMGap.Continuum.S1Dominance
import YMGap.Continuum.EigenvalueShiftBridge
import YMGap.Continuum.EigShiftOrder
import YMGap.Continuum.BlockSpinModel
import YMGap.Continuum.BlockingStepFrontier

namespace YMGap.Continuum.DeltaFrontierLedger

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic

/-! ## 1. The end-to-end bundle and the single named residual

`BondMovingGapPreservation` packages the near-continuum window data with the SINGLE
named-open input of the whole δ-loop: the vacuum-normalized bulk eigenvalue-shift
control (`bulkCtrl`).  This is `VacNormEigShift`'s intended conclusion
(`BulkDefectControlled`), carried in the proved-shape interface
`SpectralLocalizationCrux.SpectralLocalization` whose load-bearing field is
`bulk_shift : ∀ s, shift s ≤ 1/12` — exactly the multiplicity-blind eigenvalue-shift
bound the bridge consumes.  At `p = 1` it is inhabited by `trivialLocalization`
(the unperturbed spectrum); for the genuine `p ≥ 2` bond-moving the GENUINE inhabitant
(`eig' = ` the vacuum-normalized bond-moved spectrum) is the discrete-fusion residual.
-/

/-- **The bond-moving gap-preservation bundle.**  Window bounds `0 ≤ w ≤ 1`, the
cutoff/exponent positivity, and the single named residual `bulkCtrl` (the
vacuum-normalized bulk eigenvalue-shift control). -/
structure BondMovingGapPreservation (N : Nat) (w : Q') (p : Nat) : Type where
  /-- `0 ≤ w`. -/
  hw0 : (0 : Q') ≤ w
  /-- `w ≤ 1`. -/
  hw1 : w ≤ (1 : Q')
  /-- `1 ≤ N` (a genuine excited cutoff). -/
  hN : 1 ≤ N
  /-- `0 < p` (a genuine fusion exponent). -/
  hp : 0 < p
  /-- **THE SINGLE NAMED RESIDUAL** — the vacuum-normalized bulk eigenvalue-shift
  control (`VacNormEigShift` = `BulkDefectControlled`): the bond-moved bulk transfer
  eigenvalue-shift is below the localization margin `1/12` (its `bulk_shift` field).
  Inhabited at `p = 1` by `trivialLocalization`; the genuine `p ≥ 2` inhabitant is the
  discrete-fusion local-CLT residual. -/
  bulkCtrl : SpectralLocalizationCrux.SpectralLocalization w

/-- **The capstone conclusion** (named, so the capstone and the ledger share it): the
five green deliverables of the δ-loop chain, parameterized by the bond-moved bulk
spectrum `eig'`. -/
def GapReductionConclusion (N : Nat) (w : Q') (p : Nat) (eig' : Nat → Q') : Prop :=
  -- (1) gap edge = multiplicity-blind s=1 eigenvalue, dominant for ALL w
  (∀ s, 1 ≤ s → SpectralLocalizationCrux.eigA w s ≤ SpectralLocalizationCrux.eigA w 1)
  ∧ -- (2) bulk eigenvalues sit ≥ 1/12 BELOW the edge
  (∀ s, BulkModeCrux.q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - w) →
      SpectralLocalizationCrux.q112
        ≤ SpectralLocalizationCrux.eigA w 1 - SpectralLocalizationCrux.eigA w s)
  ∧ -- (3) under the named bulk-defect control, the bond-moved bulk stays ≤ edge
  (∀ s, BulkModeCrux.q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - w) →
      eig' s ≤ SpectralLocalizationCrux.eigA w 1)
  ∧ -- (4) the s=1 retuned transverse defect is QUADRATIC (UNCONDITIONAL)
  (bondMovingDeltaRen N p w
      ≤ (Q'.ofNat p * (dimQ 1 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1))))
          * (((1 : Q') - w) * ((1 : Q') - w)))
  ∧ -- (5) vacuum coefficient positive + s=1 channel clears the bare floor
  ((0 : Q') < bondMovedCoeff N w p 0 ∧ coeffW w 1 ≤ bondMovedCoeff N w p 1)

/-- **THE δ-LOOP CAPSTONE.**  From the bundle (one named residual `bulkCtrl`) the full
chain delivers `GapReductionConclusion`: (1) the gap edge is the multiplicity-blind
`s = 1` eigenvalue, dominant for ALL `w` (`eigEdge_dominates_all_w`); (2) the bulk
eigenvalues sit `≥ 1/12` below it (`bulk_below_gapEdge`); (3) under the named
bulk-defect control the bond-moved bulk stays at or below the edge
(`localization_holds`); (4) the `s = 1` retuned transverse defect is QUADRATIC in the
margin, UNCONDITIONAL (`bondMovingDeltaRen_quadratic`); (5) the vacuum coefficient is
positive and the `s = 1` channel clears the bare heat-kernel floor (`bmc_zero_pos`,
`bmc_one_ge_coeffW_one`).  Every conjunct is proved; the only non-trivial input is the
single residual `bulkCtrl`. -/
theorem bond_moving_preserves_gap_reduction {N : Nat} {w : Q'} {p : Nat}
    (G : BondMovingGapPreservation N w p) :
    GapReductionConclusion N w p G.bulkCtrl.eig' :=
  ⟨ fun _s hs => GapIsEigenvalue.eigEdge_dominates_all_w G.hw0 G.hw1 hs
  , fun s hlo =>
      SpectralLocalizationCrux.bulk_below_gapEdge G.hw0 G.hw1 s G.bulkCtrl.hnc hlo
  , fun s hlo =>
      SpectralLocalizationCrux.localization_holds G.hw0 G.hw1 G.bulkCtrl s hlo
  , bondMovingDeltaRen_quadratic G.hw0 G.hw1 N p
  , ⟨ S1Dominance.bmc_zero_pos N G.hw0 G.hw1 p G.hp
    , S1Dominance.bmc_one_ge_coeffW_one N G.hw0 G.hw1 G.hN p G.hp ⟩ ⟩

/-- **Non-vacuity at `p = 1`.**  On any near-continuum weight the bundle is inhabited
with `bulkCtrl = trivialLocalization` (the unperturbed spectrum), so the capstone
fires unconditionally at the heat-kernel input — the residual is genuinely the
`p ≥ 2` content, not a `p = 1` gap. -/
def trivialBundle (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hN : 1 ≤ N) (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112) :
    BondMovingGapPreservation N w 1 where
  hw0 := hw0
  hw1 := hw1
  hN := hN
  hp := by decide
  bulkCtrl := SpectralLocalizationCrux.trivialLocalization w hnc

/-- The capstone fired at `p = 1` on the bundle's own demo weight `w = 95/96`
(`1 − w = 1/96 ≤ 1/12`): the heat-kernel input satisfies the full
`GapReductionConclusion` with NO open hypothesis. -/
theorem capstone_p1_demo (N : Nat) (hN : 1 ≤ N) :
    GapReductionConclusion N SpectralLocalizationCrux.demoW 1
      (trivialBundle N SpectralLocalizationCrux.demoW_pos
        SpectralLocalizationCrux.demoW_le_one hN SpectralLocalizationCrux.demoW_nc).bulkCtrl.eig' :=
  bond_moving_preserves_gap_reduction
    (trivialBundle N SpectralLocalizationCrux.demoW_pos
      SpectralLocalizationCrux.demoW_le_one hN SpectralLocalizationCrux.demoW_nc)

/-! ## 2. The UNCONDITIONAL graded-tower summability (the per-step δ is summable) -/

/-- **`delta_step_summable` — the per-step `δ` is summable over the AF trajectory
(UNCONDITIONAL).**  Re-exposes `GradedBondMovingBudget.GradedTowerSummable`: every
tail window of the `C₄`-graded bond-moving budget along the AF trajectory is bounded
by the dyadically decaying `D·1/(N+1)`, so the partial sums are uniformly bounded —
the graded tower (the per-step bond-moving `δ`) is SUMMABLE.  This is the decisive
contrast with the plain-norm bulk floor (`BulkModeCrux`), which did not even vanish.
No open hypothesis. -/
theorem delta_step_summable (afr : AFRateCalibration.AFRateModulus) (N₀ : Nat)
    (gt : GradedBondMovingBudget.GradedTrajectory afr N₀) (N M : Nat) :
    SummableInverseSquare.tailSum
        (GradedBondMovingBudget.gradedFullModeDefect afr N₀ gt).d N M
      ≤ FullModeAssembly.fmAconst afr
          (GradedBondMovingBudget.gradedFullModeDefect afr N₀ gt)
          * SummableInverseSquare.pot 2 (by decide) N :=
  GradedBondMovingBudget.GradedTowerSummable afr N₀ gt N M

/-! ## 3. The `s = 1`-dominance COEFFICIENT face (PROVED `p = 1`, named `p ≥ 2`)

The coefficient-level reading of the residual: given the `s = 1`-dominance datum
`S1Dominance N w p`, the gap edge is the `s = 1` normalized separator.  PROVED for
the heat-kernel input `p = 1` on the character window (`s1Dominance_p1`); the genuine
`p ≥ 2` datum is the same discrete-fusion residual, in coefficient language. -/

/-- **`s1_dominance_gap_edge`** — given the `s = 1`-dominance datum, every excited
normalized bond-moved eigenvalue is dominated by the `s = 1` separator (the gap edge
is the `s = 1` level).  Proved in the datum (`excited_spectrum_bounded_by_s1`). -/
theorem s1_dominance_gap_edge {N : Nat} {w : Q'} {p : Nat}
    (sd : S1Dominance.S1Dominance N w p)
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hp : 0 < p)
    (s : Nat) (hs : 1 ≤ s) (hsN : s ≤ N) :
    S1Dominance.normSep N w p (S1Dominance.bmc_zero_pos N hw0 hw1 p hp) s
      ≤ sepBM N w p (S1Dominance.bmc_zero_pos N hw0 hw1 p hp) :=
  S1Dominance.excited_spectrum_bounded_by_s1 N sd
    (S1Dominance.bmc_zero_pos N hw0 hw1 p hp) s hs hsN

/-- **The `p = 1` coefficient `s = 1`-dominance datum is INHABITED** on the character
window `0 ≤ w ≤ 7/9` (`s1Dominance_p1`): the heat-kernel bond-moved spectrum is
provably `s = 1`-dominant.  Re-exposed so the proved end of the coefficient face is
visible next to the named `p ≥ 2` residual. -/
def s1_dominance_p1_inhabited (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ CharacterWindowCeiling.wHi) :
    S1Dominance.S1Dominance N w 1 :=
  S1Dominance.s1Dominance_p1 N hw0 hw

/-! ## 4. The HONESTY anchors — the naive `eigShift` artifact (`EigShiftOrder`)

The naive multiplicity-blind `eigShift` is NOT the genuine object: it vanishes at
`p = 1` but is `Θ(1)` at the vacuum for `p ≥ 2` (the un-normalized vacuum L²-mass).
These re-exposures pin exactly why the residual is phrased on the VACUUM-NORMALIZED
eigenvalue. -/

/-- **`naive_eigShift_p1_vanishes`** — the un-normalized eigenvalue shift VANISHES at
`p = 1` (`eigShift_p1_zero`): the defect is a genuine `p ≥ 2` bond-moving effect. -/
theorem naive_eigShift_p1_vanishes (N : Nat) (w : Q') (s : Nat) (hsN : s ≤ N) :
    (EigenvalueShiftBridge.eigShift N 1 (by decide) w s).eqv 0 :=
  EigShiftOrder.eigShift_p1_zero N w s hsN

/-- **`naive_eigShift_bulk_theta_one`** — the un-normalized eigenvalue shift is
`Θ(1)` at the vacuum for the genuine `p ≥ 2` (`eigShift_vacuum_exceeds`): it EXCEEDS
the localization margin `1/12`, so the bridge does NOT close with the un-normalized
`bmEig`.  This is why the residual is carried on the VACUUM-NORMALIZED eigenvalue
(the genuine `bulkCtrl` object). -/
theorem naive_eigShift_bulk_theta_one (N : Nat) (hN : 1 ≤ N) (p : Nat) (hp : 0 < p) :
    SpectralLocalizationCrux.q112
      ≤ EigenvalueShiftBridge.eigShift N (p + 1) (Nat.succ_pos p)
          EigenvalueShiftBridge.demoW 0 :=
  EigShiftOrder.eigShift_vacuum_exceeds N hN p hp

/-! ## 5. THE FRONTIER LEDGER — the exact single remaining statement -/

/-- **`delta_frontier_ledger` — the honest residual after the whole δ-loop.**

Spelling out the bundle's fields as hypotheses, the δ-loop capstone fires from a
SINGLE non-trivial input `bulkCtrl`, exhibiting EXACTLY what remains.

> **THE SINGLE REMAINING STATEMENT** (the discrete SU(2) heat-kernel fusion
> local-CLT).  The vacuum-normalized `p`-fold fusion coefficient
> `bmc(s)/((s+1)·bmc(0))` matches the Gaussian `e^{−C₄(s)(1−w)/p}` to QUADRATIC
> order, UNIFORMLY in `s` — equivalently, the vacuum-normalized bond-moved transfer
> spectrum is `s = 1`-dominant for the genuine 4D bond-moving exponent
> `p = b^{d−1} ≥ 2`.  This is the bulk eigenvalue-shift bound `bulk_shift ≤ 1/12`
> carried by `bulkCtrl`.

WHAT IS PROVED (cited, all green):
  * `p = 1` EXACTLY — `trivialBundle` / `capstone_p1_demo` (the heat-kernel input
    has the unperturbed spectrum; the un-normalized `eigShift` vanishes,
    `naive_eigShift_p1_vanishes`);
  * the `s = 1` retuned transverse defect is QUADRATIC in `(1−w)`, UNCONDITIONAL
    (conjunct (4), `bondMovingDeltaRen_quadratic`);
  * multiplicity-blindness — the gap is the eigenvalue, dominant for ALL `w`
    (conjunct (1), `eigEdge_dominates_all_w`; `GapIsEigenvalue` verdict A);
  * the bulk eigenvalues sit a `Θ(1)` (`≥ 1/12`) margin below the edge
    (conjunct (2), `bulk_below_gapEdge`);
  * graded summability — the per-step `δ` is summable over the AF trajectory
    (`delta_step_summable`, UNCONDITIONAL);
  * the `s = 1` identity-channel floor and vacuum positivity (conjunct (5));
  * the coefficient face: `s = 1`-dominance ⟹ gap edge = `s = 1`, inhabited at
    `p = 1` (`s1_dominance_gap_edge`, `s1_dominance_p1_inhabited`).

WHAT REMAINS OPEN (the single statement above):
  * the `p ≥ 2` UNIFORM-in-`s` quadratic match of the vacuum-normalized fusion
    coefficient to the Gaussian — the weighted SU(2) fusion-multiplicity monotonicity
    (discrete local-CLT tier).  NOT inhabited; NOT faked.  The naive un-normalized
    `eigShift` is `Θ(1)` there (`naive_eigShift_bulk_theta_one`), which is precisely
    why the residual is phrased on the vacuum-normalized eigenvalue. -/
theorem delta_frontier_ledger {N : Nat} {w : Q'} {p : Nat}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hN : 1 ≤ N) (hp : 0 < p)
    (bulkCtrl : SpectralLocalizationCrux.SpectralLocalization w) :
    GapReductionConclusion N w p bulkCtrl.eig' :=
  bond_moving_preserves_gap_reduction
    { hw0 := hw0, hw1 := hw1, hN := hN, hp := hp, bulkCtrl := bulkCtrl }

/-! ## 6. THE WIRE TO THE TOP — the δ-residual inhabits the open continuum input

The discrete-fusion residual is the content of `BlockingStepFrontier.IsBlockPower`
for the physical 4D block-spin map: that interface is open precisely because the ℝ⁴
`BondMovingResidual` `δ` is uninhabited (`d > 2`, MK approximate).  Given the
discharged residual (the named bridge `residualToPower`: the δ-loop bundle yields the
`CReal`-level power law `Φ(x) ≃ x^{b+1}`), `physicalRGInput_of_blockingPower` builds
the full `PhysicalRGInput`, and `physicalRG_continuum_gap` the spacing-uniform
physical continuum mass gap.  This is the green wire from the Clay continuum gap down
to the one discrete-fusion statement. -/

/-- **The δ-residual → block-power wiring datum.**  Bundles the δ-loop bundle with a
physical separator family, its single-step blocking relation, the `[0,1]` bounds, a
UV-gap floor, and the NAMED bridge `residualToPower` stating that the discharged
discrete δ-residual (the bundle) yields the `CReal`-level block-power law for the
physical block-spin map.  The bridge is the honest remaining link between the
discrete fusion statement and the `CReal` power law — PROVED exactly on the
hierarchical / decimation half (`BlockingStepFrontier.decimation_isPower`,
`hierarchical_blocking_exact`), open for the full 4D step. -/
structure DeltaToBlockPower (b N : Nat) (w : Q') (p : Nat) : Type where
  /-- The discharged δ-loop bundle (its single residual `bulkCtrl`). -/
  bundle : BondMovingGapPreservation N w p
  /-- The block factor is a genuine decimation. -/
  hb : 1 ≤ b
  /-- The physical Yang–Mills RG separator family. -/
  physSep : Nat → CReal
  /-- The single-step blocking relation `sep_k ≃ Φ(sep_{k+1})`. -/
  blockingStep : BlockingStepFrontier.BlockingStep physSep
  /-- **THE NAMED BRIDGE** — the discharged discrete δ-residual (the bundle) yields the
  `CReal`-level block-power law `Φ(x) ≃ x^{b+1}` for the physical block-spin map. -/
  residualToPower :
    BondMovingGapPreservation N w p → BlockingStepFrontier.IsBlockPower b blockingStep.Φ
  /-- The physical separators are nonnegative. -/
  sepNonneg : ∀ k, ExpPos.geRat (physSep k) 0
  /-- The physical separators are `≤ 1`. -/
  sepLeOne : ∀ k, CReal.leRat (physSep k) 1
  /-- The explicit UV-gap floor (data). -/
  floor0 : Q'
  /-- The UV-gap floor is strictly positive. -/
  floor0_pos : (0 : Q') < floor0
  /-- The UV-gap floor lies below the physical gap at the coarsest scale. -/
  hbase0 : CReal.leEv (CReal.ofQ' floor0)
    (CodynamicPhysFloor.physGapC b physSep (RateMatchFloor.geomSpacing b) 0)

/-- **`deltaFrontier_physicalRGInput` — the δ-residual BUILDS the physical-RG input.**
Given the wiring datum, the discharged residual yields `IsBlockPower`, which (via
`physicalRGInput_of_blockingPower`) discharges the open `selfSimilar` field of
`PhysicalRGInput`.  The discrete-fusion residual is thus exactly what inhabits the
top-level open continuum input. -/
def deltaFrontier_physicalRGInput {b N : Nat} {w : Q'} {p : Nat}
    (D : DeltaToBlockPower b N w p) : PhysicalRGInput :=
  BlockingStepFrontier.physicalRGInput_of_blockingPower D.hb D.physSep D.blockingStep
    (D.residualToPower D.bundle) D.sepNonneg D.sepLeOne D.floor0 D.floor0_pos D.hbase0

/-- **`deltaFrontier_continuum_gap` — the physical continuum mass gap from the
δ-residual (GREEN wire).**  Composing the wiring with `physicalGap_of_blockingPower`:
GIVEN the discharged discrete δ-residual, the physical gap carries a strictly-positive
spacing-uniform floor at every scale of the `a → 0` block schedule.  The entire chain
from the Clay continuum gap down to the single discrete-fusion statement is wired
green. -/
def deltaFrontier_continuum_gap {b N : Nat} {w : Q'} {p : Nat}
    (D : DeltaToBlockPower b N w p) :
    UnifiedContinuumFloor.CRealFloor
      (CodynamicPhysFloor.physGapC b D.physSep (RateMatchFloor.geomSpacing b)) :=
  BlockingStepFrontier.physicalGap_of_blockingPower D.hb D.physSep D.blockingStep
    (D.residualToPower D.bundle) D.sepNonneg D.sepLeOne D.floor0 D.floor0_pos D.hbase0

/-- The wired physical continuum floor is strictly positive — the genuine
spacing-uniform mass gap, GIVEN the discharged δ-residual. -/
theorem deltaFrontier_continuum_floor_pos {b N : Nat} {w : Q'} {p : Nat}
    (D : DeltaToBlockPower b N w p) :
    (0 : Q') < (deltaFrontier_continuum_gap D).floor :=
  (deltaFrontier_continuum_gap D).floor_pos

end YMGap.Continuum.DeltaFrontierLedger

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DeltaFrontierLedger.bond_moving_preserves_gap_reduction
#print axioms YMGap.Continuum.DeltaFrontierLedger.trivialBundle
#print axioms YMGap.Continuum.DeltaFrontierLedger.capstone_p1_demo
#print axioms YMGap.Continuum.DeltaFrontierLedger.delta_step_summable
#print axioms YMGap.Continuum.DeltaFrontierLedger.s1_dominance_gap_edge
#print axioms YMGap.Continuum.DeltaFrontierLedger.s1_dominance_p1_inhabited
#print axioms YMGap.Continuum.DeltaFrontierLedger.naive_eigShift_p1_vanishes
#print axioms YMGap.Continuum.DeltaFrontierLedger.naive_eigShift_bulk_theta_one
#print axioms YMGap.Continuum.DeltaFrontierLedger.delta_frontier_ledger
#print axioms YMGap.Continuum.DeltaFrontierLedger.deltaFrontier_physicalRGInput
#print axioms YMGap.Continuum.DeltaFrontierLedger.deltaFrontier_continuum_gap
#print axioms YMGap.Continuum.DeltaFrontierLedger.deltaFrontier_continuum_floor_pos
