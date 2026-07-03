/-
Track B-converge / R2 — **ASSEMBLING the three Stage-2 (a→0) reduction arrows
onto the single unifier `AsymptoticSpectralLoc.SpectralMarginInput`, and the ONE
genuine merge lemma `hlocalize ⇒ hbridge`.**

# What this module does (read first)

Three previously-separate continuum-gap reduction arrows all consume the SAME
scaled bulk eigenvalue-shift datum, but were phrased on three different carriers:

  * **#1 (Balaban)** — `BalabanExactProgress.gradedCodynamicGap`, the FULL-model
    codynamic gap, whose sole open input is `SpectralLocalization.hlocalize`;
  * **#2 (defect-gap recursion)** — `ContinuumClosureProgram.DefectGapRecursion`,
    whose sole open field is the per-step degradation `(1−δ_k)·Δ_k ≤ Δ_{k+1}`;
  * **#3 (asymptotic descent)** — `AFDeltaDecay.AsymptoticDescentInput`, whose
    sole open field is the margin recursion `(1−δ_k)·g_k ≤ g_{k+1}`.

`AsymptoticSpectralLoc.SpectralMarginInput` already discharges #3's `recursion`
(via `margin_recursion_of_eigShift`) from its two open fields `hadd`/`hbridge`,
and carries the graded `sl` feeding #1.  This module contributes:

  * **`SpectralMarginInput.toDefectGapRecursion`** (§1) — the sole new glue: it
    packages a `SpectralMarginInput` as a `DefectGapRecursion`, discharging #2's
    `recursion` field with the SAME converter call used for #3 (byte-identical
    arrow), and supplying the product floor from the tower `T` (`towerFloor·anchor`).

  * **`stage2_convergence`** (§2) — the assembled convergence theorem: from ONE
    `SpectralMarginInput`, all three floors are strictly positive / uniform.  Every
    component is a direct call to a proved lemma; no new open field is introduced.

  * **`ScaledBulkShift` + `hbridge_of_hlocalize`** (§3) — the ONE genuine merge
    lemma.  `SpectralMarginInput` carries the scaled shift as TWO un-merged fields
    (`hbridge`, feeding #2/#3, and `sl.hlocalize`, feeding #1).  `ScaledBulkShift`
    is the trajectory↔graded DICTIONARY (the reindexing `idx` and the two
    identifications `shift_k = gapDefect(idx k)`, `δ_k·g_k = gradedBudget(w_{idx k})`);
    `hbridge_of_hlocalize` then DERIVES `hbridge` from `hlocalize` by rewriting both
    sides.  So `hbridge` collapses onto `hlocalize` modulo the dictionary — the
    single remaining residual.

# Honest scope

`SpectralMarginInput` is NOT inhabited on ℝ⁴.  §1/§2 are axiom-clean assembly of
already-proved reduction arrows (a genuine convergence theorem localizing B1=B2=B3
onto one input).  §3's `ScaledBulkShift` is the honest naming of the trajectory↔
graded dictionary: its two fields `shift_eq`/`budget_eq` ARE the residual, and the
merge lemma reduces `hbridge` to `hlocalize` given them.  The single genuine open
core is unchanged (the p≥2 discrete SU(2)-fusion local-CLT / `LineSumLogConcaveCR`
w-monotonicity carried inside `hlocalize`).  The Clay mass gap remains OPEN; this
is reduction-mode.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition over already-proved engines; every carrier is
`Type`-level data.  Each load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`.
-/

import YMGap.Continuum.AsymptoticSpectralLoc
import YMGap.Continuum.BalabanExactProgress
import YMGap.Continuum.ContinuumClosureProgram

namespace YMGap.Continuum.Stage2ConvergesToMargin

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.AsymptoticSpectralLoc

/-! ## 0. A small prefix-product nonnegativity helper -/

/-- `0 ≤ ∏_{i<k} ρ_i` whenever each factor is nonnegative.  By induction on `k`;
`prodPrefix ρ 0 = 1 ≥ 0`, `prodPrefix ρ (k+1) = prodPrefix ρ k · ρ_k`. -/
theorem prodPrefix_nonneg (rho : Nat → Q') (h : ∀ i, (0 : Q') ≤ rho i) :
    ∀ k, (0 : Q') ≤ RGGapPersistence.prodPrefix rho k
  | 0 => by show (0 : Q') ≤ (1 : Q'); decide
  | k + 1 => Q'.mul_nonneg _ _ (prodPrefix_nonneg rho h k) (h k)

/-! ## 1. The sole new glue — `SpectralMarginInput.toDefectGapRecursion` -/

/-- **THE GLUE (target #2).**  A `SpectralMarginInput` yields a
`ContinuumClosureProgram.DefectGapRecursion` whose open `recursion` field is
DISCHARGED via `margin_recursion_of_eigShift` — the SAME arrow that discharges
`AsymptoticDescentInput.recursion` (target #3), applied verbatim.  The physical
gap is `g_k = m_lat(a_k)/a_k`; the defect is the tower's `δ_k` (with `δ_k ≤ ½ ≤ 1`);
the product floor is `towerFloor T · anchor` from the summable tower.  No new open
field is introduced. -/
def toDefectGapRecursion {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (I : SpectralMarginInput b afr N₀) :
    ContinuumClosureProgram.DefectGapRecursion where
  physGap := I.g
  physGap0_pos :=
    ContinuumClosureProgram.q'_lt_of_lt_of_le I.anchor_pos I.anchor_le
  defect := I.T.δ
  defect_nonneg := I.T.δ_nonneg
  defect_le_one := fun k => AFDeltaDecay.δ_le_one I.T k
  -- byte-identical arrow to `toAsymptotic.recursion`
  recursion := fun k =>
    margin_recursion_of_eigShift (I.T.δ k) (I.shift k) (I.g k) (I.g (k + 1))
      (I.hadd k) (I.hbridge k)
  prodFloor := AFDeltaDecay.towerFloor I.T * I.anchor
  prodFloor_pos := Q'.mul_pos (AFDeltaDecay.towerFloor_pos I.T) I.anchor_pos
  prodFloor_le := fun k => by
    -- towerFloor·anchor ≤ (∏ ρ)·anchor ≤ (∏ ρ)·g0
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (AFDeltaDecay.towerFloor I.T)
        (RGGapPersistence.prodPrefix (fun i => 1 - I.T.δ i) k) I.anchor
        (AFDeltaDecay.towerFloor_le I.T k) (Q'.le_of_lt I.anchor_pos)) ?_
    exact Q'.mul_le_mul_of_nonneg_left I.anchor (I.g 0)
      (RGGapPersistence.prodPrefix (fun i => 1 - I.T.δ i) k) I.anchor_le
      (prodPrefix_nonneg (fun i => 1 - I.T.δ i)
        (fun i => AFDeltaDecay.oneSub_nonneg I.T i) k)

/-- The defect-gap recursion's uniform floor is strictly positive at every scale:
`0 < Δ_k` for the `SpectralMarginInput`-derived recursion (target #2, sharp form). -/
theorem defectGap_physGap_pos {b : Nat} {afr : AFRateModulus}
    {N₀ : Nat} (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (0 : Q') < (toDefectGapRecursion I).physGap k :=
  ContinuumClosureProgram.DefectGapRecursion.physGap_pos (toDefectGapRecursion I) k

/-! ## 2. The assembled convergence theorem -/

/-- **STAGE-2 CONVERGENCE (the assembly).**  From a SINGLE
`AsymptoticSpectralLoc.SpectralMarginInput`, the three Stage-2 continuum-gap floors
all hold simultaneously:

  * **#1** the FULL-model codynamic gap is strictly positive
    (`gradedCodynamicGap_pos`, sole input `sl.hlocalize`);
  * **#3** the spacing-uniform physical-gap floor `physGapMin > 0` survives `a → 0`
    (`AsymptoticDescentInput.continuum_floor_pos`, via the discharged margin
    recursion);
  * **#2** the defect-gap recursion is uniformly floored below by `prodFloor > 0`
    at every scale (`DefectGapRecursion.uniform_floor`, via the discharged
    degradation recursion).

Every component is a direct call to a proved lemma; the ONLY open inputs are
`I.hbridge` / `I.hadd` / `I.sl.hlocalize` carried by the single `SpectralMarginInput`.
This is a genuine convergence theorem: B1=B2=B3 all reduce to one datum.  No 4D
inhabitant of `SpectralMarginInput` is exhibited; the Clay problem stays OPEN. -/
theorem stage2_convergence {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (I : SpectralMarginInput b afr N₀) :
    (0 : Q') < (BalabanExactProgress.gradedCodynamicGap afr N₀ I.sl).1
  ∧ (0 : Q') < (RGGapPersistence.toScalingBand I.toAsymptotic.toUniform).physGapMin
  ∧ (∀ k, (toDefectGapRecursion I).prodFloor ≤ (toDefectGapRecursion I).physGap k) :=
  ⟨ BalabanExactProgress.gradedCodynamicGap_pos afr N₀ I.sl,
    I.toAsymptotic.continuum_floor_pos,
    ContinuumClosureProgram.DefectGapRecursion.uniform_floor (toDefectGapRecursion I) ⟩

/-- The defect-gap floor `prodFloor` is itself strictly positive (companion to the
uniform bound in `stage2_convergence`). -/
theorem stage2_prodFloor_pos {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (I : SpectralMarginInput b afr N₀) :
    (0 : Q') < (toDefectGapRecursion I).prodFloor :=
  (toDefectGapRecursion I).prodFloor_pos

/-! ## 3. The ONE genuine merge lemma — `hlocalize ⇒ hbridge`

`SpectralMarginInput` carries the scaled bulk eigenvalue-shift as TWO un-merged
fields: `hbridge` (`shift_k ≤ δ_k·g_k`, feeding #2/#3) and `sl.hlocalize`
(`gapDefect_k ≤ gradedBudget(w_k)`, feeding #1).  To collapse them to one, we name
the trajectory↔graded DICTIONARY `ScaledBulkShift`: a reindexing `idx` and the two
identifications that translate the physical shift/budget into the graded ones.
`hbridge_of_hlocalize` then DERIVES `hbridge` from `hlocalize` — the honest merge. -/

/-- **THE TRAJECTORY↔GRADED DICTIONARY.**  Carries a per-scale reindexing `idx`
and the two identifications collapsing the physical scaled-shift data
`(shift_k, δ_k·g_k)` onto the graded spectral-localization data
`(gapDefect(idx k), gradedBudget(w_{idx k}))`.  These identifications ARE the
residual (the trajectory↔graded translation of the p≥2 SU(2)-fusion local-CLT);
`ScaledBulkShift` is NOT inhabited on ℝ⁴. -/
structure ScaledBulkShift (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) : Type where
  /-- The per-scale eigenvalue-shift budget `shift_k`. -/
  shift : Nat → Q'
  /-- The exponent-level defect `δ_k`. -/
  δ : Nat → Q'
  /-- The physical margin `g_k = m_lat(a_k)/a_k`. -/
  g : Nat → Q'
  /-- The trajectory↔graded reindexing (e.g. `idx k = k + gradedCutoff`). -/
  idx : Nat → Nat
  /-- **DICTIONARY (residual, shift side)** — the physical shift IS the graded
  gap-defect at the reindexed scale. -/
  shift_eq : ∀ k, shift k = sl.gapDefect (idx k)
  /-- **DICTIONARY (residual, budget side)** — the physical scaled budget `δ_k·g_k`
  IS the graded low-mode budget at the reindexed scale. -/
  budget_eq : ∀ k, δ k * g k = gradedBudget (afr.w (idx k)) N₀ (sl.traj.hZ (idx k))

/-- **THE MERGE LEMMA — `hlocalize ⇒ hbridge`.**  Given the trajectory↔graded
dictionary `S`, the trajectory shift control `hbridge : shift_k ≤ δ_k·g_k` follows
from the graded spectral-localization input `sl.hlocalize` by rewriting both sides
through the dictionary.  This collapses the two un-merged fields of
`SpectralMarginInput` onto the SINGLE open datum `hlocalize`. -/
theorem hbridge_of_hlocalize {afr : AFRateModulus} {N₀ : Nat}
    {sl : SpectralLocalization afr N₀} (S : ScaledBulkShift afr N₀ sl) (k : Nat) :
    S.shift k ≤ S.δ k * S.g k := by
  rw [S.shift_eq k, S.budget_eq k]
  exact sl.hlocalize (S.idx k)

/-- **THE MERGE, packaged as the full `hbridge` field.**  A `ScaledBulkShift`
supplies the entire `hbridge : ∀ k, shift_k ≤ δ_k·g_k` sequence from `hlocalize`,
i.e. the datum a `SpectralMarginInput` needs for its `hbridge` field is now DERIVED,
not assumed — leaving `sl.hlocalize` (plus the dictionary equalities) as the sole
residual. -/
theorem hbridge_of_scaledBulkShift {afr : AFRateModulus} {N₀ : Nat}
    {sl : SpectralLocalization afr N₀} (S : ScaledBulkShift afr N₀ sl) :
    ∀ k, S.shift k ≤ S.δ k * S.g k :=
  fun k => hbridge_of_hlocalize S k

/-! ## 4. The honest ledger (English)

  1. Three Stage-2 continuum-gap reduction arrows (#1 Balaban codynamic gap,
     #2 defect-gap recursion, #3 asymptotic-descent margin recursion) were
     phrased on three carriers but consume ONE scaled bulk eigenvalue-shift datum.

  2. `SpectralMarginInput` unifies them: it discharges #3's `recursion` via the
     converter `margin_recursion_of_eigShift`, carries `sl` for #1, and — via the
     new `toDefectGapRecursion` glue (§1) — discharges #2's degradation recursion
     with the byte-identical converter call, supplying the product floor from the
     summable tower.

  3. `stage2_convergence` (§2) assembles all three floors from the single input;
     every component is a proved lemma.

  4. The scaled shift sits as TWO un-merged fields (`hbridge`, `sl.hlocalize`).
     `ScaledBulkShift` (§3) names the trajectory↔graded dictionary, and
     `hbridge_of_hlocalize` DERIVES `hbridge` from `hlocalize` — collapsing to the
     SINGLE residual `hlocalize` (the p≥2 discrete SU(2)-fusion local-CLT /
     `LineSumLogConcaveCR` w-monotonicity), modulo the honest dictionary equalities.

No 4D inhabitant of `SpectralMarginInput` / `ScaledBulkShift` is exhibited; the
Clay mass gap remains OPEN.  This module contributes the PROVED assembly (#1–#3
convergence) and the PROVED merge lemma; nothing is faked. -/

end YMGap.Continuum.Stage2ConvergesToMargin

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Stage2ConvergesToMargin.prodPrefix_nonneg
#print axioms YMGap.Continuum.Stage2ConvergesToMargin.toDefectGapRecursion
#print axioms YMGap.Continuum.Stage2ConvergesToMargin.defectGap_physGap_pos
#print axioms YMGap.Continuum.Stage2ConvergesToMargin.stage2_convergence
#print axioms YMGap.Continuum.Stage2ConvergesToMargin.stage2_prodFloor_pos
#print axioms YMGap.Continuum.Stage2ConvergesToMargin.hbridge_of_hlocalize
#print axioms YMGap.Continuum.Stage2ConvergesToMargin.hbridge_of_scaledBulkShift
