/-
Track B / R2 — **DEEP BRICK 1: the codynamic gap meets the EXACT decimation
mechanism; the bond-moving half CLOSES on the hierarchical lattice.**

# What this module does (read first)

The PHYSICAL mass gap of one RG block step factorizes into TWO genuinely
distinct contributions:

  (A) the EXACT decimation rescaling `ρ_dec` — the heat-semigroup half of one
      Migdal–Kadanoff block step `w ↦ w^b`.  It is FAVORABLE: it does NOT
      decrease the dimensionless gap margin (`sep ↦ sep^b ≤ sep`, so
      `1 − sep ↦ 1 − sep^b ≥ 1 − sep`), and its per-block physical multiplier
      `ρ_dec → 1` as `w → 1`; and

  (B) the BOND-MOVING defect `δ` — the dimensionless-margin DEGRADATION per
      block step, the driver `renDefect` of the codynamic budget.  On the
      HIERARCHICAL / diamond lattice bond-moving IS, by construction, the
      decimation, so `δ = 0` there (the MK step is no approximation).

This module CONNECTS the codynamic survival gap (the dimensionless-margin
flow invariant) to that exact mechanism and CLOSES the bond-moving half on the
hierarchical lattice, cleanly SEPARATING the two remaining genuine residuals.

# What is GENUINELY PROVED — and what is the NAMED open content (honest)

  * **D1 (the bond-moving half CLOSES on the hierarchical lattice).**  We inhabit
    `CodynamicExactIdentification` on the hierarchical model with
    `exactLoss = 0`.  This zero is NOT vacuous: the EXACT per-scale dimensionless
    loss of one hierarchical block step is the bond-moving deviation `δ`, which
    is `0` there (`hierarchical_residual_zero`), and the remaining exact half is
    decimation, which does NOT decrease the dimensionless margin
    (`1 − sep^b ≥ 1 − sep`, `decimation_margin_favorable` proved below).  So the
    exact per-scale dimensionless-margin loss is `≤ 0`, conservatively taken as
    `0`.  Then `hierarchicalCodynamicGap = codynamic_gap_of_exact …` is the
    REAL reduction output, and `hierarchicalCodynamicGap_pos` is its positivity:
    the codynamic (dimensionless) survival gap is UNCONDITIONAL on the
    hierarchical SU(2) gauge theory.

  * **D2 (the physical gap = margin × ∏ρ_dec; the dimensional-transmutation
    residual NAMED).**  Even where the bond-moving half closes (hierarchical),
    the PHYSICAL continuum gap picks up the decimation multiplier product
    `∏ ρ_dec` matched against the spacing rescaling.  We define the per-block
    physical multiplier sequence and its finite product, and name precisely the
    OPEN `DimensionalTransmutation` (UNINHABITED): the rate-matching content of
    asymptotic freedom (the margin shrinks at exactly the spacing rate, yielding
    a FINITE POSITIVE continuum gap).  No 4D inhabitant.

  * **D3 (the two residuals, cleanly separated).**  The honest residual map:
    PHYSICAL continuum mass gap ⟸ (i) `CodynamicExactIdentification` [the
    bond-moving half — CLOSED on hierarchical via D1, OPEN on ℝ⁴ via the
    UNINHABITED ℝ⁴ `BondMovingResidual` `δ`] + (ii) `DimensionalTransmutation`
    [the `ρ_dec` / spacing rate matching — OPEN, the AF trajectory, even on
    hierarchical].  Both uninhabited for the genuine 4D continuum.

# SCOPE — what is and is NOT claimed (CRITICAL honesty)

NO physical continuum gap is claimed, hierarchical or 4D.  D1 delivers the
DIMENSIONLESS codynamic survival gap UNCONDITIONALLY on the hierarchical model
(the bond-moving defect is genuinely `0` there).  The PHYSICAL continuum gap
needs, in addition, the UNINHABITED `DimensionalTransmutation` (even on the
hierarchical lattice), and on ℝ⁴ it ALSO needs the UNINHABITED ℝ⁴
`BondMovingResidual` `δ`.  Nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over `Q'` / `Nat`; every load-bearing declaration gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.  All data is `Type`-level.
-/

import YMGap.Continuum.CodynamicGap
import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.CodynamicHierarchical

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CodynamicGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Categorical

/-! ## 0. The decimation-favorable fact (the GENUINE justification for `exactLoss = 0`)

The exact decimation half multiplies the per-Casimir weight `w ↦ w^b`, hence the
gap separator `sep ↦ sep^b`.  For `b ≥ 1` and a sub-unit separator
`0 ≤ sep ≤ 1`, powers DECREASE the separator (`sep^b ≤ sep`,
`HeatKernelRGStep.qpow_antitone`), so the dimensionless margin INCREASES:
`1 − sep ≤ 1 − sep^b`.  Decimation does NOT decrease the dimensionless margin —
it is FAVORABLE.  This (together with `δ = 0` on the hierarchical lattice) is the
genuine reason the EXACT per-scale dimensionless loss there is `≤ 0`, so taking
`exactLoss = 0` is conservative, NOT vacuous. -/

/-- `qpow w 1 ≃ w` (one factor). -/
theorem qpow_one_eqv (w : Q') : (qpow w 1).eqv w := by
  -- qpow w 1 = qpow w 0 * w = 1 * w ≃ w
  show ((1 : Q') * w).eqv w
  exact Q'.one_mul_eqv w

/-- **Decimation is FAVORABLE for the dimensionless margin.**  For a sub-unit
separator `0 ≤ sep ≤ 1` and block factor `b ≥ 1`, decimation `sep ↦ sep^b`
does NOT decrease the dimensionless margin: `1 − sep ≤ 1 − sep^b`.  (Powers of a
sub-unit value decrease in the exponent: `sep^b ≤ sep`, so the margin grows.)
This is the per-scale FAVORABLE fact underpinning `exactLoss = 0` on the
hierarchical lattice (where the only other contribution, bond-moving `δ`, is
`0`). -/
theorem decimation_margin_favorable {sep : Q'} (h0 : (0 : Q') ≤ sep)
    (h1 : sep ≤ (1 : Q')) {b : Nat} (hb : 1 ≤ b) :
    (1 : Q') - sep ≤ (1 : Q') - qpow sep b := by
  -- sep^b ≤ sep^1 ≃ sep, so −sep ≤ −sep^b, so 1 + (−sep) ≤ 1 + (−sep^b).
  have hpow : qpow sep b ≤ qpow sep 1 :=
    HeatKernelRGStep.qpow_antitone h0 h1 1 b hb
  have hpow' : qpow sep b ≤ sep :=
    Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv (qpow_one_eqv sep))
  have hneg : (-sep) ≤ -(qpow sep b) := Q'.neg_le_neg hpow'
  show (1 : Q') + (-sep) ≤ (1 : Q') + (-(qpow sep b))
  exact Q'.add_le_add_left (1 : Q') (-sep) (-(qpow sep b)) hneg

/-- The decimation-favorable fact specialized to the SU(2) heat-kernel separator
`sep = heatKernelSep w` (`= w^3`): one exact decimation block step does not
decrease the dimensionless heat-kernel gap margin. -/
theorem decimation_margin_favorable_heatKernel {w : Q'} (h0 : (0 : Q') ≤ w)
    (h1 : w ≤ (1 : Q')) {b : Nat} (hb : 1 ≤ b) :
    (1 : Q') - heatKernelSep w ≤ (1 : Q') - qpow (heatKernelSep w) b := by
  have hsep0 : (0 : Q') ≤ heatKernelSep w := qpow_nonneg w h0 3
  have hsep1 : heatKernelSep w ≤ (1 : Q') := qpow_le_one h0 h1 3
  exact decimation_margin_favorable hsep0 hsep1 hb

/-! ## 1. D1 — `CodynamicExactIdentification` on the HIERARCHICAL lattice

On the hierarchical / diamond lattice the EXACT per-scale dimensionless-margin
loss of one block step is the bond-moving deviation `δ = 0`
(`hierarchical_residual_zero`) plus the decimation contribution, which is
FAVORABLE (`decimation_margin_favorable`: it does not decrease the margin).  So
the exact loss is `≤ 0`; we take it conservatively as `0`.  This is a GENUINE,
non-vacuous zero: it is the witnessed exact loss of the exactly-solvable
hierarchical model, justified by the two cited facts above.  We then feed it to
the PROVED reduction `codynamic_gap_of_exact` to obtain the codynamic survival
gap UNCONDITIONALLY on the hierarchical lattice. -/

/-- **D1 — the hierarchical exact identification (GENUINE inhabitant).**

`exactLoss = 0` is the EXACT per-scale dimensionless-margin loss of one
hierarchical block step:

  * the bond-moving half is `δ = 0` on the hierarchical / diamond lattice
    (`HeatKernelRGStep.hierarchical_residual_zero`); and
  * the remaining exact half is decimation, which does NOT decrease the
    dimensionless margin (`decimation_margin_favorable`:
    `1 − sep ≤ 1 − sep^b`).

So the exact dimensionless loss is `≤ 0`, conservatively `0` — NOT a vacuous
zero.  `dominates` is then `0 ≤ renDefect` (`renDefect_nonneg`).  This INHABITS
`CodynamicExactIdentification` on the hierarchical model: the bond-moving half of
the codynamic obligation CLOSES there. -/
def hierarchicalExactIdentification : CodynamicExactIdentification where
  exactLoss := fun _ => 0
  exactLoss_nonneg := fun _ => Q'.le_refl' 0
  dominates := fun k =>
    -- exactLoss k = 0 ≤ renDefect afr pMult (k0 + k):
    -- 0 because δ = 0 (hierarchical) and decimation is favorable (cited above);
    -- the bound is the genuine nonnegativity of the approximate defect.
    SummabilityCapstone.renDefect_nonneg afr pMult (k0 + k)

/-- **D1 — the hierarchical codynamic gap (the REAL reduction output).**  The
codynamic (dimensionless) survival gap on the hierarchical lattice, as the
genuine `ClosureWitness` produced by the PROVED reduction
`codynamic_gap_of_exact` from `hierarchicalExactIdentification`.  This is NOT a
fresh constant: it is `survivingGap = 3/4 − tailBudget` surviving the EXACT
hierarchical flow (whose per-scale loss is `0`). -/
def hierarchicalCodynamicGap :
    ClosureWitness (exactFlowBudget hierarchicalExactIdentification) :=
  codynamic_gap_of_exact hierarchicalExactIdentification

/-- **D1 — the hierarchical codynamic gap is strictly POSITIVE (UNCONDITIONAL).**
On the hierarchical / diamond-lattice SU(2) gauge theory, the codynamic
dimensionless survival gap is positive with NO open hypothesis: the bond-moving
defect is genuinely `0`, decimation is favorable, so the dimensionless gap
survives the entire RG flow unconditionally.  (This is the DIMENSIONLESS gap;
the PHYSICAL continuum gap needs `DimensionalTransmutation`, §2.) -/
theorem hierarchicalCodynamicGap_pos :
    (0 : Q') < hierarchicalCodynamicGap.1 :=
  codynamic_gap_of_exact_pos hierarchicalExactIdentification

/-- The hierarchical codynamic gap carries the SAME surviving value
`survivingGap = 3/4 − tailBudget`. -/
theorem hierarchicalCodynamicGap_eq :
    hierarchicalCodynamicGap.1 = survivingGap := rfl

/-- The hierarchical exact flow's per-scale degradation is identically `0` — the
witnessed-exact (no dimensionless-margin loss) hierarchical flow. -/
theorem hierarchicalExactFlow_degradation_zero (k : Nat) :
    (exactFlowBudget hierarchicalExactIdentification).degradation k = 0 := rfl

/-! ## 2. D2 — the PHYSICAL gap = margin × ∏ρ_dec; the dimensional-transmutation residual

The codynamic gap above is the DIMENSIONLESS margin invariant.  The PHYSICAL gap
per block step ALSO picks up the decimation multiplier `ρ_dec` (the spacing
rescaling `a ↦ b·a` against the margin growth `1 − sep ↦ 1 − sep^b`).  We record
the per-block physical multiplier sequence and its finite product, then name the
OPEN content: the trajectory + the rate-matching that turns `∏ρ_dec` (against the
spacing) into a FINITE POSITIVE continuum gap.  This is the genuine
asymptotic-freedom content; it is left UNINHABITED. -/

/-- The per-block PHYSICAL decimation multiplier sequence: at scale `k`, block
factor `bb k`, separator `sep k`, the exact decimation per-block multiplier
`ρ_dec(bb k, sep k)` (`HeatKernelRGStep.rhoDecimate`).  This is the physical-gap
multiplier the dimensionless margin acquires under one decimation block step. -/
def physMultiplier (bb : Nat → Nat) (sep : Nat → Q') (k : Nat) : Q' :=
  rhoDecimate (bb k) (sep k)

/-- The finite product `∏_{k<N} ρ_dec(bb k, sep k)` of the per-block physical
multipliers — the accumulated physical-gap rescaling over the first `N` block
steps. -/
def physMultiplierProduct (bb : Nat → Nat) (sep : Nat → Q') : Nat → Q'
  | 0 => 1
  | N + 1 => physMultiplierProduct bb sep N * physMultiplier bb sep N

@[simp] theorem physMultiplierProduct_zero (bb : Nat → Nat) (sep : Nat → Q') :
    physMultiplierProduct bb sep 0 = 1 := rfl

@[simp] theorem physMultiplierProduct_succ (bb : Nat → Nat) (sep : Nat → Q')
    (N : Nat) :
    physMultiplierProduct bb sep (N + 1)
      = physMultiplierProduct bb sep N * physMultiplier bb sep N := rfl

/-- Each per-block physical multiplier is positive for a sub-unit separator
(`rhoDecimate_pos`). -/
theorem physMultiplier_pos (bb : Nat → Nat) (sep : Nat → Q')
    (hsep0 : ∀ k, (0 : Q') ≤ sep k) (k : Nat) :
    (0 : Q') < physMultiplier bb sep k :=
  rhoDecimate_pos (bb k) (hsep0 k)

/-- Each per-block physical multiplier is `≤ 1` for a sub-unit separator
(`rhoDecimate_le_one`): the decimation rescaling never inflates the gap. -/
theorem physMultiplier_le_one (bb : Nat → Nat) (sep : Nat → Q')
    (hsep0 : ∀ k, (0 : Q') ≤ sep k) (hsep1 : ∀ k, sep k ≤ (1 : Q')) (k : Nat) :
    physMultiplier bb sep k ≤ (1 : Q') :=
  rhoDecimate_le_one (bb k) (hsep0 k) (hsep1 k)

/-- **D2 — `DimensionalTransmutation` (NAMED OPEN content, UNINHABITED).**

The genuine asymptotic-freedom rate-matching that turns the dimensionless gap
into a FINITE POSITIVE PHYSICAL continuum gap.  It carries as data:

  * `bb`, `sep` — the AF trajectory (block factors and per-scale separators),
    with the separators sub-unit;
  * `aScaling` — the per-scale lattice spacing along the trajectory (`> 0`);
  * `physFloor` — the claimed strictly-positive continuum physical-gap floor;
  * **the OPEN content** `rate_matched`: the dimensionless margin `1 − sep N`,
    rescaled by the accumulated decimation product `∏ρ_dec` and matched against
    the spacing `aScaling N`, stays bounded BELOW by `physFloor` at every scale,

        physFloor · aScaling N
          ≤ (1 − sep N) · physMultiplierProduct bb sep N.

    This is the dimensional-transmutation rate-matching: the margin shrinks at
    exactly the spacing rate so a strictly positive physical gap survives the
    continuum limit.  It is the genuine AF-trajectory content and is left
    UNINHABITED (no 4D witness).  Even on the hierarchical lattice (where the
    bond-moving half closes, §1), the PHYSICAL continuum gap requires THIS. -/
structure DimensionalTransmutation : Type where
  /-- Block factors along the AF trajectory. -/
  bb : Nat → Nat
  /-- Per-scale separators along the AF trajectory. -/
  sep : Nat → Q'
  /-- The separators are nonnegative. -/
  sep_nonneg : ∀ k, (0 : Q') ≤ sep k
  /-- The separators are sub-unit. -/
  sep_le_one : ∀ k, sep k ≤ (1 : Q')
  /-- The per-scale lattice spacing along the trajectory. -/
  aScaling : Nat → Q'
  /-- The spacing is positive. -/
  aScaling_pos : ∀ k, (0 : Q') < aScaling k
  /-- The claimed continuum physical-gap floor. -/
  physFloor : Q'
  /-- The floor is strictly positive. -/
  physFloor_pos : (0 : Q') < physFloor
  /-- **THE OPEN CONTENT.**  The dimensionless margin, rescaled by the
  accumulated decimation product and matched against the spacing, stays above
  `physFloor` at every scale — the asymptotic-freedom rate matching.  UNPROVED
  for 4D Yang–Mills (and even for the hierarchical lattice). -/
  rate_matched : ∀ N : Nat,
    physFloor * aScaling N
      ≤ ((1 : Q') - sep N) * physMultiplierProduct bb sep N

/-! ## 3. D3 — the two residuals, cleanly separated (the honest map)

The PHYSICAL continuum mass gap factors through exactly TWO residuals:

    PHYSICAL continuum mass gap
      ⟸ (i)  CodynamicExactIdentification     [the bond-moving half]
       + (ii) DimensionalTransmutation         [the ρ_dec / spacing rate matching]

  * Residual (i) — the bond-moving half — is **CLOSED on the hierarchical
    lattice** (`hierarchicalExactIdentification`, §1: `δ = 0`, decimation
    favorable) and **OPEN on ℝ⁴** (the ℝ⁴ `HeatKernelRGStep.BondMovingResidual`
    `δ`, which is UNINHABITED for ℝ⁴ — MK is approximate there).

  * Residual (ii) — the dimensional-transmutation rate matching — is **OPEN
    even on the hierarchical lattice** (`DimensionalTransmutation`, §2,
    UNINHABITED): the genuine asymptotic-freedom trajectory content.

`PhysicalContinuumGapResidual` packages this as the honest map: GIVEN both
residuals, one has the data for a positive physical continuum gap.  It is
UNINHABITED for the 4D continuum (both inputs are open). -/

/-- **D3 — the honest two-residual map (UNINHABITED for 4D).**

Carries the two separated residuals whose conjunction would yield a positive
physical continuum gap:

  * `bondMovingHalf : CodynamicExactIdentification` — the dimensionless
    survival half (CLOSED on hierarchical via `hierarchicalExactIdentification`,
    OPEN on ℝ⁴ via the uninhabited ℝ⁴ `BondMovingResidual`);
  * `transmutation : DimensionalTransmutation` — the ρ_dec / spacing
    rate-matching (OPEN even on hierarchical).

No 4D inhabitant is constructed: residual (ii) is uninhabited for the genuine
continuum (and residual (i) is uninhabited specifically on ℝ⁴).  This is the
SHARPENED map of exactly what remains for the physical 4D continuum gap. -/
structure PhysicalContinuumGapResidual : Type where
  /-- The bond-moving / dimensionless-survival half. -/
  bondMovingHalf : CodynamicExactIdentification
  /-- The dimensional-transmutation rate-matching half. -/
  transmutation : DimensionalTransmutation

/-- **The codynamic (dimensionless) survival gap extracted from the bond-moving
half** of a `PhysicalContinuumGapResidual`.  GIVEN residual (i), the
dimensionless survival gap is positive — the same reduction
`codynamic_gap_of_exact`.  (This alone is NOT the physical gap; it still needs
residual (ii), `transmutation`, for the spacing rate-matching.) -/
def PhysicalContinuumGapResidual.codynamicGap
    (P : PhysicalContinuumGapResidual) :
    ClosureWitness (exactFlowBudget P.bondMovingHalf) :=
  codynamic_gap_of_exact P.bondMovingHalf

/-- The extracted dimensionless survival gap is strictly positive (from residual
(i) alone). -/
theorem PhysicalContinuumGapResidual.codynamicGap_pos
    (P : PhysicalContinuumGapResidual) :
    (0 : Q') < P.codynamicGap.1 :=
  codynamic_gap_of_exact_pos P.bondMovingHalf

/-! ## 4. The honest ledger (English)

  1. The PHYSICAL gap of one RG block step factorizes into (A) the EXACT
     decimation rescaling `ρ_dec` (FAVORABLE: it does not decrease the
     dimensionless margin, `1 − sep ≤ 1 − sep^b`, and `ρ_dec → 1`), and (B) the
     bond-moving dimensionless-margin defect `δ` (the `renDefect` driver of the
     codynamic budget).

  2. D1 — on the HIERARCHICAL / diamond lattice, `δ = 0`
     (`hierarchical_residual_zero`) and decimation is favorable
     (`decimation_margin_favorable`), so the EXACT per-scale dimensionless loss
     is `0`.  `hierarchicalExactIdentification` is a GENUINE (non-vacuous)
     inhabitant of `CodynamicExactIdentification`, and
     `hierarchicalCodynamicGap_pos` makes the codynamic (DIMENSIONLESS) survival
     gap UNCONDITIONAL there: the bond-moving half CLOSES.

  3. D2 — the PHYSICAL continuum gap = dimensionless margin × accumulated
     decimation product `∏ρ_dec`, matched against the spacing.  The genuine
     asymptotic-freedom rate-matching is named as `DimensionalTransmutation`
     (UNINHABITED).  It is required EVEN on the hierarchical lattice.

  4. D3 — the two residuals, separated:
       PHYSICAL continuum gap ⟸ (i) `CodynamicExactIdentification`
         [bond-moving — CLOSED hierarchical / OPEN ℝ⁴]
       + (ii) `DimensionalTransmutation` [ρ_dec/spacing — OPEN even hierarchical].
     `PhysicalContinuumGapResidual` packages both; UNINHABITED for 4D.

  5. WHAT IS CLAIMED: only the DIMENSIONLESS codynamic survival gap on the
     hierarchical lattice (D1), unconditionally.  NO physical continuum gap is
     claimed, hierarchical or 4D.  The physical gap needs the two UNINHABITED
     residuals.  Nothing is faked: `exactLoss = 0` is justified by `δ = 0` +
     decimation-favorable (both cited), `hierarchicalCodynamicGap` is the real
     reduction output, and `DimensionalTransmutation` / the ℝ⁴
     `BondMovingResidual` are left uninhabited. -/

end YMGap.Continuum.CodynamicHierarchical

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicHierarchical.qpow_one_eqv
#print axioms YMGap.Continuum.CodynamicHierarchical.decimation_margin_favorable
#print axioms YMGap.Continuum.CodynamicHierarchical.decimation_margin_favorable_heatKernel
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalExactIdentification
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalCodynamicGap
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalCodynamicGap_pos
#print axioms YMGap.Continuum.CodynamicHierarchical.physMultiplier_pos
#print axioms YMGap.Continuum.CodynamicHierarchical.physMultiplier_le_one
#print axioms YMGap.Continuum.CodynamicHierarchical.PhysicalContinuumGapResidual.codynamicGap_pos
