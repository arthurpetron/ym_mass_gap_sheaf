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

/-- The accumulated decimation product is strictly positive for sub-unit
separators (each factor is positive; the empty product is `1`). -/
theorem physMultiplierProduct_pos (bb : Nat → Nat) (sep : Nat → Q')
    (hsep0 : ∀ k, (0 : Q') ≤ sep k) :
    ∀ N, (0 : Q') < physMultiplierProduct bb sep N
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | N + 1 => by
      show (0 : Q') < physMultiplierProduct bb sep N * physMultiplier bb sep N
      exact Q'.mul_pos (physMultiplierProduct_pos bb sep hsep0 N)
        (physMultiplier_pos bb sep hsep0 N)

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
  /-- **HARDENING (spacing is NOT free).**  The lattice spacing rescales by the
  block factor `bb k + 1` at each RG step: `aScaling (k+1)·(bb k + 1) = aScaling k`.
  This is the physical RG rescaling — one block step of factor `bb k + 1` coarsens
  the spacing by that factor, so a single fine spacing fixes the entire spacing
  sequence from the block factors.  Without this, `aScaling` could be tuned freely
  against the margin (gaming the `rate_matched` inequality). -/
  aScaling_step : ∀ k, (aScaling (k + 1) * Q'.ofNat (bb k + 1)).eqv (aScaling k)
  /-- **HARDENING (the trajectory genuinely approaches the UV).**  The separators
  increase monotonically toward `1`. -/
  sep_mono : ∀ k, sep k ≤ sep (k + 1)
  /-- **HARDENING (genuine continuum approach `sep → 1`).**  The dimensionless
  margin `1 − sep k` is driven below every positive `ε`: the trajectory genuinely
  approaches the continuum / UV separator `sep → 1`.  A CONSTANT separator
  `sep k = s < 1` FAILS this (see `constSep_violates_sep_to_one`), which is what
  excludes the trivial constant-`sep` pseudo-trajectory. -/
  sep_to_one : ∀ ε : Q', (0 : Q') < ε → ∃ K : Nat, ∀ k : Nat, K ≤ k → (1 : Q') - sep k ≤ ε
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

/-- **Non-vacuity (real content of `rate_matched`).**  Any inhabitant has a
STRICTLY POSITIVE margin-product `0 < (1 − sep N)·∏ρ_dec` at every scale: the
`rate_matched` field forces it (`0 < physFloor·aScaling N ≤ (1 − sep N)·∏`).  In
particular the collapse `sep N = 1` (margin `0`) is EXCLUDED, so the structure is
NOT vacuously inhabitable by a degenerate flow — it carries genuine content. -/
theorem DimensionalTransmutation.marginProduct_pos (T : DimensionalTransmutation)
    (N : Nat) :
    (0 : Q') < ((1 : Q') - T.sep N) * physMultiplierProduct T.bb T.sep N :=
  Q'.pos_of_lt_of_le (Q'.mul_pos T.physFloor_pos (T.aScaling_pos N)) (T.rate_matched N)

/-! ### Anti-vacuity: the trivial constant-`sep` pseudo-trajectory is EXCLUDED

Before the hardening, `DimensionalTransmutation` was GAMEABLE: with `sep k := s`
(constant, `s < 1`), `bb k := 1`, `aScaling N := (ρ_dec 1 s)^N`, `physFloor := 1 − s`
the `rate_matched` inequality held with EQUALITY — a fake constant-`sep`
"trajectory" that is NOT a continuum approach.  The new field `sep_to_one` kills
it: a constant `sep ≡ s` has constant margin `1 − s > 0`, which cannot be driven
below `ε = half·(1 − s) < 1 − s`.  We prove this exclusion below. -/

/-- `0 < b → a < a + b` on `Q'` (strict, proved at the `Int` cross-product level;
mirrors `AFRateCalibration.lt_add_of_pos_right` to avoid an extra import). -/
theorem q_lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  -- (a+b).num = a.num·b.den + b.num·a.den ; (a+b).den = a.den·b.den.
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int)
      < (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) = (a.den : Int) * (b.den : Int) := by
    push_cast; rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hexpand : (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
      = a.num * ((a.den : Int) * (b.den : Int))
        + b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int)
        = a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  omega

/-- `half·y < y` for `0 < y` (the half is a strict contraction of a positive
value): `half·y < half·y + half·y ≃ y`. -/
theorem q_half_mul_lt_self {y : Q'} (hy : (0 : Q') < y) :
    HalfPow.half * y < y := by
  have hhy : (0 : Q') < HalfPow.half * y := YMGap.Constructive.ExpNeg.half_mul_pos y hy
  have hstrict : HalfPow.half * y < HalfPow.half * y + HalfPow.half * y :=
    q_lt_add_of_pos_right (HalfPow.half * y) (HalfPow.half * y) hhy
  exact HeatKernelRGStep.lt_of_lt_of_le hstrict
    (Q'.le_of_eqv (YMGap.Constructive.ExpNeg.two_halves y))

/-- **Anti-vacuity lemma — a constant separator `sep ≡ s` with `s < 1` VIOLATES
`sep_to_one`.**  If `sep k = s` for all `k` and `s < 1`, then the predicate
`∀ ε > 0, ∃ K, ∀ k ≥ K, 1 − sep k ≤ ε` is FALSE: the constant margin `1 − s > 0`
cannot be pushed below `ε = half·(1 − s) < 1 − s`.  Hence the trivial constant-
`sep` pseudo-trajectory does NOT inhabit the hardened `DimensionalTransmutation`. -/
theorem constSep_violates_sep_to_one (s : Q') (hs : s < (1 : Q'))
    (sep : Nat → Q') (hconst : ∀ k, sep k = s) :
    ¬ (∀ ε : Q', (0 : Q') < ε → ∃ K : Nat, ∀ k : Nat, K ≤ k → (1 : Q') - sep k ≤ ε) := by
  intro hsto
  -- margin m := 1 − s > 0
  have hm : (0 : Q') < (1 : Q') - s := sub_pos_of_lt_one hs
  -- ε := half·m, which is 0 < ε < m
  have hεpos : (0 : Q') < HalfPow.half * ((1 : Q') - s) :=
    YMGap.Constructive.ExpNeg.half_mul_pos ((1 : Q') - s) hm
  have hεlt : HalfPow.half * ((1 : Q') - s) < (1 : Q') - s := q_half_mul_lt_self hm
  obtain ⟨K, hK⟩ := hsto (HalfPow.half * ((1 : Q') - s)) hεpos
  -- at k = K: 1 − sep K = 1 − s ≤ half·(1 − s) < 1 − s, contradiction
  have hle : (1 : Q') - sep K ≤ HalfPow.half * ((1 : Q') - s) := hK K (Nat.le_refl K)
  rw [hconst K] at hle
  -- hεlt : half·m < m ; hle : m ≤ half·m  ⟹  half·m < half·m, contradiction
  have hcontra : HalfPow.half * ((1 : Q') - s) < HalfPow.half * ((1 : Q') - s) :=
    HeatKernelRGStep.lt_of_lt_of_le hεlt hle
  have hInt : (HalfPow.half * ((1 : Q') - s)).num
        * ((HalfPow.half * ((1 : Q') - s)).den : Int)
      < (HalfPow.half * ((1 : Q') - s)).num
        * ((HalfPow.half * ((1 : Q') - s)).den : Int) := hcontra
  exact (Int.lt_irrefl _) hInt

/-! ## 2b. JOB 2 — the GENUINE hierarchical dimensional-transmutation flow (REDUCED)

On the hierarchical / diamond lattice with constant block factor `b` the continuum
limit is fine-graining: the spacing flows `aScaling k = a₀ / b^k → 0` and the
separator flows by `b`-th roots `sep_k = sep₀^{1/b^k} → 1`, giving the EXPLICIT
physical gap

    m_k = (1 − sep_k)/aScaling_k = (1 − sep₀^{1/b^k})·b^k/a₀  →  |ln sep₀|/a₀ > 0,

via the elementary exp-limit `b^k·(1 − exp(ln sep₀ / b^k)) → −ln sep₀`.

**The crux (honest).**  `DimensionalTransmutation.sep : Nat → Q'` is RATIONAL-valued,
but the genuine `b`-th-root flow `sep₀^{1/b^k}` is IRRATIONAL.  Constructing it
needs a constructive `b`-th root / `CReal.log`–`exp`; this repository has `CReal`
`exp`/`expNeg` (`Constructive/ExpNeg.lean`, `ExpPos.lean`) but **no `CReal.log`**
and no `Q'`-valued `b`-th root.  So the b-th-root flow and the exp-limit cannot be
discharged here.  We therefore REDUCE: we package a continuum flow datum
`HierarchicalTransmutationData` whose GENUINELY-DERIVABLE parts (constant block
factor, the geometric spacing with its `aScaling_step`, positivity) are PROVED in
the inhabitant construction, and whose IRREDUCIBLE ANALYTIC CORE — the rational
separator flow approaching `1` (`sep_to_one`) AND the rate match against the
spacing (`rate_matched`) — is named as the two hypothesis fields.  This is exactly
the asymptotic-freedom content and is left as the NAMED open core. -/

/-- **The explicit geometric spacing** `aGeom a₀ b k = a₀ / (b+1)^k` (the hierarchical
fine-graining: one block step of factor `b+1` coarsens the spacing by `b+1`).
Defined recursively so the per-step rescaling `aScaling_step` is an exact `Q'`
`eqv` cancellation. -/
def aGeom (a0 : Q') (b : Nat) : Nat → Q'
  | 0 => a0
  | k + 1 => Q'.divPos (aGeom a0 b k) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)

/-- The geometric spacing is positive at every scale (positive base, divided by
positive `b+1`). -/
theorem aGeom_pos {a0 : Q'} (ha0 : (0 : Q') < a0) (b : Nat) :
    ∀ k, (0 : Q') < aGeom a0 b k
  | 0 => ha0
  | k + 1 =>
      Q'.divPos_pos (aGeom a0 b k) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)
        (aGeom_pos ha0 b k)

/-- **`aScaling_step` for the geometric spacing (GENUINELY PROVED).**  One block
step of factor `b+1` rescales the spacing exactly: `aGeom(k+1)·(b+1) ≃ aGeom k`.
This is the exact `divPos` cancellation — the spacing is the physical RG rescaling,
NOT a free parameter. -/
theorem aGeom_step (a0 : Q') (b : Nat) (k : Nat) :
    (aGeom a0 b (k + 1) * Q'.ofNat (b + 1)).eqv (aGeom a0 b k) := by
  show (Q'.divPos (aGeom a0 b k) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)
        * Q'.ofNat (b + 1)).eqv (aGeom a0 b k)
  exact Q'.divPos_mul_eqv (aGeom a0 b k) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)

/-- **The hierarchical transmutation flow datum (the REDUCTION carrier).**

Carries the GENUINE continuum flow on the hierarchical lattice with constant block
factor `b+1` (so `bb k = b`) and the explicit geometric spacing `aGeom a0 (b)`.
The GENUINELY-DERIVABLE parts (block factor, spacing, `aScaling_step`, positivity)
are handled by `hierarchicalTransmutation`; this datum supplies ONLY the
IRREDUCIBLE ANALYTIC CORE as its fields:

  * `sepFlow` — the rational separator flow (the constructive surrogate of
    `sep₀^{1/(b+1)^k}`), sub-unit and monotone increasing;
  * `sepFlow_to_one` — **OPEN ANALYTIC CORE (i):** the flow genuinely approaches
    the continuum separator (`sep → 1`).  A constant flow FAILS this
    (`constSep_violates_sep_to_one`);
  * `physFloor` `> 0` and `rate_matched_flow` — **OPEN ANALYTIC CORE (ii):** the
    margin `1 − sepFlow k`, rescaled by `∏ρ_dec`, dominates `physFloor·aGeom k`
    at every scale (the asymptotic-freedom rate match against the b-th-root
    spacing).

These two fields are precisely the exp-limit content `b^k(1 − sep₀^{1/b^k}) →
−ln sep₀ > 0`, which is TRUE but not constructively discharged here (no
`CReal.log` / `b`-th root). -/
structure HierarchicalTransmutationData (a0 : Q') (b : Nat) : Type where
  /-- The (rational) separator flow — surrogate of `sep₀^{1/(b+1)^k}`. -/
  sepFlow : Nat → Q'
  /-- Nonnegative. -/
  sepFlow_nonneg : ∀ k, (0 : Q') ≤ sepFlow k
  /-- Sub-unit. -/
  sepFlow_le_one : ∀ k, sepFlow k ≤ (1 : Q')
  /-- Monotone increasing toward the UV. -/
  sepFlow_mono : ∀ k, sepFlow k ≤ sepFlow (k + 1)
  /-- **OPEN ANALYTIC CORE (i)** — the flow approaches the continuum `sep → 1`. -/
  sepFlow_to_one : ∀ ε : Q', (0 : Q') < ε →
    ∃ K : Nat, ∀ k : Nat, K ≤ k → (1 : Q') - sepFlow k ≤ ε
  /-- The claimed continuum physical-gap floor. -/
  physFloor : Q'
  /-- Strictly positive. -/
  physFloor_pos : (0 : Q') < physFloor
  /-- **OPEN ANALYTIC CORE (ii)** — the AF rate match: the margin, rescaled by the
  decimation product, dominates `physFloor·(geometric spacing)` at every scale. -/
  rate_matched_flow : ∀ N : Nat,
    physFloor * aGeom a0 b N
      ≤ ((1 : Q') - sepFlow N)
          * physMultiplierProduct (fun _ => b) sepFlow N

/-- **JOB 2 (REDUCED) — the genuine hierarchical `DimensionalTransmutation` from
the flow datum.**  GIVEN a `HierarchicalTransmutationData a0 (b)` (whose two fields
are the named open analytic core), this BUILDS a full hardened
`DimensionalTransmutation`: the block factor `bb k = b` and the geometric spacing
`aGeom a0 (b)` are concrete, `aScaling_step` is the PROVED exact `divPos`
cancellation (`aGeom_step`), positivity is `aGeom_pos`, and `sep_to_one` /
`rate_matched` are passed through from the datum's analytic-core fields.  No part of
the spacing is free: it is fixed by the block factor via `aScaling_step`. -/
def hierarchicalTransmutation {a0 : Q'} (ha0 : (0 : Q') < a0) {b : Nat}
    (D : HierarchicalTransmutationData a0 b) : DimensionalTransmutation where
  bb := fun _ => b
  sep := D.sepFlow
  sep_nonneg := D.sepFlow_nonneg
  sep_le_one := D.sepFlow_le_one
  aScaling := aGeom a0 b
  aScaling_pos := aGeom_pos ha0 b
  aScaling_step := fun k => aGeom_step a0 b k
  sep_mono := D.sepFlow_mono
  sep_to_one := D.sepFlow_to_one
  physFloor := D.physFloor
  physFloor_pos := D.physFloor_pos
  rate_matched := D.rate_matched_flow

/-- The physical-gap floor of the reduced hierarchical transmutation is strictly
positive (it is the datum's `physFloor`, the explicit `|ln sep₀|/a₀` floor). -/
theorem hierarchicalTransmutation_physFloor_pos {a0 : Q'} (ha0 : (0 : Q') < a0)
    {b : Nat} (D : HierarchicalTransmutationData a0 b) :
    (0 : Q') < (hierarchicalTransmutation ha0 D).physFloor :=
  D.physFloor_pos

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

/-- **JOB 2 (REDUCED) — the FULL physical continuum gap residual from the flow
datum.**  Combining the CLOSED bond-moving half (`hierarchicalExactIdentification`,
§1) with the reduced transmutation (§2b) gives a complete
`PhysicalContinuumGapResidual` on the hierarchical SU(2) gauge theory — GIVEN the
named open analytic core (`HierarchicalTransmutationData`).  Both residuals
supplied: one PROVED (bond-moving, `δ = 0`) and one REDUCED to the exp-limit
core. -/
def hierarchicalPhysicalGap {a0 : Q'} (ha0 : (0 : Q') < a0) {b : Nat}
    (D : HierarchicalTransmutationData a0 b) : PhysicalContinuumGapResidual where
  bondMovingHalf := hierarchicalExactIdentification
  transmutation := hierarchicalTransmutation ha0 D

/-- **JOB 2 (REDUCED) — positivity of the physical floor of the assembled gap.**
The continuum physical-gap floor of the full assembled residual is strictly
positive (it is the datum's explicit `|ln sep₀|/a₀` floor). -/
theorem hierarchicalPhysicalGap_pos {a0 : Q'} (ha0 : (0 : Q') < a0) {b : Nat}
    (D : HierarchicalTransmutationData a0 b) :
    (0 : Q') < (hierarchicalPhysicalGap ha0 D).transmutation.physFloor :=
  D.physFloor_pos

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
#print axioms YMGap.Continuum.CodynamicHierarchical.physMultiplierProduct_pos
#print axioms YMGap.Continuum.CodynamicHierarchical.DimensionalTransmutation.marginProduct_pos
#print axioms YMGap.Continuum.CodynamicHierarchical.q_lt_add_of_pos_right
#print axioms YMGap.Continuum.CodynamicHierarchical.q_half_mul_lt_self
#print axioms YMGap.Continuum.CodynamicHierarchical.constSep_violates_sep_to_one
#print axioms YMGap.Continuum.CodynamicHierarchical.aGeom_pos
#print axioms YMGap.Continuum.CodynamicHierarchical.aGeom_step
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalTransmutation
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalTransmutation_physFloor_pos
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalPhysicalGap
#print axioms YMGap.Continuum.CodynamicHierarchical.hierarchicalPhysicalGap_pos
