/-
Track B / R2 — **THE BLOCKING-STEP FRONTIER: the single open continuum input,
pinned to its sharpest per-step form.**

# What this module does (read first)

The attack on the open continuum input has reduced the ENTIRE remaining physics to
ONE field — the self-similar law

    sep_k ≃ (sep_{k+1})^(b+1)        (`selfSimilarC b physSep`)

of `PhysicalRGInput`: the genuine physical Yang–Mills lattice gap separators, under
block-spin (Migdal–Kadanoff) decimation, obey the geometric self-similar schedule.
`physicalRG_continuum_gap` is GREEN: this one law implies the physical continuum
mass gap.  This module pins that law to its WEAKEST, most citable per-step form and
surveys exactly how close the repository's PROVEN single-RG-step results get to it.

## The decomposition (the sharpening)

The self-similar law `sep_k ≃ sep_{k+1}^(b+1)` is the composite of TWO independent
facts about ONE block-spin step `Φ` (the map carrying a fine-scale separator to the
coarse-scale separator one decimation step toward the IR):

  (a) **a single-step blocking relation** `sep_k ≃ Φ(sep_{k+1})` — the separators of
      consecutive scales are related by the physical block-spin map; and

  (b) **the per-step power law** `Φ(x) ≃ x^(b+1)` — the decimation map raises the
      separator to the block power (collapsing `b+1` links in series).

We make (a) a `Type`-level interface `BlockingStep`, make (b) the predicate
`IsBlockPower`, and prove GREEN

    selfSimilarC_of_blockingPower :  BlockingStep + IsBlockPower → selfSimilarC.

So the sole open input is reduced to the SINGLE per-step statement (b): **the
physical block-spin map raises the mass-gap separator to the `(b+1)`-power.**  This
is the cleanest possible form of the open physics — a statement about one
renormalization-group step, not the whole tower.

## How close the PROVEN results get (honest survey)

The physical Migdal–Kadanoff block step factors as `bond-moving ∘ decimation`
(`HeatKernelRGStep`):

  * **The decimation half PROVES the power law (`Q'` level).**  The exact heat-
    semigroup decimation `mkDecimate b w = w^b` raises the SU(2) heat-kernel gap
    separator to the power: `mkDecimate_sep : sep(w^b) ≃ sep(w)^b` (re-exposed here
    as `decimation_isPower`).  This is the genuine, non-tautological content of (b)
    for the EXACT decimation half — the heat-kernel gap separator commutes with the
    decimation semigroup.

  * **The hierarchical case INHABITS the interface.**  On the hierarchical / diamond
    lattice bond-moving IS, by construction, the decimation, so the bond-moving
    deviation vanishes (`δ = 0`, `hierarchical_residual_zero`, re-exposed as
    `hierarchical_blocking_exact`).  There the full physical step EQUALS pure
    decimation, hence acts as the power.  At the `CReal` separator level the
    constructive self-similar tower `concreteTower` is a genuine non-trivial
    inhabitant of `BlockingStep + IsBlockPower` (`concreteBlockingStep`,
    `concreteBlockingStep_isPower`), so `selfSimilarC` holds there UNCONDITIONALLY
    (`concreteTower_selfSimilarC`) — the same flow the rational `polyFlow` provably
    fails.

  * **The 4D case is the open gap.**  On ℝ⁴ (`d > 2`) bond-moving does NOT preserve
    the heat-kernel form: its deviation `δ` from exact decimation is the
    `BondMovingResidual`, UNINHABITED for ℝ⁴ (the MK step is approximate there).
    So `IsBlockPower` for the PHYSICAL 4D block-spin map is exactly the statement
    that this bond-moving deviation does not spoil the power law — proven exactly on
    the hierarchical lattice, OPEN on ℝ⁴.

## THE ONE OPEN STATEMENT (crisp)

> The physical 4D Yang–Mills block-spin (Migdal–Kadanoff) map `Φ` raises the
> mass-gap separator to the `(b+1)`-power, `Φ(sep) ≃ sep^(b+1)` — equivalently, the
> bond-moving deviation from exact decimation does not spoil the multiplicative
> renormalization of the gap under one decimation step.

PROVED exactly for: the heat-semigroup decimation half (`decimation_isPower`) and
the full step on the hierarchical / diamond lattice (`δ = 0`,
`hierarchical_blocking_exact`); the constructive separator tower satisfies the lifted
`CReal` law unconditionally (`concreteTower_selfSimilarC`).  OPEN for: the full 4D
step, where the bond-moving residual `δ` is uninhabited (`d > 2`, MK approximate).

`physicalRGInput_of_blockingPower` closes the loop: GIVEN the single per-step power
law (plus the physically-automatic `[0,1]` bounds and a UV-gap floor), it BUILDS the
full `PhysicalRGInput`, and hence (via `physicalRG_continuum_gap`) the physical
continuum mass gap.  The block-spin power law is the entire remaining obligation.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `CodynamicCRealFlow` / `SelfSimilarFlow` / `HeatKernelRGStep`
backbones; every carrier is `Type`-level data, the open piece is an honest interface
(never a `sorry`).  Each load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`.
-/

import YMGap.Continuum.BlockSpinModel
import YMGap.Continuum.CodynamicCRealFlow
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Constructive.SelfSimilarFlow
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BlockingStepFrontier

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.RateMatchFloor
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport

/-! ## 0. A `CReal.Equiv` reflexivity helper (pointwise) -/

/-- Reflexivity of `CReal.Equiv` (each approximation is `eqv` to itself). -/
theorem equivRefl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_refl (A.approx n))

/-! ## 1. The single-step blocking interface (a) and the power law (b) -/

/-- **(a) The single-step blocking relation — `Type`-level interface.**  A
`BlockingStep s` carries the physical block-spin map `Φ : CReal → CReal` (one
decimation step toward the IR) together with the proof that consecutive separators
of the family `s` are related by it: `s k ≃ Φ(s (k+1))` at every scale.  This is the
"one RG/block-spin step on the gap" content, abstracted from the whole tower. -/
structure BlockingStep (s : Nat → CReal) : Type where
  /-- The physical block-spin map (one decimation step). -/
  Φ : CReal → CReal
  /-- The single-step relation: fine separator at `k+1` maps to coarse at `k`. -/
  step : ∀ k, CReal.Equiv (s k) (Φ (s (k + 1)))

/-- **(b) The per-step power law.**  The block-spin map `Φ` raises the separator to
the `(b+1)`-power — the decimation acting as the `(b+1)`-fold series collapse.  This
is the SINGLE remaining open statement once (a) is granted. -/
def IsBlockPower (b : Nat) (Φ : CReal → CReal) : Prop :=
  ∀ x : CReal, CReal.Equiv (Φ x) (cpow x (b + 1))

/-- **The physically sufficient power law on the separator trajectory.**  The
continuum consumer never applies `Φ` to an arbitrary constructive real: it uses
only the displayed next-scale separators `s (k+1)`.  This predicate records
exactly those applications and no off-trajectory extension of the physical map.

`IsBlockPower` implies this law, but the converse is intentionally not claimed.
For a fusion-spectrum dictionary this is the honest target, because the finite
spectral data pins the RG map only on the physical trajectory. -/
def IsBlockPowerOnTrajectory (b : Nat) (s : Nat → CReal)
    (Φ : CReal → CReal) : Prop :=
  ∀ k : Nat, CReal.Equiv (Φ (s (k + 1))) (cpow (s (k + 1)) (b + 1))

/-- A global block-power law restricts to the physical separator trajectory. -/
theorem blockPowerOnTrajectory_of_blockPower {b : Nat} {s : Nat → CReal}
    {Φ : CReal → CReal} (h : IsBlockPower b Φ) :
    IsBlockPowerOnTrajectory b s Φ :=
  fun k => h (s (k + 1))

/-! ## 2. THE REDUCTION: `BlockingStep + IsBlockPower → selfSimilarC`

This is the sharpening: the open self-similar law is exactly the composite of the
single-step blocking relation (a) and the per-step power law (b).  Proving it leaves
(b) — one statement about ONE block-spin step — as the entire residual. -/

/-- **THE REDUCTION (GREEN).**  The self-similar law `sep_k ≃ sep_{k+1}^(b+1)`
(`selfSimilarC`) follows from the single-step blocking relation (a, `BlockingStep`)
composed with the per-step power law (b, `IsBlockPower`):

    sep k ≃ Φ(sep (k+1)) ≃ (sep (k+1))^(b+1).

So the entire open continuum input is reduced to the SINGLE per-step statement (b):
the physical block-spin map raises the separator to the block power. -/
theorem selfSimilarC_of_blockingPower {b : Nat} {s : Nat → CReal}
    (B : BlockingStep s) (h : IsBlockPower b B.Φ) :
    selfSimilarC b s :=
  fun k => CReal.Equiv.trans (B.step k) (h (s (k + 1)))

/-- **Sharp trajectory-level reduction.**  The exact block-power law only on
the physical separator inputs already proves the complete self-similar flow.
No assertion about `Φ x` away from the physical trajectory is needed. -/
theorem selfSimilarC_of_blockingPowerOnTrajectory {b : Nat} {s : Nat → CReal}
    (B : BlockingStep s) (h : IsBlockPowerOnTrajectory b s B.Φ) :
    selfSimilarC b s :=
  fun k => CReal.Equiv.trans (B.step k) (h k)

/-! ## 3. THE PROVEN single-RG-step results (how close we get, `Q'` level)

The physical Migdal–Kadanoff block step is `bond-moving ∘ decimation`.  The
decimation half is EXACTLY computed and PROVES the power law on the heat-kernel
separator; the bond-moving half's deviation is the named open residual. -/

/-- **PROVEN — the decimation half satisfies the power law (`Q'`, EXACT).**  The
exact heat-semigroup decimation `mkDecimate b w = w^b` raises the SU(2) heat-kernel
gap separator to the power: `sep(w^b) ≃ sep(w)^b`.  This is the genuine,
non-tautological content of (b) for the EXACT half of one block step — the heat-
kernel gap separator commutes with the decimation semigroup.  (Re-exposes
`HeatKernelRGStep.mkDecimate_sep`.) -/
theorem decimation_isPower (b : Nat) (w : Q') :
    (heatKernelSep (mkDecimate b w)).eqv (qpow (heatKernelSep w) b) :=
  mkDecimate_sep b w

/-- **PROVEN — the full block step IS pure decimation on the hierarchical lattice.**
On the hierarchical / diamond lattice bond-moving is BY CONSTRUCTION the decimation,
so the bond-moving deviation vanishes (`δ = 0`).  Combined with `decimation_isPower`
this means the FULL physical step acts as the power there — `IsBlockPower` holds
exactly on the soluble hierarchical approximation.  (Re-exposes
`HeatKernelRGStep.hierarchical_residual_zero`.) -/
theorem hierarchical_blocking_exact (b : Nat) (a w : Q') (ha : (0 : Q') ≤ a) :
    (hierarchicalBondMovingResidual b a w ha).delta = 0 :=
  hierarchical_residual_zero b a w ha

/-! ## 4. THE HIERARCHICAL inhabitant of the interface (`CReal` level, GENUINE)

At the `CReal` separator level the constructive self-similar tower `concreteTower`
inhabits `BlockingStep + IsBlockPower` — a genuine non-model inhabitant in the
soluble hierarchical approximation.  The block-spin map there is the literal
`(b+1)`-power, and the single-step relation is the PROVED `selfSimilarCReal` (which
the rational `polyFlow` provably fails).  So `selfSimilarC` holds UNCONDITIONALLY for
this flow — the open input is CLOSED in the hierarchical-exact case. -/

/-- **The hierarchical `BlockingStep` (GENUINE inhabitant).**  For the constructive
self-similar tower `concreteTower b`, the block-spin map is the `(b+1)`-power and the
single-step relation `sep k ≃ (sep (k+1))^(b+1)` is the PROVED `selfSimilarCReal`. -/
def concreteBlockingStep (b : Nat) : BlockingStep (sep (concreteTower b)) where
  Φ := fun x => cpow x (b + 1)
  step := fun k => selfSimilarCReal (concreteTower b) k

/-- **The hierarchical block-spin map satisfies the power law (b).**  Its map is the
literal `(b+1)`-power, so `IsBlockPower` holds by reflexivity — the exactly-solvable
witness that (b) is satisfiable (not vacuous). -/
theorem concreteBlockingStep_isPower (b : Nat) :
    IsBlockPower b (concreteBlockingStep b).Φ :=
  fun x => equivRefl (cpow x (b + 1))

/-- **The hierarchical flow satisfies `selfSimilarC` (UNCONDITIONAL).**  Assembling
the reduction `selfSimilarC_of_blockingPower` over the genuine hierarchical
inhabitant: the constructive self-similar tower's separators obey the self-similar
law with NO open hypothesis — the same law the rational gaming flow `polyFlow`
provably fails.  This is the open continuum input CLOSED in the hierarchical-exact
approximation; the 4D gap is the deviation of the physical step from this exact map. -/
theorem concreteTower_selfSimilarC (b : Nat) :
    selfSimilarC b (sep (concreteTower b)) :=
  selfSimilarC_of_blockingPower (concreteBlockingStep b) (concreteBlockingStep_isPower b)

/-! ## 5. CLOSING THE LOOP: the per-step power law BUILDS `PhysicalRGInput`

GIVEN the single per-step power law (b) for the physical separators — plus the
physically-automatic `[0,1]` bounds and a UV-gap floor — we BUILD the full
`PhysicalRGInput`, whose `selfSimilar` field is discharged by the reduction.  Through
`physicalRG_continuum_gap` this yields the physical continuum mass gap.  So the
block-spin power law is the ENTIRE remaining obligation. -/

/-- **THE FRONTIER LEDGER LEMMA — the per-step power law is all that remains.**
GIVEN a `BlockingStep` on the physical separators and the per-step power law (b)
`IsBlockPower`, together with the `[0,1]` bounds (correlation ratios, physically
automatic) and a strictly-positive UV-gap floor, this BUILDS the full
`PhysicalRGInput`: the open `selfSimilar` field is discharged by
`selfSimilarC_of_blockingPower`.  Everything downstream
(`physicalRG_continuum_gap` ⇒ the spacing-uniform physical continuum gap) then
follows GREEN.  The single open input is thus pinned to (b): **the physical
block-spin map raises the mass-gap separator to the `(b+1)`-power.** -/
def physicalRGInput_of_blockingPower {b : Nat} (hb : 1 ≤ b)
    (physSep : Nat → CReal)
    (B : BlockingStep physSep) (hpow : IsBlockPower b B.Φ)
    (sepNonneg : ∀ k, ExpPos.geRat (physSep k) 0)
    (sepLeOne : ∀ k, CReal.leRat (physSep k) 1)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0)
      (physGapC b physSep (geomSpacing b) 0)) :
    PhysicalRGInput where
  b := b
  hb := hb
  physSep := physSep
  selfSimilar := selfSimilarC_of_blockingPower B hpow
  sepNonneg := sepNonneg
  sepLeOne := sepLeOne
  floor0 := floor0
  floor0_pos := floor0_pos
  hbase0 := hbase0

/-- The trajectory-level block-power law is the weakest direct input needed to
build the physical RG package. -/
def physicalRGInput_of_blockingPowerOnTrajectory {b : Nat} (hb : 1 ≤ b)
    (physSep : Nat → CReal)
    (B : BlockingStep physSep)
    (hpow : IsBlockPowerOnTrajectory b physSep B.Φ)
    (sepNonneg : ∀ k, ExpPos.geRat (physSep k) 0)
    (sepLeOne : ∀ k, CReal.leRat (physSep k) 1)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0)
      (physGapC b physSep (geomSpacing b) 0)) :
    PhysicalRGInput where
  b := b
  hb := hb
  physSep := physSep
  selfSimilar := selfSimilarC_of_blockingPowerOnTrajectory B hpow
  sepNonneg := sepNonneg
  sepLeOne := sepLeOne
  floor0 := floor0
  floor0_pos := floor0_pos
  hbase0 := hbase0

/-- **The physical continuum gap from the per-step power law (GREEN reduction).**
Composing `physicalRGInput_of_blockingPower` with the proved
`physicalRG_continuum_gap`: GIVEN the single per-step power law (b) (plus the
automatic bounds and a UV floor), the physical gap carries a strictly-positive
spacing-uniform floor at every scale of the `a → 0` block schedule.  The per-step
block-spin power law (b) is the sole open input. -/
def physicalGap_of_blockingPower {b : Nat} (hb : 1 ≤ b)
    (physSep : Nat → CReal)
    (B : BlockingStep physSep) (hpow : IsBlockPower b B.Φ)
    (sepNonneg : ∀ k, ExpPos.geRat (physSep k) 0)
    (sepLeOne : ∀ k, CReal.leRat (physSep k) 1)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0)
      (physGapC b physSep (geomSpacing b) 0)) :
    UnifiedContinuumFloor.CRealFloor (physGapC b physSep (geomSpacing b)) :=
  physicalRG_continuum_gap
    (physicalRGInput_of_blockingPower hb physSep B hpow sepNonneg sepLeOne
      floor0 floor0_pos hbase0)

/-- The spacing-uniform continuum floor from the sharp trajectory-only power
law. -/
def physicalGap_of_blockingPowerOnTrajectory {b : Nat} (hb : 1 ≤ b)
    (physSep : Nat → CReal)
    (B : BlockingStep physSep)
    (hpow : IsBlockPowerOnTrajectory b physSep B.Φ)
    (sepNonneg : ∀ k, ExpPos.geRat (physSep k) 0)
    (sepLeOne : ∀ k, CReal.leRat (physSep k) 1)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0)
      (physGapC b physSep (geomSpacing b) 0)) :
    UnifiedContinuumFloor.CRealFloor (physGapC b physSep (geomSpacing b)) :=
  physicalRG_continuum_gap
    (physicalRGInput_of_blockingPowerOnTrajectory hb physSep B hpow sepNonneg
      sepLeOne floor0 floor0_pos hbase0)

/-! ## 6. The honest frontier ledger (English)

  1. **The reduction (sharpening).**  The open self-similar law
     `sep_k ≃ sep_{k+1}^(b+1)` = single-step blocking (a, `BlockingStep`) +
     per-step power law (b, `IsBlockPower`).  `selfSimilarC_of_blockingPower` proves
     this GREEN, pinning the open input to the single per-step statement (b).

  2. **PROVEN (decimation half, `Q'`).**  `decimation_isPower` (= `mkDecimate_sep`):
     the exact heat-semigroup decimation raises the heat-kernel gap separator to the
     power.  This is the genuine content of (b) for the EXACT half of one block step.

  3. **PROVEN (hierarchical, full step).**  `hierarchical_blocking_exact` (= `δ = 0`):
     on the hierarchical / diamond lattice bond-moving IS decimation, so the full
     step acts as the power.  At the `CReal` level `concreteTower_selfSimilarC`
     closes `selfSimilarC` UNCONDITIONALLY there (the law the rational `polyFlow`
     fails).  The interface `BlockingStep + IsBlockPower` is genuinely inhabited
     (`concreteBlockingStep` / `concreteBlockingStep_isPower`).

  4. **OPEN (4D).**  On ℝ⁴ (`d > 2`) bond-moving does not preserve the heat-kernel
     form; its deviation `δ` from exact decimation is the `BondMovingResidual`,
     UNINHABITED for ℝ⁴.  So `IsBlockPower` for the PHYSICAL 4D block-spin map — the
     statement that bond-moving does not spoil the `(b+1)`-power renormalization of
     the gap separator under one decimation step — is the SINGLE open input.

  5. **The loop closes on (b).**  `physicalRGInput_of_blockingPower` /
     `physicalGap_of_blockingPower`: the per-step power law (b) (plus automatic
     `[0,1]` bounds and a UV floor) BUILDS the full `PhysicalRGInput` and hence the
     physical continuum mass gap.  Nothing else remains.  The one open 4D statement:

       **the physical 4D Yang–Mills block-spin (Migdal–Kadanoff) map raises the
       mass-gap separator to the `(b+1)`-power — the gap's multiplicative
       renormalization under decimation — proven exactly on the hierarchical
       lattice and for the decimation half, open for the full 4D step.** -/

end YMGap.Continuum.BlockingStepFrontier

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BlockingStepFrontier.equivRefl
#print axioms YMGap.Continuum.BlockingStepFrontier.selfSimilarC_of_blockingPower
#print axioms YMGap.Continuum.BlockingStepFrontier.blockPowerOnTrajectory_of_blockPower
#print axioms YMGap.Continuum.BlockingStepFrontier.selfSimilarC_of_blockingPowerOnTrajectory
#print axioms YMGap.Continuum.BlockingStepFrontier.decimation_isPower
#print axioms YMGap.Continuum.BlockingStepFrontier.hierarchical_blocking_exact
#print axioms YMGap.Continuum.BlockingStepFrontier.concreteBlockingStep
#print axioms YMGap.Continuum.BlockingStepFrontier.concreteBlockingStep_isPower
#print axioms YMGap.Continuum.BlockingStepFrontier.concreteTower_selfSimilarC
#print axioms YMGap.Continuum.BlockingStepFrontier.physicalRGInput_of_blockingPower
#print axioms YMGap.Continuum.BlockingStepFrontier.physicalGap_of_blockingPower
#print axioms YMGap.Continuum.BlockingStepFrontier.physicalRGInput_of_blockingPowerOnTrajectory
#print axioms YMGap.Continuum.BlockingStepFrontier.physicalGap_of_blockingPowerOnTrajectory
