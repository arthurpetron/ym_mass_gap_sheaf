/-
Track B / R2 — **INSTALLING the proved `hadd` theorem into `SpectralMarginInput`
via a constructor, eliminating `hadd` as an independent open field.**

# What this module does (read first)

`AsymptoticSpectralLoc.SpectralMarginInput` carries an `hadd` field — the
located-2nd-eigenvalue ↔ physical-margin dictionary

    g_k − shift_k ≤ g_{k+1},        g_k := `Q'.divPos (floorRate_k) (a_k)`.

Two separate files already exist but NO file imports both:

  * `AsymptoticSpectralLoc` DEFINES `SpectralMarginInput` (the `hadd` field);
  * `SpectralMarginBridge` PROVES `hadd` as a `Q'`/`Nat` theorem
    (`EdgeLocalizationResidual.hadd`) from strictly-sharper named content
    (`hEdge`, `hFR`, and node ① `bulk_shift` bundled inside `L`).

This module is the missing WIRING seam: it imports both and authors

  * **`spectralMarginInput_of_edgeLocalization`** — the constructor that installs
    the PROVED `EdgeLocalizationResidual.hadd R` verbatim into the `hadd` field
    (with `spacing := fun _ => R.spacing`,
    `shift := fun k => divPos ((R.L k).shift 1) R.spacing`).  The `hadd` field
    reduces DEFINITIONALLY to `R.hadd`, so no unification work is needed.  `hadd`
    stops being an independent atom of Sub-wall B: it becomes a theorem of
    `{hEdge, hFR, node ①}`.

  * **`continuum_floor_pos_of_edgeLocalization`** — the end-to-end payoff: the
    constructed input's strictly-positive spacing-uniform continuum physical-gap
    floor, with BOTH `recursion` (via `AsymptoticSpectralLoc`) and `hadd` (via
    `SpectralMarginBridge`) discharged, leaving only `hbridge` (node ①) and the
    graded `sl.hlocalize` as the named Type-level residuals.

# Honest scope

Nothing here conjures the gap.  The constructor still CONSUMES an
`EdgeLocalizationResidual R` (NOT inhabited on ℝ⁴ — its `L k` still carries the
open `bulk_shift` = node ①), an `hbridge_atom` hypothesis (= node ①, the
trajectory form), and the graded `sl`, tower `T`, and physical
ceiling/anchor data.  It manufactures NO new inhabitant of any frontier type; it
only relocates the already-proved `hadd` into the field where it is consumed.  The
net ledger effect: Sub-wall B drops from 3 atoms `{hadd, hbridge, sl.hlocalize}`
to 2 `{hbridge, sl.hlocalize}`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure structure plumbing over the proved `SpectralMarginBridge` /
`AsymptoticSpectralLoc` lemmas; every carrier is `Type`-level data.  Each
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`,
no custom `axiom`.
-/

import YMGap.Continuum.AsymptoticSpectralLoc
import YMGap.Continuum.SpectralMarginBridge

namespace YMGap.Continuum.HaddDischarge

open YMGap.Constructive
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.SpectralMarginBridge
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.FullModeAssembly

/-! ## The wiring constructor -/

/-- **THE CONSTRUCTOR (the wiring seam).**  Assemble a `SpectralMarginInput` from

  * an `EdgeLocalizationResidual R` — carries the RG weight trajectory `w`, the
    per-scale spectral-localization certificates `L` (each still carrying the OPEN
    `bulk_shift` = node ①), the edge identification `hEdge`, the fixed physical
    spacing, and the floor-rate dictionary `hFR`.  Its `EdgeLocalizationResidual.hadd`
    is the PROVED `hadd` theorem;
  * the graded spectral-localization datum `sl`, the summable-defect tower `T`, and
    the stack-collapse identification `hδ` (all feeding the `recursion`/`hbridge`
    side);
  * the physical ceiling `ceilConst`/`physCeil` and UV anchor `anchor`/`anchor_pos`/
    `anchor_le` (verbatim schedule data);
  * `hbridge_atom` — the shift control `shift_k ≤ δ_k · g_k` (= node ①, trajectory
    form).

The `hadd` field is installed by `R.hadd` and reduces to it DEFINITIONALLY under
`spacing := fun _ => R.spacing`, `shift := fun k => divPos ((R.L k).shift 1) …`.

NOT an unconditional inhabitant: it consumes `R` (uninhabited on ℝ⁴) and
`hbridge_atom` (node ①).  It only relocates the already-proved `hadd`. -/
def spectralMarginInput_of_edgeLocalization
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (R : EdgeLocalizationResidual)
    (sl : GradedBondMovingBudget.SpectralLocalization afr N₀)
    (T : AFDeltaDecay.SummableDescentTower b)
    (hδ : ∀ k, T.δ k =
      (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl).d
        (k + fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl)))
    (ceilConst : Q')
    (physCeil : ∀ j,
      Q'.divPos ((R.atSpacing j).floorRate) R.spacing R.spacing_pos ≤ ceilConst)
    (anchor : Q')
    (anchor_pos : (0 : Q') < anchor)
    (anchor_le : anchor ≤
      Q'.divPos ((R.atSpacing 0).floorRate) R.spacing R.spacing_pos)
    (hbridge_atom : ∀ k,
      Q'.divPos ((R.L k).shift 1) R.spacing R.spacing_pos
        ≤ T.δ k * Q'.divPos ((R.atSpacing k).floorRate) R.spacing R.spacing_pos) :
    SpectralMarginInput b afr N₀ where
  sl := sl
  T := T
  hδ := hδ
  spacing := fun _ => R.spacing
  spacing_pos := fun _ => R.spacing_pos
  atSpacing := R.atSpacing
  ceilConst := ceilConst
  physCeil := physCeil
  anchor := anchor
  anchor_pos := anchor_pos
  anchor_le := anchor_le
  shift := fun k => Q'.divPos ((R.L k).shift 1) R.spacing R.spacing_pos
  hadd := R.hadd
  hbridge := hbridge_atom

/-- The `hadd` field of the constructed input is DEFINITIONALLY the proved
`EdgeLocalizationResidual.hadd R` — witnessing that no independent `hadd` atom
survives. -/
theorem hadd_is_installed
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (R : EdgeLocalizationResidual)
    (sl : GradedBondMovingBudget.SpectralLocalization afr N₀)
    (T : AFDeltaDecay.SummableDescentTower b)
    (hδ : ∀ k, T.δ k =
      (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl).d
        (k + fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl)))
    (ceilConst : Q')
    (physCeil : ∀ j,
      Q'.divPos ((R.atSpacing j).floorRate) R.spacing R.spacing_pos ≤ ceilConst)
    (anchor : Q')
    (anchor_pos : (0 : Q') < anchor)
    (anchor_le : anchor ≤
      Q'.divPos ((R.atSpacing 0).floorRate) R.spacing R.spacing_pos)
    (hbridge_atom : ∀ k,
      Q'.divPos ((R.L k).shift 1) R.spacing R.spacing_pos
        ≤ T.δ k * Q'.divPos ((R.atSpacing k).floorRate) R.spacing R.spacing_pos) :
    (spectralMarginInput_of_edgeLocalization R sl T hδ ceilConst physCeil
        anchor anchor_pos anchor_le hbridge_atom).hadd = R.hadd :=
  rfl

/-! ## The end-to-end payoff -/

/-- **THE CONTINUUM PHYSICAL-GAP FLOOR IS STRICTLY POSITIVE — with `hadd`
DISCHARGED.**  Composing the wiring constructor with
`SpectralMarginInput.continuum_floor_pos`: from an `EdgeLocalizationResidual` plus
the graded/tower/ceiling/anchor data and node-① `hbridge_atom`, the strictly
positive spacing-uniform continuum physical-gap floor surviving `a → 0` holds, with
BOTH `recursion` and `hadd` proved (not assumed). -/
theorem continuum_floor_pos_of_edgeLocalization
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (R : EdgeLocalizationResidual)
    (sl : GradedBondMovingBudget.SpectralLocalization afr N₀)
    (T : AFDeltaDecay.SummableDescentTower b)
    (hδ : ∀ k, T.δ k =
      (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl).d
        (k + fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl)))
    (ceilConst : Q')
    (physCeil : ∀ j,
      Q'.divPos ((R.atSpacing j).floorRate) R.spacing R.spacing_pos ≤ ceilConst)
    (anchor : Q')
    (anchor_pos : (0 : Q') < anchor)
    (anchor_le : anchor ≤
      Q'.divPos ((R.atSpacing 0).floorRate) R.spacing R.spacing_pos)
    (hbridge_atom : ∀ k,
      Q'.divPos ((R.L k).shift 1) R.spacing R.spacing_pos
        ≤ T.δ k * Q'.divPos ((R.atSpacing k).floorRate) R.spacing R.spacing_pos) :
    (0 : Q') <
      (RGGapPersistence.toScalingBand
        (spectralMarginInput_of_edgeLocalization R sl T hδ ceilConst physCeil
            anchor anchor_pos anchor_le hbridge_atom).toAsymptotic.toUniform).physGapMin :=
  (spectralMarginInput_of_edgeLocalization R sl T hδ ceilConst physCeil
      anchor anchor_pos anchor_le hbridge_atom).continuum_floor_pos

end YMGap.Continuum.HaddDischarge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HaddDischarge.spectralMarginInput_of_edgeLocalization
#print axioms YMGap.Continuum.HaddDischarge.hadd_is_installed
#print axioms YMGap.Continuum.HaddDischarge.continuum_floor_pos_of_edgeLocalization
