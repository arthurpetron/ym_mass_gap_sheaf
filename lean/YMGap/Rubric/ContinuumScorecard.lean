/-
The LEGACY CONTINUUM-SURROGATE SCORECARD.

This module records implications among previously defined fixed-spacing,
heat-kernel-fusion, and finite spectral-gap surrogates.  In particular,
`ContinuumTargetReduction` contains exactly two fields, `fixedSpacing` and
`discreteFusion`.  It does not contain a two-parameter Wilson-functional limit,
a common reflected positive-time carrier, a physical OS quotient, a `C0`
semigroup, its generator, or a theorem identifying the generator's spectral
edge.  It is therefore not a reduction of the full Clay problem.

The unconditional declarations below are still genuine Lean theorems, but their
mathematical scope is narrower than their historical names suggest:

  * `fixed_spacing_met` re-exports the legacy `ClayFixedSpacingMet` aggregate;
  * `os2_reflection_positive_wired` is a cutoff heat-kernel reflection-positivity
    precursor, not positivity of a pinned continuum functional on a canonical
    half-space algebra;
  * `reconstructed_mass_gap_wired` is the formal consequence of supplying an
    abstract `SpectralGapData` to the older complete-GNS model.  It neither
    constructs that datum from Yang--Mills nor pins it to a continuum generator;
  * the `*_continuum_floor` theorems derive the scalar floor encoded by the named
    fusion/RG surrogate inputs.  They do not construct a physical mass gap.

with all the constructive pieces in between PROVED and re-exported.  The
σ-additive Bochner–Minlos lift is NO LONGER a required continuum input (it was an
OS-over-requirement): OS0–OS4 are conditions on the Schwinger FUNCTIONAL and OS
reconstruction is functional-analytic (GNS), so σ-additivity is optional downstream
packaging.  `CitedMinlosLift` is retained below only as that OPTIONAL classical
corollary object, not as a frontier atom.

# The proved pieces wired here (each a real theorem, NOT `True`)

  * `fixed_spacing_met` — the entire fixed-spacing rubric line
    (`ClayScorecard.clay_fixed_spacing_met`): positive spectral gap, geometric
    clustering, nontriviality, OS2 reflection positivity, positive infinite-volume
    mass — all about SPECIFIC Yang–Mills objects, UNCONDITIONAL.
  * `os2_reflection_positive_wired` — OS2 / reflection positivity, all orders, all
    real coefficient vectors, every Euclidean time `t ≥ 0`, UNCONDITIONAL
    (`ReflectionPositivity.reflectionPositiveSchwinger_holds`; the analytic heart).
  * `reconstructed_mass_gap_wired` — on the genuine constructive COMPLETE GNS
    Hilbert space, ANY located transfer-operator gap yields a strictly-positive
    mass gap `Δ = 1 − sep > 0` with geometric two-point decay `G(n) ≤ G(0)·sepⁿ`
    (`mass_gap_of_spectralGap`).
  * `discreteFusion_gives_physical_continuum_floor` — GIVEN the single discrete
    residual (Input A, below) the PHYSICAL spacing-uniform continuum gap floor is
    strictly positive at every scale of the genuine `a → 0` block schedule
    (`DeltaFrontierLedger.deltaFrontier_continuum_floor_pos`).
  * `physicalRG_gives_continuum_floor` — the equivalent statement routed through
    the physical-RG self-similar law (`physicalRG_continuum_floor_pos`).

# The remaining open input (NAMED, NO inhabitant), + the deleted Minlos atom

  * **Input A — the discrete SU(2) heat-kernel-fusion local-CLT.**  Carried as the
    wiring datum `DeltaFrontierLedger.DeltaToBlockPower`, whose sole non-trivial
    content is the historical vacuum-normalized bulk eigenvalue-shift control
    (`SpectralLocalizationCrux.SpectralLocalization`, `bulk_shift ≤ 1/12`) for the
    genuine 4D bond-moving exponent `p = b^{d−1} ≥ 2`, together with the block-power
    bridge `residualToPower`.  PROVED at `p = 1` and for `s = 1`; OPEN at `p ≥ 2`
    (the weighted fusion-multiplicity monotonicity tier).  Once supplied, the whole
    δ-loop fires and the physical continuum gap floor is positive.

    The canonical `FrontierDAG.bulkCtrl` field has since been reviewed and
    repointed to `CanonicalBulkControl N w p`, whose analytic input is the
    corrected finite re-based family `s ≤ 2*N`.  This legacy `DeltaToBlockPower`
    route is not silently identified with that corrected carrier; transporting
    canonical finite localization into the physical block-power law is now
    routed explicitly by `CanonicalBulkBlockPowerTransport`: the route reaches
    `PhysicalRGInput` and a positive `CRealFloor`, conditional on the single named
    physical identification `localizationToPower`.  That identification remains
    open for the genuine four-dimensional blocking map.

  * **(DELETED as an atom) — the cited-classical Minlos σ-additive lift.**  Carried
    as the token `ClayScorecard.ClayContinuumExistence` (= `CitedMinlosLift`): the
    `a → 0` MEASURE existence / tightness (defect recursion, loopy correlator
    residual, a tightness modulus).  The continuum target is now stated on the
    positive Schwinger FUNCTIONAL (`FunctionalContinuumTarget`, OS0–OS4 + GNS,
    measure-free), which is the Jaffe–Witten requirement.  Minlos's dynamical
    content (`defectRecursion`) = Sub-wall B's `DefectGapRecursion` and its
    correlator content (`loopyResidual`) = Sub-wall A's `LoopyCorrelatorResidual`,
    both already counted; its ONLY genuinely-new datum is the σ-additive
    `tightnessRate`, an OPTIONAL Bochner–Minlos packaging DOWNSTREAM of the
    functional target (`FunctionalContinuumTarget.minlos_is_optional_corollary`),
    NOT an OS / Jaffe–Witten input.  `CitedMinlosLift` is retained as that optional
    corollary object; it is no longer a required target field.

# Honesty (AGENTS.md Rules 1, 6, 8)

`ContinuumTargetReduction` bundles the PROVED fixed-spacing line together with the
one open discrete input; it is provided with **NO inhabitant**.  Inhabiting it —
i.e. supplying the `p ≥ 2` discrete local-CLT (and, functionally, the open `a → 0`
modulus of `FunctionalContinuumTarget`) WITHOUT `sorry` / `axiom` / `Prop := True`
— is exactly the open continuum Clay problem.
The conditional theorems (`reduction_*`) take the bundle as a hypothesis; the
unconditional ones re-export already-proved facts.  Every carrier is `Type`-level
data; each load-bearing declaration is `#print axioms`-gated (permitted: `propext`
/ `Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no custom
`axiom`.  Underclaim: the Clay problem remains OPEN.
-/

import YMGap.Continuum.DeltaFrontierLedger
import YMGap.Continuum.OSAxioms
import YMGap.Continuum.GNSDynamics
import YMGap.Rubric.ClayScorecard

namespace YMGap.Rubric.ContinuumScorecard

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Rubric.ClayScorecard

/-! ## 1. The proved legacy fixed-spacing aggregate (re-exported) -/

/-- Re-export of `ClayScorecard.clay_fixed_spacing_met`.  This inhabits the
fields of the legacy `ClayFixedSpacingMet` surrogate; it is not, by itself, a
fixed-spacing construction of the canonical physical Yang--Mills theory. -/
theorem fixed_spacing_met : ClayFixedSpacingMet :=
  clay_fixed_spacing_met

/-! ## 2. Proved implications in the legacy reconstruction route -/

/-- A cutoff heat-kernel reflection-positivity theorem for the named Schwinger
form.  This is a useful OS2 precursor, but it is not yet positivity of one pinned
continuum Wilson functional on the canonical reflected half-space carrier. -/
theorem os2_reflection_positive_wired (t : Q') (ht : (0 : Q') ≤ t) :
    ReflectionPositivity.ReflectionPositiveSchwinger t ht :=
  ReflectionPositivity.reflectionPositiveSchwinger_holds t ht

/-- From a supplied `SpectralGapData` on the older complete-GNS model, extract
the encoded margin `Δ = 1 - sep > 0` and its geometric correlator inequality.
The theorem is an abstract projection from that datum; it does not construct a
physical transfer operator, continuum semigroup, generator, or spectral edge. -/
theorem reconstructed_mass_gap_wired {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, SpectralGap.corr G.model n
        ≤ (SpectralGap.corr G.model 0) * G.gap.sep ^ n :=
  mass_gap_of_spectralGap G

/-! ## 3. A historical quantitative input: discrete heat-kernel fusion

The datum below packages the vacuum-normalized `p`-fold SU(2) heat-kernel fusion
estimate used by the older delta-loop route.  It is a substantive discrete
subproblem, but it is not an exhaustive encoding of continuum existence or of
the canonical OS reconstruction. -/

/-- The discrete SU(2) heat-kernel-fusion local-CLT surrogate, packaged as the
delta-residual-to-block-power wiring datum. -/
abbrev DiscreteFusionLocalCLT (b N : Nat) (w : Q') (p : Nat) : Type :=
  DeltaFrontierLedger.DeltaToBlockPower b N w p

/-- Given the discrete-fusion datum, the scalar continuum-gap surrogate defined
in `DeltaFrontierLedger` has a positive encoded floor.  This conclusion is only
about that surrogate and is not a physical generator mass-gap theorem. -/
theorem discreteFusion_gives_physical_continuum_floor
    {b N : Nat} {w : Q'} {p : Nat} (D : DiscreteFusionLocalCLT b N w p) :
    (0 : Q') < (DeltaFrontierLedger.deltaFrontier_continuum_gap D).floor :=
  DeltaFrontierLedger.deltaFrontier_continuum_floor_pos D

/-- The analogous scalar-floor implication from the historically named
`PhysicalRGInput`.  Its `selfSimilar` field is assumed; the result does not build
the canonical continuum time evolution. -/
theorem physicalRG_gives_continuum_floor (P : PhysicalRGInput) :
    (0 : Q') < (physicalRG_continuum_gap P).floor :=
  physicalRG_continuum_floor_pos P

/-! ## 4. Optional sigma-additive measure packaging -/

/-- A legacy token for a sigma-additive Bochner--Minlos-style lift.  Such a lift
can be useful downstream measure packaging, but it is not required to formulate
the Schwinger functional or the canonical reflected OS root.  It is retained for
compatibility and is not inhabited here. -/
abbrev CitedMinlosLift : Type := ClayContinuumExistence

/-! ## 5. The legacy two-field reduction record (uninhabited here) -/

/-- Bundles the legacy `ClayFixedSpacingMet` aggregate with one discrete-fusion
datum.  These are literally the record's only fields.  In particular this type
does not assert a common continuum functional, reflected half-space quotient,
strongly continuous time semigroup, generator, or generator spectral gap.

There is no inhabitant in this file.  Supplying one would solve the discrete
subproblem encoded here, not the additional canonical reconstruction and
continuum-identification obligations. -/
structure ContinuumTargetReduction (b N : Nat) (w : Q') (p : Nat) : Type where
  /-- The proved legacy fixed-spacing aggregate. -/
  fixedSpacing : ClayFixedSpacingMet
  /-- The discrete SU(2) heat-kernel-fusion datum. -/
  discreteFusion : DiscreteFusionLocalCLT b N w p

/-- Projects the proved legacy fixed-spacing field, independently of the
discrete-fusion field. -/
theorem reduction_fixedSpacing_proved {b N : Nat} {w : Q'} {p : Nat}
    (red : ContinuumTargetReduction b N w p) : ClayFixedSpacingMet :=
  red.fixedSpacing

/-- Projects the positive scalar floor already implied by the reduction's
discrete-fusion field.  This is a theorem about the legacy gap-floor surrogate,
not about the spectrum of a continuum Hamiltonian. -/
theorem reduction_physical_continuum_floor_pos {b N : Nat} {w : Q'} {p : Nat}
    (red : ContinuumTargetReduction b N w p) :
    (0 : Q') < (DeltaFrontierLedger.deltaFrontier_continuum_gap red.discreteFusion).floor :=
  DeltaFrontierLedger.deltaFrontier_continuum_floor_pos red.discreteFusion

/-! ## 6. Documentation: proved surrogate implications and missing prerequisites

PROVED (unconditional statements at their literal declared types):

  * `fixed_spacing_met`                  ⟸ `ClayScorecard.clay_fixed_spacing_met`
      (the legacy fixed-spacing aggregate);
  * `os2_reflection_positive_wired`      ⟸ `reflectionPositiveSchwinger_holds`
      (cutoff heat-kernel reflection-positivity precursor);
  * `reconstructed_mass_gap_wired`       ⟸ `mass_gap_of_spectralGap`
      (projection from supplied abstract spectral-gap data).

PROVED (conditional implications to the encoded scalar floor):

  * `discreteFusion_gives_physical_continuum_floor`,
    `physicalRG_gives_continuum_floor`,
    `reduction_physical_continuum_floor_pos`.

HISTORICAL RESIDUALS (named, no inhabitant in this file):

  * Input A — `DiscreteFusionLocalCLT` (= legacy `DeltaToBlockPower`): the `p ≥ 2`
    discrete SU(2) heat-kernel-fusion local-CLT plus block-power bridge.  The
    canonical DAG field is the corrected finite `CanonicalBulkControl`; no
    equivalence with the historical bare carrier is claimed;
  * (functionally) the `a → 0` uniform modulus of
    `FunctionalContinuumTarget.ScalingLimitModulus` + the OS0/OS4 clauses.

OPTIONAL PACKAGING (not an OS prerequisite):

  * `CitedMinlosLift` (= `ClayContinuumExistence`): the cited-classical σ-additive
    Minlos / Daniell–Kolmogorov continuum-MEASURE extension.  The Jaffe–Witten
    requirement may be stated at the level of a Schwinger functional, so
    sigma-additivity is optional downstream packaging.

  ⟹ `ContinuumTargetReduction`  [UNINHABITED HERE — a legacy two-field bundle].

The picture this module records: the fixed-spacing surrogate rubric and several
abstract OS/GNS algebraic components are proved.  The legacy
`FunctionalContinuumTarget` (OS0--OS4 + ordinary GNS, measure-free) is not the
standard physical positive-time OS reconstruction: its predicates are not yet
pinned to one two-parameter Wilson limit, reflected half-space quotient,
semigroup, or generator.  The discrete SU(2) fusion local-CLT and scaling
modulus remain open quantitative inputs, while the canonical reconstruction is
an additional open prerequisite.  The sigma-additive Minlos lift remains an
optional classical corollary; nothing here claims the continuum Clay target. -/

end YMGap.Rubric.ContinuumScorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ContinuumScorecard.fixed_spacing_met
#print axioms YMGap.Rubric.ContinuumScorecard.os2_reflection_positive_wired
#print axioms YMGap.Rubric.ContinuumScorecard.reconstructed_mass_gap_wired
#print axioms YMGap.Rubric.ContinuumScorecard.discreteFusion_gives_physical_continuum_floor
#print axioms YMGap.Rubric.ContinuumScorecard.physicalRG_gives_continuum_floor
#print axioms YMGap.Rubric.ContinuumScorecard.reduction_fixedSpacing_proved
#print axioms YMGap.Rubric.ContinuumScorecard.reduction_physical_continuum_floor_pos
