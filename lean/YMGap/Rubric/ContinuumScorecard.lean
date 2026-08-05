/-
The CONTINUUM SCORECARD — the honest two-input reduction of the OPEN continuum
half of the Clay rubric, wired to the already-proved pieces of this development.

# What this module is (read first — and the HONEST scope)

`Rubric/ClayScorecard.lean` machine-checks the FIXED-SPACING half of the Clay
rubric (`clay_fixed_spacing_met : ClayFixedSpacingMet`, PROVED) and carries the
FULL `ClayTarget` with NO inhabitant.  This module sharpens the OPEN half: after a
long arc of work, the continuum (`a → 0`) obligation has been reduced to a SHORT,
NAMED list of inputs, and every PROVED piece that feeds it is wired here in one
place.  The shape recorded is:

    continuum target  =  {one discrete SU(2) heat-kernel-fusion local-CLT}
                       (FUNCTIONAL formulation: OS0–OS4 + GNS reconstruction,
                        measure-free — see `FunctionalContinuumTarget`)

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
    canonical finite localization into the physical block-power law remains a
    named downstream bridge.

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

/-! ## 1. The PROVED fixed-spacing line (re-exported, UNCONDITIONAL) -/

/-- **The fixed-spacing rubric line is MET (PROVED).**  Re-export of
`ClayScorecard.clay_fixed_spacing_met`: every fixed-spacing rubric clause is
genuinely inhabited by a real theorem about a SPECIFIC Yang–Mills object. -/
theorem fixed_spacing_met : ClayFixedSpacingMet :=
  clay_fixed_spacing_met

/-! ## 2. PROVED pieces of the continuum reconstruction (re-exported) -/

/-- **OS2 / reflection positivity, UNCONDITIONAL.**  The all-order, all-real-`c`
reflection Schwinger form of the SU(2) heat-kernel functional is `≥ 0` for every
Euclidean time `t ≥ 0` (`ReflectionPositivity.reflectionPositiveSchwinger_holds`).
The analytic heart of OS reconstruction, with no open input. -/
theorem os2_reflection_positive_wired (t : Q') (ht : (0 : Q') ≤ t) :
    ReflectionPositivity.ReflectionPositiveSchwinger t ht :=
  ReflectionPositivity.reflectionPositiveSchwinger_holds t ht

/-- **The reconstructed mass gap on the COMPLETE GNS Hilbert space.**  From ANY
located transfer-operator `SpectralGapData` on a complete constructive GNS Hilbert
space, extract the strictly-positive eigenvalue-gap margin `Δ = 1 − sep > 0`
together with the geometric two-point decay `G(n) ≤ G(0)·sepⁿ`
(`mass_gap_of_spectralGap`).  The genuine spacing-uniform such datum is itself the
open continuum input; the extraction is PROVED. -/
theorem reconstructed_mass_gap_wired {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, SpectralGap.corr G.model n
        ≤ (SpectralGap.corr G.model 0) * G.gap.sep ^ n :=
  mass_gap_of_spectralGap G

/-! ## 3. Input A — the discrete SU(2) heat-kernel-fusion local-CLT

The genuinely-open continuum content, after the whole δ-loop, is ONE discrete
statement: the vacuum-normalized `p`-fold SU(2) heat-kernel fusion coefficient
matches the Gaussian to quadratic order uniformly in `s` (equivalently,
`s = 1`-dominance of the vacuum-normalized bond-moved spectrum for the genuine 4D
exponent `p = b^{d−1} ≥ 2`).  It is carried as the wiring datum
`DeltaToBlockPower`, whose sole non-trivial content is that residual; once supplied,
the δ-loop bundle BUILDS the physical-RG input and the physical continuum gap
floor. -/

/-- **Input A — the discrete SU(2) heat-kernel-fusion local-CLT** (the single
remaining discrete statement), packaged as the δ-residual → block-power wiring
datum. -/
abbrev DiscreteFusionLocalCLT (b N : Nat) (w : Q') (p : Nat) : Type :=
  DeltaFrontierLedger.DeltaToBlockPower b N w p

/-- **Input A ⇒ the PHYSICAL spacing-uniform continuum gap floor is positive.**
Given the discrete-fusion residual datum, the physical gap carries a
strictly-positive spacing-uniform floor at every scale of the genuine `a → 0`
block schedule (`DeltaFrontierLedger.deltaFrontier_continuum_floor_pos`). -/
theorem discreteFusion_gives_physical_continuum_floor
    {b N : Nat} {w : Q'} {p : Nat} (D : DiscreteFusionLocalCLT b N w p) :
    (0 : Q') < (DeltaFrontierLedger.deltaFrontier_continuum_gap D).floor :=
  DeltaFrontierLedger.deltaFrontier_continuum_floor_pos D

/-- **The physical-RG self-similar route to the same floor.**  Routed through the
named `PhysicalRGInput` (the physical separators obey the self-similar geometric
law), the physical continuum gap floor is strictly positive
(`physicalRG_continuum_floor_pos`).  The `selfSimilar` field is the open dynamical
input; the implication is PROVED. -/
theorem physicalRG_gives_continuum_floor (P : PhysicalRGInput) :
    (0 : Q') < (physicalRG_continuum_gap P).floor :=
  physicalRG_continuum_floor_pos P

/-! ## 4. The OPTIONAL cited-classical Minlos σ-additive lift (NOT a target field) -/

/-- **The cited-classical continuum-MEASURE (Minlos) lift — an OPTIONAL corollary
object, NOT a required continuum-target input.**  The token for the `a → 0`
σ-additive MEASURE existence / tightness (defect recursion + loopy correlator
residual + a tightness modulus), discharged classically in the external GFF
formalization by Bochner–Minlos + Daniell–Kolmogorov.  Since the continuum target
is now the positive Schwinger FUNCTIONAL (`FunctionalContinuumTarget`, OS0–OS4 +
GNS, measure-free = the Jaffe–Witten requirement), σ-additivity is optional
downstream packaging: `FunctionalContinuumTarget.minlos_is_optional_corollary`
shows this object's only genuinely-new datum beyond Sub-wall A/B is the σ-additive
`tightnessRate`.  Aliased from `ClayScorecard.ClayContinuumExistence`; retained as
the optional-corollary object, UNINHABITED here. -/
abbrev CitedMinlosLift : Type := ClayContinuumExistence

/-! ## 5. The (one-discrete-input, functional) continuum reduction (DELIBERATELY
UNINHABITED) -/

/-- **THE CONTINUUM TARGET, REDUCED TO ONE NAMED DISCRETE INPUT (FUNCTIONAL
FORMULATION).**  Bundles the PROVED fixed-spacing line (`ClayFixedSpacingMet`)
together with the single open discrete continuum input: the discrete SU(2)
heat-kernel-fusion local-CLT (Input A).

**ARCHITECTURAL NOTE (Minlos removed as a required input).**  The σ-additive
Bochner–Minlos lift (`CitedMinlosLift`) is NO LONGER a required field of the
continuum target.  The Jaffe–Witten / Osterwalder–Schrader requirement is a
condition on the POSITIVE LINEAR FUNCTIONAL (the Schwinger functional), not on a
σ-additive measure; that functional formulation is carried by
`Continuum.FunctionalContinuumTarget.FunctionalContinuumTarget` (the measure-free
continuum-existence object: OS0–OS4 clauses + GNS reconstruction, with the open
`a → 0` modulus).  `CitedMinlosLift`'s dynamical content is Sub-wall B's
`DefectGapRecursion` and its correlator content is Sub-wall A's
`LoopyCorrelatorResidual`; its ONLY genuinely-new datum is the σ-additive tightness
modulus — an OPTIONAL classical corollary DOWNSTREAM of the functional target
(`FunctionalContinuumTarget.minlos_is_optional_corollary`), NOT a Jaffe–Witten
input.

**There is no inhabitant of this structure in this file, by design.**  Supplying
the discrete input WITHOUT `sorry` / `axiom` / `Prop := True` — i.e. proving the
`p ≥ 2` discrete fusion local-CLT (and, functionally, the open `a → 0` modulus of
`FunctionalContinuumTarget`) — is exactly the open continuum Clay Yang–Mills
mass-gap problem.  The fixed-spacing field is the only one already proved
(`fixed_spacing_met`). -/
structure ContinuumTargetReduction (b N : Nat) (w : Q') (p : Nat) : Type where
  /-- PROVED — the fixed-spacing rubric line (`clay_fixed_spacing_met`). -/
  fixedSpacing : ClayFixedSpacingMet
  /-- OPEN Input A — the discrete SU(2) heat-kernel-fusion local-CLT (`p ≥ 2`). -/
  discreteFusion : DiscreteFusionLocalCLT b N w p

/-- **The fixed-spacing half of any reduction is the PROVED line** — independent of
the open discrete input. -/
theorem reduction_fixedSpacing_proved {b N : Nat} {w : Q'} {p : Nat}
    (red : ContinuumTargetReduction b N w p) : ClayFixedSpacingMet :=
  red.fixedSpacing

/-- **GIVEN the reduction, the physical spacing-uniform continuum gap floor is
positive.**  The conditional payoff: from the discrete-fusion input carried by the
reduction, the physical continuum mass gap floor is strictly positive at every
scale of the genuine `a → 0` block schedule.  (The reduction is NOT inhabited; this
is the honest "Input A ⇒ continuum floor" wire.) -/
theorem reduction_physical_continuum_floor_pos {b N : Nat} {w : Q'} {p : Nat}
    (red : ContinuumTargetReduction b N w p) :
    (0 : Q') < (DeltaFrontierLedger.deltaFrontier_continuum_gap red.discreteFusion).floor :=
  DeltaFrontierLedger.deltaFrontier_continuum_floor_pos red.discreteFusion

/-! ## 6. Documentation: PROVED vs OPEN (AGENTS.md Rule 6)

PROVED (UNCONDITIONAL, re-exported real theorems):

  * `fixed_spacing_met`                  ⟸ `ClayScorecard.clay_fixed_spacing_met`
      (the whole fixed-spacing rubric line about SPECIFIC YM objects);
  * `os2_reflection_positive_wired`      ⟸ `reflectionPositiveSchwinger_holds`
      (OS2, all orders / all real `c` / every `t ≥ 0`);
  * `reconstructed_mass_gap_wired`       ⟸ `mass_gap_of_spectralGap`
      (positive `Δ` + geometric decay on the complete GNS Hilbert space).

PROVED (CONDITIONAL — Input A ⇒ continuum floor):

  * `discreteFusion_gives_physical_continuum_floor`,
    `physicalRG_gives_continuum_floor`,
    `reduction_physical_continuum_floor_pos`.

OPEN (NAMED, NO inhabitant in this file):

  * Input A — `DiscreteFusionLocalCLT` (= legacy `DeltaToBlockPower`): the `p ≥ 2`
    discrete SU(2) heat-kernel-fusion local-CLT plus block-power bridge.  The
    canonical DAG field is the corrected finite `CanonicalBulkControl`; no
    equivalence with the historical bare carrier is claimed;
  * (functionally) the `a → 0` uniform modulus of
    `FunctionalContinuumTarget.ScalingLimitModulus` + the OS0/OS4 clauses.

NOT a frontier atom (DELETED as an over-requirement):

  * `CitedMinlosLift` (= `ClayContinuumExistence`): the cited-classical σ-additive
    Minlos / Daniell–Kolmogorov continuum-MEASURE extension.  The Jaffe–Witten
    requirement is functional (OS0–OS4 on the Schwinger functional + GNS), so
    σ-additivity is optional downstream packaging; `CitedMinlosLift`'s only
    genuinely-new content is the σ-additive `tightnessRate`
    (`FunctionalContinuumTarget.minlos_is_optional_corollary`).

  ⟹ `ContinuumTargetReduction`  [DELIBERATELY UNINHABITED — the open continuum
  Clay problem].

The picture this module records: the fixed-spacing Clay rubric is PROVED and the
OS / GNS reconstruction pieces are PROVED; the continuum (`a → 0`) target is stated
FUNCTIONALLY (`FunctionalContinuumTarget`: OS0–OS4 + GNS, measure-free) and reduced
to the single discrete SU(2) fusion local-CLT plus the open `a → 0` functional
modulus.  The σ-additive Minlos lift is removed as an atom (optional classical
corollary).  Inhabiting the open inputs is the open continuum Yang–Mills mass-gap
problem; nothing here claims to have done so. -/

end YMGap.Rubric.ContinuumScorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ContinuumScorecard.fixed_spacing_met
#print axioms YMGap.Rubric.ContinuumScorecard.os2_reflection_positive_wired
#print axioms YMGap.Rubric.ContinuumScorecard.reconstructed_mass_gap_wired
#print axioms YMGap.Rubric.ContinuumScorecard.discreteFusion_gives_physical_continuum_floor
#print axioms YMGap.Rubric.ContinuumScorecard.physicalRG_gives_continuum_floor
#print axioms YMGap.Rubric.ContinuumScorecard.reduction_fixedSpacing_proved
#print axioms YMGap.Rubric.ContinuumScorecard.reduction_physical_continuum_floor_pos
