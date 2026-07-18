/-
The legacy Clay-inspired scorecard.

This module packages several machine-checked finite character, correlator, and
finite-spectral-model statements.  Its names record the historical route by
which those statements were compared with clauses in the Clay problem; they do
not make the packaged objects the continuum four-dimensional Yang--Mills theory.
In particular:

  * `reconTransfer` and `wilsonG` are named finite/cutoff surrogate models;
  * `ReflectionPositiveSchwinger` is a heat-kernel cutoff precursor to OS2, not
    reflection positivity of the canonical limiting Schwinger functional;
  * positivity of `realContinuumRate` is a scalar correlator-rate statement, not
    a spectral theorem for a reconstructed Hamiltonian;
  * `RubricO4Restoration` is only a weak scalar eventuality; and
  * `RubricUniformInCoupling` is also a weak existential schedule predicate.  It
    has explicit inhabitants elsewhere (for example
    `UniformCouplingFromAF.rubricUniformInCoupling_met` and
    `TwoDYangMillsAdequacy.rubricUniform_trivially_satisfiable`) and therefore is
    not an open four-dimensional mass-gap obligation.

Consequently `ClayFixedSpacingMet` is a proved conjunction of legacy surrogates,
while `ClayTarget` is only a weak compatibility aggregate.  No `ClayTarget` term
is constructed here, but even constructing one would not solve the Clay problem:
the aggregate lacks a pinned compact global gauge group and action, a genuine
two-parameter continuum limit, the reflected positive-time carrier, the full
continuous Euclidean-time semigroup, its self-adjoint generator, and the
physical spectral/non-Wick pins.

The canonical direction is stated in
`Continuum.CanonicalOSRoot.PositiveTimeOSRoot`: ordinary state GNS data are
ambient, whereas the physical Hilbert space must arise from the reflected
half-space form.  Nothing in this file supplies that root for 4D Yang--Mills.

Mathlib-free; pure `Q'` / `Nat` / `CReal`; no `sorry`, hidden axiom, or vacuous
proof is introduced.  The theorems below genuinely establish exactly the
displayed predicates, but those predicates are deliberately described at their
actual surrogate strength.  The Clay Yang--Mills mass-gap problem remains open.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.MayerClustering
import YMGap.Continuum.MultiPlaquetteMayer
import YMGap.Continuum.RealCorrMass
import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.ContinuumClosureProgram

namespace YMGap.Rubric.ClayScorecard

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.MultiPlaquetteMayer
open YMGap.Continuum.RealCorrMass
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.ContinuumClosureProgram

/-! ## 1. Legacy Clay-inspired surrogate clauses

Each predicate is non-vacuous as a statement about its displayed finite or scalar
input.  None by itself identifies that input with the canonical continuum
Yang--Mills theory or with the spectrum of its Hamiltonian. -/

/-- **`RubricSpectralGap` (finite-model analogue of `HasMassGapSpectrum`).**  For a finite
(compact) transfer model `S` carrying a located gap `g`, and a candidate gap
size `Δ : Q'`: `Δ > 0` AND `Δ ≤ g.gapMargin`.  Here `g.gapMargin = 1 − sep`,
the located distance from the top of the EXCITED spectrum (`sep < 1`) up to the
vacuum eigenvalue `1`.  This genuinely constrains the finite model's eigenvalues:
`gapMargin` is computed from `g.sep`, the located second eigenvalue; it is `> 0`
iff `sep < 1`, and a too-large `Δ` makes it false.  It is not, without a
reconstruction and spectral pin, a mass-gap statement for the physical theory. -/
def RubricSpectralGap {S : SpectralModel} (g : LocatedSpectralGap S) (Δ : Q') : Prop :=
  (0 : Q') < Δ ∧ Δ ≤ g.gapMargin

/-- **`RubricClustering` (scalar analogue of `ClusteringProperty` / OS4).**  A connected
correlator `corr : Nat → Q'` exhibits geometric (exponential) clustering: there
are a prefactor `C` and a rate `μ` with `0 ≤ C`, `0 < μ`, `μ < 1`, and
`corr n ≤ C·μ^n` for every separation `n`.  `μ < 1` is the genuine decay
condition (the constructive form of `≤ exp(−C·dist)`, `μ = e^{−mass}`); a
non-decaying correlator (`μ ≥ 1`) does not satisfy it.  The predicate does not
assert that `corr` is a connected correlator of a continuum Yang--Mills field. -/
def RubricClustering (corr : Nat → Q') : Prop :=
  ∃ C μ : Q', (0 : Q') ≤ C ∧ (0 : Q') < μ ∧ μ < (1 : Q') ∧
    ∀ n : Nat, corr n ≤ C * μ ^ n

/-- **`RubricNontrivial` (finite-model nontriviality surrogate).**  The
finite spectral model `S` genuinely has an EXCITED mode: a mode index `i < S.k`
whose spectral weight is strictly positive (`0 < S.w i`).  The constructive
analogue of a vacuum plus one populated mode.  It rules out an empty finite model,
but it neither constructs the physical Hilbert space nor proves non-Wick
interaction of a continuum theory. -/
def RubricNontrivial (S : SpectralModel) : Prop :=
  ∃ i : Nat, i < S.k ∧ (0 : Q') < S.w i

/-- **`RubricReflectionPositive` (heat-kernel cutoff OS2 precursor).**  The all-order reflection
Schwinger form of the named heat-kernel functional at Euclidean time `t > 0` is
nonnegative for EVERY real coefficient vector and every order `N`:
`0 ≤ E(θ(a)*·a)` for `a = Σ c_s χ_s`.  This is the genuine Osterwalder–Seiler
positivity statement (`ReflectionPositivity.ReflectionPositiveSchwinger`), on all
real `c` rather than merely a nonnegative cone.  It is not yet OS2 for the
canonical two-parameter limit on a reflected positive-time algebra. -/
def RubricReflectionPositive (t : Q') (ht : (0 : Q') ≤ t) : Prop :=
  ReflectionPositiveSchwinger t ht

/-- **`RubricInfiniteVolumeMass` (positive scalar-rate surrogate).**
A constructive real `m` is strictly positive: `CReal.IsPositive m`, i.e. bounded
below by a positive `Q'` rational.  This is non-vacuous for the supplied scalar,
but the definition does not connect `m` to a reconstructed generator or its
spectral edge. -/
def RubricInfiniteVolumeMass (m : CReal) : Prop :=
  CReal.IsPositive m

/-! ## 2. Proved clauses about named finite/scalar surrogates

The witness objects are fixed rather than existentially chosen, so the results
are genuine theorems about those named objects.  Their provenance does not turn
them into the canonical continuum theory: `reconTransfer` is a finite spectral
model, `wilsonG` a character/correlator model, the heat-kernel form a cutoff OS2
precursor, and `realContinuumRate` a scalar-rate construction. -/

/-- **Proved finite-model gap.**  For every cutoff `M`, the named finite spectral
model `reconTransfer gw gw_nonneg (M+1)` has located margin
`Δ := 1 − rho gw = 107/108`.  The proof uses `gapMargin_pos` and reflexivity of
the upper bound.  This is a non-vacuous gap in that finite model; no theorem here
identifies its operator or margin with the continuum physical transfer operator
or Hamiltonian spectrum. -/
theorem rubric_gap_met (M : Nat) :
    RubricSpectralGap (reconTransfer_located_gap M) ((1 : Q') - rho gw) :=
  ⟨(reconTransfer_located_gap M).gapMargin_pos,
   Q'.le_refl' ((1 : Q') - rho gw)⟩

/-- **Proved character-correlator decay.**  For every cutoff `M`, the named
character-double-sum sequence `wilsonG gw (M+1)` obeys the displayed geometric
bound with `C := ofNat M · rho gw` and `μ := rho gw < 1`, by
`WilsonConnCorr.wilsonG_decay`.  This is not an existential toy witness, but it
also is not yet pinned as a connected correlator of the canonical limiting
Yang--Mills functional. -/
theorem rubric_clustering_met (M : Nat) :
    RubricClustering (fun n => wilsonG gw (M + 1) n) := by
  refine ⟨Q'.ofNat M * rho gw, rho gw, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ C = ofNat M · rho gw
    exact Q'.mul_nonneg _ _ (YMGap.Continuum.ClusterCount.ofNat_nonneg M)
      (rho_nonneg gw_nonneg)
  · -- 0 < μ = rho gw  (= coeffW gw 1 = 2·(1/6)³ > 0)
    show (0 : Q') < rho gw
    have := coeffW_gw_pos 0
    simpa using this
  · -- μ = rho gw < 1  (strong coupling)
    exact rho_lt_one gw_nonneg (by decide)
  · -- The named character-correlator bound `wilsonG_decay`.
    intro n
    exact wilsonG_decay gw_nonneg (by decide) M n

/-- **Proved finite-model nontriviality.**  For every `M`, the finite model
`reconTransfer gw gw_nonneg (M+1)` has the positive mode weight
`coeffW gw 1 > 0`.  This supplies `RubricNontrivial` for that model, but a
positive finite spectral weight does not prove existence or non-Wick interaction
of the continuum Yang--Mills theory. -/
theorem rubric_nontrivial_met (M : Nat) :
    RubricNontrivial (reconTransfer gw gw_nonneg (M + 1)) := by
  refine ⟨0, ?_, ?_⟩
  · -- 0 < (reconTransfer gw gw_nonneg (M+1)).k = M+1
    show 0 < M + 1; exact Nat.succ_pos M
  · -- 0 < (reconTransfer gw gw_nonneg (M+1)).w 0 = coeffW gw (0+1)
    show (0 : Q') < coeffW gw (0 + 1)
    exact coeffW_gw_pos 0

/-- **Proved heat-kernel cutoff OS2 precursor.**  For every `t ≥ 0`, the named
SU(2) heat-kernel character form is nonnegative at all finite orders and for all
real coefficient vectors, by `reflectionPositiveSchwinger_holds`.  This is a
substantive cutoff calculation, not OS2 for the as-yet-unconstructed canonical
continuum functional and reflected positive-time carrier. -/
theorem rubric_os2_met (t : Q') (ht : (0 : Q') ≤ t) :
    RubricReflectionPositive t ht :=
  reflectionPositiveSchwinger_holds t ht

/-- **Proved positive scalar rate.**  `RealCorrMass.realContinuumRate`, formed
from the repository's per-volume surrogate rate sequence, is constructively
positive by `realCorr_continuum_mass_isPositive`.  No generator, spectral edge,
or equality between this scalar and a physical mass is supplied here. -/
theorem rubric_infinite_volume_mass_met :
    RubricInfiniteVolumeMass realContinuumRate :=
  realCorr_continuum_mass_isPositive

/-! ## 3. Historical continuum fields of the legacy aggregate

`ClayContinuumExistence` records difficult RG/loopy/tightness data, but is not a
complete continuum construction.  The O4 and uniform-coupling propositions are
weak compatibility slots with model inhabitants; neither is the corresponding
physical Clay obligation. -/

/-- **Historical continuum-existence package.**
`Type`-level data used by the earlier reduction route: the
`a → 0` defect-controlled gap recursion (`ContinuumClosureProgram.DefectGapRecursion`,
whose `recursion` field is the open non-abelian block-spin gap-degradation law),
TOGETHER WITH the loopy/multi-component correlator generalization
(`MultiPlaquetteMayer.LoopyCorrelatorResidual`, the cyclic-geometry wall) and a
continuum tightness rate (a modulus `Nat → Q'` controlling the `a → 0`
fluctuation).

No term is constructed in this file.  Even a term would provide only these
fields: it would not by itself construct the canonical Schwinger limit, reflected
OS quotient, continuous semigroup, or Hamiltonian. -/
structure ClayContinuumExistence : Type where
  /-- The open `a → 0` defect-controlled gap recursion (its `recursion` field is
  the open non-abelian multi-link block-spin step). -/
  defectRecursion : DefectGapRecursion
  /-- The open loopy / multi-component correlator generalization (the cyclic
  re-shared-link wall, beyond the acyclic tree case). -/
  loopyResidual : LoopyCorrelatorResidual gw
  /-- A continuum tightness modulus: an `a → 0` fluctuation-control rate. -/
  tightnessRate : Nat → Q'
  /-- The tightness rate is genuinely controlling (each value nonnegative). -/
  tightnessRate_nonneg : ∀ n : Nat, (0 : Q') ≤ tightnessRate n

/-- **Legacy weak O(4)-restoration slot.**  The classical rubric requires full
continuum `O(4)` covariance, but the historical formalization below does not
state it: the defect family is existential inside each scale and is not tied to
an observable action.  It has unconditional model inhabitants elsewhere and
must not be used as the full Euclidean-invariance theorem.

Note: `Continuum/O4DecayFromMargin.lean` provides a PRECURSOR only (a margin-fed
decay bound feeding rotational restoration), NOT full `O(4)` restoration; the
honest frontier (per the open-boundary ledger) is the absence of a non-trivial
`O(4)`-restoration precursor, with an `H₄ *-homomorphism` the best next target.
The declaration is statement-guard pinned for compatibility; the corrected
same-action obligation lives in the sharp O4/observable-symmetry modules. -/
def RubricO4Restoration : Prop :=
  -- Weak scalar eventuality: because `defect` is chosen inside `∀ k`, this does
  -- not identify one anisotropy schedule or an observable action.
  ∀ ε : Q', (0 : Q') < ε →
    ∃ N : Nat, ∀ k : Nat, N ≤ k →
      -- An existential defect family meeting the tolerance at this scale.
      ∃ defect : Nat → Q', defect k < ε ∧ (0 : Q') ≤ defect k ∧
        -- A positive upper baseline; this does not pin physical provenance.
        (∃ base : Q', (0 : Q') < base ∧ defect k ≤ base)

/-- **Legacy weak uniform-schedule slot.**  This proposition merely existentially
chooses a positive sequence, a floor, and a compatible nonnegative defect.  It
does not pin that sequence to a Yang--Mills coupling flow or to a reconstructed
Hamiltonian.  It is demonstrably inhabitable elsewhere in the repository
(`UniformCouplingFromAF.rubricUniformInCoupling_met` and the explicitly trivial
schedule in `TwoDYangMillsAdequacy`), so it must not be counted as an open
four-dimensional uniform-gap theorem. -/
def RubricUniformInCoupling : Prop :=
  -- A weak existential schedule with a positive lower bound.
  ∃ (physGap : Nat → Q') (c : Q'),
    (0 : Q') < c ∧ (0 : Q') < physGap 0 ∧
    -- The one-sided recursion permits simple model schedules; no physical
    -- provenance is encoded.
    (∀ k : Nat, c ≤ physGap k) ∧
    (∃ defect : Nat → Q', (∀ k, (0 : Q') ≤ defect k) ∧
      ∀ k, (1 - defect k) * physGap k ≤ physGap (k + 1))

/-! ## 4. The legacy top-level scorecard.

`ClayFixedSpacingMet` is the proved conjunction of the named finite/scalar
surrogate clauses.  `ClayTarget` adds the historical continuum package and two
weak propositions.  No term is provided here, and the type is not the complete
external Clay requirement. -/

/-- **The fixed-spacing surrogate line.**  For every cutoff `M`, the named finite
spectral model has positive margin and a positive mode, the named character
correlator has geometric decay, the heat-kernel cutoff form is reflection
positive, and the scalar `realContinuumRate` is positive.  These exact clauses
are proved by `clay_fixed_spacing_met`; the definition contains no continuum
OS reconstruction or physical spectral identification. -/
def ClayFixedSpacingMet : Prop :=
  (∀ M : Nat, RubricSpectralGap (reconTransfer_located_gap M) ((1 : Q') - rho gw)) ∧
  (∀ M : Nat, RubricClustering (fun n => wilsonG gw (M + 1) n)) ∧
  (∀ M : Nat, RubricNontrivial (reconTransfer gw gw_nonneg (M + 1))) ∧
  (∀ (t : Q') (ht : (0 : Q') ≤ t), RubricReflectionPositive t ht) ∧
  RubricInfiniteVolumeMass realContinuumRate

/-- **The fixed-spacing surrogate conjunction is proved.**  This term assembles
the five displayed clauses from `gapMargin_pos`, `wilsonG_decay`,
`coeffW_gw_pos`, `reflectionPositiveSchwinger_holds`, and
`realCorr_continuum_mass_isPositive`. -/
theorem clay_fixed_spacing_met : ClayFixedSpacingMet :=
  ⟨rubric_gap_met,
   rubric_clustering_met,
   rubric_nontrivial_met,
   rubric_os2_met,
   rubric_infinite_volume_mass_met⟩

/-- **The weak legacy aggregate.**

No inhabitant is constructed in this file.  Its fixed-spacing field is proved;
its `ClayContinuumExistence` field retains historical RG/loopy/tightness data;
its O4 and uniform fields are weak predicates with model inhabitants.  Thus
absence of a constructor here is not a faithful census of the Clay frontier,
and producing a constructor would not solve the problem.  The type omits, among
other data, the compact global group/action pin, a two-parameter canonical
Schwinger limit, the reflected half-space quotient, a full continuous-time
semigroup, its generator, and physical spectral and interaction identifications. -/
structure ClayTarget : Type where
  /-- The fixed-spacing clauses — PROVED (`clay_fixed_spacing_met`). -/
  fixedSpacing : ClayFixedSpacingMet
  /-- Historical RG/loopy/tightness package; not a complete continuum limit. -/
  continuumExistence : ClayContinuumExistence
  /-- Legacy weak O4 slot; full same-action covariance is stronger. -/
  o4Restoration : RubricO4Restoration
  /-- Weak existential schedule slot; known to have model inhabitants. -/
  uniformInCoupling : RubricUniformInCoupling

/-! ## 5. Documentation: proved surrogates vs the physical frontier

PROVED for the named finite/scalar models:

  * `rubric_gap_met M`  ⟸ `reconTransfer_located_gap` / `gapMargin_pos`
      (positive located gap `1 − rho gw = 107/108` of the finite
      `reconTransfer gw gw_nonneg (M+1)` model);
  * `rubric_clustering_met M`       ⟸ `wilsonG_decay`
      (geometric decay of the named character correlator
      `wilsonG gw (M+1)`, rate `rho gw < 1`);
  * `rubric_nontrivial_met M`       ⟸ `coeffW_gw_pos`
      (a positive mode of the finite `reconTransfer gw gw_nonneg (M+1)` model,
      weight `coeffW gw 1 > 0`);
  * `rubric_os2_met t ht`           ⟸ `reflectionPositiveSchwinger_holds`
      (reflection positivity of the heat-kernel cutoff form, all finite orders,
      all real `c`, every `t ≥ 0`);
  * `rubric_infinite_volume_mass_met` ⟸ `realCorr_continuum_mass_isPositive`
      (strict positivity of the scalar surrogate `realContinuumRate`).

  ⟹ `clay_fixed_spacing_met : ClayFixedSpacingMet`  [PROVED].

LEGACY AGGREGATE STATUS:

  * `ClayContinuumExistence` is not constructed here and retains nontrivial
    historical RG/loopy/tightness inputs, but is not a complete continuum target;
  * `RubricO4Restoration` is an inhabitable weak scalar slot, not full O(4);
  * `RubricUniformInCoupling` is an inhabitable weak schedule slot, not a
    physical uniform generator gap.

  ⟹ `ClayTarget` has no constructor in this file and is in any event insufficient
     for the external Clay problem.

The canonical open path requires the global group/action and two-parameter limit,
reflected positive-time carrier, continuous semigroup, generator, and physical
spectral/non-Wick pins described by the current Clay-resolution root and work
plan. -/

end YMGap.Rubric.ClayScorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Rubric.ClayScorecard.rubric_gap_met
#print axioms YMGap.Rubric.ClayScorecard.rubric_clustering_met
#print axioms YMGap.Rubric.ClayScorecard.rubric_nontrivial_met
#print axioms YMGap.Rubric.ClayScorecard.rubric_os2_met
#print axioms YMGap.Rubric.ClayScorecard.rubric_infinite_volume_mass_met
#print axioms YMGap.Rubric.ClayScorecard.clay_fixed_spacing_met
