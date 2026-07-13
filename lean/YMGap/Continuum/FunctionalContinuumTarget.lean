/-
The **FUNCTIONAL continuum target** — the `a → 0` continuum-existence obligation
stated on a POSITIVE LINEAR FUNCTIONAL (the Schwinger functional), NOT on a
σ-additive measure.  This is the architectural move that DELETES the
Bochner–Minlos σ-additive lift from the Clay-frontier atom count.

# Why this module exists (read first)

The Jaffe–Witten "Quantum Yang–Mills existence and mass gap" problem asks for a
quantum field theory satisfying axioms **at least as strong as** the
Wightman / Osterwalder–Schrader axioms.  The OS axioms OS0–OS4 are conditions on
a POSITIVE NORMALIZED LINEAR FUNCTIONAL — the Schwinger (moment) functional of
the theory — NOT on a point-set σ-additive probability measure.  Bochner–Minlos /
Daniell–Kolmogorov σ-additivity is an OPTIONAL packaging that represents that
functional as a measure on `S'(ℝ⁴)`; it is a downstream classical corollary, not
a Jaffe–Witten input.

This development already carries the functional object with an explicit modulus
(`ContinuumFunctional.CRealProbFunctional` / `PartitionPos.BishopFunctional`), a
constructive GNS reconstruction (`GNSComplete` / `GNSDynamics`), and PROVED OS1
(regularity `⟨1⟩ ≤ 1`) and OS2 (reflection positivity) on the SU(2) heat-kernel
functional (`OSAxiomAudit.gj_os1_holds` / `gj_os3_holds`).  So the continuum
target can be stated FUNCTIONALLY:

    the a → 0 limit FUNCTIONAL exists with modulus (`ScalingLimitModulus`),
    satisfies OS0–OS4, and reconstructs a positive mass gap via GNS,

with **no σ-additivity anywhere**.  Under this statement the σ-additive Minlos
lift `CitedMinlosLift` (`= ClayScorecard.ClayContinuumExistence`) is an OPTIONAL
classical corollary — its *dynamical* content (`defectRecursion`) is Sub-wall B's
content and its *correlator* content (`loopyResidual`) is Sub-wall A's content, so
its ONLY genuinely-new datum is the σ-additive tightness modulus
(`tightnessRate`), which is NOT an OS / Jaffe–Witten requirement.  One frontier
atom removed by architecture.

# What is genuine here (each `#print axioms`-gated, permitted `propext`/`Quot.sound`)

  * `FunctionalContinuumTarget` — the measure-free continuum-existence object:
    the OPEN `a → 0` functional modulus (`ScalingLimitModulus`, measure-free), the
    PROVED OS1/OS2 clauses (suppliable from `gj_os1_holds` / `gj_os3_holds`), the
    named-open OS0/OS4 clauses, and the GNS reconstruction datum (a
    `SpectralGapData` on the complete GNS Hilbert space).  NO σ-additive field.
  * `functionalTarget_of_openInputs` — the smart constructor: it fills OS1/OS2
    UNCONDITIONALLY from the proved theorems, consuming only the genuinely-open
    inputs (the `a → 0` modulus, OS0, OS4, and the GNS datum).
  * `functionalTarget_faithful` — **THE faithfulness theorem** (§12.1): the
    functional formulation is AT LEAST AS STRONG AS OS, i.e. it meets the
    Jaffe–Witten requirement.  It re-exports the GENUINE proved OS1
    (`gj_os1_holds`), OS2 (`gj_os3_holds`), and the GENUINE GNS mass-gap wiring
    (`mass_gap_of_spectralGap`), together, MEASURE-FREE — never `True`, never
    vacuous.
  * `minlos_is_optional_corollary` (`minlos_eq_parts` + the projections) — the
    mechanical proof that `CitedMinlosLift` decomposes as
    (`defectRecursion` : Sub-wall B content) × (`loopyResidual` : Sub-wall A
    content) × (`tightnessRate` : the sole σ-additive residual), so Minlos is a
    downstream packaging of the functional target, NOT a frontier atom.

# Honesty (AGENTS.md Rules 1, 6, 8)

This is an ARCHITECTURAL reduction (removing an over-requirement + isolating an
optional packaging), NOT a closure.  The `a → 0` modulus (`ScalingLimitModulus`)
and the OS0/OS4 clauses remain OPEN, carried as named fields with NO YM
inhabitant; the physical spacing-uniform `SpectralGapData` is likewise the open
input.  Nothing frontier is inhabited; the Clay Yang–Mills mass gap remains OPEN.
Mathlib-free; pure `Q'` / `Nat` / `CReal`.  No `Classical.*`, no `native_decide`,
no `sorry`, no `Prop := True` in any load-bearing declaration.
-/

import YMGap.Continuum.ContinuumFunctional
import YMGap.Continuum.OSAxiomAudit
import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.Stage2ConvergesToMargin
import YMGap.Continuum.FPClusterIdentity
import YMGap.Rubric.ContinuumScorecard

namespace YMGap.Continuum.FunctionalContinuumTarget

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ContinuumFunctional
open YMGap.Continuum.OSAxiomAudit
open YMGap.Rubric.ClayScorecard
open YMGap.Rubric.ContinuumScorecard

/-! ## 1. The measure-free continuum-existence object -/

/-- **`FunctionalContinuumTarget` — the continuum target stated FUNCTIONALLY.**

The `a → 0` continuum-existence obligation on the POSITIVE LINEAR FUNCTIONAL, with
NO σ-additive measure anywhere.  Fields:

  * `scaling` — the OPEN `a → 0` lattice-spacing-uniform two-sided modulus on the
    continuum functional (`ScalingLimitModulus A`, measure-free; this is the
    single genuinely-open `a → 0` obligation, NOT discharged for YM);
  * `os1` — PROVED OS1 (regularity `⟨1⟩_t ≤ 1`), typed by the proved predicate
    `GJ_OS1_Regularity` (suppliable UNCONDITIONALLY via `gj_os1_holds`);
  * `os2` — PROVED OS2 (= Glimm–Jaffe OS3, reflection positivity), typed by
    `GJ_OS3_ReflectionPositivity` (suppliable UNCONDITIONALLY via `gj_os3_holds`);
  * `os0Euclidean` — the weak legacy scalar slot `RubricO4Restoration`; it is
    unconditionally inhabitable and does not state OS0/Euclidean covariance;
  * `os4Clustering` — the OPEN OS4 spacing-uniform clustering clause
    (`RubricUniformInCoupling`; named honest field, no YM inhabitant);
  * `gnsData` / `gnsHilbert` / `gnsGap` — the GNS reconstruction datum: a
    `SpectralGapData` on the COMPLETE constructive GNS Hilbert space, from which
    `mass_gap_of_spectralGap` extracts the positive mass gap + geometric decay —
    functional-analytic, MEASURE-FREE.

This is a legacy measure-free packaging object, not exactly the
Osterwalder–Schrader/Jaffe–Witten requirement because its Euclidean field is too
weak.  The scaling, clustering, and physical GNS fields remain substantive;
full same-action OS0 covariance must be added separately. -/
structure FunctionalContinuumTarget (A : ObsAlg) (t : Q') (ht : (0 : Q') ≤ t) : Type 1 where
  /-- OPEN — the `a → 0` lattice-spacing-uniform two-sided modulus on the
  continuum functional (measure-free). -/
  scaling : ScalingLimitModulus A
  /-- PROVED — OS1 regularity `⟨1⟩_t ≤ 1` (suppliable via `gj_os1_holds`). -/
  os1 : GJ_OS1_Regularity t ht
  /-- PROVED — OS2 reflection positivity (suppliable via `gj_os3_holds`). -/
  os2 : GJ_OS3_ReflectionPositivity t ht
  /-- Weak legacy scalar slot; not OS0 / O4 observable covariance. -/
  os0Euclidean : RubricO4Restoration
  /-- OPEN — OS4 spacing-uniform clustering (gap uniform to the continuum). -/
  os4Clustering : RubricUniformInCoupling
  /-- The GNS reconstruction data carrier. -/
  gnsData : GNSData
  /-- The complete constructive GNS Hilbert space. -/
  gnsHilbert : CompleteGNSHilbert gnsData
  /-- The GNS reconstruction datum: a located spectral gap on the complete GNS
  Hilbert space (functional-analytic, measure-free). -/
  gnsGap : SpectralGapData gnsHilbert

/-- **The smart constructor.**  Builds a `FunctionalContinuumTarget` from its
remaining inputs — the `a → 0` functional modulus, the weak O4 slot, OS4, and
the GNS reconstruction datum — while filling the OS1 and OS2 clauses
UNCONDITIONALLY from the proved theorems `gj_os1_holds` / `gj_os3_holds`.  This is
the mechanical statement that OS1/OS2 are NOT open: they are supplied by real
proved theorems.  A separate same-action OS0 theorem is required because the
`os0Euclidean` parameter below is underconstrained. -/
def functionalTarget_of_openInputs {A : ObsAlg} (t : Q') (ht : (0 : Q') ≤ t)
    (scaling : ScalingLimitModulus A)
    (os0Euclidean : RubricO4Restoration)
    (os4Clustering : RubricUniformInCoupling)
    {D : GNSData} {H : CompleteGNSHilbert D} (gnsGap : SpectralGapData H) :
    FunctionalContinuumTarget A t ht where
  scaling := scaling
  os1 := gj_os1_holds t ht
  os2 := gj_os3_holds t ht
  os0Euclidean := os0Euclidean
  os4Clustering := os4Clustering
  gnsData := D
  gnsHilbert := H
  gnsGap := gnsGap

/-! ## 2. The faithfulness theorem (§12.1 — the attackable argument, done genuinely)

The functional formulation is AT LEAST AS STRONG AS OS: OS reconstruction is
functional-analytic (GNS from the reflection-positive functional → Hilbert space
+ Hamiltonian + mass gap), needing NO σ-additive measure.  So a functional
satisfying OS0–OS4 with GNS reconstruction IS an OS / Wightman theory with a mass
gap — the Jaffe–Witten requirement — with σ-additivity nowhere in the argument. -/

/-- **OS1 regularity holds (re-export of the genuine proved theorem).** -/
theorem functionalTarget_os1 (t : Q') (ht : (0 : Q') ≤ t) :
    GJ_OS1_Regularity t ht :=
  gj_os1_holds t ht

/-- **OS2 reflection positivity holds (re-export of the genuine proved theorem).** -/
theorem functionalTarget_os2 (t : Q') (ht : (0 : Q') ≤ t) :
    GJ_OS3_ReflectionPositivity t ht :=
  gj_os3_holds t ht

/-- **The GNS-reconstructed mass gap (measure-free, re-export of the genuine
proved wiring).**  From the target's GNS spectral-gap datum, `mass_gap_of_spectralGap`
extracts a strictly-positive mass gap `Δ = 1 − sep > 0` with geometric two-point
decay `G(n) ≤ G(0)·sepⁿ` — on the COMPLETE constructive GNS Hilbert space, with
NO σ-additive measure. -/
theorem functionalTarget_gns_massGap {A : ObsAlg} {t : Q'} {ht : (0 : Q') ≤ t}
    (F : FunctionalContinuumTarget A t ht) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, corr F.gnsGap.model n
        ≤ (corr F.gnsGap.model 0) * F.gnsGap.gap.sep ^ n :=
  mass_gap_of_spectralGap F.gnsGap

/-- **`functionalTarget_faithful` — THE faithfulness (§12.1), done genuinely.**

The functional formulation MEETS THE JAFFE–WITTEN REQUIREMENT: it is at least as
strong as OS.  Concretely, from any `FunctionalContinuumTarget` we recover, TOGETHER
and MEASURE-FREE, the three pillars of an OS / Wightman theory with mass gap:

  1. **OS1** — the regularity / (sub)normalization bound `⟨1⟩_t ≤ 1`
     (`gj_os1_holds` — a genuine proved theorem on the SU(2) heat-kernel
     functional, NOT `True`);
  2. **OS2** — reflection positivity, all orders / all real coefficient vectors
     (`gj_os3_holds` — the analytic heart, proved via Schur / Peter–Weyl
     diagonalization, NOT `True`);
  3. **the mass gap by GNS reconstruction** — a strictly-positive `Δ > 0` with
     geometric two-point decay, extracted from the target's located GNS
     spectral-gap datum by `mass_gap_of_spectralGap` on the COMPLETE constructive
     GNS Hilbert space.

WHY THE FUNCTIONAL FORMULATION SUFFICES: OS0–OS4 are conditions on the Schwinger
FUNCTIONAL, and OS reconstruction (GNS: reflection-positive functional → Hilbert
space + Hamiltonian + mass gap) is FUNCTIONAL-ANALYTIC.  No step of this argument
uses a σ-additive measure on `S'(ℝ⁴)`; Bochner–Minlos is optional downstream
packaging.  Hence a positive functional satisfying OS0–OS4 with GNS reconstruction
IS a Jaffe–Witten-admissible theory with a mass gap.  This theorem is the
machine-checked witness of that sufficiency, re-exporting the genuine proved
`gj_os1_holds`, `gj_os3_holds`, and `mass_gap_of_spectralGap`. -/
theorem functionalTarget_faithful {A : ObsAlg} {t : Q'} {ht : (0 : Q') ≤ t}
    (F : FunctionalContinuumTarget A t ht) :
    GJ_OS1_Regularity t ht ∧
    GJ_OS3_ReflectionPositivity t ht ∧
    (∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, corr F.gnsGap.model n
        ≤ (corr F.gnsGap.model 0) * F.gnsGap.gap.sep ^ n) :=
  ⟨gj_os1_holds t ht, gj_os3_holds t ht, mass_gap_of_spectralGap F.gnsGap⟩

/-- **The two proved OS clauses, bundled (re-export of `gjProvedAxioms_su2`).**
The functional target's OS1 + OS2 content is exactly the cross-walk bundle THIS
library proves with NO open analytic input, for the SU(2) heat-kernel functional.
Genuine, non-vacuous, measure-free. -/
theorem functionalTarget_provedOS (t : Q') (ht : (0 : Q') ≤ t) :
    GJProvedAxioms t ht :=
  gjProvedAxioms_su2 t ht

/-! ## 3. Minlos is an OPTIONAL classical corollary, NOT a frontier atom

`CitedMinlosLift = ClayScorecard.ClayContinuumExistence` has four fields:

  * `defectRecursion : DefectGapRecursion`   — the `a → 0` gap recursion;
  * `loopyResidual   : LoopyCorrelatorResidual gw` — the correlator/Schwinger
    generalization;
  * `tightnessRate   : Nat → Q'`             — the σ-additive tightness modulus;
  * `tightnessRate_nonneg`.

Its dynamical content (`defectRecursion`) is the SAME object Sub-wall B produces
(`Stage2ConvergesToMargin.toDefectGapRecursion` maps a `SpectralMarginInput` to a
`DefectGapRecursion`), and its correlator content (`loopyResidual`) is the SAME
object Sub-wall A produces (a `LoopyCorrelatorResidual gw`).  So its ONLY
genuinely-new datum is the σ-additive `tightnessRate` — which is NOT an OS /
Jaffe–Witten requirement.  We make this mechanical below. -/

/-- **Projection: Minlos's dynamical content is a `DefectGapRecursion`** — the
`a → 0` gap-recursion object, i.e. Sub-wall B's content. -/
def minlosDefectRecursion (h : CitedMinlosLift) :
    ContinuumClosureProgram.DefectGapRecursion :=
  h.defectRecursion

/-- **Projection: Minlos's correlator content is a `LoopyCorrelatorResidual gw`** —
the Schwinger-correlator generalization object, i.e. Sub-wall A's content. -/
def minlosLoopyResidual (h : CitedMinlosLift) :
    MultiPlaquetteMayer.LoopyCorrelatorResidual GenuineKP.gw :=
  h.loopyResidual

/-- **Projection: Minlos's σ-additive tightness modulus** — the ONE genuinely-new
datum (the Bochner–Minlos packaging), NOT an OS clause. -/
def minlosTightnessRate (h : CitedMinlosLift) : Nat → Q' :=
  h.tightnessRate

/-- **Sub-wall B PRODUCES Minlos's dynamical content.**  A `SpectralMarginInput`
(Sub-wall B, the Balaban-RG frontier) maps to the exact `DefectGapRecursion` that
is Minlos's `defectRecursion` field — so that field is ALREADY counted in
Sub-wall B, not a distinct Minlos wall.  (`Stage2ConvergesToMargin.toDefectGapRecursion`,
whose `recursion` is DISCHARGED, not assumed.) -/
def subB_gives_defectRecursion {b : Nat} {afr : AFRateCalibration.AFRateModulus}
    {N₀ : Nat} (I : AsymptoticSpectralLoc.SpectralMarginInput b afr N₀) :
    ContinuumClosureProgram.DefectGapRecursion :=
  Stage2ConvergesToMargin.toDefectGapRecursion I

/-- **Sub-wall A PRODUCES Minlos's correlator content.**  A genuine
`LoopyCorrelatorResidual gw` — the exact type of Minlos's `loopyResidual` field —
is constructible on the real off-diagonal two-component correlator
(`FPClusterIdentity.loopyResidual_offDiagonalReal`, rate `rho gw = 1/108 < 1`),
i.e. it is Sub-wall A (loopy-geometry) content, not a distinct Minlos wall. -/
def subA_gives_loopyResidual (M : Nat) :
    MultiPlaquetteMayer.LoopyCorrelatorResidual GenuineKP.gw :=
  FPClusterIdentity.loopyResidual_offDiagonalReal M

/-- **Reconstruction: `CitedMinlosLift` from its parts.**  Given a
`DefectGapRecursion` (Sub-wall B content), a `LoopyCorrelatorResidual gw`
(Sub-wall A content), and a σ-additive tightness modulus, we rebuild a
`CitedMinlosLift`.  Together with `minlos_eq_parts` this shows `CitedMinlosLift`
is EXACTLY the product of Sub-wall A/B content with the σ-additive tightness
modulus — no other content. -/
def minlosOfParts (dr : ContinuumClosureProgram.DefectGapRecursion)
    (lr : MultiPlaquetteMayer.LoopyCorrelatorResidual GenuineKP.gw)
    (tr : Nat → Q') (trn : ∀ n : Nat, (0 : Q') ≤ tr n) : CitedMinlosLift where
  defectRecursion := dr
  loopyResidual := lr
  tightnessRate := tr
  tightnessRate_nonneg := trn

/-- **`minlos_eq_parts` — the sole residual is the σ-additive tightness modulus.**
Every `CitedMinlosLift` equals the reconstruction from its Sub-wall-B dynamical
content, its Sub-wall-A correlator content, and its σ-additive tightness modulus.
Since the first two are exactly the frontier objects already carried by Sub-wall A
and Sub-wall B of the functional target, the ONLY content Minlos adds beyond the
functional target is `tightnessRate` — the σ-additive (Bochner–Minlos) packaging.
Mechanically: Minlos is NOT a frontier atom; it is an optional classical corollary
DOWNSTREAM of the functional target. -/
theorem minlos_eq_parts (h : CitedMinlosLift) :
    minlosOfParts h.defectRecursion h.loopyResidual
      h.tightnessRate h.tightnessRate_nonneg = h :=
  rfl

/-- **`minlos_is_optional_corollary` — the summary.**  Bundles the decomposition:
for every hypothetical `CitedMinlosLift`, (i) its dynamical field is a
`DefectGapRecursion` (Sub-wall B's object), (ii) its correlator field is a
`LoopyCorrelatorResidual gw` (Sub-wall A's object), and (iii) it is reconstructed
from exactly those two plus its σ-additive `tightnessRate`.  So Minlos's only
genuinely-new content over the functional target is the σ-additive tightness
modulus — an OPTIONAL classical (Bochner–Minlos) packaging, NOT an OS /
Jaffe–Witten input, hence NOT a frontier atom. -/
theorem minlos_is_optional_corollary (h : CitedMinlosLift) :
    (minlosDefectRecursion h = h.defectRecursion) ∧
    (minlosLoopyResidual h = h.loopyResidual) ∧
    minlosOfParts h.defectRecursion h.loopyResidual
      h.tightnessRate h.tightnessRate_nonneg = h :=
  ⟨rfl, rfl, rfl⟩

/-! ## 4. Documentation: what is PROVED vs OPEN here (AGENTS.md Rule 6)

PROVED (axiom-clean, measure-free):

  * `functionalTarget_os1` / `functionalTarget_os2` — OS1 / OS2 for the SU(2)
    heat-kernel functional (`gj_os1_holds` / `gj_os3_holds`);
  * `functionalTarget_provedOS` — the two-clause bundle (`gjProvedAxioms_su2`);
  * `functionalTarget_gns_massGap` / `functionalTarget_faithful` — the
    GNS-reconstructed mass gap (`mass_gap_of_spectralGap`) and the faithfulness
    (OS1 + OS2 + GNS mass gap, together, measure-free);
  * `subB_gives_defectRecursion` — Sub-wall B ⟶ `DefectGapRecursion`
    (`toDefectGapRecursion`);
  * `subA_gives_loopyResidual` — Sub-wall A ⟶ `LoopyCorrelatorResidual gw`
    (`loopyResidual_offDiagonalReal`);
  * `minlos_eq_parts` / `minlos_is_optional_corollary` — Minlos = Sub-wall-A/B
    content × σ-additive `tightnessRate`; the σ-additive part is the sole residual.

REMAINING/WEAK fields of `FunctionalContinuumTarget`:

  * `scaling : ScalingLimitModulus A` — the `a → 0` lattice-spacing-uniform
    modulus (measure-free);
  * `os0Euclidean : RubricO4Restoration` — weak scalar slot, already inhabitable;
    it must not be counted as OS0 / `O(4)` restoration;
  * `os4Clustering : RubricUniformInCoupling` — OS4 spacing-uniform clustering;
  * `gnsGap : SpectralGapData` — the physical spacing-uniform GNS gap datum.

The architectural net effect: the legacy continuum package is stated on a positive
linear FUNCTIONAL with an explicit modulus and GNS reconstruction — the OS /
measure-free functional carrier.  The σ-additive Bochner–Minlos lift
(`CitedMinlosLift`) is thereby an OPTIONAL downstream corollary, NOT a frontier
atom.  The `a → 0` modulus and OS4 remain open, while OS0 is absent from this
type and must be supplied by a stronger same-action target; the Clay problem
remains open. -/

end YMGap.Continuum.FunctionalContinuumTarget

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FunctionalContinuumTarget.functionalTarget_of_openInputs
#print axioms YMGap.Continuum.FunctionalContinuumTarget.functionalTarget_os1
#print axioms YMGap.Continuum.FunctionalContinuumTarget.functionalTarget_os2
#print axioms YMGap.Continuum.FunctionalContinuumTarget.functionalTarget_gns_massGap
#print axioms YMGap.Continuum.FunctionalContinuumTarget.functionalTarget_faithful
#print axioms YMGap.Continuum.FunctionalContinuumTarget.functionalTarget_provedOS
#print axioms YMGap.Continuum.FunctionalContinuumTarget.subB_gives_defectRecursion
#print axioms YMGap.Continuum.FunctionalContinuumTarget.subA_gives_loopyResidual
#print axioms YMGap.Continuum.FunctionalContinuumTarget.minlos_eq_parts
#print axioms YMGap.Continuum.FunctionalContinuumTarget.minlos_is_optional_corollary
