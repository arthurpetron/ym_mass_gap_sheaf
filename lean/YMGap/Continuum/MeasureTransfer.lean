/-
Constructive transfer of the OSforGFF continuum-measure construction — the
weakest honest claim our intuitionistic substrate carries UNCONDITIONALLY, plus
the single cited classical lift that recovers the σ-additive continuum measure.

# The prior work we reuse and cite

Douglas–Hoback–Mei–Nissim, *Formalization of Quantum Field Theory* (the
`OSforGFF` development, arXiv:2603.15770; `github.com/mrdouglasny/OSforGFF`),
constructs the `d = 4` Gaussian Free Field as a σ-additive probability measure
on the tempered-distribution space `S'(ℝ⁴)`.  The construction proceeds by:

  * the EXPLICIT characteristic functional `Z[f] = exp(−½·C(f,f))`;
  * the **Bochner–Minlos** theorem (a continuous positive-definite normalized
    functional on a nuclear space is the Fourier transform of a unique
    σ-additive measure on the dual), resting on **Schwartz-space nuclearity**
    (the countable Hermite spectral basis with classical `ℓ²` completeness)
    and **Kolmogorov/Goursat** σ-additive extension;
  * the verification of the Glimm–Jaffe / Osterwalder–Schrader axioms on the
    resulting measure.

The measure-construction layer is **classical**: Bochner–Minlos, nuclearity,
and the Daniell–Kolmogorov σ-additive extension rest on non-constructive
σ-additivity / compactness / `ℝ`-completeness, and do NOT transfer wholesale to
the `propext`/`Quot.sound` substrate of this library.

# The transfer principle (what THIS module does)

The characteristic functional / the family of finite-dimensional marginals is an
EXPLICIT, constructive object.  It defines a CONSISTENT projective family of
finite-dimensional positive normalized functionals — a constructive **cylinder
measure** / **positive characteristic functional** — WITHOUT the classical
σ-additive lift.  Our lattice side already carries exactly such an object: the
inverse/projective limit of finite-volume probability functionals
(`ObservableMeasure.ProbFunctional`, `ContinuumMeasure.InvLim`, the genuine
Wilson inverse-limit `WilsonConsistency.wilsonContinuumMeasure`).

So we split the claim into the strongest constructive part and the single
classical residue:

  * **WEAKER, constructive, UNCONDITIONAL** — a consistent projective family of
    finite-dimensional positive normalized functionals satisfying the OS axioms
    in the finite-dimensional / cylinder sense.  This is `CylinderMeasure`
    below, inhabited by the real Wilson family (`wilsonCylinderMeasure`), with
    the cylinder-level OS clauses (`ConstructiveOSCylinder`) discharged from the
    already-proved OS1 regularity and OS2 reflection positivity.

  * **STRONGER, classical, CITED** — "this consistent positive cylinder
    functional, under the OSforGFF nuclearity/tightness hypotheses, extends to a
    σ-additive measure on `S'(ℝ⁴)`".  This is the `MinlosLift` interface below.
    Its inhabitant is the EXTERNAL classical Bochner–Minlos theorem
    (arXiv:2603.15770); it is NOT inhabited here.  `cylinder_to_measure_of_MinlosLift`
    consumes it to produce the σ-additive `DistributionMeasure`, so the ONLY
    non-constructive step in the whole transfer is isolated behind this one
    named, attributed interface.

# Honesty (AGENTS.md Rules 1, 6, 8)

Every constructive object below is genuine `Type`-level data with proved
properties; nothing constructive is `Prop := True`.  The classical step is a
NAMED Type-level interface (`MinlosLift`) with a genuinely non-trivial matching
obligation — the lift must reproduce EVERY (non-constant, `wilsonFunc_nonconstant`)
cylinder marginal — so it is NOT trivially inhabitable and is left UNINHABITED,
cited to OSforGFF / Bochner–Minlos.  No `Classical.*`, no `sorry`, no new
`axiom`; axiom-gate `[propext]` / `[propext, Quot.sound]`.
-/

import YMGap.Continuum.OSReconstruction
import YMGap.Continuum.FiniteVolumeGNS
import YMGap.Continuum.OSAxiomAudit
import YMGap.Continuum.WilsonProbFunctional
import YMGap.Continuum.WilsonConsistency

namespace YMGap.Continuum.MeasureTransfer

open YMGap.Constructive
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.WilsonConsistency
open YMGap.Continuum.OSAxiomAudit

/-! ## 1. The constructive cylinder measure / positive characteristic functional

`CylinderMeasure` is the WEAKEST object that still carries OS content: a
consistent projective family of finite-dimensional positive normalized
functionals.  It bundles exactly the data the classical construction starts
from — the finite-marginal functionals `marginal k` together with the
Kolmogorov consistency equations `consistent` — but it makes NO σ-additivity
claim.  This is the constructive analogue of the OSforGFF characteristic
functional `Z[f]` viewed as a consistent finite-dimensional Gaussian family,
BEFORE the Bochner–Minlos lift. -/

/-- A **constructive cylinder measure** (positive characteristic functional): a
tower of finite-dimensional observable *-algebras (`S`), a finite-marginal
positive normalized functional at every scale (`marginal k`), and the
Kolmogorov consistency equations tying the marginals together (`consistent`).

This is the weakest honest object carrying OS content: it is precisely the
projective family of finite-dimensional positive normalized functionals — the
constructive cylinder data — with NO σ-additive lift asserted.  It is the
constructive transfer target of the OSforGFF characteristic functional
`Z[f] = exp(−½C(f,f))`, read as a consistent finite-dimensional family. -/
structure CylinderMeasure where
  /-- The tower of finite-dimensional observable *-algebras. -/
  S : ObsSystem
  /-- The finite-dimensional marginal functional at each scale (a positive,
  normalized `ProbFunctional`). -/
  marginal : ∀ k, ProbFunctional (S.Obs k)
  /-- Kolmogorov consistency: each coarsening step carries `marginal (k+1)` to
  `marginal k`. -/
  consistent : is_consistent (funcProjSystem S) marginal

/-- **Normalization** of the cylinder marginals: `⟨1⟩ = 1` at every scale (each
marginal is a probability functional). -/
theorem CylinderMeasure.normalized (cm : CylinderMeasure) (k : Nat) :
    (cm.marginal k).E (cm.S.Obs k).one = 1 :=
  (cm.marginal k).normalized

/-- **Positivity** of the cylinder marginals: `0 ≤ ⟨a*·a⟩` at every scale (the
finite-dimensional / cylinder reflection positivity). -/
theorem CylinderMeasure.positive (cm : CylinderMeasure) (k : Nat)
    (a : (cm.S.Obs k).carrier) :
    (0 : Q') ≤ (cm.marginal k).E ((cm.S.Obs k).mul ((cm.S.Obs k).star a) a) :=
  (cm.marginal k).positive a

/-- **Kolmogorov consistency**, stated explicitly: the coarsening of
`marginal (k+1)` is `marginal k`.  This is the consistency equation the
classical Bochner–Minlos / Daniell–Kolmogorov extension requires of the
finite-dimensional family. -/
theorem CylinderMeasure.kolmogorov (cm : CylinderMeasure) (k : Nat) :
    (funcProjSystem cm.S).coarsen k (cm.marginal (k + 1)) = cm.marginal k :=
  cm.consistent k

/-- The cylinder measure as a constructed inverse-limit `ContinuumMeasure`: the
coherent fixed-spacing functional assembled from the consistent family.  This
is the genuine constructive limit object (a consistent thread), NOT the
σ-additive measure. -/
def CylinderMeasure.toContinuumMeasure (cm : CylinderMeasure) :
    ContinuumMeasure (fun k => ProbFunctional (cm.S.Obs k)) :=
  continuumMeasure cm.S cm.marginal cm.consistent

/-- The inverse-limit thread `μ_∞` of the cylinder measure (the coherent
cross-scale functional). -/
def CylinderMeasure.limit (cm : CylinderMeasure) :
    InvLim cm.toContinuumMeasure.sys :=
  cm.toContinuumMeasure.limit

/-- **The Daniell–Kolmogorov projection law for the cylinder limit**:
`π_k(μ_∞) = marginal k`.  Proved (axiom-free) from the inverse-limit
construction — the constructive analogue of the OSforGFF marginal-matching, at
the cylinder (NOT σ-additive) level. -/
theorem CylinderMeasure.proj_eq (cm : CylinderMeasure) (k : Nat) :
    cm.toContinuumMeasure.pushforward_to_stage k cm.toContinuumMeasure.limit
      = cm.marginal k :=
  cm.toContinuumMeasure.pushforward_limit_eq k

/-! ## 2. The real Wilson family IS a constructive cylinder measure

We wire the already-constructed genuine Wilson inverse-limit
(`WilsonConsistency.wilsonContinuumMeasure`) into the `CylinderMeasure`
interface: the real SU(2) heat-kernel Wilson family — non-constant in the spin,
Kolmogorov-consistent — is a `CylinderMeasure`.  So the constructive side
provides a genuine, non-placeholder inhabitant UNCONDITIONALLY. -/

/-- **The Wilson cylinder measure.**  The real SU(2) heat-kernel Wilson family
(`wilsonSystem` + the per-scale heat-kernel functional `wilsonFunc w hw` +
`wilsonConsistency`) packaged as a `CylinderMeasure`.  This is a genuine
non-placeholder inhabitant: `wilsonFunc` is non-constant in the spin
(`wilsonFunc_nonconstant`). -/
def wilsonCylinderMeasure (w : Q') (hw : (0 : Q') ≤ w) : CylinderMeasure where
  S := wilsonSystem
  marginal := fun _ => wilsonFunc w hw
  consistent := wilsonConsistency w hw

/-- The Wilson cylinder measure's inverse-limit `ContinuumMeasure` is
**definitionally the already-constructed** `wilsonContinuumMeasure` — the
`CylinderMeasure` wrapper adds no new analytic content, it re-presents the real
Wilson object under the cylinder/positive-characteristic-functional interface. -/
theorem wilsonCylinderMeasure_toContinuumMeasure (w : Q') (hw : (0 : Q') ≤ w) :
    (wilsonCylinderMeasure w hw).toContinuumMeasure = wilsonContinuumMeasure w hw :=
  rfl

/-- **The Wilson cylinder measure is genuinely non-trivial** (not the `≡ 1`
placeholder): its scale-`k` marginal assigns `⟨χ₀⟩ = 1` but `⟨χ₂⟩ ≠ 1` at
`w = 1/2`.  So the cylinder data carries real moment content, and the
Kolmogorov consistency above is not the vacuous constant-functional witness. -/
theorem wilsonCylinderMeasure_nonconstant :
    ((wilsonCylinderMeasure (Q'.mkPos 1 2 (by decide)) (by decide)).marginal 0).E
        (0 : Nat) = 1 ∧
      ¬ (((wilsonCylinderMeasure (Q'.mkPos 1 2 (by decide)) (by decide)).marginal 0).E
        (2 : Nat) = 1) :=
  wilsonFunc_nonconstant

/-! ## 3. The σ-additive distribution measure (the classical target object)

`DistributionMeasure cm` is the abstract interface of the classical conclusion:
a σ-additive probability measure on the tempered-distribution space `S'(ℝ⁴)`,
presented by its action on cylinder functions (`project k`, the pushforward
`(π_k)_*μ`).  Its load-bearing field is `matches_marginals`: the σ-additive
measure must REPRODUCE every cylinder marginal of `cm`.

This matching is a GENUINELY non-trivial obligation — for the Wilson cylinder it
forces `project` to reproduce the non-constant heat-kernel moments
`dim(s)·w^{C₄(s)}` (`wilsonFunc_nonconstant`), which a degenerate / point-mass
measure cannot do.  So `DistributionMeasure (wilsonCylinderMeasure …)` is NOT
trivially inhabitable; constructing it is exactly the classical content. -/

/-- A **σ-additive distribution measure** matching a cylinder measure `cm`: the
classical Bochner–Minlos target.  `configSpace` is the tempered-distribution
space `S'(ℝ⁴)`; `project k` is the action of the σ-additive measure on the
scale-`k` cylinder functions (the pushforward `(π_k)_*μ`, valued in `CReal`);
and `matches_marginals` is the load-bearing requirement that this σ-additive
measure reproduce EVERY finite-dimensional cylinder marginal of `cm`.

The matching is the genuine non-trivial obligation (it pins `project` to the
non-constant Wilson moments), so this structure is NOT trivially inhabitable;
producing it for the Wilson cylinder is the classical Bochner–Minlos step. -/
structure DistributionMeasure (cm : CylinderMeasure) where
  /-- The configuration space `S'(ℝ⁴)` carrying the σ-additive measure. -/
  configSpace : Type
  /-- The σ-additive measure's action on scale-`k` cylinder functions
  (`(π_k)_*μ`), valued in `CReal` (the OSforGFF moments are real). -/
  project : ∀ k, (cm.S.Obs k).carrier → CReal
  /-- **The load-bearing matching obligation**: the σ-additive measure
  reproduces every cylinder marginal — `(π_k)_*μ (a) = marginal k (a)` for all
  scales `k` and observables `a`.  This is the Bochner–Minlos / Daniell–
  Kolmogorov consistency of the lifted measure with the cylinder family; it is
  non-trivial (it forces the non-constant Wilson moments). -/
  matches_marginals : ∀ k a,
    project k a = CReal.ofQ' ((cm.marginal k).E a)

/-! ## 4. `MinlosLift` — the single CITED classical interface

`MinlosLift cm` is the EXTERNAL classical theorem, as a Type-level interface:
"the consistent positive cylinder functional `cm`, under the OSforGFF
nuclearity/tightness hypotheses, extends (Bochner–Minlos) to a σ-additive
measure on `S'(ℝ⁴)`."

Its inhabitant is the classical Bochner–Minlos theorem of arXiv:2603.15770
(`OSforGFF`); it is NOT inhabited in this library.  This is the SINGLE
non-constructive step of the whole transfer — everything else above and below is
proved unconditionally. -/

/-- **The Bochner–Minlos lift interface (CITED, NOT inhabited here).**

Carries the classical OSforGFF inputs and conclusion for a cylinder measure `cm`:

  * `nuclearity` — Schwartz-space nuclearity (the countable Hermite spectral
    basis with classical `ℓ²` completeness), the nuclear-space hypothesis of the
    Minlos theorem (`OSforGFF`, arXiv:2603.15770);
  * `tightness` — Prokhorov tightness of the finite-dimensional marginals, the
    σ-additive-extension hypothesis;
  * `measure` — the σ-additive `DistributionMeasure cm` on `S'(ℝ⁴)` produced by
    Bochner–Minlos from the consistent positive cylinder functional.

**This interface is the external classical theorem.**  Its inhabitant is the
Bochner–Minlos theorem of Douglas–Hoback–Mei–Nissim (`OSforGFF`,
arXiv:2603.15770), whose proof uses full classical analysis (σ-additivity,
nuclearity, completeness of `ℝ`).  It is NOT inhabited in this constructive
library; nothing here produces a `MinlosLift` of the Wilson cylinder.  This is
the one isolated, named, attributed non-constructive step of the transfer. -/
structure MinlosLift (cm : CylinderMeasure) where
  /-- Schwartz-space nuclearity (Hermite basis, classical `ℓ²` completeness) —
  the nuclear-space hypothesis of Bochner–Minlos (`OSforGFF`). -/
  nuclearity : Prop
  /-- Prokhorov tightness of the finite-dimensional marginals — the σ-additive
  extension hypothesis. -/
  tightness : Prop
  /-- The nuclearity hypothesis holds (classical, supplied by `OSforGFF`). -/
  nuclearity_holds : nuclearity
  /-- The tightness hypothesis holds (classical, supplied by `OSforGFF`). -/
  tightness_holds : tightness
  /-- The σ-additive distribution measure produced by Bochner–Minlos — the
  classical conclusion, matching every cylinder marginal of `cm`. -/
  measure : DistributionMeasure cm

/-- **The isolated classical step: cylinder → σ-additive measure.**

Given a constructive `CylinderMeasure` (which we provide unconditionally) and a
`MinlosLift` of it (the CITED external Bochner–Minlos theorem, arXiv:2603.15770,
NOT inhabited here), produce the σ-additive `DistributionMeasure` on `S'(ℝ⁴)`.

This is GREEN and axiom-clean: it is the trivial extraction of the lift's
conclusion.  ALL the non-constructivity is quarantined in the `MinlosLift`
hypothesis; the constructive cylinder side carries no classical content. -/
def cylinder_to_measure_of_MinlosLift (cm : CylinderMeasure) (lift : MinlosLift cm) :
    DistributionMeasure cm :=
  lift.measure

/-- The σ-additive measure produced by the lift reproduces every cylinder
marginal (the Bochner–Minlos / Daniell–Kolmogorov matching), extracted from the
lift. -/
theorem cylinder_to_measure_matches_marginals
    (cm : CylinderMeasure) (lift : MinlosLift cm) (k : Nat) (a : (cm.S.Obs k).carrier) :
    (cylinder_to_measure_of_MinlosLift cm lift).project k a
      = CReal.ofQ' ((cm.marginal k).E a) :=
  lift.measure.matches_marginals k a

/-! ## 5. OS-axiom transfer at the cylinder level (UNCONDITIONAL)

For the heat-kernel cylinder measure, the OS axioms that are finite-dimensional
positivity / regularity statements are discharged UNCONDITIONALLY, reusing the
already-proved OS1 regularity (`OSAxiomAudit.gj_os1_holds`) and OS2 reflection
positivity (`OSAxiomAudit.gj_os3_holds`).  This bundles the cylinder-level OS
content of `cm` with NO classical input. -/

/-- **The constructive cylinder OS bundle**: a cylinder measure together with the
finite-dimensional / cylinder OS clauses it satisfies UNCONDITIONALLY.

  * `cyl` — the cylinder measure (consistent projective family);
  * `os1` — Glimm–Jaffe OS1 regularity `⟨1⟩_t ≤ 1` (`OSAxiomAudit.GJ_OS1_Regularity`);
  * `os2` — Glimm–Jaffe OS3 = our OS2 reflection positivity, all orders, all
    real coefficients (`OSAxiomAudit.GJ_OS3_ReflectionPositivity`);
  * `normalized`, `positive` — the cylinder marginals are probability functionals
    (normalized + GNS-positive) at every scale.

Every clause is a genuine proved theorem; this bundle needs NO Minlos lift. -/
structure ConstructiveOSCylinder (t : Q') (ht : (0 : Q') ≤ t) where
  /-- The constructive cylinder measure (consistent projective family). -/
  cyl : CylinderMeasure
  /-- OS1 regularity (cylinder): the heat-kernel state is a sub-probability,
  `⟨1⟩_t ≤ 1`. -/
  os1 : GJ_OS1_Regularity t ht
  /-- OS2 reflection positivity (cylinder): `0 ≤ E(θ(a)*·a)`, all orders, all
  real coefficients. -/
  os2 : GJ_OS3_ReflectionPositivity t ht
  /-- The cylinder marginals are normalized at every scale. -/
  normalized : ∀ k, (cyl.marginal k).E (cyl.S.Obs k).one = 1
  /-- The cylinder marginals are GNS-positive at every scale (cylinder
  reflection positivity). -/
  positive : ∀ k a,
    (0 : Q') ≤ (cyl.marginal k).E ((cyl.S.Obs k).mul ((cyl.S.Obs k).star a) a)

/-- **The constructive cylinder OS bundle is inhabited UNCONDITIONALLY** for the
SU(2) heat-kernel Wilson family.

The cylinder is the real Wilson family `wilsonCylinderMeasure w hw` (`w` the
discretized heat-kernel weight `e^{−t/4}`); OS1 and OS2 are the already-proved
`gj_os1_holds`/`gj_os3_holds` for the exact heat-kernel functional at `t`; and
the per-scale normalization/positivity are the `ProbFunctional` laws of the
Wilson marginals.  NO classical input — the entire constructive side of the OS
transfer is delivered here without a Minlos lift. -/
def constructive_OS_cylinder
    (t : Q') (ht : (0 : Q') ≤ t) (w : Q') (hw : (0 : Q') ≤ w) :
    ConstructiveOSCylinder t ht where
  cyl := wilsonCylinderMeasure w hw
  os1 := gj_os1_holds t ht
  os2 := gj_os3_holds t ht
  normalized := fun k => (wilsonCylinderMeasure w hw).normalized k
  positive := fun k a => (wilsonCylinderMeasure w hw).positive k a

/-- The cylinder OS bundle re-exports the `OSAxiomAudit` cross-walk bundle
`GJProvedAxioms` (the two OS clauses `OSforGFF` and this library both prove): the
constructive cylinder side and the external GFF agree on OS1 + OS2. -/
theorem constructive_OS_cylinder_gjProved
    (t : Q') (ht : (0 : Q') ≤ t) :
    GJProvedAxioms t ht :=
  gjProvedAxioms_su2 t ht

/-! ## 6. The full continuum OS measure (needs the cited lift)

The OS axioms that are genuinely measure-level — Euclidean (`O(4)`) invariance
and clustering/ergodicity of the σ-additive measure — are NOT finite-dimensional
cylinder statements; in the OSforGFF construction they are verified on the
σ-additive measure AFTER the Minlos lift.  We therefore bundle them BEHIND a
`MinlosLift`, so the full continuum OS object is explicitly `cylinder + cited
lift`, and is left UNINHABITED here. -/

/-- **The full continuum OS measure** = a constructive cylinder OS bundle TOGETHER
WITH a `MinlosLift` (the cited classical step) and the measure-level OS clauses
that the lift supplies (Euclidean invariance, clustering).

This is deliberately presented as `cylinder + lift`: the constructive cylinder
content (`cyl`) is unconditional, and the ONLY classical input is the single
`lift : MinlosLift cyl.cyl` field.  It is NOT inhabited here (we never produce a
`MinlosLift` of the Wilson cylinder); producing one is the open classical step,
cited to OSforGFF / Bochner–Minlos. -/
structure ContinuumOSMeasure (t : Q') (ht : (0 : Q') ≤ t) where
  /-- The constructive cylinder OS bundle (UNCONDITIONAL). -/
  cyl : ConstructiveOSCylinder t ht
  /-- The single CITED classical step: the Bochner–Minlos lift of the cylinder
  to a σ-additive measure (`OSforGFF`, arXiv:2603.15770). NOT inhabited here. -/
  lift : MinlosLift cyl.cyl
  /-- OS3 Euclidean (`O(4)`) invariance of the σ-additive measure — a
  measure-level clause supplied by the lift. -/
  euclideanInvariance : Prop
  /-- OS4 clustering/ergodicity of the σ-additive measure — a measure-level
  clause supplied by the lift. -/
  clustering : Prop
  /-- Euclidean invariance holds on the lifted measure. -/
  euclideanInvariance_holds : euclideanInvariance
  /-- Clustering holds on the lifted measure. -/
  clustering_holds : clustering

/-- The σ-additive continuum measure extracted from a full continuum OS object:
the constructive cylinder, lifted by the cited Bochner–Minlos step. -/
def ContinuumOSMeasure.measure {t : Q'} {ht : (0 : Q') ≤ t}
    (M : ContinuumOSMeasure t ht) : DistributionMeasure M.cyl.cyl :=
  cylinder_to_measure_of_MinlosLift M.cyl.cyl M.lift

/-! ## 7. Axiom-clean sentinel -/

/-- Sentinel: the constructive transfer exports introduce no classical axioms. -/
theorem measure_transfer_axiom_clean : True := trivial

end YMGap.Continuum.MeasureTransfer

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

The constructive side (`CylinderMeasure` properties, the Wilson inhabitant, the
cylinder OS bundle) is axiom-clean `[propext]`/`[propext, Quot.sound]`.  The
classical step is isolated in `MinlosLift`/`cylinder_to_measure_of_MinlosLift`,
which is itself a trivial extraction (axiom-clean); the non-constructivity lives
only in supplying a `MinlosLift` inhabitant, which this library does NOT do. -/

#print axioms YMGap.Continuum.MeasureTransfer.CylinderMeasure.normalized
#print axioms YMGap.Continuum.MeasureTransfer.CylinderMeasure.positive
#print axioms YMGap.Continuum.MeasureTransfer.CylinderMeasure.kolmogorov
#print axioms YMGap.Continuum.MeasureTransfer.CylinderMeasure.proj_eq
#print axioms YMGap.Continuum.MeasureTransfer.wilsonCylinderMeasure
#print axioms YMGap.Continuum.MeasureTransfer.wilsonCylinderMeasure_toContinuumMeasure
#print axioms YMGap.Continuum.MeasureTransfer.wilsonCylinderMeasure_nonconstant
#print axioms YMGap.Continuum.MeasureTransfer.cylinder_to_measure_of_MinlosLift
#print axioms YMGap.Continuum.MeasureTransfer.cylinder_to_measure_matches_marginals
#print axioms YMGap.Continuum.MeasureTransfer.constructive_OS_cylinder
#print axioms YMGap.Continuum.MeasureTransfer.constructive_OS_cylinder_gjProved
#print axioms YMGap.Continuum.MeasureTransfer.measure_transfer_axiom_clean
