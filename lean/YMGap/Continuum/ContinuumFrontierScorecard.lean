/-
Track B / R2 — **Legacy scalar-floor consolidation scorecard.**

# Why this module exists (read first — and the HONEST scope)

This module proves that several pre-existing NUMERICAL surrogate routes consume
one common positive scalar.  It does not enumerate or solve the full continuum
OS/Yang--Mills frontier.

  * `Continuum/UnifiedContinuumFloor.lean` proved that the several named
    spacing-uniform continuum-gap walls (codynamic physical-gap floor, Bakry–Émery
    curvature mode-energy floor, finite-volume gap-margin persistence, the
    dimensionless `Δ/√σ̂` ratio band, and the dimensional-transmutation rate match)
    are ONE canonical interface, `UniformSpacingFloor`: a single strictly-positive
    rational `floor` lying below a per-scale gap quantity uniformly in the scale.
    Its capstone `unified_continuum_gap` drives BOTH the codynamic and the
    curvature continuum conclusions from the SAME scalar `cur.floor`.

  * `Continuum/GNSComplete.lean` built a constructive complete ORDINARY state-GNS
    space for a finite-volume Wilson datum
    (`WilsonGNSData.completeGnsHilbert`): the metric completion of the GNS
    pre-Hilbert quotient, with a `CReal`-valued inner product and metric
    completeness.  `PositiveIsometricTimeNoGo` shows that this invariant
    ordinary-GNS space is not automatically the physical reflected positive-time
    OS Hilbert space.  It is only an ambient/test substrate here.

This module records, at the project (scorecard) level, the resulting picture:

  1. `clay_continuum_reduced_to_uniform_floor` — the codynamic and curvature
     scalar conclusions are reduced to a shared `UniformSpacingFloor`:
     given ONE such floor (presented codynamically AND curvature-wise against the
     same scalar), BOTH the codynamic physical-gap floor and the curvature
     continuum mass are positive.  (Thin, honest re-export of
     `unified_continuum_gap` at the scorecard altitude.)

  2. `OSReconstructedGap` / `reconstructed_gap_ge_uniform_floor` — a LEGACY
     interface carrying a freely supplied per-scale `genGap` is numerically tied
     to the same scalar.  It neither constructs a generator nor proves that
     `genGap` is its spectrum.

  3. `all_routes_converge_on_uniform_floor` — those three scalar inequalities
     share one floor.  This is arithmetic consolidation only.

# HONESTY — this is CONSOLIDATION, not closure

`UniformSpacingFloor` is uninhabited here for the intended 4D continuum and is a
major quantitative input.  But it is not the only Clay prerequisite.  This file
does not construct the group/action-pinned two-parameter Schwinger limit,
geometry-derived reflected OS carrier, semigroup, unbounded generator, or
spectral identification.  `OSReconstructedGap.genGap` is simply supplied data.
What is proved is only that the displayed inequalities share a scalar.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure repackaging over `unified_continuum_gap` and the `UniformSpacingFloor`
interface; every carrier is `Type`-level data (the `genGap` field is a plain
`Nat → Q'` family and every `bound` is a `Pi` of the order relation, never a
`Prop`-∃ witness).  Each load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`,
no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.UnifiedContinuumFloor
import YMGap.Continuum.GNSComplete
import YMGap.Rubric.ClayScorecard

namespace YMGap.Continuum.ContinuumFrontierScorecard

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.SpacingUniformProgress
open YMGap.Continuum.UnifiedContinuumFloor
open YMGap.Continuum.GNSQuotient

/-! ## 1. Two numerical routes share one `UniformSpacingFloor`

`clay_continuum_reduced_to_uniform_floor` records, at the scorecard altitude, that
the codynamic and curvature surrogate routes are driven by a single shared scalar
floor `cur.floor`.  It is a thin, honest re-export of the unification capstone
`unified_continuum_gap`: within this numerical implication, its hypotheses are
presented as one `UniformSpacingFloor` (split as `cod` and `cur`, tied by
`hshared`).  This does not reduce the full continuum construction, or even all
inputs to the displayed surrogate routes, to that scalar. -/

/-- **SCORECARD LINE: the continuum-gap obligation is reduced to one shared floor.**
Given the self-similar flow data (`T`, `uvSeed`, `A`), curvature spectral template
`M`, and a shared positive scalar floor — presented codynamically as `cod` (a
`CRealFloor` on the named per-scale gap surrogate) and curvature-wise as `cur`
(a `QFloor` on the mode-energy family), tied together by `hshared` — both
displayed numerical conclusions follow:

  * the codynamic gap-surrogate floor `0 < cur.floor` with the per-scale bound
    `∀ N, ofQ' cur.floor ≤ physGapC N`, AND
  * the curvature route's strictly-positive continuum mass.

This is exactly `unified_continuum_gap`, surfaced as a numerical scorecard line.
Nothing here inhabits `cod`/`cur` for the intended `a → 0` limit, and the
canonical reconstruction has additional prerequisites. -/
theorem clay_continuum_reduced_to_uniform_floor {b : Nat}
    (T : SelfSimilarTower b) (uvSeed : PosEv (T.w 0)) (A : SpacingSchedule)
    (M : ModeEnergyFloor)
    (cod : CRealFloor (physGapC b (sep T) A))
    (cur : QFloor (fun p : Nat × Nat => M.eigval p.1 p.2))
    (hshared : cod.floor = cur.floor)
    (hstep : M.s * cur.floor < (1 : Q')) :
    ( (0 : Q') < cur.floor
        ∧ (∀ N, CReal.leEv (CReal.ofQ' cur.floor) (physGapC b (sep T) A N)) )
    ∧ CReal.IsPositive
        (toModeEnergyFloor M cur hstep).toModeCurvatureBound.continuumRate :=
  unified_continuum_gap T uvSeed A M cod cur hshared hstep

/-! ## 2. Legacy generator-gap placeholder — same scalar input

`OSReconstructedGap` stores an ordinary complete GNS wrapper and an unconstrained
family `genGap : Nat → Q'`.  It is a historical placeholder: there is no
generator field and no spectral-identification law.  A `QFloor` merely bounds
that supplied family by the same scalar used above. -/

/-- **Legacy generator-gap placeholder.**  Stores an ordinary completed GNS datum
and a per-scale number family.  It does not state that a generator exists or that
`genGap` is spectral data, so it must not be used as the canonical physical
mass-gap interface. -/
structure OSReconstructedGap (D : GNSData) : Type 1 where
  /-- A selected complete constructive ordinary state-GNS space. -/
  hilbert : CompleteGNSHilbert D
  /-- A freely supplied per-scale number family historically labelled a generator
  gap.  No generator or spectral interpretation is encoded here. -/
  genGap : Nat → Q'

/-- **Arithmetic projection from the legacy placeholder.**  Given an
`OSReconstructedGap` interface `R` and a `QFloor` `F` on its freely supplied
family `R.genGap`, that family is bounded below, uniformly in the index, by the
scalar `F.floor > 0`:

  * `0 < F.floor`, and
  * `∀ n, F.floor ≤ R.genGap n`.

This is exactly the pair of fields already stored by `F`; it neither reconstructs
a mass gap nor asserts that `F` is uninhabited. -/
def reconstructed_gap_ge_uniform_floor {D : GNSData}
    (R : OSReconstructedGap D) (F : QFloor R.genGap) :
    (0 : Q') < F.floor ∧ ∀ n : Nat, F.floor ≤ R.genGap n :=
  ⟨F.floor_pos, F.bound⟩

/-- **Ordinary Wilson-GNS specialization of the legacy placeholder.**  The
`_hbuilt` equality pins only the selected ordinary state-GNS completion.  It
does not identify that space with the reflected physical OS space or identify
`genGap` with a generator spectrum. -/
def wilson_reconstructed_gap_ge_uniform_floor
    {A : ObservableMeasure.ObsAlg} (W : WilsonGNS.WilsonGNSData A)
    (R : OSReconstructedGap W.toGNSData)
    (_hbuilt : R.hilbert = W.completeGnsHilbert)
    (F : QFloor R.genGap) :
    (0 : Q') < F.floor ∧ ∀ n : Nat, F.floor ≤ R.genGap n :=
  -- `_hbuilt` pins the selected ordinary completion; the numerical bound is read
  -- directly from the supplied floor.
  reconstructed_gap_ge_uniform_floor R F

/-! ## 3. Legacy numerical capstone — three inequalities share one floor

`all_routes_converge_on_uniform_floor` ties the codynamic, curvature, AND
legacy reconstruction placeholders to a shared positive scalar `cur.floor`: the
codynamic floor `cod`, the curvature floor `cur`, and the reconstruction floor
`rec` are all the same number (`hshared`, `hsharedRec`).  From that ONE scalar, all
three positive-gap conclusions follow simultaneously. -/

/-- **Legacy numerical-consolidation capstone.**  One shared positive scalar
floor `cur.floor` — instantiated codynamically (`cod`), curvature-wise (`cur`), and
on the supplied placeholder family (`rec`), all tied to the same number by
`hshared`/`hsharedRec` — yields:

  * the codynamic gap-surrogate floor `0 < cur.floor` and `∀ N, ofQ' cur.floor ≤
    physGapC N`;
  * the curvature route's strictly-positive continuum mass;
  * the legacy placeholder bound `∀ n, cur.floor ≤ R.genGap n`.

The three displayed numerical conclusions therefore share one scalar.  This is
not a total continuum reduction: `cod`/`cur`/`rec` are uninhabited here for the
intended limit, `R` contains no generator, and the canonical OS construction
has the independent prerequisites listed in the module footer. -/
theorem all_routes_converge_on_uniform_floor {b : Nat}
    (T : SelfSimilarTower b) (uvSeed : PosEv (T.w 0)) (A : SpacingSchedule)
    (M : ModeEnergyFloor) {D : GNSData}
    (cod : CRealFloor (physGapC b (sep T) A))
    (cur : QFloor (fun p : Nat × Nat => M.eigval p.1 p.2))
    (R : OSReconstructedGap D) (rec : QFloor R.genGap)
    (hshared : cod.floor = cur.floor)
    (hsharedRec : rec.floor = cur.floor)
    (hstep : M.s * cur.floor < (1 : Q')) :
    ( ( (0 : Q') < cur.floor
          ∧ (∀ N, CReal.leEv (CReal.ofQ' cur.floor) (physGapC b (sep T) A N)) )
      ∧ CReal.IsPositive
          (toModeEnergyFloor M cur hstep).toModeCurvatureBound.continuumRate )
    ∧ ( ∀ n : Nat, cur.floor ≤ R.genGap n ) := by
  refine ⟨clay_continuum_reduced_to_uniform_floor T uvSeed A M cod cur hshared hstep, ?_⟩
  -- OS-reconstruction side: transport the reconstruction floor along the shared
  -- scalar equation, then read off the bound.
  intro n
  exact hsharedRec ▸ rec.bound n

/-! ## 4. Documentation: quantitative floor and reconstruction prerequisites (AGENTS.md Rule 6)

PROVED (the REDUCTION — all routes consume one shared input):

  * `clay_continuum_reduced_to_uniform_floor`  ⟸ `unified_continuum_gap`
      (codynamic gap surrogate + curvature-rate surrogate from one scalar);
  * `reconstructed_gap_ge_uniform_floor`       ⟸ the `QFloor` `bound`/`floor_pos`
      (the supplied `genGap` family is bounded below by the same scalar);
  * `wilson_reconstructed_gap_ge_uniform_floor`
      (the same after pinning the selected ordinary Wilson completion);
  * `all_routes_converge_on_uniform_floor`
      (codynamic + curvature + OS-reconstruction, one shared scalar floor).

OPEN (distinct prerequisites, NO physical inhabitant in this file):

  * `UniformSpacingFloor` (and its `QFloor`/`CRealFloor` specializations) — the one
    strictly-positive spacing-uniform gap floor for the genuine `a → 0` limit
    (Bałaban / Shen–Zhu–Zhu spectral-gap physics).  Uninhabited here.
  * an actual time-translation generator and spectral identification — neither is
    represented inside `OSReconstructedGap`; its `genGap` field is only a number
    family;
  * the standard reflected positive-time realization specified by
    `CanonicalOSRoot.PositiveTimeOSRoot` — its geometry-derived support,
    essentially-surjective observable realization, representative transfer
    laws, and strict nonzero/nonidentity Rayleigh probe are not constructed for
    4D Yang--Mills;
  * downstream of that root, the strongly continuous semigroup and its
    unbounded generator are also unconstructed.  They are not fields of
    `PositiveTimeOSRoot` itself.

The picture this module records is narrower: the codynamic flow, Bakry--Emery,
and legacy reconstruction reductions consume the SAME quantitative
`UniformSpacingFloor`.  That common scalar does not construct the independent
physical Schwinger limit, reflected OS carrier, semigroup, generator, or
spectral identification.  All of those are required before the floor becomes a
Clay-facing mass-gap theorem; nothing here claims to have built them. -/

end YMGap.Continuum.ContinuumFrontierScorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumFrontierScorecard.clay_continuum_reduced_to_uniform_floor
#print axioms YMGap.Continuum.ContinuumFrontierScorecard.reconstructed_gap_ge_uniform_floor
#print axioms YMGap.Continuum.ContinuumFrontierScorecard.wilson_reconstructed_gap_ge_uniform_floor
#print axioms YMGap.Continuum.ContinuumFrontierScorecard.all_routes_converge_on_uniform_floor
