/-
Track B / R2 — **The continuum-frontier scorecard line: ONE open input, every
route converges on it.**

# Why this module exists (read first — and the HONEST scope)

Two independent pieces of this development now meet at a single point.

  * `Continuum/UnifiedContinuumFloor.lean` proved that the several named
    spacing-uniform continuum-gap walls (codynamic physical-gap floor, Bakry–Émery
    curvature mode-energy floor, finite-volume gap-margin persistence, the
    dimensionless `Δ/√σ̂` ratio band, and the dimensional-transmutation rate match)
    are ONE canonical interface, `UniformSpacingFloor`: a single strictly-positive
    rational `floor` lying below a per-scale gap quantity uniformly in the scale.
    Its capstone `unified_continuum_gap` drives BOTH the codynamic and the
    curvature continuum conclusions from the SAME scalar `cur.floor`.

  * `Continuum/GNSComplete.lean` built a genuine constructive COMPLETE GNS Hilbert
    space for the finite-volume Wilson theory
    (`WilsonGNSData.completeGnsHilbert`): the metric completion of the GNS
    pre-Hilbert quotient, with a `CReal`-valued inner product and metric
    completeness.  That is the Hilbert space on which an OS-reconstructed
    time-translation generator (the Hamiltonian) would act, and whose spectral gap
    above the vacuum is the physical mass gap.

This module records, at the project (scorecard) level, the resulting picture:

  1. `clay_continuum_reduced_to_uniform_floor` — the project's continuum-gap
     obligation has been REDUCED to the single shared input `UniformSpacingFloor`:
     given ONE such floor (presented codynamically AND curvature-wise against the
     same scalar), BOTH the codynamic physical-gap floor and the curvature
     continuum mass are positive.  (Thin, honest re-export of
     `unified_continuum_gap` at the scorecard altitude.)

  2. `OSReconstructedGap` / `reconstructed_gap_ge_uniform_floor` — the
     OS-reconstruction route is tied to the SAME input.  The reconstructed GNS
     Hilbert space's mass gap (the spectral gap of the time-translation generator)
     is presented as an honest `Type`-level interface `OSReconstructedGap` over the
     complete GNS Hilbert space; a `QFloor` on its per-scale gap shows the gap is
     bounded below by the `UniformSpacingFloor` scalar at every scale.

  3. `all_routes_converge_on_uniform_floor` — the grand convergence: codynamic,
     curvature, AND OS-reconstruction routes all bottom out at one shared scalar
     floor.

# HONESTY — this is CONSOLIDATION, not closure

`UniformSpacingFloor` is **UNINHABITED** for the genuine `a → 0` continuum: it IS
the open spacing-uniform spectral-gap / dimensional-transmutation physics
(Bałaban / Shen–Zhu–Zhu class).  Nothing here inhabits it for 4D Yang–Mills, and
nothing here inhabits the open generator of `OSReconstructedGap` (the
time-translation Hamiltonian on the reconstructed Hilbert space is NOT
constructed — its per-scale gap family `genGap` is carried as honest interface
data a full OS reconstruction must supply).  What is PROVED is the REDUCTION: the
codynamic, curvature, and OS-reconstruction routes are not three separate open
problems but one — they converge on the single `UniformSpacingFloor` scalar.  No
wall is removed; they are shown to coincide.

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

/-! ## 1. The continuum-gap obligation is reduced to ONE shared `UniformSpacingFloor`

`clay_continuum_reduced_to_uniform_floor` records, at the scorecard altitude, that
the codynamic and curvature continuum routes are driven by a SINGLE shared scalar
floor `cur.floor`.  It is a thin, honest re-export of the unification capstone
`unified_continuum_gap`: the only genuinely open input on either side is one
`UniformSpacingFloor` (here split as the codynamic `cod` and the curvature `cur`,
tied to the same scalar by `hshared`). -/

/-- **SCORECARD LINE: the continuum-gap obligation is reduced to one shared floor.**
Given the already-proved self-similar flow data (`T`, `uvSeed`, `A`) and curvature
spectral template `M`, and a SINGLE shared positive scalar floor — presented
codynamically as `cod` (a `CRealFloor` on the per-scale physical gap) and
curvature-wise as `cur` (a `QFloor` on the generator energies), tied together by
`hshared` — BOTH continuum conclusions follow:

  * the codynamic physical-gap floor `0 < cur.floor` with the per-scale bound
    `∀ N, ofQ' cur.floor ≤ physGapC N`, AND
  * the curvature route's strictly-positive continuum mass.

This is exactly `unified_continuum_gap`, surfaced as the project's continuum
scorecard line: the continuum-gap obligation bottoms out at the SINGLE open input
`UniformSpacingFloor`.  Nothing here inhabits `cod`/`cur` for the genuine
`a → 0` limit. -/
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

/-! ## 2. The OS-reconstruction route — same open input

The reconstructed GNS Hilbert space carries an (as-yet-unconstructed)
time-translation generator whose spectral gap above the vacuum is the physical
mass gap.  We present this honestly as a `Type`-level interface
`OSReconstructedGap` over the COMPLETE GNS Hilbert space
(`CompleteGNSHilbert D`).  Its per-scale gap family `genGap : Nat → Q'` is the
open datum a full OS reconstruction must supply (the generator itself is NOT built
here).  A `QFloor` on `genGap` then exhibits the reconstructed gap as bounded
below — uniformly in the scale — by the SAME `UniformSpacingFloor` scalar the
codynamic and curvature routes use. -/

/-- **The OS-reconstructed mass-gap interface (honest, unbuilt generator).**  Over
a complete GNS Hilbert space `hilbert : CompleteGNSHilbert D`, the `Type`-level
datum a full OS reconstruction must supply: a per-(volume)scale spectral-gap family
`genGap n` of the time-translation generator (the Hamiltonian) above the vacuum.

The generator and the proof that `genGap` is its genuine spectral gap are NOT
constructed in this development — they are the open OS-reconstruction content.
This structure carries only the gap quantity as honest interface data; it is NOT
inhabited for 4D Yang–Mills here. -/
structure OSReconstructedGap (D : GNSData) : Type 1 where
  /-- The complete constructive GNS Hilbert space the generator acts on. -/
  hilbert : CompleteGNSHilbert D
  /-- The per-scale spectral gap of the (open, unbuilt) time-translation generator
  above the vacuum — the datum a full OS reconstruction must supply. -/
  genGap : Nat → Q'

/-- **The OS-reconstruction route bottoms out at `UniformSpacingFloor`.**  Given an
`OSReconstructedGap` interface `R` over the complete GNS Hilbert space and a
`QFloor` `F` on its per-scale generator gap `R.genGap`, the reconstructed mass gap
is bounded below, uniformly in the scale, by the `UniformSpacingFloor` scalar
`F.floor > 0`:

  * `0 < F.floor`, and
  * `∀ n, F.floor ≤ R.genGap n`.

So the OS-reconstruction route consumes the SAME single open input the codynamic
and curvature routes do.  `F` is uninhabited for the genuine `a → 0` limit. -/
def reconstructed_gap_ge_uniform_floor {D : GNSData}
    (R : OSReconstructedGap D) (F : QFloor R.genGap) :
    (0 : Q') < F.floor ∧ ∀ n : Nat, F.floor ≤ R.genGap n :=
  ⟨F.floor_pos, F.bound⟩

/-- **The Wilson finite-volume specialization.**  An `OSReconstructedGap`
interface over the ACTUAL complete GNS Hilbert space of a finite-volume Wilson
theory (`WilsonGNSData.completeGnsHilbert`) consumes the same shared floor: its
reconstructed gap is bounded below by `F.floor` at every scale.  Records that the
OS-reconstruction route on the real Wilson Hilbert space converges on
`UniformSpacingFloor` too.  `R`/`F` are uninhabited for the genuine `a → 0`
limit. -/
def wilson_reconstructed_gap_ge_uniform_floor
    {A : ObservableMeasure.ObsAlg} (W : WilsonGNS.WilsonGNSData A)
    (R : OSReconstructedGap W.toGNSData)
    (_hbuilt : R.hilbert = W.completeGnsHilbert)
    (F : QFloor R.genGap) :
    (0 : Q') < F.floor ∧ ∀ n : Nat, F.floor ≤ R.genGap n :=
  -- `_hbuilt` pins the interface to the ACTUAL Wilson complete Hilbert space; the
  -- bound is read off the shared floor.
  reconstructed_gap_ge_uniform_floor R F

/-! ## 3. CAPSTONE — all three continuum routes converge on one shared floor

`all_routes_converge_on_uniform_floor` ties the codynamic, curvature, AND
OS-reconstruction routes to a SINGLE shared positive scalar `cur.floor`: the
codynamic floor `cod`, the curvature floor `cur`, and the reconstruction floor
`rec` are all the same number (`hshared`, `hsharedRec`).  From that ONE scalar, all
three positive-gap conclusions follow simultaneously. -/

/-- **THE CONTINUUM-FRONTIER CONVERGENCE CAPSTONE.**  ONE shared positive scalar
floor `cur.floor` — instantiated codynamically (`cod`), curvature-wise (`cur`), and
on the OS-reconstructed generator gap (`rec`), all tied to the SAME number by
`hshared`/`hsharedRec` — yields:

  * the codynamic physical-gap floor `0 < cur.floor` and `∀ N, ofQ' cur.floor ≤
    physGapC N`;
  * the curvature route's strictly-positive continuum mass;
  * the OS-reconstruction bound `∀ n, cur.floor ≤ R.genGap n`.

All three continuum routes therefore bottom out at the SINGLE open input
`UniformSpacingFloor`.  This is CONSOLIDATION: `cod`/`cur`/`rec` are uninhabited
for the genuine `a → 0` limit, and the OS generator inside `R` is unbuilt. -/
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

/-! ## 4. Documentation: the single open continuum input (AGENTS.md Rule 6)

PROVED (the REDUCTION — all routes consume one shared input):

  * `clay_continuum_reduced_to_uniform_floor`  ⟸ `unified_continuum_gap`
      (codynamic physical-gap floor + curvature continuum mass from one scalar);
  * `reconstructed_gap_ge_uniform_floor`       ⟸ the `QFloor` `bound`/`floor_pos`
      (the OS-reconstructed generator gap is bounded below by the same scalar);
  * `wilson_reconstructed_gap_ge_uniform_floor`
      (the same on the ACTUAL Wilson `completeGnsHilbert`);
  * `all_routes_converge_on_uniform_floor`
      (codynamic + curvature + OS-reconstruction, one shared scalar floor).

OPEN (the SINGLE remaining continuum input, NO inhabitant in this file):

  * `UniformSpacingFloor` (and its `QFloor`/`CRealFloor` specializations) — the one
    strictly-positive spacing-uniform gap floor for the genuine `a → 0` limit
    (Bałaban / Shen–Zhu–Zhu spectral-gap physics).  Uninhabited here.
  * the time-translation generator inside `OSReconstructedGap` — the unbuilt OS
    Hamiltonian whose spectral gap `genGap` is the open reconstruction datum.

The picture this module records: the project's continuum mass-gap obligation is no
longer several separate walls but ONE.  The codynamic flow route, the Bakry–Émery
curvature route, and the OS-reconstruction route (on the genuine complete GNS
Hilbert space of the Wilson theory) all converge on the SAME single open input,
`UniformSpacingFloor`.  Inhabiting it for 4D Yang–Mills — together with building
the OS generator — is exactly the open continuum mass-gap problem; nothing here
claims to have done so. -/

end YMGap.Continuum.ContinuumFrontierScorecard

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumFrontierScorecard.clay_continuum_reduced_to_uniform_floor
#print axioms YMGap.Continuum.ContinuumFrontierScorecard.reconstructed_gap_ge_uniform_floor
#print axioms YMGap.Continuum.ContinuumFrontierScorecard.wilson_reconstructed_gap_ge_uniform_floor
#print axioms YMGap.Continuum.ContinuumFrontierScorecard.all_routes_converge_on_uniform_floor
