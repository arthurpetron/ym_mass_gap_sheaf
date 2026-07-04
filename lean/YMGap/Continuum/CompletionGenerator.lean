/-
Milestone 11.11(b) — **transport: `FiniteVolumeBoundedH` → `genGap` consumed from a
BUILT operator on the completion.**

# Why this module exists (read first — and the HONEST scope)

Stage (a) (`Continuum/BoundedHamiltonianFiniteVol.lean`) built a genuine
finite-volume located-spectrum datum `FiniteVolumeBoundedH` over the excited
character tower `excG` — a self-adjoint bounded carrier `op = idTransfer.T` on the
ACTUAL complete GNS Hilbert space, with `spectrum_nonneg` (`H ≥ 0`), `vacuum_zero`
(`H ψ_vac = 0`), `Δ = −log sep`, `Δ_pos`, and the `noSpectrumIn` floor.

The scorecard interface (`Continuum/ContinuumFrontierScorecard.lean`) exposes the
OS-reconstruction leg as `OSReconstructedGap`, whose per-scale generator gap
`genGap : Nat → Q'` was, until now, a FREE datum — a `Nat → Q'` family posited by
the caller, with `wilson_reconstructed_gap_ge_uniform_floor` carrying a decorative
`_hbuilt : R.hilbert = W.completeGnsHilbert` pin.

This module performs the stage-(b) TRANSPORT: it stops treating
`OSReconstructedGap.genGap` and its `QFloor` as free parameters and instead
*constructs* them from the BUILT objects.  Concretely, for a finite-volume Wilson
theory `W`:

  * `builtSpectralGapData W …  := excG W.idTransfer …`   — the located spectral
    model over the real Wilson completion (`W.completeGnsHilbert` is
    DEFINITIONALLY `W.toGNSData.gnsComplete`, so `W.idTransfer` is a transfer
    operator on exactly this carrier — no completion-lift is needed);
  * `wilsonBuiltBoundedH W …   := mkFiniteVolumeBoundedH W.idTransfer …`  — the
    stage-(a) bounded-H carrier on that completion (supplies `Δ = −log sep`,
    `Δ_pos`, `spectrum_nonneg`, `selfAdjoint`);
  * `builtOSReconstructedGap W …` — an `OSReconstructedGap` whose `hilbert` is
    DEFINITIONALLY `W.completeGnsHilbert` (so the `_hbuilt` pin is `rfl`) and whose
    `genGap n := (builtSpectralGapData W …).massGap` is READ OFF the built located
    gap margin, not posited;
  * `builtQFloor W …` — the `QFloor` on that `genGap`, with `floor := massGap`,
    `floor_pos := massGap_pos`, `bound := rfl-reflexivity`.

The capstone `wilson_reconstructed_gap_from_built_operator` then feeds these BUILT
objects to `wilson_reconstructed_gap_ge_uniform_floor`, discharging the `_hbuilt`
pin by `rfl` — the OS-reconstruction leg now consumes a gap READ OFF a built
self-adjoint operator, not a free field.

# HONEST scope (do NOT overclaim)

FULLY BUILT (fixed-spacing / finite-volume):
  * the generator carrier `wilsonBuiltBoundedH.op = W.idTransfer.T` on the ACTUAL
    completion — self-adjoint, a genuine bounded object (no scaffolding gap);
  * `genGap` consumed from `massGap = gapMargin` (a BUILT located-gap margin), not
    a free `Nat → Q'`;
  * the per-scale domination `∀ n, floor ≤ genGap n` with `0 < floor` — from
    `massGap_pos`;
  * the `_hbuilt` pin discharged by `rfl`.

REDUCED (the single named transport residual):
  * **Q'/CReal boundary.** `OSReconstructedGap.genGap : Nat → Q'` is rational; the
    physical H-gap `builtBoundedH.Δ = −log sep` is `CReal`.  The honest rational
    surrogate tying them is `massGap = gapMargin = 1 − sep`.  Making `genGap`
    literally reflect `−log sep` requires ADDING a `CReal` field to
    `OSReconstructedGap` (a struct change forbidden here — it is load-bearing).
    Absent that, `genGap := massGap` is used and the physical `CReal` witness
    `Δ`/`Δ_pos` is carried ALONGSIDE (`wilson_reconstructed_gap_with_physical_gap`).
    This is the ONE named residual of the transport.

STILL OPEN (unchanged — this module does NOT close the continuum frontier):
  * Spacing-uniformity.  `massGap` is a FIXED-spacing margin, NOT spacing-uniform,
    so the genuine `a → 0` `UniformSpacingFloor` remains UNINHABITED.  Stage (b)
    upgrades the OS-reconstruction interface from "free datum" to "consumed from a
    built operator"; it does not inhabit the open continuum input.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure construction over `excG` / `mkFiniteVolumeBoundedH` and the scorecard
interface; every carrier is `Type`-level data (`genGap` is a `Nat → Q'` family,
`bound` is a `Pi` of the order relation, never a `Prop`-∃).  Each load-bearing
declaration is `#print axioms`-gated (permitted: `propext` / `Quot.sound`).  No
`Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.  No
deliberately-uninhabited Clay-frontier type is inhabited.
-/

import YMGap.Continuum.ContinuumFrontierScorecard
import YMGap.Continuum.BoundedHamiltonianFiniteVol

namespace YMGap.Continuum.CompletionGenerator

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.WilsonGNS
open YMGap.Continuum.HamiltonianSpectrumInf
open YMGap.Continuum.BoundedHamiltonianFiniteVol
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.SpacingUniformProgress
open YMGap.Continuum.UnifiedContinuumFloor
open YMGap.Continuum.ContinuumFrontierScorecard

/-! ## 1. The BUILT located spectral model on the real Wilson completion

`W.idTransfer : TransferOperator W.toGNSData.gnsComplete` and
`W.completeGnsHilbert := W.toGNSData.gnsComplete` are DEFINITIONALLY the same
carrier, so `excG W.idTransfer …` is a genuine located spectral-gap datum over the
actual Wilson complete Hilbert space — no completion-lift. -/

/-- **The BUILT located spectral-gap datum** on the finite-volume Wilson
completion: the excited character tower over the (identity) Wilson transfer
operator.  Its `.op` is a genuine bounded self-adjoint carrier on
`W.completeGnsHilbert`; its `.massGap = gapMargin = 1 − sep` is a strictly-positive
LOCATED margin. -/
def builtSpectralGapData {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat) :
    SpectralGapData W.toGNSData.gnsComplete :=
  excG W.idTransfer w hw0 hw1 N

/-- The built margin is strictly positive (`massGap_pos = gapMargin_pos`). -/
theorem builtSpectralGapData_massGap_pos {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) :
    (0 : Q') < (builtSpectralGapData W w hw0 hw1 N).massGap :=
  (builtSpectralGapData W w hw0 hw1 N).massGap_pos

/-! ## 2. The BUILT bounded-H carrier (stage (a))

The stage-(a) constructor `mkFiniteVolumeBoundedH` builds the bounded-H carrier
over ANY transfer operator `op : TransferOperator H` (self-adjoint `op = op.T`,
`Δ = −log sep` with `Δ_pos`, `spectrum_nonneg`, `vacuum_zero`, the reduced
`noSpectrumIn` floor) — conditional on the two pre-existing analytic residuals
`YOfMonotone` / `ArtanhMonotoneWindow` and the per-mode window certificates (NO new
frontier).  `builtBoundedH` re-exports it generically; `wilsonBuiltBoundedH`
specializes it to the ACTUAL Wilson completion at `op := W.idTransfer` (the plan's
`B`). -/

/-- **The BUILT stage-(a) bounded-H carrier** over a transfer operator `op`.  A thin
re-export of `mkFiniteVolumeBoundedH`.  Supplies the self-adjoint bounded carrier
`op.T`, the physical gap `Δ = −log sep` with `Δ_pos`, `spectrum_nonneg`,
`vacuum_zero`.  The return type is left to be INFERRED from
`mkFiniteVolumeBoundedH`. -/
def builtBoundedH {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (Y : YOfMonotone) (Aw : ArtanhMonotoneWindow)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (win : ∀ i (_hi : i < (excG op w hw0 hw1 N).model.k),
      Q'.abs (yOf ((excG op w hw0 hw1 N).model.lam i)
        (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)))
        ≤ recipOdd 1) :=
  mkFiniteVolumeBoundedH op w hw0 hw1 N Y Aw hwin win

/-- The built bounded-H physical gap `Δ` is `−log sep`, and it is strictly
positive — the located H-gap, read off the built carrier over any `op`. -/
theorem builtBoundedH_Δ_pos {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (Y : YOfMonotone) (Aw : ArtanhMonotoneWindow)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (win : ∀ i (_hi : i < (excG op w hw0 hw1 N).model.k),
      Q'.abs (yOf ((excG op w hw0 hw1 N).model.lam i)
        (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)))
        ≤ recipOdd 1) :
    CReal.IsPositive (builtBoundedH op w hw0 hw1 N Y Aw hwin win).Δ :=
  (builtBoundedH op w hw0 hw1 N Y Aw hwin win).Δ_pos

/-- **The Wilson-specialized BUILT bounded-H carrier** on the ACTUAL Wilson
completion `W.completeGnsHilbert` (defeq `W.toGNSData.gnsComplete`): the stage-(a)
carrier over the Wilson (identity) transfer operator `W.idTransfer`.  This is the
plan's `B := mkFiniteVolumeBoundedH W.idTransfer …` — the self-adjoint bounded
carrier `op = W.idTransfer.T`, `Δ = −log sep`, `Δ_pos`, `spectrum_nonneg` on the
real Wilson Hilbert space. -/
def wilsonBuiltBoundedH {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (Y : YOfMonotone) (Aw : ArtanhMonotoneWindow)
    (hwin : Q'.abs (yOf (excG W.idTransfer w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG W.idTransfer w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (win : ∀ i (_hi : i < (excG W.idTransfer w hw0 hw1 N).model.k),
      Q'.abs (yOf ((excG W.idTransfer w hw0 hw1 N).model.lam i)
        (plusOne_pos_of_nonneg ((excG W.idTransfer w hw0 hw1 N).model.lam_nonneg i)))
        ≤ recipOdd 1) :=
  builtBoundedH W.idTransfer w hw0 hw1 N Y Aw hwin win

/-! ## 3. The OS-reconstruction interface, `genGap` READ OFF the built margin

`builtOSReconstructedGap.hilbert` is DEFINITIONALLY `W.completeGnsHilbert`, so the
`_hbuilt` pin of `wilson_reconstructed_gap_ge_uniform_floor` becomes `rfl`.  Its
`genGap n := (builtSpectralGapData W …).massGap` is the rational surrogate
(`= 1 − sep`) read off the BUILT located gap, not a posited free family. -/

/-- **The BUILT OS-reconstruction interface.**  `hilbert` is definitionally the
real Wilson complete Hilbert space; `genGap n` is the BUILT located-gap margin
`massGap = 1 − sep` (constant in the scale at fixed spacing).  The `−log sep`
physical gap lives on the `CReal` side (`builtBoundedH.Δ`) — see the Q'/CReal
residual in the header. -/
def builtOSReconstructedGap {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat) :
    OSReconstructedGap W.toGNSData where
  hilbert := W.completeGnsHilbert
  genGap := fun _ => (builtSpectralGapData W w hw0 hw1 N).massGap

/-- The `_hbuilt` pin is now `rfl`: the interface hilbert IS the Wilson
completion. -/
theorem builtOSReconstructedGap_hilbert {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) :
    (builtOSReconstructedGap W w hw0 hw1 N).hilbert = W.completeGnsHilbert :=
  rfl

/-- **The BUILT `QFloor`** on the reconstructed `genGap`: the floor is the built
`massGap` itself, strictly positive (`massGap_pos`), dominating the (constant)
per-scale gap by reflexivity. -/
def builtQFloor {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat) :
    QFloor (builtOSReconstructedGap W w hw0 hw1 N).genGap where
  floor := (builtSpectralGapData W w hw0 hw1 N).massGap
  floor_pos := builtSpectralGapData_massGap_pos W w hw0 hw1 N
  bound := fun _ => Q'.le_refl' _

/-! ## 4. CAPSTONE — the OS-reconstruction leg consumed from a BUILT operator

`wilson_reconstructed_gap_from_built_operator` feeds the BUILT
`OSReconstructedGap` and `QFloor` (whose `genGap` is read off the built located
spectral model `builtSpectralGapData`) to the scorecard consumer
`wilson_reconstructed_gap_ge_uniform_floor`, discharging its `_hbuilt` pin by
`rfl`.  The reconstructed gap is now bounded below at every scale by a floor read
off a BUILT self-adjoint operator, not by a free field. -/

/-- **TRANSPORT CAPSTONE.**  The OS-reconstruction leg on the real Wilson
completion, with `genGap` CONSTRUCTED from the built located spectral model
(`builtSpectralGapData`) rather than posited:

  * `0 < floor` (`= massGap = 1 − sep > 0`, from `massGap_pos`), and
  * `∀ n, floor ≤ genGap n` (the built per-scale domination).

The `_hbuilt` pin is discharged by `rfl` — the interface hilbert IS
`W.completeGnsHilbert`.  This does NOT inhabit the open spacing-uniform floor:
`massGap` is a fixed-spacing margin. -/
theorem wilson_reconstructed_gap_from_built_operator
    {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat) :
    (0 : Q') < (builtQFloor W w hw0 hw1 N).floor
      ∧ ∀ n : Nat, (builtQFloor W w hw0 hw1 N).floor
          ≤ (builtOSReconstructedGap W w hw0 hw1 N).genGap n :=
  wilson_reconstructed_gap_ge_uniform_floor W
    (builtOSReconstructedGap W w hw0 hw1 N) rfl (builtQFloor W w hw0 hw1 N)

/-- **The transport with the physical `CReal` gap carried alongside** (the Q'/CReal
residual made explicit).  In addition to the rational-surrogate bound above, the
built located model supplies the genuine physical gap `Δ = −log sep` on the `CReal`
side, strictly positive:

  * `0 < floor` and `∀ n, floor ≤ genGap n`     (Q'-surrogate, `= 1 − sep`), AND
  * `IsPositive ((builtSpectralGapData …).hamiltonianGapReal hwin)`  (the physical
    `−log sep > 0`, the same `CReal` gap `builtBoundedH.Δ` carries).

The two are tied by `massGap = 1 − sep` (rational) vs `hamiltonianGapReal = −log
sep` (`CReal`) — the single named transport residual; carrying both is the honest
interface until `OSReconstructedGap` gains a `CReal` gap field.  The physical gap
`hamiltonianGapReal_pos` is definitionally the `Δ_pos` field of
`wilsonBuiltBoundedH`. -/
theorem wilson_reconstructed_gap_with_physical_gap
    {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (hwin : Q'.abs (yOf (excG W.idTransfer w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG W.idTransfer w hw0 hw1 N).gap)) ≤ recipOdd 1) :
    ( (0 : Q') < (builtQFloor W w hw0 hw1 N).floor
        ∧ ∀ n : Nat, (builtQFloor W w hw0 hw1 N).floor
            ≤ (builtOSReconstructedGap W w hw0 hw1 N).genGap n )
      ∧ CReal.IsPositive
          ((builtSpectralGapData W w hw0 hw1 N).hamiltonianGapReal hwin) :=
  ⟨wilson_reconstructed_gap_from_built_operator W w hw0 hw1 N,
   (builtSpectralGapData W w hw0 hw1 N).hamiltonianGapReal_pos hwin⟩

/-! ## 5. Specialization of the grand convergence with a BUILT reconstruction leg

The scorecard capstone `all_routes_converge_on_uniform_floor` takes the
OS-reconstruction floor `rec` as a free `QFloor`.  Here we feed it the BUILT
`builtQFloor`, so its OS-reconstruction conjunct is driven by a gap read off the
built operator (`hsharedRec := rfl` when the shared scalar is chosen to be
`massGap`).  The codynamic/curvature legs stay the honest open
`UniformSpacingFloor` inputs. -/

/-- **The grand convergence with the OS-reconstruction leg BUILT.**  Choosing the
shared floor scalar to be the built `massGap`, the OS-reconstruction conjunct of
`all_routes_converge_on_uniform_floor` is discharged by the built `builtQFloor`
(`hsharedRec := rfl`).  The codynamic (`cod`) and curvature (`cur`) floors remain
the open spacing-uniform inputs, tied to `massGap` by `hshared`. -/
theorem all_routes_with_built_reconstruction {b : Nat}
    {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (T : SelfSimilarTower b) (uvSeed : PosEv (T.w 0)) (Asch : SpacingSchedule)
    (M : ModeEnergyFloor)
    (cod : CRealFloor (physGapC b (sep T) Asch))
    (cur : QFloor (fun p : Nat × Nat => M.eigval p.1 p.2))
    (hshared : cod.floor = cur.floor)
    (hcur : cur.floor = (builtSpectralGapData W w hw0 hw1 N).massGap)
    (hstep : M.s * cur.floor < (1 : Q')) :
    ( ( (0 : Q') < cur.floor
          ∧ (∀ N', CReal.leEv (CReal.ofQ' cur.floor) (physGapC b (sep T) Asch N')) )
      ∧ CReal.IsPositive
          (toModeEnergyFloor M cur hstep).toModeCurvatureBound.continuumRate )
    ∧ ( ∀ n : Nat, cur.floor
          ≤ (builtOSReconstructedGap W w hw0 hw1 N).genGap n ) :=
  all_routes_converge_on_uniform_floor T uvSeed Asch M cod cur
    (builtOSReconstructedGap W w hw0 hw1 N) (builtQFloor W w hw0 hw1 N)
    hshared hcur.symm hstep

end YMGap.Continuum.CompletionGenerator

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CompletionGenerator.builtSpectralGapData
#print axioms YMGap.Continuum.CompletionGenerator.builtSpectralGapData_massGap_pos
#print axioms YMGap.Continuum.CompletionGenerator.builtBoundedH
#print axioms YMGap.Continuum.CompletionGenerator.builtBoundedH_Δ_pos
#print axioms YMGap.Continuum.CompletionGenerator.wilsonBuiltBoundedH
#print axioms YMGap.Continuum.CompletionGenerator.builtOSReconstructedGap
#print axioms YMGap.Continuum.CompletionGenerator.builtOSReconstructedGap_hilbert
#print axioms YMGap.Continuum.CompletionGenerator.builtQFloor
#print axioms YMGap.Continuum.CompletionGenerator.wilson_reconstructed_gap_from_built_operator
#print axioms YMGap.Continuum.CompletionGenerator.wilson_reconstructed_gap_with_physical_gap
#print axioms YMGap.Continuum.CompletionGenerator.all_routes_with_built_reconstruction
