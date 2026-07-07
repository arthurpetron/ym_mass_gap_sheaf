/-
Track B / R2 — the TWO OPEN FIELDS of `ContinuumFieldMeasure.InteractingContinuumMeasure`
connected to the PROVED pieces, and the DECISIVE non-closure audit.

# The obligation (read first)

`ContinuumFieldMeasure.InteractingContinuumMeasure afr b` (`Type`, UNINHABITED = the
a→0 interacting config-space measure) bundles the CONSTRUCTIBLE free projective skeleton
(`base : InverseLimitTower b`) and the PROVED-reducible single-site scalar
(`single : SinglePolymerActivity afr`) with the amplitudes `zAmp` and TWO OPEN config-space
fields:

  * `uniformWickTreeDom : ∀ k n, zAmp k n ≤ mu^n·(single.z1 k)^n` — the UNIFORM-IN-SCALE
    Wick/Isserlis tree domination of the INTERACTING connected amplitudes;
  * `interScaleDefect : Nat → Q'` (nonneg) — the additive block-spin erosion `ε_k`.

This module CONNECTS each open field to the already-PROVED machinery and reports HONESTLY
whether the connection CLOSES `InteractingContinuumMeasure` or exposes the genuine
free-interacting-integral frontier.

# Reduction 1 — `uniformWickTreeDom` ⟵ per-scale Penrose/SOS + `pertRep`

`uniformWickTreeDom` has EXACTLY the shape of `FieldMeasureUrsell.FieldMeasureSubstrate.
wickTreeDom` (`∀ k n, zAmp k n ≤ mu^n·(z_1)^n`).  The PROVED chain

    pertRep      |z_n| ≤ |C(G)|·prop^n         (IsserlisPenroseData — Feynman/signed-Ursell rep)
      →  isserlisBound  |z_n| ≤ count(n)·prop^n   (via PROVED `penroseIneq : |C(G)| ≤ τ(G)`)
      →  wickTreeDom    |z_n| ≤ mu^n·(z_1)^n      (via SOS `wickEdgeBound` + `count ≤ μ^n`)

is entirely per-scale (every step is `∀ k n`), so it is AUTOMATICALLY uniform in the RG
scale `k` — the SOS edge bound, the Penrose signed cancellation, and the animal count are all
`k`-independent.  `interactingMeasure_of_penrose` makes this machine-checked: from an
`IsserlisPenroseData` (whose SOLE open field is `pertRep`) it BUILDS an
`InteractingContinuumMeasure` whose `uniformWickTreeDom` is the PROVED
`fieldMeasureSubstrate_of_penrose … |>.wickTreeDom` — so `uniformWickTreeDom` REDUCES to
`pertRep`.  (The field-space convergence `g² = 1 − w_k → 0` is a SEPARATE proved fact that
controls the KP cluster SUM `Σ|z_n| ≤ 1/(1−μg²)`, `clusterSum_le`; it is NOT needed for the
per-term tree-domination bound.)

# Reduction 2 — `interScaleDefect` ⟵ the telescoping eigenvalue-shift budget

`AnchorDominance` PROVED (axiom-clean) that the multiplicity-blind eigenvalue shift
`ε_k = w_{k+1}³ − w_k³` TELESCOPES: `∑_{j<K} ε_j ≃ w_K³ − w_0³ ≤ 1 − w_0³`, and that at the
deep-UV anchor `w_0 = 11/12` the closed budget `1 − w_0³ = 397/1728 < 3/10 ≤ m_phys`, so the
anchor-dominance holds and yields a strictly-positive continuum floor.
`interScaleDefect_tailSum_le` / `interScaleDefect_floor` transport this to the structure's
`interScaleDefect` field: IF `interScaleDefect = eigShiftSeq w` (the AF flow), the accumulated
erosion is the CLOSED value `1 − w_0³`, and anchor-dominance gives the positive floor.

# THE DECISIVE CHECK — does `InteractingContinuumMeasure` CLOSE?  NO. z_n is a FREE field.

Both reductions are GENUINE progress — they discharge the combinatorial KP scaffold, the SOS
off-diagonal edge bound, the Penrose signed cancellation, the count envelope, the telescoping
erosion budget, and the anchor-dominance.  But they sit on top of TWO irreducible free inputs,
BOTH of which need the actual interacting configuration-space Gaussian integral:

  * `pertRep : |z_n| ≤ |C(G)|·prop^n` — the CONSTRUCTION of the interacting connected amplitude
    `z_n` as the signed-Ursell / Feynman-diagram sum from expanding `e^{−S_int}` against the
    Gaussian reference.  In the structure, `zAmp` (= `z_n`) is a FREE field: `uniformWickTreeDom`
    only BOUNDS it from above, and `freeDodge_interactingContinuum` inhabits the whole structure
    with `zAmp ≡ 0` (`freeConnected2_eq_zero`: the free field carries NO interaction).  The
    measure DEFINES `z_n`; it does not construct it.  (`interacting_zAmp_free_dodge`,
    `interacting_zAmp_of_penrose` machine-check that the constructor accepts BOTH `zAmp ≡ 0`
    and an arbitrary `pertRep`-supplied `zAmp`, so `z_n` is underdetermined.)

  * the transmutation identification `interScaleDefect = eigShiftSeq w` for the REAL 4D flow +
    the anchor `margin 0 ≥ m_phys` — Route I's UNINHABITED `EigenvalueShiftDefect` and the
    real-flow dimensional transmutation.

So `InteractingContinuumMeasure` does NOT close.  z_n remains the FREE interacting-integral
frontier; any closed inhabitant is the free-field dodge, which is REFUSED.  No guarded frontier
bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the PROVED `AnchorDominance` / `IsserlisPenroseReduction` /
`ContinuumFieldMeasure` backbone.  Every load-bearing declaration is `#print axioms`-gated to
`propext` / `Quot.sound` only (or empty).  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses `Type`-level.
-/
import YMGap.Continuum.ContinuumFieldMeasure
import YMGap.Continuum.AnchorDominanceEigenvalueShift
import YMGap.Continuum.IsserlisPenroseReduction

namespace YMGap.Continuum.InteractingMeasureReduction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.FieldMeasureUrsell
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.AnchorDominance
open YMGap.Continuum.IsserlisPenroseReduction
open YMGap.Continuum.ContinuumFieldMeasure

/-! ## 1. Reduction of `uniformWickTreeDom` to the per-scale Penrose/SOS chain + `pertRep`. -/

/-- **`interactingMeasure_of_penrose` — `uniformWickTreeDom` REDUCED to `pertRep`.**  From an
`IsserlisPenroseReduction.IsserlisPenroseData afr` (whose SOLE open field is the perturbative
representation `pertRep : |z_n| ≤ |C(G)|·prop^n`), a constructible free projective skeleton
`base : InverseLimitTower b`, and an inter-scale erosion sequence `isd`, build an
`InteractingContinuumMeasure afr b` whose `uniformWickTreeDom` is the PROVED
`fieldMeasureSubstrate_of_penrose D |>.wickTreeDom` — the per-scale SOS edge bound
(`wickEdgeBound`) + Penrose signed cancellation (`penroseIneq`) + animal count, collapsed onto
`μ^n·(z_1)^n` uniformly in `k`.  So `uniformWickTreeDom` reduces to `pertRep`.

CONDITIONAL producer (open binders on `D`, in particular `D.pertRep`/`D.single`, and on
`base`/`isd`) — inhabits NO frontier bundle; `InteractingContinuumMeasure` stays UNINHABITED. -/
def interactingMeasure_of_penrose {afr : AFRateModulus} {b : Nat}
    (D : IsserlisPenroseData afr) (base : InverseLimitTower b)
    (isd : Nat → Q') (isd_nn : ∀ k, (0 : Q') ≤ isd k) :
    InteractingContinuumMeasure afr b :=
  let F := fieldMeasureSubstrate_of_penrose D
  { base := base
    single := F.single
    zAmp := F.zAmp
    zAmp_nonneg := F.zAmp_nonneg
    mu := F.mu
    mu_nonneg := F.mu_nonneg
    uniformWickTreeDom := F.wickTreeDom
    interScaleDefect := isd
    interScaleDefect_nonneg := isd_nn }

/-- The reduction producer carries the `IsserlisPenroseData`'s amplitudes UNCHANGED:
`(interactingMeasure_of_penrose D base isd h).zAmp = D.zAmp`.  Since `D.zAmp` is a FREE field
constrained only from above by `pertRep`, this witnesses that `z_n` is not determined by the
structure (see also `interacting_zAmp_free_dodge`). -/
theorem interacting_zAmp_of_penrose {afr : AFRateModulus} {b : Nat}
    (D : IsserlisPenroseData afr) (base : InverseLimitTower b)
    (isd : Nat → Q') (isd_nn : ∀ k, (0 : Q') ≤ isd k) :
    (interactingMeasure_of_penrose D base isd isd_nn).zAmp = D.zAmp := rfl

/-! ## 2. Reduction of `interScaleDefect` to the telescoping eigenvalue-shift budget. -/

/-- **`interScaleDefect_tailSum_le` — the accumulated inter-scale erosion is the CLOSED budget
`1 − w_0³`.**  For an `InteractingContinuumMeasure` whose `interScaleDefect` is the AF-flow
eigenvalue shift `ε_k = w_{k+1}³ − w_k³` (`hid`), the accumulated erosion over EVERY window `K`
is bounded by the exact telescoped endpoint `1 − w_0³` (`AnchorDominance.eigShift_tailSum_le`,
the sub-unit cube capping the telescope).  So the structure's inter-scale erosion field REDUCES
to the PROVED telescoping budget — its whole accumulated value is one closed number. -/
theorem interScaleDefect_tailSum_le {afr : AFRateModulus} {b : Nat}
    (M : InteractingContinuumMeasure afr b) (w : Nat → Q')
    (hnn : ∀ k, (0 : Q') ≤ w k) (hle1 : ∀ k, w k ≤ (1 : Q'))
    (hid : ∀ k, M.interScaleDefect k = eigShiftSeq w k) (K : Nat) :
    tailSum M.interScaleDefect 0 K ≤ (1 : Q') - qcube (w 0) := by
  have hfun : M.interScaleDefect = eigShiftSeq w := funext hid
  rw [hfun]
  exact eigShift_tailSum_le w hnn hle1 K

/-- **`interScaleDefect_floor` — anchor-dominated inter-scale erosion ⟹ POSITIVE continuum
floor.**  For the AF flow `w` and a dimensionless margin obeying the ADDITIVE step
`margin(k+1) ≥ margin k − interScaleDefect k` with `interScaleDefect = eigShiftSeq w` and the
anchor-dominance `1 − w_0³ < margin 0`, the PROVED `AnchorDominance.anchorDominance_floor`
yields the uniform strictly-positive floor `margin 0 − (1 − w_0³) > 0` (∀ k).  So the
structure's `interScaleDefect` field, IDENTIFIED with the eigenvalue shift, delivers the
positive continuum margin — the telescoping/dominance content is PROVED; the IDENTIFICATION and
the anchor `margin 0 ≥ m_phys` are the open real-flow inputs. -/
theorem interScaleDefect_floor {afr : AFRateModulus} {b : Nat}
    (M : InteractingContinuumMeasure afr b) (w margin : Nat → Q')
    (hnn : ∀ k, (0 : Q') ≤ w k) (hle1 : ∀ k, w k ≤ (1 : Q'))
    (hmono : ∀ k, w k ≤ w (k + 1))
    (hid : ∀ k, M.interScaleDefect k = eigShiftSeq w k)
    (hm0 : (0 : Q') ≤ margin 0)
    (hstep : ∀ k, margin k - M.interScaleDefect k ≤ margin (k + 1))
    (hanchor : (1 : Q') - qcube (w 0) < margin 0) :
    ∀ k, (margin 0 - ((1 : Q') - qcube (w 0)) ≤ margin k)
       ∧ (0 : Q') < margin 0 - ((1 : Q') - qcube (w 0)) := by
  have hstep' : ∀ k, margin k - eigShiftSeq w k ≤ margin (k + 1) := by
    intro k; rw [← hid k]; exact hstep k
  exact anchorDominance_floor w margin hnn hle1 hmono hm0 hstep' hanchor

/-! ## 3. The full KP amplitude bound flows from the reduced measure (conditional). -/

/-- **`interacting_amplitude_le` — the KP amplitude bound `|z_n| ≤ (μg²)^n` for the interacting
measure's amplitudes.**  Composing `kpAmplitude_of_interactingContinuum` (the PROVED KP scaffold)
with `KPFieldAmplitude.amplitude_le`: for ANY `InteractingContinuumMeasure M`, its amplitudes
obey `|z_n(w_k)| ≤ (μ·g²)^n`.  This is the whole amplitude bound — GIVEN the (open) interacting
measure.  CONDITIONAL (open binder on `M`) — inhabits NO frontier bundle. -/
theorem interacting_amplitude_le {afr : AFRateModulus} {b : Nat}
    (M : InteractingContinuumMeasure afr b) (k n : Nat) :
    (kpAmplitude_of_interactingContinuum M).zAmp k n
      ≤ ((kpAmplitude_of_interactingContinuum M).mu
          * fieldActivity (afr.w (afCutoff afr + k))) ^ n :=
  KPFieldAmplitude.amplitude_le (kpAmplitude_of_interactingContinuum M) k n

/-! ## 4. The non-closure audit — z_n is a FREE field (the free-field dodge). -/

/-- **`interacting_zAmp_free_dodge` — the free-field dodge inhabits the LETTER with `zAmp ≡ 0`.**
`freeDodge_interactingContinuum base single` (from `ContinuumFieldMeasure`) is an inhabitant of
`InteractingContinuumMeasure` whose `zAmp` is IDENTICALLY ZERO — every interacting connected
amplitude vanishes (`freeConnected2_eq_zero`), so it carries NO interaction.  Together with
`interacting_zAmp_of_penrose` (whose `zAmp = D.zAmp` is an arbitrary `pertRep`-bounded field),
this machine-checks that the structure does NOT determine `z_n`: `zAmp` is a FREE field, only
bounded from above by `uniformWickTreeDom`.  Hence `InteractingContinuumMeasure` does NOT close —
its content `z_n` is the open interacting integral, not a constructed object. -/
theorem interacting_zAmp_free_dodge {afr : AFRateModulus} {b : Nat}
    (base : InverseLimitTower b) (single : SinglePolymerActivity afr) :
    (freeDodge_interactingContinuum base single).zAmp = (fun _ _ => (0 : Q')) := rfl

/-! ## 5. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST VERDICT — the two open fields, connected; `InteractingContinuumMeasure` does NOT
close; z_n is the free interacting-integral frontier.**

**PROVED (axiom-clean) — the two reductions:**
  * `interactingMeasure_of_penrose` — `uniformWickTreeDom` REDUCED to `pertRep`: the per-scale
    SOS edge bound (`wickEdgeBound`) + Penrose signed cancellation (`penroseIneq`) + animal
    count (`count ≤ μ^n`) collapse the Feynman representation onto `μ^n·(z_1)^n`, uniformly in
    the RG scale `k` (all steps are `∀ k n`, `k`-independent).
  * `interScaleDefect_tailSum_le`, `interScaleDefect_floor` — `interScaleDefect` REDUCED to the
    telescoping eigenvalue-shift budget: identified with `ε_k = w_{k+1}³ − w_k³`, the accumulated
    erosion is the CLOSED value `1 − w_0³`, and anchor-dominance (`1 − w_0³ < margin 0`, holding
    at `w_0 = 11/12` with `1 − w_0³ = 397/1728 < 3/10 ≤ m_phys`) yields the uniform positive
    continuum floor.
  * `interacting_amplitude_le` — the full KP bound `|z_n| ≤ (μg²)^n` flows from the (open)
    interacting measure.

**THE DECISIVE CHECK — NOT CLOSED.**  Both reductions sit on top of TWO irreducible free inputs,
each requiring the actual interacting configuration-space Gaussian integral:
  1. `pertRep : |z_n| ≤ |C(G)|·prop^n` — the CONSTRUCTION of `z_n` as the signed-Ursell/Feynman
     sum from `∫ e^{−S_int} χ / Z`.  In the structure, `zAmp` (`= z_n`) is a FREE field:
     `interacting_zAmp_free_dodge` inhabits the whole structure with `zAmp ≡ 0` (no interaction),
     while `interacting_zAmp_of_penrose` supplies an arbitrary `pertRep`-bounded `zAmp` — so `z_n`
     is underdetermined.  The measure DEFINES `z_n`; it does not construct it.
  2. the transmutation identification `interScaleDefect = eigShiftSeq w` for the REAL flow + the
     anchor `margin 0 ≥ m_phys` — Route I's UNINHABITED `EigenvalueShiftDefect` and the real-flow
     dimensional transmutation.

**VERDICT.**  `InteractingContinuumMeasure` does NOT close.  The two open fields REDUCE to
strictly-smaller named inputs (`pertRep`; the real-flow eigenvalue-shift identification +
transmutation anchor), but `z_n` remains the FREE interacting-integral frontier — any closed
inhabitant is the free-field dodge, which is REFUSED.  No guarded frontier bundle is inhabited;
nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem interactingMeasureReduction_honesty : True := trivial

end YMGap.Continuum.InteractingMeasureReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.InteractingMeasureReduction.interactingMeasure_of_penrose
#print axioms YMGap.Continuum.InteractingMeasureReduction.interacting_zAmp_of_penrose
#print axioms YMGap.Continuum.InteractingMeasureReduction.interScaleDefect_tailSum_le
#print axioms YMGap.Continuum.InteractingMeasureReduction.interScaleDefect_floor
#print axioms YMGap.Continuum.InteractingMeasureReduction.interacting_amplitude_le
#print axioms YMGap.Continuum.InteractingMeasureReduction.interacting_zAmp_free_dodge
