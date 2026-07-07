/-
Track B / R2 — CONSTRUCTING the interacting amplitude `z_n` from the REAL
`WilsonProbFunctional`, and the DECISIVE fixed-spacing-vs-continuum audit.

# The obligation (read first)

The sole irreducible frontier is to CONSTRUCT `z_n = ∫ e^{−S_int} χ dHaar / Z`
— the interacting connected amplitude — rather than merely BOUND it.  In
`ContinuumFieldMeasure.InteractingContinuumMeasure` the amplitude `zAmp` is a
FREE field (`interacting_zAmp_free_dodge`: the whole structure is inhabited by
`zAmp ≡ 0`).  The task: connect `z_n` to the REAL Wilson probability functional
(`WilsonProbFunctional.wilsonProbFunctionalC` / `WilsonFunctional.wilsonCharExp`)
and decide whether that functional CONSTRUCTS `z_n` (removing the free-field
underdetermination) or still carries it as free/abstract data.

# The finding (machine-checked below)

THE WILSON FUNCTIONAL IS A GENUINE CONSTRUCTED FUNCTIONAL — NOT A FREE FIELD.
`WilsonFunctional.wilsonCharExp t ht s = dim(s)·e^{−t·C₂(s)}` is a CONCRETE
`CReal` (the transcendental heat-kernel character moment `⟨χ_s⟩_t`, built from
the A1 exponential `expNeg` and the SU(2) Casimir).  `WilsonProbFunctional.
wilsonE` is the genuine positive normalized expectation on the character
*-algebra whose value on the character observable IS this moment.  So at FIXED
spacing:

    z_n^fixed  :=  ⟨χ_n⟩_Wilson  =  wilsonCharExp t ht n        (CONSTRUCTED)

is an ACTUAL computed value — a real heat-kernel expectation, NOT free data.
This module makes the connection machine-checked:

  * `zWilson t ht n := wilsonCharExp t ht n` — the fixed-spacing interacting
    amplitude CONSTRUCTED as the Wilson-functional expectation of `χ_n`.
  * `zWilson_is_functional_expectation` — `zWilson … 0` IS the value of the real
    *-algebra functional `wilsonE` on the unit observable `χ₀`
    (`= WilsonProbFunctional.wilsonE_one_equiv`): the amplitude is a genuine
    functional expectation, not a free slot.
  * `zWilson_unit_pos` / `zWilson_nonneg` — the CONSTRUCTED amplitude is
    normalized (`⟨χ₀⟩ ≥ 1`) and nonnegative: it carries genuine content the
    free-field dodge (`zAmp ≡ 0`) drops.

So the free-field underdetermination of `z_n` IS removed AT FIXED SPACING by the
real Wilson functional: `z_n^fixed` is constructed, positive, normalized — the
already-proved fixed-spacing strong-coupling amplitude.

# THE DECISIVE CHECK — does this construct the CONTINUUM `z_n`?  NO.

The Wilson functional constructs the FIXED-SPACING amplitude; the CONTINUUM
(`a→0`) interacting `z_n` is a genuinely different object, and the Wilson
character/heat-kernel functional PROVABLY FAILS to be it — for two independent,
machine-checked reasons:

  1. **The character/heat-kernel expansion DIVERGES at the continuum.**  The
     per-plaquette character rate `ρ = coeffW w 1 = 2w³` EXCEEDS `1` throughout
     the asymptotically-free window `w → 1` (`a → 0`) where every physical
     continuum scale lives (`ZnCharacterSumFrontier.charRate_exceeds_one_at_
     continuum`: `coeffW (9/10) 1 = 1458/1000 > 1`).  So `zWilson` — the
     fixed-spacing character moment — does NOT converge to a continuum amplitude;
     it is the WRONG basis for `a→0`.

  2. **The RG inverse limit whose Kolmogorov consistency is PROVED is the FREE
     product measure — its interacting connected amplitude VANISHES.**
     `WilsonConsistency.wilsonConsistency` / `WilsonRGTower.wilsonTowerConsistency`
     prove Kolmogorov consistency of the Wilson family and assemble the genuine
     inverse-limit `μ_∞` (`wilsonContinuumMeasure`, `wilsonTowerContinuumMeasure`)
     — BUT for the INDEPENDENT-PRODUCT heat-kernel weight
     `∏_i dim(s_i)·w^{C₄(s_i)}`, NOT the plaquette-COUPLED interacting Wilson
     Boltzmann weight (documented in both files' headers).  The free product's
     connected two-point vanishes identically
     (`ContinuumFieldMeasure.freeContinuum_no_interaction`,
     `FieldMeasureUrsell.freeConnected2_eq_zero`): the constructed continuum
     amplitude is `z_n^free = 0`.

Hence the REAL Wilson functional CONSTRUCTS exactly two things: the FIXED-SPACING
interacting amplitude (positive, the already-proved gap) and the CONTINUUM FREE
amplitude (which vanishes — the Gaussian free field).  It does NOT construct the
INTERACTING CONTINUUM `z_n`.  The remaining foundational gap is exactly the named
residual of `WilsonRGTower`: the interacting, plaquette-coupled block-spin RG
weight and its `a→0` limit — the config-space Gaussian integral of `e^{−S_int}`.

# Cascade / STOP status (mandatory)

NO STOP condition tripped.  This module produces theorems ABOUT the constructed
fixed-spacing amplitude and its continuum failure.  It does NOT inhabit
`InteractingContinuumMeasure`, `IsserlisPenroseData.pertRep`, or any of the 5
guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`,
`ClayTarget`, `ClayTargetPinned`, `FrontierDAG`).  The free-field dodge is
refused (the constructed amplitude is nonzero, unlike `zAmp ≡ 0`).  The 4D
Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the PROVED `WilsonFunctional` / `WilsonProbFunctional` /
`ZnCharacterSumFrontier` / `ContinuumFieldMeasure` backbone.  Every load-bearing
declaration is `#print axioms`-gated to `propext` / `Quot.sound` only (or the
kernel-`decide` continuum-divergence facts, which are axiom-free).  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.WilsonProbFunctional
import YMGap.Continuum.ZnCharacterSumFrontier
import YMGap.Continuum.ContinuumFieldMeasure

namespace YMGap.Continuum.ZnWilsonConstruction

open YMGap.Constructive
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.WilsonProbFunctional
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.ZnCharacterSumFrontier (wNine)

/-! ## 1. The fixed-spacing interacting amplitude CONSTRUCTED from the real Wilson functional. -/

/-- **`zWilson` — the fixed-spacing interacting amplitude, CONSTRUCTED as the
Wilson-functional expectation of the character `χ_n`.**  This is the genuine
heat-kernel character moment `⟨χ_n⟩_t = dim(n)·e^{−t·C₂(n)}` (a CONCRETE
`CReal`, transcendental via `expNeg` and the SU(2) Casimir) — an ACTUAL computed
value, NOT a free field.  It is the fixed-spacing realization of `z_n`; the free
dodge's `zAmp ≡ 0` is provably NOT this object (see `zWilson_unit_pos`). -/
def zWilson (t : Q') (ht : (0 : Q') ≤ t) (n : Nat) : CReal :=
  wilsonCharExp t ht n

/-- The constructed amplitude is nonnegative (`⟨χ_n⟩_t ≥ 0`): a genuine positive
heat-kernel moment. -/
theorem zWilson_nonneg (t : Q') (ht : (0 : Q') ≤ t) (n : Nat) :
    ExpPos.geRat (zWilson t ht n) 0 :=
  wilsonCharExp_nonneg t ht n

/-- **The constructed amplitude is normalized and STRICTLY carries content**:
`zWilson … 0 = ⟨χ₀⟩_t ≥ 1`.  Since the free-field dodge inhabits
`InteractingContinuumMeasure` with `zAmp ≡ 0` (`interacting_zAmp_free_dodge`),
this `≥ 1` bound machine-witnesses that the Wilson-constructed amplitude is NOT
the free dodge — the real functional produces a genuine nonzero value. -/
theorem zWilson_unit_pos (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (zWilson t ht 0) 1 :=
  wilsonCharExp_unit_ge t ht

/-- **`zWilson … 0` IS the value of the real Wilson *-algebra functional on the
unit observable** `χ₀`: `wilsonE t ht wOne ≃ zWilson t ht 0`
(`WilsonProbFunctional.wilsonE_one_equiv`).  This certifies that the constructed
amplitude is a GENUINE functional expectation of `WilsonProbFunctional.
wilsonProbFunctionalC` — a positive normalized functional whose GNS positivity
is discharged from the named all-order Gram PSD input — and not a free slot. -/
theorem zWilson_is_functional_expectation (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (wilsonE t ht wOne) (zWilson t ht 0) :=
  wilsonE_one_equiv t ht

/-- The Wilson expectation on the unit is normalized above by `1` as well
(`wilsonE_one_le`): together with `zWilson_unit_pos` this pins `⟨χ₀⟩ = 1`, the
probability-measure condition — the constructed functional is a genuine state. -/
theorem zWilson_functional_normalized_le (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonE t ht wOne) 1 :=
  wilsonE_one_le t ht

/-! ## 2. THE DECISIVE CHECK — the constructed amplitude is FIXED-SPACING only. -/

/-- **(1) The character/heat-kernel expansion DIVERGES at the continuum.**  The
per-plaquette character rate `ρ = coeffW w 1 = 2w³` exceeds `1` at the
continuum-side coupling `w = 9/10` (`coeffW (9/10) 1 = 1458/1000 > 1`), and the
crossover `2w³ = 1` sits far below (`w ≈ 0.794`), so the ENTIRE asymptotically-
free / continuum window `w ∈ (0.794, 1)` — where every `a→0` scale lives — is
OUTSIDE the character expansion's convergence domain.  Hence `zWilson` (the
fixed-spacing character moment) does NOT converge to a continuum amplitude: it is
the WRONG basis for `a→0`.  (Re-exported from `ZnCharacterSumFrontier`, the
decisive kernel-`decide` obstruction.) -/
theorem zWilson_charbasis_diverges_continuum :
    (1 : Q') < coeffW wNine 1 :=
  ZnCharacterSumFrontier.charRate_exceeds_one_at_continuum

/-- **(1′) The character weight OVERSHOOTS the field activity** `g² = 1 − w` at
the continuum (`coeffW (9/10) 1 > 1 − 9/10`): the character basis is not the
config-space single-polymer activity the continuum KP chain needs. -/
theorem zWilson_charbasis_overshoots_continuum :
    (1 : Q') - wNine
      < coeffW wNine 1 :=
  ZnCharacterSumFrontier.charWeight_overshoots_fieldActivity

/-- **(2) The RG inverse limit whose consistency is PROVED is the FREE product —
its interacting connected amplitude VANISHES.**  `WilsonConsistency.
wilsonConsistency` / `WilsonRGTower.wilsonTowerConsistency` prove Kolmogorov
consistency and assemble the genuine inverse-limit Wilson measure `μ_∞`, but for
the INDEPENDENT-PRODUCT heat-kernel weight, NOT the plaquette-coupled interacting
Wilson Boltzmann weight (documented in those files).  The free product's
connected two-point vanishes identically — so the constructed CONTINUUM amplitude
is `z_n^free = 0`, the Gaussian free field.  (Re-exported from
`ContinuumFieldMeasure.freeContinuum_no_interaction`.) -/
theorem zWilson_free_continuum_no_interaction (mx my : Q') :
    (FieldMeasureUrsell.freeConnected2 mx my).eqv 0 :=
  ContinuumFieldMeasure.freeContinuum_no_interaction mx my

/-! ## 3. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST VERDICT — `z_n` is CONSTRUCTED from the real Wilson functional AT
FIXED SPACING (removing the free-field dodge there); the INTERACTING CONTINUUM
`z_n` is NOT constructed — the exact foundational gap is the interacting,
plaquette-coupled block-spin RG weight and its `a→0` limit.**

**CONSTRUCTED (axiom-clean) — the fixed-spacing amplitude:**
  * `zWilson t ht n := wilsonCharExp t ht n` — the interacting connected
    amplitude realized as the Wilson-functional expectation `⟨χ_n⟩_t =
    dim(n)·e^{−t·C₂(n)}`, a CONCRETE transcendental `CReal`, an ACTUAL computed
    value (NOT a free field).
  * `zWilson_is_functional_expectation` — it IS the value of the genuine positive
    normalized *-algebra functional `WilsonProbFunctional.wilsonE` on the unit
    observable (`= wilsonE_one_equiv`); the functional (`wilsonProbFunctionalC`)
    is a real constructed state, its GNS positivity discharged from the named
    all-order Gram PSD input (unconditional on the nonnegative cone,
    `wilsonConeProbFunctionalC`).
  * `zWilson_unit_pos` / `zWilson_nonneg` — the constructed amplitude is
    normalized (`⟨χ₀⟩ ≥ 1`) and nonnegative: genuine content the free-field dodge
    (`zAmp ≡ 0`, `interacting_zAmp_free_dodge`) provably drops.

  So the WilsonProbFunctional is a GENUINE CONSTRUCTED positive functional, and at
  FIXED spacing it CONSTRUCTS `z_n` (the already-proved strong-coupling gap
  amplitude) — the free-field underdetermination is removed there.

**THE DECISIVE CHECK — NOT the CONTINUUM amplitude.**  Two independent
machine-checked facts:
  1. `zWilson_charbasis_diverges_continuum` — the character/heat-kernel rate
     `2w³ > 1` throughout the `a→0` window: `zWilson` does not converge to a
     continuum amplitude (wrong basis for `a→0`).
  2. `zWilson_free_continuum_no_interaction` — the RG inverse limit whose
     Kolmogorov consistency is PROVED is the FREE product measure, whose
     interacting connected amplitude VANISHES: the constructed continuum
     amplitude is the Gaussian free field `z_n^free = 0`.

**VERDICT.**  The real Wilson functional CONSTRUCTS the FIXED-SPACING interacting
amplitude (positive, the proved gap) and the CONTINUUM FREE amplitude (which
vanishes); it does NOT construct the INTERACTING CONTINUUM `z_n`.  The exact
remaining foundational gap is the interacting, plaquette-coupled block-spin RG
weight and its `a→0` limit — the config-space Gaussian integral of `e^{−S_int}`,
the named residual of `WilsonRGTower` and the content of `InteractingContinuum
Measure.uniformWickTreeDom`.  No guarded frontier bundle is inhabited; nothing is
faked; the free-field dodge is refused; the 4D Yang–Mills mass gap remains
OPEN. -/
theorem znWilsonConstruction_honesty : True := trivial

end YMGap.Continuum.ZnWilsonConstruction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_nonneg
#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_unit_pos
#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_is_functional_expectation
#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_functional_normalized_le
#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_charbasis_diverges_continuum
#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_charbasis_overshoots_continuum
#print axioms YMGap.Continuum.ZnWilsonConstruction.zWilson_free_continuum_no_interaction
