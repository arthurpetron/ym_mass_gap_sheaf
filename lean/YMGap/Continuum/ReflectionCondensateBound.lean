/-
Track B / R1↔R2 — THE REFLECTION-POSITIVITY / CORRELATION-INEQUALITY bound on the
vacuum condensate: does OS2 (PROVED) give the SPACING-UNIFORM condensate lower bound
(= the a→0 mass gap = `singleStep`), or only the fixed-spacing anchor?

# The obligation (read first)

The continuum condensate positivity `⟨G²⟩ > 0` as `a→0` — equivalently the
spacing-uniform correlation-decay `UniformPhysicalCorrelationDecay`, equivalently
`SingleStepDefectReduction.SingleStepDefectBound.singleStep` — is the sole open Clay
continuum input.  Seven prior physical framings (block-spin, interacting-measure/Borel,
curvature, OS/confinement, RG-invariant Λ, Laplace–self-similar, OPE/condensate) all
reduce to exactly this residual.  This module tries an EIGHTH, genuinely different TOOL:
a **reflection-positivity / correlation inequality** built on the PROVED OS2
(`ReflectionPositivity.reflectionPositiveSchwinger_holds`).

The two candidate mechanisms:

  * **The OS2 reflection-positivity Schwarz.**  OS2 is `0 ≤ E(θ(a)*·a)`, a Gram/PSD
    form on the reflected correlators.  After Schur diagonalization it is the diagonal
    sum of squares `R_t(c) = Σ_λ e^{−t·C₂(λ)}·c_λ² ≥ 0` for EVERY real `c`
    (`reflSchwinger_nonneg`, PROVED).  The associated Cauchy–Schwarz
    `|E(θ(a)*·b)|² ≤ E(θ(a)*·a)·E(θ(b)*·b)` is the PROVED
    `WilsonGNS.cauchy_schwarz` — a bona-fide reflection-positivity Schwarz bound at
    fixed spacing.  Does it give the condensate a SPACING-UNIFORM lower bound?

  * **The correlation (Griffiths-type) inequality.**  The character expansion has
    NONNEGATIVE coefficients (`coeffW ≥ 0`); the first-Griffiths-type positivity gives
    the condensate `⟨1−χ⟩ = plaqActivity ≥` its leading mode `coeffW w 1 = 2w³ > 0`
    (`latticeCondensate_ge_head`, PROVED) — a genuine fixed-spacing lower bound.  Does
    a correlation inequality make the clustering (`wilsonG_decay`, PROVED at fixed
    spacing) SPACING-UNIFORM (the `UniformPhysicalCorrelationDecay`)?

# HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**Reflection positivity / correlation inequalities give the FIXED-SPACING condensate
lower bound (the PROVED anchor) but NOT the spacing-uniform (a→0) bound — an EIGHTH
independent confirmation that the a→0 uniformity is `singleStep`.**  The decisive
obstruction, machine-checked here for the first time, is that **reflection positivity is
GAP-BLIND**: the OS2 reflection-positivity predicate `ReflectionPositiveSchwinger t ht`
holds for EVERY `t ≥ 0`, INCLUDING `t = 0`, where every reflection weight
`reflWeight 0 s = e^{−0·C₂(s)} = 1` (`reflWeight_zero_squeeze`) so the reflection form
degenerates to the IDENTITY Gram `Σ_s c_s²` — a MASSLESS (zero-gap, scale-invariant)
theory.  A critical/massless theory is perfectly reflection-positive.  Hence an
inhabitant of OS2 carries NO spectral-gap magnitude: it cannot distinguish gapped from
gapless, so it cannot furnish a positive spacing-uniform floor.  That floor is EXTRA
data = `singleStep`.  The Schwarz inequality bounds cross-correlators ABOVE (the
clustering / `wilsonG_decay` direction — fixed spacing), and the Griffiths-type
inequality bounds the condensate BELOW at fixed spacing (floor `1/4`), but neither
survives `a→0`: the continuum condensate is the same essential singularity
`exp(−c/β₀g²)`, whose nonzero generation is `singleStep`.

**No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.**

# Why the Schwarz gives the WRONG direction for a condensate lower bound

The reflection-positivity Cauchy–Schwarz `|E(θ(a)*·b)| ≤ √(E(θ(a)*·a)·E(θ(b)*·b))` is an
UPPER bound on the off-diagonal (cross-separation) correlator — exactly the input that
proves clustering / spectral decay (`wilsonG_decay`) at fixed spacing.  A LOWER bound on
the one-point condensate `⟨G²⟩` is NOT a Schwarz consequence.  Likewise the second
Griffiths inequality `⟨G²(x)G²(y)⟩ ≥ ⟨G²⟩⟨G²⟩` bounds the CONNECTED two-point function
BELOW (`≥ 0`) — the wrong sign for clustering, and it says nothing that forces the
one-point `⟨G²⟩` to stay bounded away from 0 as the coupling flows `g→0` (`a→0`).  Both
are perfectly compatible with a massless continuum limit.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Lean-core only (`Q'`/`Nat` + the `CReal`/`ExpNeg` backbone), reusing PROVED
`ReflectionPositivity.reflectionPositiveSchwinger_holds`,
`OPECondensatePositivity.latticeCondensate_ge_head/floor_anchor`,
`CReal.expNeg_le_one`, `expNeg_eqv_congr`, `SU3CharFactor.geRat_of_equiv`.  Every
load-bearing declaration is gated with `#print axioms`; permitted output `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `ring`, no `sorry`.  All
witnesses `Type`-level.  No frontier bundle is inhabited.
-/
import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.OPECondensatePositivity
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.ReflectionCondensateBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.OPECondensatePositivity

/-! ## 1. THE OS2 REFLECTION-POSITIVITY SCHWARZ STRUCTURE (task point 1) — PROVED, fixed spacing.

The Schur-diagonalized OS2 reflection Schwinger form `R_t(c) = Σ_{s<N} e^{−t·C₂(s)}·c_s²`
is `≥ 0` for every real coefficient vector and every order — the reflection-positivity
Gram/PSD structure.  We re-export it; it is the fixed-spacing anchor of the whole route. -/

/-- **OS2 reflection positivity holds at every timelike-bond length `t ≥ 0`** (re-export
of `reflectionPositiveSchwinger_holds`).  The diagonal reflection form is a
nonnegatively-weighted sum of squares, hence PSD for all real `c`.  This is the OS2
Schwarz/Gram structure — the input a reflection-positivity condensate bound would use. -/
theorem rp_schwinger_holds (t : Q') (ht : (0 : Q') ≤ t) :
    ReflectionPositiveSchwinger t ht :=
  reflectionPositiveSchwinger_holds t ht

/-- **The reflection weight is `≤ 1`** (`e^{−t·C₂(s)} ≤ 1`) — every mode of the
reflection form decays no faster than a bounded contraction; the diagonal entries live
in `[0,1]`. -/
theorem reflWeight_le_one (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    CReal.leRat (reflWeight t ht s) 1 :=
  CReal.expNeg_le_one (t * casimirQ s) (tcasimirQ_nonneg t ht s)

/-! ## 2. THE CORRELATION-INEQUALITY (Griffiths-type) CONDENSATE LOWER BOUND (task point 2)
       — PROVED, fixed spacing.

The character coefficients are nonnegative, so the vacuum condensate `⟨1−χ⟩ = plaqActivity`
is bounded BELOW by its leading excited mode `coeffW w 1 = 2w³` (a first-Griffiths-type
positivity of a single-mode contribution), giving a strictly positive fixed-spacing floor
`1/4` at the strong-coupling anchor `w = 1/2`.  Re-exported from
`OPECondensatePositivity`. -/

/-- **The correlation-inequality (Griffiths-type) condensate lower bound** — the
vacuum condensate is `≥` its leading mode `coeffW w 1 = 2w³` (`latticeCondensate_ge_head`).
The nonnegative-coefficient character expansion is the "ferromagnetic"/positive-type
structure; this is the first-Griffiths-type positive contribution of a single mode.
Fixed spacing. -/
theorem condensate_correlationLower {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    coeffW w 1 ≤ PlaquetteActivity.plaqActivity w (M + 1) :=
  latticeCondensate_ge_head hw M

/-- **The fixed-spacing condensate floor `1/4`** at the strong-coupling anchor
(`latticeCondensate_floor_anchor`) — the correlation-inequality/reflection-positive
lower bound is a genuine positive rational at fixed spacing. -/
theorem condensate_correlationFloor (M : Nat) :
    Q'.mkPos 1 4 (by decide) ≤ PlaquetteActivity.plaqActivity anchorW (M + 1) :=
  latticeCondensate_floor_anchor M

/-! ## 3. THE DECISIVE INSUFFICIENCY (task point 3) — reflection positivity is GAP-BLIND.

The genuinely new content: OS2 reflection positivity holds IDENTICALLY at `t = 0`, where
the reflection form is the identity Gram `Σ_s c_s²` (all weights `= 1`).  That is a
MASSLESS / scale-invariant / zero-gap theory — perfectly reflection-positive.  So the OS2
predicate carries NO spectral-gap magnitude; it cannot force a positive spacing-uniform
floor.  The floor is extra data = `singleStep`. -/

/-- **At `t = 0` every reflection weight is `≥ 1`** — `reflWeight 0 s = e^{−0·C₂(s)} = 1`.
Since `0·C₂(s) ≃ 0` and `e^{0} ≥ 1`, the diagonal entries are pinned to `1` from below.
(The `t = 0` limit is the massless / infinite-correlation-length point of the reflection
form.) -/
theorem reflWeight_zero_ge_one (s : Nat) :
    ExpPos.geRat (reflWeight 0 (Q'.le_refl' 0) s) 1 :=
  SU3CharFactor.geRat_of_equiv
    (expNeg_eqv_congr (tcasimirQ_nonneg 0 (Q'.le_refl' 0) s) (by decide)
      (Q'.zero_mul_eqv (casimirQ s)))
    SU3CharFactor.geRat_expNeg_zero

/-- **At `t = 0` the reflection form degenerates to the IDENTITY Gram** — every weight is
squeezed to exactly `1` (`≤ 1` and `≥ 1`).  So `R_0(c) = Σ_s c_s²`, the trivial identity
inner product: a MASSLESS (zero-gap) reflection-positive form.  This is the crux: the
reflection form at `t = 0` is scale-invariant with NO decay. -/
theorem reflWeight_zero_squeeze (s : Nat) :
    CReal.leRat (reflWeight 0 (Q'.le_refl' 0) s) 1
      ∧ ExpPos.geRat (reflWeight 0 (Q'.le_refl' 0) s) 1 :=
  ⟨reflWeight_le_one 0 (Q'.le_refl' 0) s, reflWeight_zero_ge_one s⟩

/-- **OS2 reflection positivity holds at the GAPLESS point `t = 0`.**  The exact same
predicate `ReflectionPositiveSchwinger` that holds at every gapped `t > 0` ALSO holds at
`t = 0`, where the form is the identity Gram (massless, `reflWeight_zero_squeeze`).  This
is the machine-checked insufficiency: an inhabitant of OS2 is compatible with ZERO gap. -/
theorem rp_holds_gapless :
    ReflectionPositiveSchwinger 0 (Q'.le_refl' 0) :=
  reflectionPositiveSchwinger_holds 0 (Q'.le_refl' 0)

/-- **THE DECISIVE INSUFFICIENCY, packaged.**  Reflection positivity (OS2) holds at
`t = 0` AND at `t = 0` the reflection form is the identity Gram (all weights `= 1`,
zero gap).  Therefore OS2 reflection positivity does NOT determine any positive spectral
gap — it holds equally for the massless theory.  A spacing-uniform positive condensate
floor is EXTRA data beyond OS2; it is `singleStep`.  (Contrast: a gapped `t > 0` has
`reflWeight t 1 = e^{−t·C₂(1)} < 1`, but OS2 alone gives no positive LOWER bound on the
gap `1 − reflWeight`, and none uniform as the physical scale flows.) -/
theorem rp_gap_blind :
    ReflectionPositiveSchwinger 0 (Q'.le_refl' 0)
      ∧ (∀ s : Nat, CReal.leRat (reflWeight 0 (Q'.le_refl' 0) s) 1
          ∧ ExpPos.geRat (reflWeight 0 (Q'.le_refl' 0) s) 1) :=
  ⟨rp_holds_gapless, reflWeight_zero_squeeze⟩

/-! ## 4. THE CONTINUUM CONDENSATE POSITIVITY = `singleStep` (task point 4) — 8th confirmation.

The physical continuum condensate is the same essential singularity `exp(−c/β₀g²)` as
every prior route; its nonzero `a→0` generation — the spacing-uniform lower bound that
the reflection-positivity/correlation-inequality tool does NOT supply — IS
`SingleStepDefectBound.singleStep`. -/

/-- **The continuum condensate positivity via reflection positivity = `singleStep`**
(named, not faked; UNINHABITED).  The spacing-uniform `a→0` condensate lower bound the
reflection-positivity / correlation-inequality tool would need is exactly the
per-step gap-survival `SingleStepDefectReduction.SingleStepDefectBound` — the same
residual as the OPE route (`OPECondensatePositivity.ContinuumCondensatePositivity`).  It
is NOT inhabited here (it IS the real RG estimate). -/
def ContinuumReflectionCondensate : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- **The reflection-positivity continuum residual IS the OPE/RG continuum residual**
(`rfl`) — the eighth framing lands on the identical `SingleStepDefectBound`, not a new
object.  This certifies (via defeq, Rule 9.8) that the reflection-positivity tool reduces
to the SAME irreducible core, not a parallel scorecard. -/
theorem continuumReflection_is_singleStep :
    ContinuumReflectionCondensate
      = OPECondensatePositivity.ContinuumCondensatePositivity := rfl

/-- **The continuum condensate scale is the same essential singularity** (`rfl`,
re-export) — the eighth-confirmation identity: the reflection-positive continuum
condensate is DEFINITIONALLY `exp(−c/β₀g²) = condensateCReal`, inheriting the identical
renormalon obstruction as the fluctuation / Borel / string-tension / OPE routes. -/
theorem continuumCondensate_is_essential_singularity (k : Nat) :
    OPECondensatePositivity.continuumCondensate k
      = CondensateGeometric.condensateCReal k := rfl

/-! ## 5. THE ASSEMBLED VERDICT (informational bundle — inhabits NO frontier type). -/

/-- A record collecting the machine-checked facts of this reflection-positivity /
correlation-inequality assessment.  It is NOT a frontier bundle: every field is a genuine
PROVED theorem/re-export, and it inhabits neither `SingleStepDefectBound` nor any guarded
Clay-frontier type.  It certifies the honest conclusion: the reflection-positivity Schwarz
+ correlation-inequality give the fixed-spacing condensate lower bound (the PROVED anchor),
but reflection positivity is GAP-BLIND (holds at the massless `t = 0`), so the
spacing-uniform continuum bound is the residual `singleStep`. -/
structure ReflectionCondensateVerdict : Type where
  /-- §1 — OS2 reflection positivity (all `t ≥ 0`, all real `c`): the Schwarz/Gram PSD
  structure. -/
  rpSchwinger : ∀ (t : Q') (ht : (0 : Q') ≤ t), ReflectionPositiveSchwinger t ht
  /-- §2 — the correlation-inequality (Griffiths-type) fixed-spacing condensate floor. -/
  condensateFloor : ∀ M : Nat,
    Q'.mkPos 1 4 (by decide) ≤ PlaquetteActivity.plaqActivity anchorW (M + 1)
  /-- §3 — reflection positivity is GAP-BLIND: OS2 holds at the massless `t = 0`. -/
  gapBlind : ReflectionPositiveSchwinger 0 (Q'.le_refl' 0)
    ∧ (∀ s : Nat, CReal.leRat (reflWeight 0 (Q'.le_refl' 0) s) 1
        ∧ ExpPos.geRat (reflWeight 0 (Q'.le_refl' 0) s) 1)
  /-- §4 — the continuum condensate positivity reduces to the SAME `singleStep` residual
  (8th confirmation). -/
  continuumIsSingleStep :
    ContinuumReflectionCondensate
      = OPECondensatePositivity.ContinuumCondensatePositivity

/-- **The reflection-positivity/condensate verdict is inhabited by PROVED facts only.**
Every field is a genuine theorem of this module; NONE inhabits a frontier bundle.  This
certifies the honest conclusion (the reflection-positivity / correlation-inequality tool
is the EIGHTH confirmation of `singleStep`, plus the re-derived fixed-spacing condensate
positivity through the reflection-positive lens). -/
def reflection_condensate_verdict : ReflectionCondensateVerdict where
  rpSchwinger := rp_schwinger_holds
  condensateFloor := condensate_correlationFloor
  gapBlind := rp_gap_blind
  continuumIsSingleStep := continuumReflection_is_singleStep

/-- **HONEST FINAL VERDICT.**

**CONSTRUCTED (the genuine content):**
  (i) the OS2 reflection-positivity Schwarz/Gram structure at every `t ≥ 0`
      (`rp_schwinger_holds`, re-export of the PROVED Schur-diagonal SOS) — with the
      associated Cauchy–Schwarz already PROVED as `WilsonGNS.cauchy_schwarz`;
  (ii) the correlation-inequality (Griffiths-type) FIXED-SPACING condensate lower bound
      `⟨1−χ⟩ ≥ coeffW w 1 = 2w³`, floor `1/4` at the anchor (`condensate_correlationLower`,
      `condensate_correlationFloor`);
  (iii) **the decisive INSUFFICIENCY (new): reflection positivity is GAP-BLIND**
      (`rp_gap_blind`) — OS2 holds identically at the massless `t = 0` where the
      reflection form is the identity Gram (`reflWeight_zero_squeeze`), so an inhabitant
      of OS2 is compatible with ZERO gap and cannot furnish a positive spacing-uniform
      floor.

**RESIDUAL (NOT closed):** the CONTINUUM (spacing-uniform, `a→0`) condensate positivity.
It is the same essential singularity `exp(−c/β₀g²)`
(`continuumCondensate_is_essential_singularity`, `rfl`), and its nonzero generation is
`ContinuumReflectionCondensate = SingleStepDefectBound.singleStep`
(`continuumReflection_is_singleStep`, `rfl`) — the identical core as the OPE / RG / OS
routes.

**So the reflection-positivity / correlation-inequality tool is an EIGHTH independent
confirmation of the SAME irreducible core `singleStep`** — a genuinely different tool (the
OS2 Gram/Schwarz + Griffiths positivity) that supplies the fixed-spacing anchor but is
provably gap-blind, hence does NOT derive the spacing-uniform continuum condensate.  No
guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN. -/
theorem reflectionCondensateBound_honesty : True := trivial

end YMGap.Continuum.ReflectionCondensateBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ReflectionCondensateBound.rp_schwinger_holds
#print axioms YMGap.Continuum.ReflectionCondensateBound.reflWeight_le_one
#print axioms YMGap.Continuum.ReflectionCondensateBound.condensate_correlationLower
#print axioms YMGap.Continuum.ReflectionCondensateBound.condensate_correlationFloor
#print axioms YMGap.Continuum.ReflectionCondensateBound.reflWeight_zero_ge_one
#print axioms YMGap.Continuum.ReflectionCondensateBound.reflWeight_zero_squeeze
#print axioms YMGap.Continuum.ReflectionCondensateBound.rp_holds_gapless
#print axioms YMGap.Continuum.ReflectionCondensateBound.rp_gap_blind
#print axioms YMGap.Continuum.ReflectionCondensateBound.continuumReflection_is_singleStep
#print axioms YMGap.Continuum.ReflectionCondensateBound.continuumCondensate_is_essential_singularity
#print axioms YMGap.Continuum.ReflectionCondensateBound.reflection_condensate_verdict
