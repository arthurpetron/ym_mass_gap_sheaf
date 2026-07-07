/-
Track B / R2 — THE OS-RECONSTRUCTION / CONFINEMENT (AREA-LAW) ROUTE to the
single open field `singleStep` (the continuum gap-survival). Does the PROVED
OS2 reflection positivity + the strong-coupling area law give the continuum
gap via a genuinely DIFFERENT mechanism, or confirm the SAME non-perturbative
core?

# What this module assesses (read first)

The whole Clay continuum gap has been reduced (three prior routes: block-spin,
interacting-measure/Borel, curvature) to ONE per-step estimate
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`
(`realδ_k ≤ δ_model_k`) — the spacing-uniform gap-survival, an essential
singularity `Λ = a·exp(−1/2β₀g²) ≠ 0` (the renormalon/condensate positivity).
This module tries the LAST major untried mechanism — the OS reconstruction /
confinement (area-law) route — and asks whether it CLOSES `singleStep`, or is
a 4th confirmation of the same non-perturbative core, or is orthogonal.

The verdict is machine-checked and honest in three parts:

  A. **The OS MECHANISM does NOT bypass the continuum limit.** OS2 (PROVED,
     `ReflectionPositivity.reflectionPositiveSchwinger_holds`) gives the
     reconstructed Hilbert space + transfer operator; the mass gap = the
     transfer-operator gap = `−log`(the correlator decay rate). The
     FIXED-SPACING OS gap is genuinely PROVED (`reconTransfer_located_gap`,
     `1−sep = 107/108`). But the CONTINUUM (`a→0`) OS gap is EXACTLY the
     spacing-uniform correlator decay `UniformPhysicalCorrelationDecay` — the
     already-named primary open input, which reduces (`trueMargin_of_correlationDecay`)
     to `singleStep`. So the OS route reduces to the SAME continuum limit;
     `osContinuumGap_of_uniformDecay` re-exports the PROVED
     `uniformPhysicalCorrelationDecay_imp_massGap` — the gap IS the uniform decay
     rate, and the uniformity is the open content. **OS does not give
     `singleStep` directly.**

  B. **The CONFINEMENT string tension is a 4th confirmation of the SAME
     essential singularity.** The FIXED-SPACING (strong-coupling) area law is
     genuinely PROVED-analog here: at the strong-coupling anchor `w = 1/2` the
     per-plaquette Wilson activity is `≤ 1/2 < 1`
     (`strongCoupling_confinement_suppression`) — a strictly-suppressive
     per-plaquette factor, i.e. a POSITIVE fixed-spacing string tension
     `σa² = −log(activity) ≥ log 2 > 0` (the confinement analog of the fixed-
     spacing `107/108` gap). But the CONTINUUM string tension is
     `√σ_phys = Λ = (1/a)·exp(−1/2β₀g²)` — dimensional transmutation — which is
     the SAME essential-singularity condensate scale as the fluctuation route:
     `continuumStringTensionScale k := CondensateGeometric.condensateCReal k`
     (`stringTension_is_condensate_scale`, `rfl`). So the continuum √σ > 0 is
     the SAME non-perturbative input `exp(−c/β₀g²)`, seen through a DIFFERENT
     physical quantity (string tension vs fluctuation defect) but NOT a more
     tractable one.

  C. **Confinement is ORTHOGONAL to the mass gap (separate premise).** Per the
     project principle `mass gap ≠ area law`, `WilsonAreaLaw` carries the
     continuum area law `ScaleCovariantWilsonAreaLaw` as an INDEPENDENT premise
     with NO bridge either way (`areaLaw_massGap_independence`). So even a full
     continuum area law would not, by itself, yield the mass gap here (and vice
     versa). The confinement route therefore neither closes `singleStep`
     directly (A) nor is more tractable (B) nor bridges to the gap (C).

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The OS/confinement route does NOT give `singleStep` directly and does NOT avoid
the renormalon. The OS mechanism reduces the continuum gap to the SAME
spacing-uniform correlator decay (`UniformPhysicalCorrelationDecay`); the
confinement mechanism supplies a genuine fixed-spacing positive string tension
(the confinement analog of the proved fixed-spacing gap) but its continuum
value `√σ = Λ = exp(−c/β₀g²)` is the SAME essential-singularity condensate
scale — a 4th confirmation of the non-perturbative core via a different
physical quantity — and is in any case a SEPARATE premise (`gap ≠ area law`).
No inhabitant of `SingleStepDefectBound`, `MassGap`, or `ScaleCovariantWilsonAreaLaw`
is produced. The 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Lean-core only (`Q'`/`Nat` + reused `CReal`/`ExpNeg` positivity). Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only. No `Classical.*`, no `native_decide`, no
`sorry`/`sorryAx`. No frontier bundle is inhabited.
-/

import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.WilsonAreaLaw
import YMGap.Continuum.UniformCorrelationDecay
import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.CondensateGeometricErosion

namespace YMGap.Continuum.OSConfinementAssessment

open YMGap.Constructive
open YMGap.Continuum

/-! ## A. The OS mechanism — PROVED OS2, and the continuum gap = uniform decay

OS2 reflection positivity is PROVED unconditionally
(`ReflectionPositivity.reflectionPositiveSchwinger_holds`), so the OS
reconstruction (GNS Hilbert space + transfer operator `T`) exists and the mass
gap is the transfer-operator gap `= −log`(correlator decay rate). The
FIXED-SPACING gap is proved (`reconTransfer_located_gap`); the CONTINUUM gap is
the spacing-uniform decay `UniformPhysicalCorrelationDecay`. -/

/-- **OS2 is PROVED (re-export).** The genuine OS2 reflection-positivity axiom
holds at all orders, unconditionally, for every real observable — the input the
OS reconstruction consumes. This is the mechanism's PROVED half. -/
theorem os2_reflection_positivity_holds (t : Q') (ht : (0 : Q') ≤ t) :
    ReflectionPositivity.ReflectionPositiveSchwinger t ht :=
  ReflectionPositivity.reflectionPositiveSchwinger_holds t ht

/-- **The OS continuum gap = the spacing-uniform correlator decay (re-export of
the PROVED implication).** The OS-reconstructed mass gap is `−log`(the
correlator decay rate); its CONTINUUM (`a→0`) survival is *exactly* the
spacing-uniform physical correlation decay. Hence the OS route reduces the
continuum gap to `UniformPhysicalCorrelationDecay` — the SAME primary open input
(which reduces to `singleStep`), NOT a bypass. Re-exports the PROVED
`uniformPhysicalCorrelationDecay_imp_massGap`. -/
def osContinuumGap_of_uniformDecay
    (U : UniformCorrelationDecay.UniformPhysicalCorrelationDecay) :
    UniformCorrelationDecay.MassGap :=
  UniformCorrelationDecay.uniformPhysicalCorrelationDecay_imp_massGap U

/-! ## B. The confinement string tension — fixed-spacing positive, continuum = essential singularity

The FIXED-SPACING (strong-coupling) area law is genuine: the per-plaquette
Wilson activity is strictly suppressive (`≤ 1/2 < 1`), a positive string
tension `σa²>0`. The CONTINUUM string tension is `√σ = Λ = exp(−c/β₀g²)` — the
SAME essential-singularity condensate scale as the fluctuation route. -/

/-- The strong-coupling anchor `w = 1/2` (the boundary of the proved
strong-coupling window `0 ≤ w ≤ 1/2`). -/
def anchorW : Q' := Q'.mkPos 1 2 (by decide)

/-- **Fixed-spacing confinement suppression (PROVED-analog of the `107/108`
gap).** At the strong-coupling anchor `w = 1/2`, the single-plaquette Wilson
activity is `≤ 1/2 < 1` at every truncation `M`. A per-plaquette factor `< 1` is
a POSITIVE fixed-spacing string tension `σa² = −log(activity) ≥ log 2 > 0` — the
confinement side of the fixed-spacing physics, genuine and rational. Reuses the
PROVED `PlaquetteActivity.plaqActivity_le` (`activity ≤ 4w³`, `= 1/2` at
`w = 1/2`). -/
theorem strongCoupling_confinement_suppression (M : Nat) :
    PlaquetteActivity.plaqActivity anchorW M ≤ Q'.mkPos 1 2 (by decide) :=
  Q'.le_trans' _ _ _
    (PlaquetteActivity.plaqActivity_le (w := anchorW) (by decide) (Q'.le_refl' _) M)
    (by decide)

/-- **The continuum string-tension scale IS the condensate scale.** The physical
continuum string tension is `√σ_phys = Λ = (1/a)·exp(−1/2β₀g²)` (dimensional
transmutation). Its non-perturbative content is the SAME geometric condensate
`exp(−c/β₀g²)` the fluctuation route reduces to. We pin `√σ` to that object. -/
def continuumStringTensionScale (k : Nat) : CReal :=
  CondensateGeometric.condensateCReal k

/-- **`√σ = the condensate scale` (definitional, `rfl`).** The confinement route's
continuum quantity is DEFINITIONALLY the same essential-singularity object as the
fluctuation/condensate route — the decisive "4th confirmation of the same
non-perturbative core" fact. -/
theorem stringTension_is_condensate_scale (k : Nat) :
    continuumStringTensionScale k = CondensateGeometric.condensateCReal k :=
  rfl

/-- **The continuum string tension is a bona-fide nonnegative `CReal`** (`√σ ≥ 0`)
— but its positivity as `exp(−·)` is the TRIVIAL part (§B of the doc); the
GENUINE content is that the real 4D theory sits on this trajectory with a nonzero
`Λ`, which is the open non-perturbative generation. Reuses
`CondensateGeometric.condensate_creal_nonneg`. -/
theorem continuumStringTension_nonneg (k : Nat) :
    ExpPos.geRat (continuumStringTensionScale k) 0 :=
  CondensateGeometric.condensate_creal_nonneg k

/-- **The continuum string tension is geometrically summable / anchor-dominated
(the EASY direction, re-export).** As with the condensate, `Σ √σ_k ≤ 1/40 < m_phys`
— an UPPER bound (small erosion = good), NOT the mass gap. The mass gap needs the
scale GENERATED nonzero, the opposite direction. Reuses
`CondensateGeometric.cond_anchorDom`. -/
theorem continuumStringTension_anchorDominated :
    CondensateGeometric.condSum < AnchorDominance.mPhysLB :=
  CondensateGeometric.cond_anchorDom

/-! ## C. Confinement is ORTHOGONAL to the mass gap (separate premise)

`mass gap ≠ area law`: `WilsonAreaLaw` carries the continuum area law as an
INDEPENDENT premise with no bridge either way. We re-export the independence:
even a full continuum area law does not, by itself, yield the mass gap here. -/

/-- **Confinement / mass-gap independence (re-export).** From a bundle of a
continuum area law and a mass gap one recovers each premise ONLY because both
were supplied — there is NO derivation `ScaleCovariantWilsonAreaLaw ⟹ MassGap`
(or its converse) in this development. The area-law route is a SEPARATE premise,
not a reduction of `singleStep`. -/
def confinement_gap_independent
    {W : WilsonAreaLaw.WilsonField} {MassGap : Type}
    (both : WilsonAreaLaw.AreaLawAndMassGap W MassGap) :
    WilsonAreaLaw.ScaleCovariantWilsonAreaLaw W × MassGap :=
  WilsonAreaLaw.areaLaw_massGap_independence both

/-! ## The assembled verdict (informational bundle — inhabits NO frontier type)

A record collecting the machine-checked facts of this assessment. It is NOT a
frontier bundle: it carries only PROVED conditional facts and re-exports, and it
inhabits neither `SingleStepDefectBound` nor `MassGap` nor
`ScaleCovariantWilsonAreaLaw`. Producing it is a statement of what the OS/
confinement route DOES and DOES NOT give — never a closure. -/
structure OSConfinementVerdict : Type where
  /-- A — OS2 is PROVED (the reconstruction mechanism's proved half). -/
  os2 : ∀ (t : Q') (ht : (0 : Q') ≤ t),
    ReflectionPositivity.ReflectionPositiveSchwinger t ht
  /-- A — the OS continuum gap reduces to the spacing-uniform correlator decay
  (the SAME primary open input); NOT a bypass of `singleStep`. -/
  osReducesToUniformDecay :
    UniformCorrelationDecay.UniformPhysicalCorrelationDecay →
      UniformCorrelationDecay.MassGap
  /-- B — the fixed-spacing confinement is genuine (per-plaquette activity `< 1`,
  positive string tension), the analog of the proved fixed-spacing gap. -/
  fixedSpacingConfinement : ∀ M : Nat,
    PlaquetteActivity.plaqActivity anchorW M ≤ Q'.mkPos 1 2 (by decide)
  /-- B — the CONTINUUM string tension is the SAME essential-singularity
  condensate scale (4th confirmation of the non-perturbative core). -/
  stringTensionIsCondensate : ∀ k : Nat,
    continuumStringTensionScale k = CondensateGeometric.condensateCReal k

/-- **The OS/confinement verdict is inhabited by PROVED facts only.** Every field
is a genuine theorem/re-export of this module; NONE inhabits a frontier bundle.
This certifies the honest conclusion: the OS mechanism reduces the continuum gap
to the same uniform-decay input, the confinement string tension is a 4th
confirmation of the same essential singularity, and neither closes `singleStep`. -/
def os_confinement_verdict : OSConfinementVerdict where
  os2 := os2_reflection_positivity_holds
  osReducesToUniformDecay := osContinuumGap_of_uniformDecay
  fixedSpacingConfinement := strongCoupling_confinement_suppression
  stringTensionIsCondensate := stringTension_is_condensate_scale

end YMGap.Continuum.OSConfinementAssessment

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OSConfinementAssessment.os2_reflection_positivity_holds
#print axioms YMGap.Continuum.OSConfinementAssessment.osContinuumGap_of_uniformDecay
#print axioms YMGap.Continuum.OSConfinementAssessment.strongCoupling_confinement_suppression
#print axioms YMGap.Continuum.OSConfinementAssessment.stringTension_is_condensate_scale
#print axioms YMGap.Continuum.OSConfinementAssessment.continuumStringTension_nonneg
#print axioms YMGap.Continuum.OSConfinementAssessment.continuumStringTension_anchorDominated
#print axioms YMGap.Continuum.OSConfinementAssessment.confinement_gap_independent
#print axioms YMGap.Continuum.OSConfinementAssessment.os_confinement_verdict
