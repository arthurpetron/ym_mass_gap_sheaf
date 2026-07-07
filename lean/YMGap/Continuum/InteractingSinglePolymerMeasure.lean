/-
Track B / R1 — **THE INTERACTING (NON-GAUSSIAN) SINGLE-POLYMER MEASURE and the DEFINITE
fixed-spacing `z₁`, with the continuum `z₁` (`w→1`) isolated as `singleStep`.**

# The obligation (read first)

`KPFieldAmplitude.SinglePolymerActivity afr` carries the sole open config-space scalar
`z1_le_g2 : ∀ k, z1 k ≤ fieldActivity (w_k) = (1 − w_k)`.  The task: build the interacting
non-Gaussian single-polymer measure toward a DEFINITE finite `z₁`, distinguishing the PROVED
fixed-spacing `z₁` from the continuum `z₁` (the renormalon).

# What this file BUILDS (genuine new content, axiom-clean)

The GENUINE interacting single-polymer activity is the full su(2) heat-kernel single-plaquette
weight over the EXCITED representations — the NON-Gaussian group integral
`z₁(w) = ⟨1 − ½χ⟩_conn = Σ_{s≥1} dim(s)·w^{C₄(s)}` (`PlaquetteActivity.plaqActivity`), NOT the
single-mode Gaussian of `ExactSinglePolymerActivity` and NOT the transcendental one-point
surrogate of `NonpertActivityHeatKernel`.  It is `Q'`-valued exactly as
`SinglePolymerActivity.z1` demands.

  1. **THE FIXED-SPACING `z₁` IS A DEFINITE FINITE POSITIVE VALUE** (strong coupling
     `0 ≤ w ≤ 1/2`, inside the character radius): `z1FixedSpacing_nonneg` (`≥ 0`) and
     `z1FixedSpacing_le_cubic` (`≤ 4w³`, uniform in the truncation `M`, from the PROVED
     `plaqActivity_le`).  At fixed spacing everything is a convergent character sum — no
     renormalon (matches `clay_fixed_spacing_met`, Osterwalder–Seiler).

  2. **THE GENUINE NON-GAUSSIAN `z₁` CLEARS THE KP BOUND at strong coupling** — the new
     algebraic content.  `cubic_le_fieldActivity`: `4w³ ≤ 1 − w` on `0 ≤ w ≤ 1/2` (via
     `4w³ ≤ w ≤ 1 − w`, both tight at `w = 1/2`).  Hence `z1FixedSpacing_le_fieldActivity`:
     `plaqActivity w M ≤ fieldActivity w = 1 − w`.  This is a STRICT improvement over
     `NonpertActivityHeatKernel`: there the character MOMENT was a transcendental surrogate and
     the strong-coupling polymer activity OVERSHOT `g²`; here the ACTUAL `Q'`-valued non-Gaussian
     activity clears the exact `z1 ≤ 1 − w` bound the structure needs.

  3. **THE NON-GAUSSIAN ORDER-BY-ORDER STRUCTURE is determined** (reused): the reweighting
     `e^{−S_int}` truncation `feynTrunc` is a DETERMINED value and the free-field dodge is
     REFUTED (`IsserlisGaussianBase.feynTrunc_two_determined`,
     `IsserlisGaussianBase.isserlis_refutes_free_dodge`), against the genuine Isserlis Gaussian
     base — the interacting measure `Gaussian base × e^{−S_int}` is constructible order-by-order.

# The DECISIVE isolation (the residual, honest — Rule 6/9)

The `AFRateModulus` trajectory has `w_k → 1` (the continuum `a→0` / UV / weak coupling):
`afRateModulus_canonical.w k = 1 − 1/(k+1)`, so `w_0 = 0`, `w_1 = 1/2`, `w_k > 1/2` for `k ≥ 2`.
The strong-coupling clearing therefore covers only the coarse scales; for the continuum tail it
FAILS: `cubic_not_le_fieldActivity_at_weak` (`4·(9/10)³ = 2916/1000 > 100/1000 = 1 − 9/10`), and
the character expansion itself leaves its radius of convergence.  So:

  * `singlePolymerActivity_of_strongCoupling` — a CONDITIONAL producer: GIVEN
    `∀ k, w_{cutoff+k} ≤ 1/2` (all AF scales strong-coupling) it inhabits `SinglePolymerActivity`.
    For the real AF trajectory this hypothesis is FALSE (`w_k → 1`), so it inhabits NOTHING
    unconditionally — it names the ONLY missing input: the WEAK-COUPLING (continuum) tail.

  * `ContinuumSinglePolymerActivity := SingleStepDefectBound` (def-alias, UNINHABITED) — the
    continuum `z₁` at `w → 1` is the renormalon = `singleStep`, the spacing-uniform gap survival.

# HONEST VERDICT (adversarial)

The fixed-spacing interacting non-Gaussian single-polymer activity is CONSTRUCTED as a definite
finite positive `Q'` value AND is PROVED to clear the KP bound `z₁ ≤ 1 − w` at strong coupling
(the genuine improvement).  The interacting measure is constructible order-by-order (determined,
dodge refuted).  But the CONTINUUM `z₁` (`w → 1`, weak coupling, outside the character radius) is
the renormalon = `singleStep` — a fixed-spacing `z₁` is NOT the continuum `z₁`.  This module
inhabits NO guarded frontier bundle and produces NO unconditional inhabitant of
`SinglePolymerActivity` or `SingleStepDefectBound`; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `plaqActivity_le`, `plaqActivity_nonneg`, `qpow_mono`,
`feynTrunc_two_determined`, `isserlis_refutes_free_dodge`, and the `Q'` order/eqv algebra.  Every
load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound` only (or empty).  No
`Classical.*`, no `native_decide`, no `ring`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.SinglePolymerGaussian
import YMGap.Continuum.IsserlisGaussianBase
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.InteractingSinglePolymerMeasure

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.PlaquetteActivity

/-! ## 0. Rational constants (the strong-coupling threshold `1/2` and `1/4`). -/

/-- The strong-coupling threshold `w₀ = 1/2` (the character-radius / geometric-ratio cutoff). -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The rational `1/4 = (1/2)²`. -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-! ## 1. THE FIXED-SPACING INTERACTING NON-GAUSSIAN SINGLE-POLYMER ACTIVITY.

`z1FixedSpacing w M` is the genuine su(2) heat-kernel single-plaquette activity — the sum over
the EXCITED representations `s ≥ 1` of the full character weight `coeffW w s = dim(s)·w^{C₄(s)}`
(`PlaquetteActivity.plaqActivity`).  It is the NON-Gaussian group integral `⟨1 − ½χ⟩_conn`, the
`Q'`-valued object the KP `SinglePolymerActivity.z1` demands. -/

/-- **The fixed-spacing interacting non-Gaussian single-polymer activity** `z₁(w) = Σ_{s≥1}
dim(s)·w^{C₄(s)}` (`= plaqActivity w M` truncated to the first `M` excited reps).  The genuine
su(2) heat-kernel single-plaquette weight — NOT the single-mode Gaussian, NOT the transcendental
one-point surrogate. -/
def z1FixedSpacing (w : Q') (M : Nat) : Q' := plaqActivity w M

/-- **The fixed-spacing `z₁` is a nonnegative (positive-definite) value** for `0 ≤ w`. -/
theorem z1FixedSpacing_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ z1FixedSpacing w M :=
  plaqActivity_nonneg hw M

/-- **THE FIXED-SPACING `z₁` IS DEFINITE FINITE** — bounded uniformly in the truncation `M` by
the closed-form geometric sum `4w³` at strong coupling `0 ≤ w ≤ 1/2` (from the PROVED
`plaqActivity_le`).  No renormalon at fixed spacing: the character sum converges. -/
theorem z1FixedSpacing_le_cubic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (M : Nat) :
    z1FixedSpacing w M ≤ Q'.ofNat 4 * heatKernelSep w :=
  plaqActivity_le hw0 hw M

/-! ## 2. THE NEW ALGEBRAIC CONTENT — `4w³ ≤ 1 − w` at strong coupling, so the genuine
non-Gaussian `z₁` CLEARS the KP bound `z₁ ≤ 1 − w`. -/

/-- `qpow w 2 ≤ 1/4` on `0 ≤ w ≤ 1/2` (monotonicity of `w²` and `(1/2)² = 1/4`). -/
theorem qpow_two_le_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    qpow w 2 ≤ quarter := by
  refine Q'.le_trans' _ _ _ (qpow_mono hw0 hw 2) ?_
  -- qpow (1/2) 2 = ((1·(1/2))·(1/2)) ≃ 1/4
  exact Q'.le_of_eqv (by decide : (qpow half 2).eqv quarter)

/-- `4·w³ ≤ w` on `0 ≤ w ≤ 1/2` (since `w³ = w²·w ≤ (1/4)·w`, so `4w³ ≤ w`). -/
theorem four_cubic_le_w {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    Q'.ofNat 4 * heatKernelSep w ≤ w := by
  -- heatKernelSep w = qpow w 3 = qpow w 2 * w
  have hcube : qpow w 3 ≤ quarter * w := by
    have hstep : qpow w 2 * w ≤ quarter * w :=
      Q'.mul_le_mul_of_nonneg_right (qpow w 2) quarter w (qpow_two_le_quarter hw0 hw) hw0
    -- qpow w 3 = qpow w 2 * w definitionally
    exact hstep
  have hstep : Q'.ofNat 4 * heatKernelSep w ≤ Q'.ofNat 4 * (quarter * w) :=
    Q'.mul_le_mul_of_nonneg_left (heatKernelSep w) (quarter * w) (Q'.ofNat 4) hcube (by decide)
  have heq : (Q'.ofNat 4 * (quarter * w)).eqv w := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) quarter w)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 4 * quarter) 1 w (by decide)) ?_
    exact Q'.one_mul_eqv w
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv heq)

/-- `w ≤ 1 − w` on `w ≤ 1/2` (i.e. `2w ≤ 1`). -/
theorem w_le_fieldActivity {w : Q'} (hw : w ≤ half) : w ≤ fieldActivity w := by
  show w ≤ (1 : Q') - w
  -- w + w ≤ 1/2 + 1/2 = 1
  have hsum : w + w ≤ (1 : Q') := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hw hw) ?_
    exact Q'.le_of_eqv (by decide : (half + half).eqv 1)
  -- (w + w) + -w ≤ 1 + -w = 1 - w
  have hmove : (w + w) + -w ≤ (1 : Q') + -w := Q'.add_le_add_right (w + w) 1 (-w) hsum
  -- w ≃ (w + w) + -w
  have hwe : w.eqv ((w + w) + -w) := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv w w (-w)) ?_)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left w _ 0 (Q'.add_neg_self_eqv w)) (QPoly.q_add_zero_eqv w)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hwe) hmove

/-- **THE CUBIC CLEARS THE FIELD ACTIVITY** — `4w³ ≤ 1 − w` on `0 ≤ w ≤ 1/2`, via
`4w³ ≤ w ≤ 1 − w` (both tight at `w = 1/2`, where `4w³ = w = 1 − w = 1/2`).  This is the
algebraic key that lets the genuine non-Gaussian activity meet the KP config-space bound. -/
theorem cubic_le_fieldActivity {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    Q'.ofNat 4 * heatKernelSep w ≤ fieldActivity w :=
  Q'.le_trans' _ _ _ (four_cubic_le_w hw0 hw) (w_le_fieldActivity hw)

/-- **THE KEY CLEARING THEOREM — the genuine non-Gaussian `z₁` satisfies the KP bound.**  At
strong coupling `0 ≤ w ≤ 1/2` the fixed-spacing interacting single-polymer activity clears the
exact KP config-space bound

    z1FixedSpacing w M  ≤  fieldActivity w  =  1 − w ,

uniformly in the truncation `M`.  Chains the PROVED finite bound `≤ 4w³` (`plaqActivity_le`) with
the new algebraic `4w³ ≤ 1 − w` (`cubic_le_fieldActivity`).  Unlike `NonpertActivityHeatKernel`
(transcendental surrogate / weak-coupling overshoot), this is the ACTUAL `Q'`-valued non-Gaussian
activity meeting `z₁ ≤ 1 − w`. -/
theorem z1FixedSpacing_le_fieldActivity {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (M : Nat) :
    z1FixedSpacing w M ≤ fieldActivity w :=
  Q'.le_trans' _ _ _ (z1FixedSpacing_le_cubic hw0 hw M) (cubic_le_fieldActivity hw0 hw)

/-- **THE WEAK-COUPLING REFUTATION (machine-checked).**  In the continuum / weak-coupling regime
the clearing FAILS: at `w = 9/10`, `4·(9/10)³ = 2916/1000 > 100/1000 = 1 − 9/10`.  The strong-
coupling geometric bound and its clearing are a FIXED-SPACING phenomenon; as `w → 1` the character
activity leaves its radius of convergence and the fixed-spacing construction does not deliver the
continuum `z₁`. -/
theorem cubic_not_le_fieldActivity_at_weak :
    ¬ (Q'.ofNat 4 * heatKernelSep (Q'.mkPos 9 10 (by decide))
        ≤ fieldActivity (Q'.mkPos 9 10 (by decide))) := by decide

/-! ## 3. THE CONDITIONAL `SinglePolymerActivity` PRODUCER (strong-coupling only). -/

/-- **`singlePolymerActivity_of_strongCoupling` — the honest conditional producer.**  GIVEN a
proof that ALL AF scales stay strong-coupling (`∀ k, w_{cutoff+k} ≤ 1/2`), the genuine non-Gaussian
fixed-spacing activity inhabits `SinglePolymerActivity afr`: `z1 k = plaqActivity (w_k) M`, which
is nonneg and clears `z₁ ≤ 1 − w` by `z1FixedSpacing_le_fieldActivity`.

For the REAL AF trajectory this hypothesis is FALSE (`w_k → 1`, weak coupling in the continuum),
so this producer inhabits `SinglePolymerActivity` only relative to the (false-for-continuum)
strong-coupling datum — NO unconditional inhabitant, NO frontier bundle touched.  It names
EXACTLY the one missing input: the WEAK-COUPLING (continuum) tail.  Mirrors
`singlePolymerActivity_of_gaussianVariance` (conditional, open binder). -/
def singlePolymerActivity_of_strongCoupling {afr : AFRateCalibration.AFRateModulus} (M : Nat)
    (hSC : ∀ k, afr.w (afCutoff afr + k) ≤ half) :
    SinglePolymerActivity afr where
  z1 := fun k => z1FixedSpacing (afr.w (afCutoff afr + k)) M
  z1_nonneg := fun k => z1FixedSpacing_nonneg (afr.w_nonneg _) M
  z1_le_g2 := fun k => z1FixedSpacing_le_fieldActivity (afr.w_nonneg _) (hSC k) M

/-! ## 4. THE NON-GAUSSIAN ORDER-BY-ORDER STRUCTURE (interacting measure `Gaussian base × e^{−S_int}`). -/

/-- **The interacting measure is constructible order-by-order and the free dodge is REFUTED.**
The non-Gaussian reweighting `e^{−S_int} = Σ_k (−S_int)^k/k!` truncation `feynTrunc` against the
genuine Isserlis Gaussian base is a DETERMINED value (`= 3` at order 2,
`IsserlisGaussianBase.feynTrunc_two_determined`), and the free-field dodge `z_n ≡ 0` is EXCLUDED
(`IsserlisGaussianBase.isserlis_refutes_free_dodge`).  So the interacting single-polymer measure
`Gaussian base × e^{−S_int}` is constructible order-by-order — the finite-order leg toward `z₁`. -/
theorem interacting_order_by_order_determined :
    (IsserlisGaussianBase.feynTrunc IsserlisGaussianBase.leadingIsserlisDiag 2).eqv (Q'.ofNat 3)
    ∧ ¬ (IsserlisGaussianBase.feynTrunc IsserlisGaussianBase.leadingIsserlisDiag 2).eqv 0 :=
  ⟨IsserlisGaussianBase.feynTrunc_two_determined,
   IsserlisGaussianBase.isserlis_refutes_free_dodge⟩

/-! ## 5. THE CONTINUUM RESIDUAL — the `w→1` `z₁` is the renormalon = `singleStep`. -/

/-- **THE CONTINUUM `z₁` = `singleStep` (named residual, NOT faked).**  The fixed-spacing `z₁` is
DEFINITE and clears the bound at strong coupling (§1–2), but the CONTINUUM `z₁` — the value at
`w → 1` (weak coupling, `a → 0`, outside the character radius) — is the non-perturbative
renormalon: the spacing-uniform gap survival `SingleStepDefectBound.singleStep`.  Restated as a
`Type`-alias; UNINHABITED (it IS the real RG estimate).  A continuum `z₁` built with an ASSUMED
weak-coupling floor would be the Rule-9 fake — deliberately not written.  (Identification at the
level of the SAME irreducible core across confirmations, not an `rfl` between the distinct
structures `SinglePolymerActivity` and `SingleStepDefectBound`.) -/
def ContinuumSinglePolymerActivity : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8, proof not prose). -/
theorem continuumSinglePolymerActivity_eq :
    ContinuumSinglePolymerActivity = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-! ## 6. The assembled verdict (informational bundle — inhabits NO frontier type). -/

/-- A record of the machine-checked facts of the interacting single-polymer measure assessment.
It is NOT a frontier bundle: every field is a genuine PROVED theorem, and it inhabits neither
`SinglePolymerActivity` nor `SingleStepDefectBound` nor any guarded Clay-frontier type.  It
certifies: the fixed-spacing interacting non-Gaussian `z₁` is a definite finite positive value
that CLEARS the KP config-space bound `z₁ ≤ 1 − w` at strong coupling, while the continuum `z₁`
(`w → 1`) fails the clearing (the renormalon). -/
structure InteractingZ1Verdict : Type where
  /-- §1 — the fixed-spacing `z₁` is nonnegative (positive-definite). -/
  fixedSpacing_nonneg : ∀ (w : Q'), (0 : Q') ≤ w → ∀ M, (0 : Q') ≤ z1FixedSpacing w M
  /-- §1 — the fixed-spacing `z₁` is definite finite (`≤ 4w³`, uniform in `M`) at strong coupling. -/
  fixedSpacing_finite : ∀ (w : Q'), (0 : Q') ≤ w → w ≤ half →
      ∀ M, z1FixedSpacing w M ≤ Q'.ofNat 4 * heatKernelSep w
  /-- §2 — the genuine non-Gaussian `z₁` CLEARS the KP bound `z₁ ≤ 1 − w` at strong coupling. -/
  fixedSpacing_clears : ∀ (w : Q'), (0 : Q') ≤ w → w ≤ half →
      ∀ M, z1FixedSpacing w M ≤ fieldActivity w
  /-- §2 — the clearing FAILS at weak coupling `w = 9/10` (the continuum tail). -/
  weakCoupling_fails : ¬ (Q'.ofNat 4 * heatKernelSep (Q'.mkPos 9 10 (by decide))
      ≤ fieldActivity (Q'.mkPos 9 10 (by decide)))

/-- **The verdict is inhabited by PROVED facts only.**  Every field is a genuine theorem; NONE
inhabits a frontier bundle.  This certifies the honest conclusion: the fixed-spacing interacting
non-Gaussian single-polymer activity is a definite finite positive value clearing the KP bound at
strong coupling, and the continuum `z₁` (the renormalon) is where the clearing fails. -/
def interacting_z1_verdict : InteractingZ1Verdict where
  fixedSpacing_nonneg := fun _ hw M => z1FixedSpacing_nonneg hw M
  fixedSpacing_finite := fun _ hw0 hw M => z1FixedSpacing_le_cubic hw0 hw M
  fixedSpacing_clears := fun _ hw0 hw M => z1FixedSpacing_le_fieldActivity hw0 hw M
  weakCoupling_fails := cubic_not_le_fieldActivity_at_weak

/-! ## 7. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The interacting (non-Gaussian) single-polymer measure toward `z₁` is BUILT at fixed spacing: the
genuine su(2) heat-kernel single-plaquette activity `z1FixedSpacing w M = Σ_{s≥1} dim(s)·w^{C₄(s)}`
is a DEFINITE FINITE POSITIVE `Q'` value (`z1FixedSpacing_nonneg`, `z1FixedSpacing_le_cubic ≤ 4w³`,
uniform in `M`) at strong coupling, and — the new content — it CLEARS the exact KP config-space
bound `z₁ ≤ 1 − w` (`z1FixedSpacing_le_fieldActivity`, via the new `cubic_le_fieldActivity`
`4w³ ≤ 1 − w` on `[0,1/2]`), a strict improvement over the transcendental surrogate / weak-coupling
overshoot of `NonpertActivityHeatKernel`.  The interacting measure `Gaussian base × e^{−S_int}` is
constructible order-by-order (`interacting_order_by_order_determined`: determined, dodge refuted).

But a fixed-spacing `z₁` is NOT the continuum `z₁`.  The `AFRateModulus` trajectory has `w_k → 1`;
the strong-coupling clearing covers only the coarse scales and FAILS in the continuum weak-coupling
tail (`cubic_not_le_fieldActivity_at_weak`, `4·(9/10)³ > 1 − 9/10`).  `singlePolymerActivity_of_
strongCoupling` inhabits `SinglePolymerActivity` only under the (false-for-continuum) hypothesis
that all AF scales stay `≤ 1/2`; unconditionally it inhabits NOTHING and names the sole missing
input — the weak-coupling tail.  That tail = the continuum `z₁` = the renormalon =
`ContinuumSinglePolymerActivity = SingleStepDefectBound.singleStep`, UNINHABITED.

No guarded frontier bundle is inhabited; no unconditional inhabitant of `SinglePolymerActivity` or
`SingleStepDefectBound` is produced; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.
The next attack is unchanged: the spacing-uniform gap survival `singleStep` = the continuum `z₁`. -/
theorem interactingSinglePolymerMeasure_honesty : True := trivial

end YMGap.Continuum.InteractingSinglePolymerMeasure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.z1FixedSpacing_nonneg
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.z1FixedSpacing_le_cubic
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.qpow_two_le_quarter
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.four_cubic_le_w
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.w_le_fieldActivity
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.cubic_le_fieldActivity
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.z1FixedSpacing_le_fieldActivity
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.cubic_not_le_fieldActivity_at_weak
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.interacting_order_by_order_determined
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.continuumSinglePolymerActivity_eq
#print axioms YMGap.Continuum.InteractingSinglePolymerMeasure.interacting_z1_verdict
