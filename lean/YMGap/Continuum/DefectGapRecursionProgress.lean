/-
Track B2-defectrec / R2 — **REDUCING and REFUTING the two `recursion` fields of the
defect-gap program, and SHARPENING the "`hbridge` collapses to `bulk_shift`" claim.**

# What this module does (read first)

The per-block defect-gap recursion has the shape `(1 − δ_k)·g_k ≤ g_{k+1}`, but it
lives on TWO very different carriers:

  * the **surrogate** carrier — `g` a survival product / constant margin
    (`afDefectGapRecursion`, `trivialDefectGapRecursion`), where the field is
    discharged by `mul_comm` / a bare tautology, carrying ZERO gap-degradation
    content;
  * the **true** carrier — `g_k := m_lat(a_k)/a_k = divPos (floorRate_k) (a_k)`
    (`AFDeltaDecay.AsymptoticDescentInput.recursion`,
    `AsymptoticSpectralLoc.SpectralMarginInput`), the dimensionless physical
    margin that survives `a → 0`.

`AsymptoticSpectralLoc.margin_recursion_of_eigShift` already reduces the TRUE
recursion to two structured fields `hadd` (located-2nd-eigenvalue ↔ physical-margin
dictionary, discharged as a theorem in `SpectralMarginBridge` modulo model
hookups) and `hbridge` (`shift_k ≤ δ_k · g_k`).  The verdict then says `hbridge`
"reduces to `bulk_shift : ∀ s, shift s ≤ 1/12`".

This module makes THREE genuine, axiom-clean contributions:

  1. **REFUTATION of the surrogate carriers** (§1).  `survivalProduct_recursion_is_mulComm`
     and `constMargin_recursion_tautology` prove that the survival-product and
     constant-margin `recursion` fields are, respectively, `mul_comm` and a bare
     `Q'`-tautology — they hold for ANY `δ ≥ 0` regardless of physics, so they carry
     no gap-degradation content and CANNOT witness the true margin.

  2. **The scaled-shift trajectory bridge** (§2).  `TrajectoryShiftControl` isolates
     the per-scale obligation the TRUE recursion actually needs —
     `hbridge : shift k ≤ δ_k · g_k` — and `trajectory_recursion` proves the true
     recursion from it plus `hadd`, reusing the converter.

  3. **The HONEST SHARPENING** (§3).  The verdict's "`hbridge` = `bulk_shift`" is
     TRUE only for the SCALED trajectory shift, NOT for the bare constant `1/12`:

       * `constantBulkShift_insufficient_*` — a CONCRETE witness (`δ = 1/100`,
         `g = 1`, `shift = 1/12`) where `bulk_shift` HOLDS (`shift ≤ 1/12`) but
         `hbridge` FAILS (`1/12 > 1/100 = δ·g`).  So the constant localization datum
         does NOT, by itself, discharge the trajectory bridge.
       * `scaledShift_implies_bulkShift` / `prodMargin_of_ceil` — the correct
         directionality: the scaled trajectory shift IMPLIES the constant
         `bulk_shift ≤ 1/12` bound whenever `δ_k·g_k ≤ 1/12` (which holds in the
         tail, `δ → 0`, `g ≤ ceiling`).  So the trajectory obligation is the
         STRONGER, correct one; the constant datum is a tail consequence, not a
         substitute.

# Honest scope

Nothing here conjures the gap.  §1 is a refutation (deadness of the surrogates),
§2 is a repackaging of the sole open trajectory obligation, §3 is a correction that
prevents a fake closure (the constant `1/12` datum is insufficient for the
per-scale bridge).  `TrajectoryShiftControl` is NOT inhabited on ℝ⁴; its `hbridge`
IS the named residual (`bulk_shift` / `BulkDefectControlled` / `VacNormEigShift`),
in its correct scale-dependent form.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over `AsymptoticSpectralLoc` / `SpectralLocalizationCrux`;
every carrier is `Type`-level data.  Each load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide` (only `decide` on decidable `Q'` numeric facts), no `sorry`, no
custom `axiom`.
-/

import YMGap.Continuum.AsymptoticSpectralLoc
import YMGap.Continuum.SpectralLocalizationCrux

namespace YMGap.Continuum.DefectGapRecursionProgress

open YMGap.Constructive
open YMGap.Continuum.AsymptoticSpectralLoc

/-! ## 1. Refutation — the surrogate/constant carriers carry no degradation content -/

/-- **THE SURVIVAL-PRODUCT RECURSION IS `mul_comm`.**  When the surrogate carrier
sets `g_{k+1} := g_k · ρ_k` with `ρ_k = 1 − δ_k`, the per-block recursion
`(1 − δ_k)·g_k ≤ g_{k+1}` is exactly `ρ_k · g_k ≤ g_k · ρ_k`, which holds by
commutativity for ANY `ρ, g` — it is an equality, carrying ZERO gap-degradation
content.  This is why `afDefectGapRecursion` / `dominantModeRecursion` cannot
witness the true margin. -/
theorem survivalProduct_recursion_is_mulComm (ρ g : Q') : ρ * g ≤ g * ρ :=
  Q'.le_of_eqv (Q'.mul_comm_eqv ρ g)

/-- **THE CONSTANT-MARGIN RECURSION IS A TAUTOLOGY.**  When the surrogate carrier
holds `g` CONSTANT (`g_k ≡ g0`), the recursion `(1 − δ)·g0 ≤ g0` holds for ANY
`δ ≥ 0` and `g0 ≥ 0` — it is a bare `Q'`-inequality with no reference to spacing,
so `trivialDefectGapRecursion` carries no physics.  PROOF: the additive→multiplicative
converter with `shift := 0` (`g0 − 0 ≤ g0` and `0 ≤ δ·g0`). -/
theorem constMargin_recursion_tautology (δ g0 : Q') (hδ : (0 : Q') ≤ δ)
    (hg : (0 : Q') ≤ g0) : (1 - δ) * g0 ≤ g0 := by
  refine margin_recursion_of_eigShift δ 0 g0 g0 ?_ ?_
  · -- g0 − 0 ≤ g0
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.sub_zero' g0))
  · -- 0 ≤ δ · g0
    exact Q'.mul_nonneg δ g0 hδ hg

/-! ## 2. The scaled-shift trajectory bridge (the obligation the TRUE recursion needs) -/

/-- **THE TRAJECTORY SHIFT CONTROL.**  The per-scale data the TRUE recursion
actually consumes: the physical margins `g_k ≥ 0`, the exponent-level defects
`δ_k`, the per-scale eigenvalue-shift budget `shift_k`, and the SINGLE named
residual — the SCALED bulk eigenvalue-shift control

    hbridge :  shift_k ≤ δ_k · g_k.

This is the trajectory (scale-dependent) form of `SpectralLocalizationCrux.bulk_shift`
/ `DeltaFrontierLedger.bulkCtrl`.  UNINHABITED on ℝ⁴. -/
structure TrajectoryShiftControl : Type where
  /-- The physical margins `g_k = m_lat(a_k)/a_k`. -/
  g : Nat → Q'
  /-- The exponent-level defects `δ_k`. -/
  δ : Nat → Q'
  /-- The per-scale eigenvalue-shift budget. -/
  shift : Nat → Q'
  /-- Each physical margin is nonnegative. -/
  g_nonneg : ∀ k, (0 : Q') ≤ g k
  /-- **THE NAMED RESIDUAL** — the scaled bulk eigenvalue-shift control. -/
  hbridge : ∀ k, shift k ≤ δ k * g k

/-- **THE TRUE RECURSION FROM THE TRAJECTORY BRIDGE.**  Given the trajectory shift
control and the additive dictionary `hadd : g_k − shift_k ≤ g_{k+1}`, the true
per-block margin recursion `(1 − δ_k)·g_k ≤ g_{k+1}` holds at every scale — via the
`AsymptoticSpectralLoc` converter, applied pointwise.  So the true `recursion`
field reduces to the pair `(hadd, TrajectoryShiftControl.hbridge)`. -/
theorem trajectory_recursion (C : TrajectoryShiftControl)
    (hadd : ∀ k, C.g k - C.shift k ≤ C.g (k + 1)) (k : Nat) :
    (1 - C.δ k) * C.g k ≤ C.g (k + 1) :=
  margin_recursion_of_eigShift (C.δ k) (C.shift k) (C.g k) (C.g (k + 1))
    (hadd k) (C.hbridge k)

/-! ## 3. The HONEST SHARPENING — constant `bulk_shift` ≠ the trajectory bridge -/

/-- The concrete counter-witness constants (§3): `δ = 1/100`, `g = 1`,
`shift = 1/12`. -/
def cShift : Q' := SpectralLocalizationCrux.q112
/-- The counter-witness defect `δ = 1/100`. -/
def cDelta : Q' := Q'.mkPos 1 100 (by decide)
/-- The counter-witness margin `g = 1`. -/
def cG : Q' := (1 : Q')

/-- **`bulk_shift` HOLDS at the witness**: `shift = 1/12 ≤ 1/12`. -/
theorem cShift_le_margin : cShift ≤ SpectralLocalizationCrux.q112 :=
  Q'.le_refl' _

/-- The witness defect is nonnegative. -/
theorem cDelta_nonneg : (0 : Q') ≤ cDelta := by decide

/-- The witness margin is nonnegative. -/
theorem cG_nonneg : (0 : Q') ≤ cG := by decide

/-- **`hbridge` FAILS at the witness**: `shift = 1/12` is NOT `≤ δ·g = 1/100`.
So the bare constant localization datum `bulk_shift ≤ 1/12` does NOT, by itself,
discharge the per-scale trajectory bridge `shift ≤ δ·g` — the two are DIFFERENT
obligations whenever `δ·g < 1/12` (i.e. in the tail as `δ → 0`). -/
theorem constantBulkShift_insufficient : ¬ (cShift ≤ cDelta * cG) := by decide

/-- **THE CORRECT DIRECTIONALITY.**  The SCALED trajectory shift IMPLIES the
constant `bulk_shift ≤ 1/12` bound whenever the product margin `δ·g` sits below the
localization margin `1/12`.  So the trajectory obligation is STRONGER: the constant
datum is a CONSEQUENCE of it (in the tail), not a substitute for it. -/
theorem scaledShift_implies_bulkShift (δ g shift : Q')
    (hb : shift ≤ δ * g) (hsm : δ * g ≤ SpectralLocalizationCrux.q112) :
    shift ≤ SpectralLocalizationCrux.q112 :=
  Q'.le_trans' _ _ _ hb hsm

/-- **THE PRODUCT-MARGIN CONTROL.**  Under a uniform physical ceiling `g ≤ C` and a
small-defect budget `δ·C ≤ 1/12`, the product margin `δ·g ≤ 1/12`.  This is the
tail hypothesis under which `scaledShift_implies_bulkShift` fires: as `δ → 0` with
`g` bounded by the ceiling, the scaled trajectory shift automatically clears the
constant localization margin. -/
theorem prodMargin_of_ceil (δ g C : Q') (hδ : (0 : Q') ≤ δ) (hgC : g ≤ C)
    (hδC : δ * C ≤ SpectralLocalizationCrux.q112) :
    δ * g ≤ SpectralLocalizationCrux.q112 := by
  have h1 : δ * g ≤ δ * C := Q'.mul_le_mul_of_nonneg_left g C δ hgC hδ
  exact Q'.le_trans' _ _ _ h1 hδC

/-- **THE COMPOSED TAIL REDUCTION.**  Combining the two: under the ceiling `g ≤ C`
and small-defect budget `δ·C ≤ 1/12`, ANY scaled trajectory shift (`shift ≤ δ·g`)
satisfies the constant localization bound `shift ≤ 1/12`.  Hence the trajectory
`hbridge` is the sharp obligation and `bulk_shift` its tail shadow. -/
theorem trajectoryShift_clears_margin (δ g C shift : Q') (hδ : (0 : Q') ≤ δ)
    (hgC : g ≤ C) (hδC : δ * C ≤ SpectralLocalizationCrux.q112)
    (hb : shift ≤ δ * g) :
    shift ≤ SpectralLocalizationCrux.q112 :=
  scaledShift_implies_bulkShift δ g shift hb (prodMargin_of_ceil δ g C hδ hgC hδC)

end YMGap.Continuum.DefectGapRecursionProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DefectGapRecursionProgress.survivalProduct_recursion_is_mulComm
#print axioms YMGap.Continuum.DefectGapRecursionProgress.constMargin_recursion_tautology
#print axioms YMGap.Continuum.DefectGapRecursionProgress.trajectory_recursion
#print axioms YMGap.Continuum.DefectGapRecursionProgress.cShift_le_margin
#print axioms YMGap.Continuum.DefectGapRecursionProgress.constantBulkShift_insufficient
#print axioms YMGap.Continuum.DefectGapRecursionProgress.scaledShift_implies_bulkShift
#print axioms YMGap.Continuum.DefectGapRecursionProgress.prodMargin_of_ceil
#print axioms YMGap.Continuum.DefectGapRecursionProgress.trajectoryShift_clears_margin
