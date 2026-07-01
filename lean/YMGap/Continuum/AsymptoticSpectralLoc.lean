/-
Track B / R2 — **DISCHARGING the sole open `recursion` field of
`AFDeltaDecay.AsymptoticDescentInput` via the additive→multiplicative
eigenvalue-shift converter.**

# What this module does (read first)

`AFDeltaDecay.AsymptoticDescentInput` packaged the spacing-uniform continuum
physical-gap floor with ONE genuinely-open field — the per-block margin recursion

    (1 − δ_k) · g_k  ≤  g_{k+1},        g_k := m_lat(a_k)/a_k
                                              = `Q'.divPos (floorRate) (spacing)`.

This module REShAPES that single opaque field into two more-structured inputs and
proves the multiplicative recursion from them by a one-line arithmetic converter:

  * **`margin_recursion_of_eigShift`** (§1, the sole new arithmetic).  The
    additive→multiplicative bridge:
        `g_k − shift_k ≤ g_{k+1}`  ∧  `shift_k ≤ δ_k · g_k`  ⟹  `(1−δ_k)·g_k ≤ g_{k+1}`,
    proved by distributing `(1−δ_k)·g_k ≃ g_k − δ_k·g_k` (`Q'.sub_mul_eqv`,
    `Q'.one_mul_eqv`) and neg-monotone + `add_le_add_left`.  NO positivity needed.

  * **`SpectralMarginInput`** (§2) — the reduced input: a summable-defect tower
    `T`, the physical spacing schedule (verbatim from `AsymptoticDescentInput`),
    and the two feeding fields `hadd` (the located-2nd-eigenvalue ↔ physical-margin
    dictionary) and `hbridge` (`shift_k ≤ δ_k·g_k`, the trajectory/physical form of
    the named vacuum-normalized bulk eigenvalue-shift control
    `SpectralLocalizationCrux.bulk_shift` / `DeltaFrontierLedger.bulkCtrl`).  It also
    carries the graded `SpectralLocalization sl` and the tail-shift identification
    `hδ : T.δ k = sl.gapDefect (k + fmCutoff …)` that COLLAPSES the two parallel
    `RGGapPersistence.prodPrefix` floor stacks into one.

  * **`SpectralMarginInput.toAsymptotic`** (§2) — feeds the converter into the
    open `recursion` field, so `recursion` stops being an independent open field
    and is DISCHARGED (proved), leaving only `hadd`/`hbridge` as the named
    Type-level residuals.

  * **`oneSub_delta_eq_tailRate`** (§3) — the stack-collapse identity
    `1 − T.δ k = fmTailRate afr (spectralLocalization_defect …) (fmCutoff …) k`,
    witnessing that `AFDeltaDecay.defect_product_floor` and
    `GradedBondMovingBudget.spectralLocalization_gap` are the SAME `Σ′` shape.

  * **The payoff** (§4) — `continuum_floor_pos` / `uniform_floor` compose the
    reduced input with the existing green tail (`AsymptoticDescentInput.uniform_floor`
    / `continuum_floor_pos`) to yield the strictly-positive spacing-uniform continuum
    physical-gap floor, with `recursion` discharged rather than assumed.

# Honest scope

The reduction does NOT conjure the gap.  It reshapes the single open `recursion`
field into `hadd` (genuine √-bridge + `a_k`-rescaling plumbing over the PROVED
eigenvalue-location facts `bulk_below_gapEdge` / `localization_holds`) and
`hbridge` (which IS the already-named open input `bulk_shift ≤ 1/12` /
`BulkDefectControlled` / `VacNormEigShift`, the `p ≥ 2` vacuum-normalized fusion
local-CLT residual, now tied to the summable graded defect instead of the bare
constant `1/12`).  `SpectralMarginInput` is NOT inhabited on ℝ⁴; the converter and
the stack-collapse identity are genuine axiom-clean advances.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition over `AFDeltaDecay` /
`GradedBondMovingBudget`; every carrier is `Type`-level data.  Each load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.AFDeltaDecay
import YMGap.Continuum.GradedBondMovingBudget

namespace YMGap.Continuum.AsymptoticSpectralLoc

open YMGap.Constructive
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.FullModeAssembly

/-! ## 1. The additive→multiplicative eigenvalue-shift converter (the sole new arithmetic) -/

/-- **THE CONVERTER.**  From the additive margin drop `g_k − shift_k ≤ g_{k+1}` and
the shift control `shift_k ≤ δ_k · g_k`, deduce the multiplicative recursion

    (1 − δ_k) · g_k  ≤  g_{k+1}.

PROOF (no positivity): `(1−δ_k)·g_k ≃ g_k − δ_k·g_k` (`Q'.sub_mul_eqv` +
`Q'.one_mul_eqv`); `hbridge` gives `−δ_k·g_k ≤ −shift_k` (neg-monotone) hence
`g_k − δ_k·g_k ≤ g_k − shift_k` (`add_le_add_left`); then `hadd`. -/
theorem margin_recursion_of_eigShift
    (δk shiftk gk gk1 : Q')
    (hadd : gk - shiftk ≤ gk1)
    (hbridge : shiftk ≤ δk * gk) :
    (1 - δk) * gk ≤ gk1 := by
  -- (a) distribute: (1 − δk)·gk ≃ gk + −(δk·gk)
  have hdist : (((1 : Q') - δk) * gk).eqv (gk + -(δk * gk)) := by
    exact Q'.eqv_trans _ _ _ (Q'.sub_mul_eqv 1 δk gk)
      (Q'.add_eqv_congr_right (1 * gk) gk (-(δk * gk)) (Q'.one_mul_eqv gk))
  -- (b) −(δk·gk) ≤ −shiftk  (neg-monotone on hbridge)
  have hneg : -(δk * gk) ≤ -shiftk := Q'.neg_le_neg hbridge
  -- (c) gk + −(δk·gk) ≤ gk + −shiftk  (add_le_add_left), and gk + −shiftk = gk − shiftk
  have hstep : gk + -(δk * gk) ≤ gk + -shiftk :=
    Q'.add_le_add_left gk _ _ hneg
  -- chain: (1−δk)·gk ≃ gk + −(δk·gk) ≤ gk − shiftk ≤ gk1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist)
    (Q'.le_trans' _ _ _ hstep hadd)

/-! ## 2. The reduced input `SpectralMarginInput` and its `AsymptoticDescentInput` -/

/-- **THE REDUCED INPUT.**  A summable-defect exponent descent tower `T` together
with the graded `SpectralLocalization sl` (supplying the summable graded defect),
the tail-shift identification `hδ` (collapsing the two product-floor stacks), the
physical spacing schedule (verbatim from `AsymptoticDescentInput`), and the two
feeding fields:

  * `hadd` — the located-2nd-eigenvalue ↔ physical-margin dictionary
    `g_k − shift_k ≤ g_{k+1}` (√-bridge + `a_k`-rescaling of the proved
    eigenvalue-location facts `bulk_below_gapEdge` / `localization_holds`);
  * `hbridge` — `shift_k ≤ δ_k · g_k`, the trajectory/physical form of the named
    vacuum-normalized bulk eigenvalue-shift control (`bulk_shift` /
    `BulkDefectControlled` / `VacNormEigShift`), now tied to the summable graded
    defect rather than the bare constant `1/12`.

These are the honest Type-level residuals; `SpectralMarginInput` is NOT inhabited
on ℝ⁴. -/
structure SpectralMarginInput (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type where
  /-- The graded spectral-localization datum (summable graded defect). -/
  sl : GradedBondMovingBudget.SpectralLocalization afr N₀
  /-- The summable-defect exponent descent tower (supplies `ρ = 1−δ`, floor). -/
  T : AFDeltaDecay.SummableDescentTower b
  /-- **THE TAIL-SHIFT IDENTIFICATION** — the two product-floor stacks coincide:
  `T.δ k = sl.gapDefect (k + fmCutoff …)`. -/
  hδ : ∀ k, T.δ k =
    (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl).d
      (k + fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ sl))
  /-- The lattice spacings `a_j > 0`. -/
  spacing : Nat → Q'
  /-- Each spacing is strictly positive. -/
  spacing_pos : ∀ j, (0 : Q') < spacing j
  /-- The fixed-spacing infinite-volume cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- A uniform physical ceiling. -/
  ceilConst : Q'
  /-- The physical gap is bounded above by the ceiling. -/
  physCeil : ∀ j,
    Q'.divPos ((atSpacing j).floorRate) (spacing j) (spacing_pos j) ≤ ceilConst
  /-- The UV anchor floor `g0 > 0`. -/
  anchor : Q'
  /-- The anchor is strictly positive. -/
  anchor_pos : (0 : Q') < anchor
  /-- The anchor bound `g0 ≤ physGap_0`. -/
  anchor_le : anchor ≤
    Q'.divPos ((atSpacing 0).floorRate) (spacing 0) (spacing_pos 0)
  /-- The per-mode eigenvalue-shift budget `shift_k = (loc k).shift`. -/
  shift : Nat → Q'
  /-- **`hadd`** — the located-2nd-eigenvalue ↔ physical-margin dictionary. -/
  hadd : ∀ k,
    Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k) - shift k
      ≤ Q'.divPos ((atSpacing (k + 1)).floorRate) (spacing (k + 1)) (spacing_pos (k + 1))
  /-- **`hbridge`** — the shift is controlled by defect·margin
  (`= bulk_shift`, trajectory form). -/
  hbridge : ∀ k,
    shift k ≤ T.δ k *
      Q'.divPos ((atSpacing k).floorRate) (spacing k) (spacing_pos k)

/-- The physical margin `g_k = m_lat(a_k)/a_k = Q'.divPos (floorRate) (spacing)`. -/
def SpectralMarginInput.g {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (I : SpectralMarginInput b afr N₀) (k : Nat) : Q' :=
  Q'.divPos ((I.atSpacing k).floorRate) (I.spacing k) (I.spacing_pos k)

/-- **THE DISCHARGE.**  A `SpectralMarginInput` yields an
`AFDeltaDecay.AsymptoticDescentInput` whose formerly-open `recursion` field is
PROVED via `margin_recursion_of_eigShift` from `hadd` and `hbridge`.  The physical
schedule, ceiling, and anchor are supplied verbatim. -/
def SpectralMarginInput.toAsymptotic {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (I : SpectralMarginInput b afr N₀) : AFDeltaDecay.AsymptoticDescentInput b where
  T := I.T
  spacing := I.spacing
  spacing_pos := I.spacing_pos
  atSpacing := I.atSpacing
  ceilConst := I.ceilConst
  physCeil := I.physCeil
  anchor := I.anchor
  anchor_pos := I.anchor_pos
  anchor_le := I.anchor_le
  recursion := fun k =>
    margin_recursion_of_eigShift (I.T.δ k) (I.shift k) (I.g k) (I.g (k + 1))
      (I.hadd k) (I.hbridge k)

/-! ## 3. The stack-collapse identity -/

/-- **THE TWO PRODUCT-FLOOR STACKS COINCIDE.**  Under the tail-shift
identification `hδ`, the tower's per-block multiplier equals the graded tail rate:

    1 − T.δ k  =  fmTailRate afr (spectralLocalization_defect …) (fmCutoff …) k,

so `AFDeltaDecay.defect_product_floor T` and
`GradedBondMovingBudget.spectralLocalization_gap afr N₀ sl` are the SAME `Σ′`
prefix-floor.  PROOF: unfold `fmTailRate` (`= 1 − d(k0+k)`); `hδ` plus
`Nat.add_comm` match the indices. -/
theorem SpectralMarginInput.oneSub_delta_eq_tailRate {b : Nat} {afr : AFRateModulus}
    {N₀ : Nat} (I : SpectralMarginInput b afr N₀) (k : Nat) :
    (1 : Q') - I.T.δ k =
      fmTailRate afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ I.sl)
        (fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ I.sl)) k := by
  show (1 : Q') - I.T.δ k =
      1 - (GradedBondMovingBudget.spectralLocalization_defect afr N₀ I.sl).d
        (fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ I.sl) + k)
  have hidx : I.T.δ k =
      (GradedBondMovingBudget.spectralLocalization_defect afr N₀ I.sl).d
        (fmCutoff afr (GradedBondMovingBudget.spectralLocalization_defect afr N₀ I.sl) + k) := by
    rw [I.hδ k, Nat.add_comm k]
  rw [hidx]

/-! ## 4. The payoff — the strictly-positive spacing-uniform continuum floor -/

/-- **THE UNIFORM PHYSICAL-GAP FLOOR.**  Composing the discharge with the existing
green tail: the reduced input yields a single positive floor below the physical gap
`g_k = m_lat(a_k)/a_k` at EVERY scale `k`, with `recursion` PROVED. -/
theorem SpectralMarginInput.uniform_floor {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (I : SpectralMarginInput b afr N₀) (k : Nat) :
    I.toAsymptotic.toBlockPersistence.prodFloor ≤
      Q'.divPos ((I.atSpacing k).floorRate) (I.spacing k) (I.spacing_pos k) :=
  I.toAsymptotic.uniform_floor k

/-- **THE CONTINUUM PHYSICAL-GAP FLOOR IS STRICTLY POSITIVE.**  With `recursion`
discharged, the reduced input yields a strictly-positive spacing-uniform continuum
physical-gap floor surviving `a → 0`. -/
theorem SpectralMarginInput.continuum_floor_pos {b : Nat} {afr : AFRateModulus}
    {N₀ : Nat} (I : SpectralMarginInput b afr N₀) :
    (0 : Q') <
      (RGGapPersistence.toScalingBand I.toAsymptotic.toUniform).physGapMin :=
  I.toAsymptotic.continuum_floor_pos

end YMGap.Continuum.AsymptoticSpectralLoc

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AsymptoticSpectralLoc.margin_recursion_of_eigShift
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.toAsymptotic
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.oneSub_delta_eq_tailRate
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.uniform_floor
#print axioms YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.continuum_floor_pos
