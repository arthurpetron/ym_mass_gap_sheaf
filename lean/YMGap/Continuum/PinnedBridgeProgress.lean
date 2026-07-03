/-
Track hbridge-hadd / R2 — **MECHANIZING the wiring lemma `edgeShift_le_gradedDefect`
that discharges the pinned `hbridge` field of `SpectralMarginInput` at the gap edge
`s = 1`, from the already-proved QUADRATIC bond-moving budget.**

# What this module does (read first)

`AsymptoticSpectralLoc.SpectralMarginInput.hbridge` is the PINNED shift-control field

    shift_k  ≤  δ_k · g_k,      g_k = divPos (floorRate_k) (a_k).

With the `hadd`-discharge pinning `shift_k := divPos ((L k).shift 1) a` and the
units dictionary `floorRate_k = heatKernelMargin (w_k) = 1 − w_k³`, BOTH sides carry
the same `1/a`, so (fixed spacing) `hbridge` cancels onto the s = 1 gap edge:

    (L k).shift 1   ≤   δ_k · (1 − w_k³).

This is the vacuum-normalized eigenvalue shift of the located SECOND eigenvalue
(the `s = 1` gap edge), measured in its own located margin `1 − w_k³`.  The
`ScaledBulkShiftClose` close only fires for the `g := 1` surrogate; with the
physical `g_k ≠ 1` this relative-edge-shift statement is the genuine content — and
this module MECHANIZES the wiring lemma for it, which did not previously exist.

# The reduction chain (as implemented)

  * **`margin_cube_ge`** (§0) — the located-margin factorization inequality
        (1 − w)  ≤  heatKernelMargin w  ( = 1 − w³ ),   on 0 ≤ w ≤ 1,
    proved from `w³ ≤ w` (i.e. `qpow w 2 · w ≤ 1 · w`).  This is the
    `1 − w³ = (1 − w)(1 + w + w²) ≥ (1 − w)` fact in eigenvalue units.

  * **`edgeShift_le_of_quad_lin`** (§0, the load-bearing arithmetic core) —
    QUADRATIC-BEATS-LINEAR: from a QUADRATIC supply `s ≤ C·(1 − w)²` and a
    LINEAR lower control `C·(1 − w) ≤ δ` (with `0 ≤ C`, `0 ≤ w ≤ 1`), deduce
        s  ≤  δ · heatKernelMargin w.
    PROOF: `C·(1−w)² ≃ (C·(1−w))·(1−w) ≤ δ·(1−w) ≤ δ·(1−w³)`.  No positivity
    hypothesis on `δ` is needed as input (it is derived from the linear control).

  * **`edgeShift_le_gradedDefect`** (§1, the named target) — the wiring lemma the
    POSTULATE flagged as "not yet in the repo": specializing the core with
    `C = bmConst p = 18p` and feeding the quadratic bond-moving budget
    `BondMovingQuadratic.bondMovingDeltaRen_quadratic`, from the MODEL
    IDENTIFICATION `s ≤ bondMovingDeltaRen N p w` and the near-continuum linear
    control `bmConst p·(1 − w) ≤ δ`, we get `s ≤ δ · heatKernelMargin w`.

  * **`hbridge_pinned_of_edge`** (§2, the `1/a` lift) — from the edge inequality
    `s ≤ δ·m` produce the PINNED field shape `divPos s a ≤ δ · divPos m a`
    (numerator-monotone `divPos` + `divPos_scalar`), i.e. the `1/a`-rescaled
    `SpectralMarginInput.hbridge`.

  * **`EdgeShiftResidual`** (§3) — the reduced input bundling the two honest
    Type-level residuals (`hId` the `(L k).shift 1 ↔ bondMovingDeltaRen`
    identification, `hLin` the near-continuum linear lower control on the graded
    defect) with the per-scale spectral-localization certificates and the fixed
    spacing schedule, producing the field-shaped pinned `hbridge` for every `k`.

# Honest scope

Nothing here conjures the gap.  `EdgeShiftResidual` is NOT inhabited on ℝ⁴: its `L`
still carries the OPEN `bulk_shift` (node ①), and `hId` (the `weight defect ⟹
eigenvalue shift` identification of `(L k).shift 1` with the bond-moving transverse
defect) and `hLin` (the graded defect not vanishing faster than linearly) are the
named residuals.  What is GENUINELY NEW: the wiring lemma `edgeShift_le_gradedDefect`
and the pinned `1/a` lift are now THEOREMS over owned quantities (the PROVED
`bondMovingDeltaRen_quadratic`), not parallel open fields.  This is the QUADRATIC
(slack) direction — disjoint from the LINEAR bulk residual `hlocalize` (Core B),
which remains the sole genuinely-open field.  The Clay YM mass gap stays OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over the already-proved `BondMovingQuadratic` /
`HeatKernelGap` / `RegularCRealArith` engines; every carrier is `Type`-level data.
Each load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`,
no custom `axiom`.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.SpectralMarginBridge

namespace YMGap.Continuum.PinnedBridgeProgress

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelLinearBound
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RegularContinuumPipeline

/-! ## 0. The located-margin factorization and the quadratic-beats-linear core -/

/-- **The located-margin factorization inequality.**  On `0 ≤ w ≤ 1`,

    (1 − w)  ≤  heatKernelMargin w   ( = 1 − w³ ),

the eigenvalue-units form of `1 − w³ = (1 − w)(1 + w + w²) ≥ (1 − w)`.  PROOF:
`w³ = w²·w ≤ 1·w = w` (`qpow_le_one` at `n = 2`), so negating and adding `1`,
`1 − w ≤ 1 − w³`; and `heatKernelMargin w = 1 − heatKernelSep w = 1 − w³`. -/
theorem margin_cube_ge {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (1 : Q') - w ≤ heatKernelMargin w := by
  -- w³ ≤ w  (heatKernelSep w = qpow w 3 = qpow w 2 · w)
  have hsep : heatKernelSep w ≤ w := by
    show qpow w 2 * w ≤ w
    have h1 : qpow w 2 * w ≤ (1 : Q') * w :=
      Q'.mul_le_mul_of_nonneg_right (qpow w 2) (1 : Q') w (qpow_le_one hw0 hw1 2) hw0
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.one_mul_eqv w))
  -- 1 − w ≤ 1 − w³
  have hneg : -w ≤ -(heatKernelSep w) := Q'.neg_le_neg hsep
  have hstep : (1 : Q') + -w ≤ (1 : Q') + -(heatKernelSep w) :=
    Q'.add_le_add_left 1 (-w) (-(heatKernelSep w)) hneg
  -- `1 − w = 1 + −w` and `heatKernelMargin w = 1 − heatKernelSep w = 1 + −(heatKernelSep w)`
  exact hstep

/-- **THE ARITHMETIC CORE — quadratic beats linear.**  From a QUADRATIC supply
`s ≤ C·(1 − w)²` and a LINEAR lower control `C·(1 − w) ≤ δ` (with `0 ≤ C`,
`0 ≤ w ≤ 1`), deduce

    s  ≤  δ · heatKernelMargin w.

PROOF: `C·((1−w)·(1−w)) ≃ (C·(1−w))·(1−w) ≤ δ·(1−w) ≤ δ·(1−w³)`.  `0 ≤ δ` is
DERIVED from the linear control (`0 ≤ C·(1−w) ≤ δ`), not assumed. -/
theorem edgeShift_le_of_quad_lin {s C δ w : Q'}
    (hC : (0 : Q') ≤ C) (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsupply : s ≤ C * (((1 : Q') - w) * ((1 : Q') - w)))
    (hlin : C * ((1 : Q') - w) ≤ δ) :
    s ≤ δ * heatKernelMargin w := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hCw : (0 : Q') ≤ C * ((1 : Q') - w) := Q'.mul_nonneg _ _ hC hnn
  have hδ0 : (0 : Q') ≤ δ := Q'.le_trans' _ _ _ hCw hlin
  -- C·((1−w)·(1−w)) ≃ (C·(1−w))·(1−w)
  have hassoc : (C * (((1 : Q') - w) * ((1 : Q') - w))).eqv
      ((C * ((1 : Q') - w)) * ((1 : Q') - w)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv C ((1 : Q') - w) ((1 : Q') - w))
  have h3 : s ≤ (C * ((1 : Q') - w)) * ((1 : Q') - w) :=
    Q'.le_trans' _ _ _ hsupply (Q'.le_of_eqv hassoc)
  -- (C·(1−w))·(1−w) ≤ δ·(1−w)
  have hstep1 : (C * ((1 : Q') - w)) * ((1 : Q') - w) ≤ δ * ((1 : Q') - w) :=
    Q'.mul_le_mul_of_nonneg_right (C * ((1 : Q') - w)) δ ((1 : Q') - w) hlin hnn
  -- δ·(1−w) ≤ δ·heatKernelMargin w
  have hfact : (1 : Q') - w ≤ heatKernelMargin w := margin_cube_ge hw0 hw1
  have hstep2 : δ * ((1 : Q') - w) ≤ δ * heatKernelMargin w :=
    Q'.mul_le_mul_of_nonneg_left ((1 : Q') - w) (heatKernelMargin w) δ hfact hδ0
  exact Q'.le_trans' _ _ _ h3 (Q'.le_trans' _ _ _ hstep1 hstep2)

/-! ## 1. The named target `edgeShift_le_gradedDefect` — the quadratic bond-moving
budget beats the linear graded defect at the gap edge -/

/-- The bond-moving quadratic modulus constant `C_p = p·dimQ 1·C₄(1)² = 18p`
(verbatim the constant of `bondMovingDeltaRen_quadratic`). -/
def bmConst (p : Nat) : Q' :=
  Q'.ofNat p * (dimQ 1 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1)))

/-- `0 ≤ bmConst p`. -/
theorem bmConst_nonneg (p : Nat) : (0 : Q') ≤ bmConst p :=
  Q'.mul_nonneg _ _ (zero_le_ofNat p)
    (Q'.mul_nonneg _ _ (dimQ_nonneg 1)
      (Q'.mul_nonneg _ _ (zero_le_ofNat (c4 1)) (zero_le_ofNat (c4 1))))

/-- **THE WIRING LEMMA `edgeShift_le_gradedDefect`.**  The pinned `hbridge`, at the
gap edge, reduced to owned quantities.  From:

  * `hId` — the MODEL IDENTIFICATION `s ≤ bondMovingDeltaRen N p w` (the `weight
    defect ⟹ eigenvalue shift` bridge: the s = 1 block-spin shift is bounded by the
    bond-moving transverse defect on the dominant mode); and
  * `hLin` — the near-continuum LINEAR lower control `bmConst p·(1 − w) ≤ δ` (the
    graded defect does not vanish faster than linearly in the margin),

conclude the located-edge relative shift bound

    s  ≤  δ · heatKernelMargin w   ( = δ·(1 − w³) ).

PROOF: `bondMovingDeltaRen_quadratic` supplies the QUADRATIC `bondMovingDeltaRen ≤
bmConst p·(1−w)²`, so `s ≤ bmConst p·(1−w)²`, and `edgeShift_le_of_quad_lin` fires. -/
theorem edgeShift_le_gradedDefect {s δ w : Q'} {N p : Nat}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hId : s ≤ bondMovingDeltaRen N p w)
    (hLin : bmConst p * ((1 : Q') - w) ≤ δ) :
    s ≤ δ * heatKernelMargin w := by
  have hquad : bondMovingDeltaRen N p w ≤ bmConst p * (((1 : Q') - w) * ((1 : Q') - w)) :=
    bondMovingDeltaRen_quadratic hw0 hw1 N p
  have hsupply : s ≤ bmConst p * (((1 : Q') - w) * ((1 : Q') - w)) :=
    Q'.le_trans' _ _ _ hId hquad
  exact edgeShift_le_of_quad_lin (bmConst_nonneg p) hw0 hw1 hsupply hLin

/-! ## 2. The `1/a` lift onto the PINNED `SpectralMarginInput.hbridge` field shape -/

/-- **THE PINNED `hbridge` LIFT.**  From the edge inequality `s ≤ δ·m`, the
`1/a`-rescaled PINNED field shape holds:

    divPos s a  ≤  δ · divPos m a.

PROOF: numerator-monotone `divPos_le_divPos_of_le` gives `divPos s a ≤
divPos (δ·m) a`, and `divPos_scalar` pulls the scalar out: `divPos (δ·m) a ≃
δ·divPos m a`.  Both sides carry the same `1/a`, so this is the pinned
`SpectralMarginInput.hbridge` with `shift_k := divPos s a` and `g_k := divPos m a`. -/
theorem hbridge_pinned_of_edge {s δ m a : Q'} (ha : (0 : Q') < a)
    (h : s ≤ δ * m) :
    Q'.divPos s a ha ≤ δ * Q'.divPos m a ha := by
  have h1 : Q'.divPos s a ha ≤ Q'.divPos (δ * m) a ha := divPos_le_divPos_of_le ha h
  have h2 : (Q'.divPos (δ * m) a ha).eqv (δ * Q'.divPos m a ha) := divPos_scalar δ m a ha
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)

/-! ## 3. The reduced input `EdgeShiftResidual` and the field-shaped pinned `hbridge` -/

/-- **THE REDUCED INPUT.**  The per-scale spectral-localization certificates and the
fixed-spacing schedule, together with the TWO honest Type-level residuals from which
the pinned `hbridge` becomes a THEOREM at the gap edge:

  * `hId` — the MODEL IDENTIFICATION `(L k).shift 1 ≤ bondMovingDeltaRen N p (w k)`
    (the s = 1 block-spin eigenvalue shift bounded by the bond-moving transverse
    defect on the dominant mode: the `weight defect ⟹ eigenvalue shift` bridge);
  * `hLin` — the near-continuum LINEAR lower control `bmConst p·(1 − w_k) ≤ δ_k`
    (the graded defect not vanishing faster than linearly in the margin).

NOT inhabited on ℝ⁴: each `L k` still carries the OPEN `bulk_shift` (node ①), and
`hId`/`hLin` are named residuals. -/
structure EdgeShiftResidual (N p : Nat) : Type where
  /-- The RG weight trajectory. -/
  w : Nat → Q'
  /-- Each weight is nonnegative. -/
  hw0 : ∀ k, (0 : Q') ≤ w k
  /-- Each weight is `≤ 1`. -/
  hw1 : ∀ k, w k ≤ (1 : Q')
  /-- The per-scale spectral-localization certificate (open `bulk_shift`). -/
  L : ∀ k, SpectralLocalization (w k)
  /-- The graded defect schedule. -/
  δ : Nat → Q'
  /-- **`hId`** — the model identification (named residual). -/
  hId : ∀ k, (L k).shift 1 ≤ bondMovingDeltaRen N p (w k)
  /-- **`hLin`** — the near-continuum linear lower control (named residual). -/
  hLin : ∀ k, bmConst p * ((1 : Q') - w k) ≤ δ k
  /-- The fixed-spacing infinite-volume cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- The (fixed) lattice spacing. -/
  spacing : Q'
  /-- The spacing is strictly positive. -/
  spacing_pos : (0 : Q') < spacing
  /-- The floor-rate dictionary `floorRate_k = 1 − w_k³`. -/
  hFR : ∀ k, (atSpacing k).floorRate = heatKernelMargin (w k)

/-- **THE EDGE FORM.**  Under an `EdgeShiftResidual`, the located-edge relative
shift bound holds at every scale `k`:

    (L k).shift 1  ≤  δ_k · heatKernelMargin (w_k)   ( = δ_k·(1 − w_k³) ). -/
theorem EdgeShiftResidual.edgeForm {N p : Nat} (R : EdgeShiftResidual N p) (k : Nat) :
    (R.L k).shift 1 ≤ R.δ k * heatKernelMargin (R.w k) :=
  edgeShift_le_gradedDefect (R.hw0 k) (R.hw1 k) (R.hId k) (R.hLin k)

/-- **THE FIELD-SHAPED PINNED `hbridge`.**  Lifting the edge form by `1/a` and
rewriting `heatKernelMargin (w_k) = floorRate_k`, the pinned
`SpectralMarginInput.hbridge` field shape holds at every scale `k`
(with `shift_k := divPos ((L k).shift 1) a`, `g_k := divPos (floorRate_k) a`):

    divPos ((L k).shift 1) a  ≤  δ_k · divPos (floorRate_k) a. -/
theorem EdgeShiftResidual.hbridge {N p : Nat} (R : EdgeShiftResidual N p) (k : Nat) :
    Q'.divPos ((R.L k).shift 1) R.spacing R.spacing_pos
      ≤ R.δ k * Q'.divPos ((R.atSpacing k).floorRate) R.spacing R.spacing_pos := by
  have h := hbridge_pinned_of_edge R.spacing_pos (R.edgeForm k)
  rw [← R.hFR k] at h
  exact h

end YMGap.Continuum.PinnedBridgeProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PinnedBridgeProgress.margin_cube_ge
#print axioms YMGap.Continuum.PinnedBridgeProgress.edgeShift_le_of_quad_lin
#print axioms YMGap.Continuum.PinnedBridgeProgress.bmConst_nonneg
#print axioms YMGap.Continuum.PinnedBridgeProgress.edgeShift_le_gradedDefect
#print axioms YMGap.Continuum.PinnedBridgeProgress.hbridge_pinned_of_edge
#print axioms YMGap.Continuum.PinnedBridgeProgress.EdgeShiftResidual.edgeForm
#print axioms YMGap.Continuum.PinnedBridgeProgress.EdgeShiftResidual.hbridge
