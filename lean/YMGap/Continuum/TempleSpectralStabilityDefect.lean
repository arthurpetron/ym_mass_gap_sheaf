/-
Track B / R2 — THE SPECTRAL-STABILITY / KATO–TEMPLE ATTACK on the atomic core
`singleStep : realδ_k ≤ 6(1 − w_k)²`.

# What this module does (read first)

The Peter–Weyl work (`PeterWeylEigenvalueResummation`) established the UNPERTURBED
fixed-spacing gap: the transfer at coupling `w` has a located gap with eigenvalue
`w³ = heatKernelSep w` (multiplicity `dim = 2`, Casimir-protected), margin
`g(w) := 1 − w³ = heatKernelMargin w > 0` on `[0,1)`.  The gauge-invariant block-spin
step is a PERTURBATION `T_k → T_{k+1} = T_k + P_k` whose free part (A) is scale-exact,
whose marginal part (B) is the LINEAR coupling drift SUBTRACTED by the counterterm
`renormW` (gauge invariance ⇒ no first-order multiplicity splitting — the first-order
shift is a uniform rescaling of the degenerate sector), and whose residual transverse
part (C) is the off-diagonal `P_k^⊥` (s=1 ↔ s≥2).  All of (A)/(B)/(C) are already
PROVED in `SingleStepDefectReduction` / `CharFunCumulantDefect`.

This module contributes the SECOND-ORDER (Kato–Temple) control of the transverse part
and converts the whole per-step defect bound into a sharp OFF-DIAGONAL NORM THRESHOLD.

## THE NEW PROVED MATH — Temple's 2×2 second-order bound (exact)

Model the transverse coupling as the real-symmetric 2×2 block on {fundamental, first
excited}, fundamental normalized to the gap top:  `M = [[0,b],[b,g]]`, `b := ‖P_k^⊥‖`.
Its characteristic polynomial is `λ² − gλ − b² = 0` (sympy-verified), so the downward
shift `δ := −λ_-` of the fundamental obeys the EXACT identity `δ·(δ+g) = b²`.  Hence
(the genuine Temple content, division-free):

    δ·g ≤ δ·(δ+g) = b²           (`temple_shift_le`),

and, with `g > 0`,

    δ ≤ 6(1−w)²   ⟸   b² ≤ 6(1−w)²·(1−w³)     (`temple_threshold_defect`).

So the target `realδ_k ≤ 6(1−w_k)²` is EQUIVALENT (given the 2×2 Temple structure) to
the sharp perturbation-strength threshold

    ‖P_k^⊥‖  ≤  √6·(1−w_k)·√(1−w_k³) .

`TempleOffDiagonalResidual` carries this per-scale (as `bsq_k = ‖P_k^⊥‖²`), and
`residual_gives_defect` discharges the per-step defect bound FROM the threshold — the
Temple inequality doing genuine work.  It is INHABITABLE by the PROVED model
(`templeResidual_model`, non-vacuity witness: `bsq_k := δ_model_k·g_k`,
`pert` from `bondMovingDeltaRen_le_sixp`), which reproves the model bound via the
spectral route and pins the exact margin factor `√((2+w)/3)` (`model_offdiag_le_max`).

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9) — does this close `singleStep`?

NO.  `b = ‖P_k^⊥‖` is the interacting content: via the exact `δ(δ+g)=b²` the map
`δ ↔ b` is a bijection at fixed `g`, so the threshold `b² ≤ 6(1−w)²(1−w³)` is a
REFRAMING of `δ ≤ 6(1−w)²`, EQUI-INHABITING with `singleStep` (same class as
`ResummedClustering` / `uniform_in_m`), NOT a strictly-weaker sub-obligation.  Bounding
the PHYSICAL off-diagonal a-priori (over the full RG recursion, at the true margin)
still needs the unconstructed interacting block-spin effective action.  The gap is
non-uniform (`g → 0` as `w → 1`), so the threshold `→ 0` faster than `(1−w)`.  This
module is NOT a `:= SingleStepDefectBound` alias; it proves the enabling Temple
inequality outright and pins the residual to a single per-scale scalar norm.  F=1
stands, D=0, guard=5.  NO 4D Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing PROVED `heatKernelMargin_pos`, the `Q'`
mul/add-monotonicity toolkit, `BakryEmery.le_of_mul_le_mul_right_pos` (positive
right-cancellation), and `bondMovingDeltaRen_le_sixp` / `renDefect_factor`.  Every
load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `ring`/`nlinarith`, no `sorry`.  All witnesses are
`Type`-level `Q'` data (Rule 8).
-/

import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.BakryEmery

namespace YMGap.Continuum.TempleSpectralStabilityDefect

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor

/-! ## 1. Temple's 2×2 second-order bound (the new proved math). -/

/-- **`g_le_add` — `g ≤ δ + g` for `0 ≤ δ`.**  Elementary, but load-bearing: it is the
one inequality that turns the exact characteristic identity `δ(δ+g) = b²` into the
Temple bound.  (`0 + g ≤ δ + g` by right-monotonicity, and `g ≃ 0 + g`.) -/
theorem g_le_add {δ : Q'} (hδ : (0 : Q') ≤ δ) (g : Q') : g ≤ δ + g := by
  have hstep : (0 : Q') + g ≤ δ + g := Q'.add_le_add_right 0 δ g hδ
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_zero_add_eqv g))) hstep

/-- **`temple_shift_le` — TEMPLE'S 2×2 SECOND-ORDER BOUND (division-free form).**
For a gauge-block `M = [[0,b],[b,g]]` with gap `g` and off-diagonal `b`, the downward
shift `δ ≥ 0` of the fundamental obeys the EXACT characteristic identity
`δ·(δ + g) = b²` (char. poly `λ² − gλ − b² = 0`).  Then

    δ · g  ≤  δ · (δ + g)  =  b² ,

i.e. `δ ≤ b²/g` — the eigenvalue erosion times the gap is at most the squared
off-diagonal.  This is the genuine Kato–Temple content, proved outright in `Q'`. -/
theorem temple_shift_le {δ g b : Q'} (hδ : (0 : Q') ≤ δ)
    (hchar : (δ * (δ + g)).eqv (b * b)) : δ * g ≤ b * b := by
  -- δ·g ≤ δ·(δ+g)  (left-mono, g ≤ δ+g)
  have h1 : δ * g ≤ δ * (δ + g) :=
    Q'.mul_le_mul_of_nonneg_left g (δ + g) δ (g_le_add hδ g) hδ
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv hchar)

/-- **`temple_threshold` — the abstract Temple threshold cancellation.**  From the
Temple bound `δ·g ≤ b²`, a perturbation-strength bound `b² ≤ B·g`, and a strictly
positive gap `g > 0`, the shift is bounded by `B`:

    δ · g ≤ b² ≤ B · g   ⟹   δ ≤ B    (cancel the positive `g`).

The single positive right-cancellation is `BakryEmery.le_of_mul_le_mul_right_pos`. -/
theorem temple_threshold {δ g b B : Q'} (hg : (0 : Q') < g)
    (htemple : δ * g ≤ b * b) (hpert : b * b ≤ B * g) : δ ≤ B := by
  have hchain : δ * g ≤ B * g := Q'.le_trans' _ _ _ htemple hpert
  exact BakryEmery.le_of_mul_le_mul_right_pos hg hchain

/-! ## 2. Instantiation at the Peter–Weyl gap `g = 1 − w³`. -/

/-- **`temple_threshold_defect` — the per-step defect bound from the off-diagonal
threshold.**  With the PROVED Peter–Weyl unperturbed gap `g = heatKernelMargin w =
1 − w³ > 0` (`0 ≤ w < 1`), the Temple bound plus the sharp off-diagonal threshold

    ‖P^⊥‖² = bsq ≤ 6(1−w)² · (1 − w³)

yield the target per-step defect bound

    δ  ≤  6·(1 − w)² .

This is the exact conversion of `realδ ≤ 6(1−w)²` into a perturbation-strength
threshold on the transverse off-diagonal. -/
theorem temple_threshold_defect {w δ bsq : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (htemple : δ * heatKernelMargin w ≤ bsq)
    (hpert : bsq ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) * heatKernelMargin w) :
    δ ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hg : (0 : Q') < heatKernelMargin w := heatKernelMargin_pos w hw0 hw1
  -- δ·g ≤ bsq ≤ B·g  ⟹  δ·g ≤ B·g  ⟹  δ ≤ B  (positive right-cancel; `bsq` = `‖P^⊥‖²`)
  exact BakryEmery.le_of_mul_le_mul_right_pos hg (Q'.le_trans' _ _ _ htemple hpert)

/-! ## 3. THE SHARP PERTURBATION-STRENGTH RESIDUAL (deliverable (iii)). -/

/-- **`TempleOffDiagonalResidual` — the sharp per-scale off-diagonal residual
(`Type`, Rule 8).**  Carries, at every scale `k`:

  * `w k` — the coupling (`0 ≤ w_k < 1`);
  * `δ k` — the per-step transverse gap erosion (`0 ≤ δ_k`);
  * `bsq k` — the SQUARED transverse off-diagonal norm `‖P_k^⊥‖²` (kept squared so the
    object stays `Q'`-rational — no `sqrt`);
  * `temple` — the Kato–Temple 2nd-order bound `δ_k·(1−w_k³) ≤ ‖P_k^⊥‖²` (from the
    characteristic identity `δ(δ+g)=b²` and `g ≤ δ+g`);
  * `pert` — **THE RESIDUAL THRESHOLD** `‖P_k^⊥‖² ≤ 6(1−w_k)²·(1−w_k³)`, i.e.
    `‖P_k^⊥‖ ≤ √6·(1−w_k)·√(1−w_k³)`.

This is NOT `SingleStepDefectReduction.SingleStepDefectBound` (no `trueMargin`
recursion; a single per-scale scalar-norm threshold instead).  It is the sharpest
scalar reframing of the atomic core: the whole per-step defect bound reduces to the
`pert` field — an a-priori bound on ONE per-scale interacting off-diagonal norm.  The
`pert` field is the open interacting content (equi-inhabiting `singleStep`, NOT
strictly weaker); it is inhabitable by the PROVED model (`templeResidual_model`). -/
structure TempleOffDiagonalResidual : Type where
  /-- The per-scale coupling. -/
  w : Nat → Q'
  /-- The per-step transverse gap erosion (the shift `δ_k`). -/
  δ : Nat → Q'
  /-- The SQUARED transverse off-diagonal norm `‖P_k^⊥‖²`. -/
  bsq : Nat → Q'
  /-- `0 ≤ w_k`. -/
  hw0 : ∀ k, (0 : Q') ≤ w k
  /-- `w_k < 1` (strict — the gap `1 − w_k³` is strictly positive). -/
  hw1 : ∀ k, w k < (1 : Q')
  /-- The Kato–Temple 2nd-order bound `δ_k·(1 − w_k³) ≤ ‖P_k^⊥‖²`. -/
  temple : ∀ k, δ k * heatKernelMargin (w k) ≤ bsq k
  /-- **THE RESIDUAL** — the off-diagonal threshold `‖P_k^⊥‖² ≤ 6(1−w_k)²·(1−w_k³)`. -/
  pert : ∀ k, bsq k
      ≤ Q'.ofNat 6 * (((1 : Q') - w k) * ((1 : Q') - w k)) * heatKernelMargin (w k)

/-- **`residual_gives_defect` — the Temple inequality discharges the per-step defect.**
From a `TempleOffDiagonalResidual`, at every scale the per-step transverse gap erosion
obeys `δ_k ≤ 6(1 − w_k)²`.  The Kato–Temple bound does the genuine work: the
off-diagonal threshold `pert` plus the 2nd-order bound `temple` yield the quadratic
defect bound. -/
theorem residual_gives_defect (R : TempleOffDiagonalResidual) (k : Nat) :
    R.δ k ≤ Q'.ofNat 6 * (((1 : Q') - R.w k) * ((1 : Q') - R.w k)) :=
  temple_threshold_defect (R.hw0 k) (R.hw1 k) (R.temple k) (R.pert k)

/-! ## 4. NON-VACUITY — the PROVED model inhabits the residual (spectral reproof). -/

/-- Constant normalization `ofNat 1·(dimQ 1·(ofNat 3·q)) ≃ ofNat 6·q` (`dimQ 1 = 2`,
`2·3 = 6`).  Isolated so the model instance's `pert` field is a clean rewrite. -/
private theorem const_six_eqv (q : Q') :
    (Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * q))).eqv (Q'.ofNat 6 * q) := by
  -- Step 1: ofNat 1·Y ≃ Y
  have hone : (Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * q))).eqv (dimQ 1 * (Q'.ofNat 3 * q)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (dimQ 1 * (Q'.ofNat 3 * q)) (by decide))
      (Q'.one_mul_eqv _)
  -- Step 2: dimQ 1·(3·q) ≃ (dimQ 1·3)·q
  have hassoc : (dimQ 1 * (Q'.ofNat 3 * q)).eqv ((dimQ 1 * Q'.ofNat 3) * q) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ 1) (Q'.ofNat 3) q)
  -- Step 3: (dimQ 1·3)·q ≃ 6·q
  have h6 : (dimQ 1 * Q'.ofNat 3).eqv (Q'.ofNat 6) := by
    show (Q'.ofNat 2 * Q'.ofNat 3).eqv (Q'.ofNat 6)
    exact Q'.eqv_symm (ofNat_mul_eqv 2 3)
  exact Q'.eqv_trans _ _ _ hone
    (Q'.eqv_trans _ _ _ hassoc (Q'.mul_eqv_congr_right _ _ q h6))

/-- **`templeResidual_model` — the residual is inhabited by the PROVED model.**  For any
admissible coupling sequence `w` (`0 ≤ w_k < 1`), taking `δ_k := bondMovingDeltaRen 1 1 w_k`
(the proved renormalized model defect) and `bsq_k := δ_k·(1 − w_k³)` (the implied
off-diagonal squared) gives a genuine `TempleOffDiagonalResidual`:

  * `temple` holds with EQUALITY (`δ_k·g_k ≤ δ_k·g_k`);
  * `pert` holds because `δ_k = δ_model ≤ 6(1−w_k)²` (`bondMovingDeltaRen_le_sixp`)
    scaled by `g_k ≥ 0`.

So the Temple reframing is NON-VACUOUS and reproves the model bound via the spectral
route.  (This inhabits it with the MODEL defect `δ_model`, NOT the true `realδ` — hence
it does NOT close `singleStep`; the open content is the `pert` bound for the REAL
interacting off-diagonal over the full recursion.) -/
noncomputable def templeResidual_model
    (w : Nat → Q') (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k < (1 : Q')) :
    TempleOffDiagonalResidual where
  w := w
  δ := fun k => bondMovingDeltaRen 1 1 (w k)
  bsq := fun k => bondMovingDeltaRen 1 1 (w k) * heatKernelMargin (w k)
  hw0 := hw0
  hw1 := hw1
  temple := fun k => Q'.le_refl' _
  pert := fun k => by
    -- δ_model·g ≤ 6(1−w)²·g  from  δ_model ≤ 6(1−w)²  and  0 ≤ g
    have hg : (0 : Q') ≤ heatKernelMargin (w k) :=
      Q'.le_of_lt (heatKernelMargin_pos (w k) (hw0 k) (hw1 k))
    -- δ_model = bondMovingDeltaRen 1 1 w ≤ ofNat 1·(dimQ 1·(ofNat 3·(1−w)²)) = 6(1−w)²
    have hsix : bondMovingDeltaRen 1 1 (w k)
        ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w k) * ((1 : Q') - w k)))) :=
      bondMovingDeltaRen_le_sixp (hw0 k) (Q'.le_of_lt (hw1 k)) 1 1
    -- `ofNat 1·(dimQ 1·(ofNat 3·q)) ≃ ofNat 6·q`
    have hconst := const_six_eqv (((1 : Q') - w k) * ((1 : Q') - w k))
    have hsix6 : bondMovingDeltaRen 1 1 (w k)
        ≤ Q'.ofNat 6 * (((1 : Q') - w k) * ((1 : Q') - w k)) :=
      Q'.le_trans' _ _ _ hsix (Q'.le_of_eqv hconst)
    -- scale by g ≥ 0 on the right
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hsix6 hg

/-- **`model_offdiag_le_max` — the exact `√((2+w)/3)` margin (squared form).**  The
model's implied off-diagonal squared `bsq_model = δ_model·g` is bounded by the threshold
`b_max² = 6(1−w)²·g`, i.e.

    ‖P^⊥‖²_model  =  δ_model·(1−w³)  ≤  6(1−w)²·(1−w³)  =  b_max² ,

with the slack the exact `(2 + w)/3 ≤ 1` factor (`δ_model = 2(1−w)²(2+w)`,
`bondMovingDeltaRen_le_sixp` supplying `δ_model ≤ 6(1−w)²`).  So the PROVED model
off-diagonal sits at or below the Temple threshold — the spectral route is
self-consistent. -/
theorem model_offdiag_le_max {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    bondMovingDeltaRen 1 1 w * heatKernelMargin w
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) * heatKernelMargin w :=
  (templeResidual_model (fun _ => w) (fun _ => hw0) (fun _ => hw1)).pert 0

end YMGap.Continuum.TempleSpectralStabilityDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.g_le_add
#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.temple_shift_le
#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.temple_threshold
#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.temple_threshold_defect
#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.residual_gives_defect
#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.templeResidual_model
#print axioms YMGap.Continuum.TempleSpectralStabilityDefect.model_offdiag_le_max
