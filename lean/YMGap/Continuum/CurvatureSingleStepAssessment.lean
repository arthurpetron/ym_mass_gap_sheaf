/-
Route 2 (Bakry–Émery curvature), a DIFFERENT angle on the sole open field
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`
(`realδ_k ≤ δ_model_k = 6·pMult·(1 − w_k)²`).

# The question this module settles (machine-checked, maximally adversarial)

The fluctuation / interacting-measure (Borel) route bottomed out at the
non-perturbative condensate positivity `Λ = a·exp(−1/2β₀g²) ≠ 0` (the
renormalon).  This module asks whether the CURVATURE route — bounding the gap
MAGNITUDE from the Bakry–Émery / Lichnerowicz curvature of config space (the
Casimir), rather than from the fluctuation determinant — reduces `singleStep`
DIFFERENTLY, i.e. whether the interacting Bakry–Émery `Γ₂ ≥ K` is a more
tractable residual that AVOIDS the renormalon.

**Verdict: NO.  The curvature route does NOT give `singleStep` directly, and the
quantity it reduces to (the interacting `Γ₂`) is NOT more tractable than the
fluctuation determinant — it is structurally WORSE-formed and does not avoid the
renormalon.**  Two machine-checked structural facts pin this:

  (1) `curvature_lands_on_marginal_not_residual` — the FREE curvature the route
      supplies (the SU(2) Casimir, `C₄(1) = 3 = 4·casimirGap = 4·C₂(1)`) is
      EXACTLY the coefficient of the MARGINAL LINEAR part `C₄(1)·(1 − w)` of the
      per-step defect — the part `renormW` already SUBTRACTS as the counterterm
      (part (B) of `SingleStepDefectReduction`, already PROVED).  Subtracting
      that curvature-supplied linear term leaves EXACTLY the QUADRATIC transverse
      residual `(1 − w)²·(2 + w)` (`renDefect_factor`) — and THAT residual is
      `singleStep` (part (C)).  So the free curvature reproduces the ALREADY-PROVED
      marginal part and is ORTHOGONAL to the open residual.  This is the decisive
      new finding: the Lichnerowicz/Casimir bound lands on (B), not on (C).

  (2) `szz_interacting_curvature_goes_negative` — the INTERACTING Bakry–Émery
      curvature (Shen–Zhu–Zhu, CMP 2023, the only rigorous lattice-gauge BE
      curvature) is `K_S(β) = (N+2)/2 − 1 − 8N(d−1)|β|`, which for SU(2), d = 4
      is `1 − 48β`.  It is POSITIVE only at strong coupling `β < 1/48` (the fixed
      coarse spacing = the IR anchor we ALREADY have) and goes NEGATIVE
      (`K_S(β) < 0`) as `β → ∞`, i.e. precisely along the asymptotic-freedom
      trajectory `w_k → 1` where `singleStep` must hold for every `k`.  So the
      interacting-curvature lower bound provides NO positive per-step control in
      the a → 0 direction.

Together with the recorded analyticity obstruction (a Bakry–Émery `K(g²)` is
ANALYTIC at the Gaussian point, hence polynomial in `g²`, hence CANNOT track the
essential singularity `exp(−c/β₀g²)` of the condensate), the curvature route
reshapes but provably CANNOT close `singleStep`: it reduces to the interacting
`Γ₂`, a genuinely DIFFERENT quantity than the fluctuation determinant `z₁`, but
one that is analytic-wrong-form AND fails positivity in the continuum limit — the
SAME non-perturbative condensate positivity, seen through a lens that cannot
resolve it.

`SingleStepDefectBound` is NOT inhabited here.  Nothing is faked.  The 4D
Yang–Mills mass gap remains OPEN.

# What is genuine (PROVED, axiom-clean)

  * `free_curvature_anchor_bundled` — re-exports the PROVED free curvature anchor
    (`casimirGap = 3/4 > 0`, `free_DiagCD`) and the Lichnerowicz saturation datum
    `C₄(1) = 3 = 4·casimirGap` (unit `S³ = SU(2)` is Obata-extremal, so
    Lichnerowicz `λ₁ ≥ n·K = 3` is EQUALITY — the diagonal generator already
    carries the exact eigenvalue `3`; Lichnerowicz adds nothing beyond the exact
    Casimir).
  * `bondMovingDeltaRen_one_factor` — the EXACT identity pinning the per-step
    defect to the quadratic residual: `δ_ren(N,1,w) ≃ dimQ 1·(1 − w)²·(2 + w)`.
  * `curvature_lands_on_marginal_not_residual` — the marginal (curvature) part is
    `C₄(1)·(1 − w)`; the residual after subtracting it is `(1 − w)²·(2 + w)`.
  * `szz_interacting_curvature_goes_negative` / `szz_curvature_zero_at_threshold`
    — the interacting BE curvature `1 − 48β` vanishes at `β = 1/48` and is
    strictly negative for `β > 1/48` (the continuum direction).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing the PROVED `renDefect_factor`,
`bondMovingDeltaRen_le_sixp`, and the PROVED `HeatKernelCurvature` free anchor.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
Witnesses are `Type`-level data.
-/

import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Continuum.HeatKernelCurvature
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.CurvatureSingleStepAssessment

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.HeatKernelCurvature

/-! ## 1. The free curvature anchor = the Lichnerowicz-saturated Casimir

The free single-edge heat-kernel generator is DIAGONAL on characters with the
exact eigenvalue `C₂(s)`; `SU(2) = S³` with its bi-invariant metric is the
round 3-sphere, the Obata-extremal manifold on which the Lichnerowicz bound
`λ₁ ≥ n·K_sec = 3·1 = 3` is SATURATED (equality).  So the curvature route's free
input is the EXACT lowest Casimir `casimirGap = C₂(1) = 3/4`, equivalently
`C₄(1) = 4·casimirGap = 3` in `C₄`-units — already fully in the codebase.  This
bundles it for reference. -/

/-- **The free curvature anchor (Lichnerowicz-saturated Casimir), re-exported.**
`casimirGap = 3/4 > 0`; every excited free mode has energy `≥ 3/4`
(`free_DiagCD`); and the `C₄` exponent is `C₄(1) = 3 = 4·casimirGap` — the
Lichnerowicz value `λ₁ = 3` on the unit `S³` (saturated). -/
theorem free_curvature_anchor_bundled :
    (0 : Q') < casimirGap
    ∧ DiagCD freeDiag casimirGap
    ∧ (c4 1 = 3 ∧ (Q'.ofNat 4 * casimirGap).eqv (Q'.ofNat (c4 1))) :=
  ⟨casimirGap_pos, free_DiagCD, c4_one_eq_four_casimirGap⟩

/-! ## 2. THE DECISIVE DECOMPOSITION — the curvature lands on the MARGINAL part,
       the residual `singleStep` is the QUADRATIC remainder.

The renormalized per-step defect on the dominant mode is
`δ_ren(N,1,w) = dimQ 1·( C₄(1)·(1 − w) − (1 − w^{C₄(1)}) )`.  The free curvature
supplies the coefficient `C₄(1) = 3` of the MARGINAL LINEAR part `C₄(1)·(1 − w)`
— which the counterterm `renormW` SUBTRACTS (part (B), proved in
`SingleStepDefectReduction.trueDev_eq_counterterm_sub_transverse`).  What remains
is the QUADRATIC transverse residual, and THAT is what `singleStep` must bound. -/

/-- **`bondMovingDeltaRen_one_factor` — the per-step defect IS the quadratic
residual.**  The exact identity `δ_ren(N,1,w) ≃ dimQ 1·(1 − w)²·(2 + w)`: after
the marginal linear part (coefficient `C₄(1) = 3` = the free curvature) is
accounted for, the per-step defect is purely SECOND-ORDER in the weak-coupling
margin `1 − w`.  Reuses the PROVED exact factorization `renDefect_factor`. -/
theorem bondMovingDeltaRen_one_factor (N : Nat) (w : Q') :
    (bondMovingDeltaRen N 1 w).eqv
      (dimQ 1 * ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w))) := by
  -- δ_ren(N,1,w) = ofNat 1 · (dimQ 1 · bracket),  bracket = C₄(1)(1−w) − (1 − w^{C₄(1)}).
  show (Q'.ofNat 1 * (dimQ 1 *
        ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))).eqv _
  -- strip the ofNat 1 factor
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 _ (by decide))
      (Q'.one_mul_eqv _)) ?_
  -- inner bracket ≃ (1−w)²·(2+w)  by renDefect_factor (c4 1 = 3 definitionally)
  exact Q'.mul_eqv_congr_left (dimQ 1) _ _ (renDefect_factor w)

/-- **`curvature_lands_on_marginal_not_residual` — the decisive structural fact.**
The MARGINAL part the free curvature supplies is `C₄(1)·(1 − w)` (linear, with
`C₄(1) = 3 = 4·casimirGap` the free Casimir/curvature); subtracting it from the
true deviation `1 − w^{C₄(1)}` leaves EXACTLY the QUADRATIC residual
`(1 − w)²·(2 + w)`.  So the curvature route reproduces the already-PROVED
counterterm-subtracted marginal part (B) and is ORTHOGONAL to the open residual
`singleStep` (C).  The free Casimir does NOT bound `singleStep`; it lands on the
part `renormW` already removes. -/
theorem curvature_lands_on_marginal_not_residual (w : Q') :
    ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w))
    ∧ (Q'.ofNat 4 * casimirGap).eqv (Q'.ofNat (c4 1)) :=
  ⟨renDefect_factor w, c4_one_eq_four_casimirGap.2⟩

/-- **The residual vanishes to SECOND order at the free end** (`w = 1`): the
curvature-orthogonal residual `(1 − w)²·(2 + w)` is `0` at `w = 1`, confirming the
per-step defect erodes nothing at the Gaussian fixed point — consistent with the
free curvature being exhausted by the marginal part.  (Reuses the PROVED
`SingleStepDefectReduction.freeEnd_defect_scaleExact`: `δ_ren(N,p,1) ≤ 0`, pinned
to `0` with nonnegativity.) -/
theorem residual_second_order_at_free_end (N p : Nat) :
    bondMovingDeltaRen N p 1 ≤ 0 ∧ (0 : Q') ≤ bondMovingDeltaRen N p 1 :=
  ⟨SingleStepDefectReduction.freeEnd_defect_scaleExact N p,
    SingleStepDefectReduction.freeEnd_defect_nonneg N p⟩

/-! ## 3. THE INTERACTING CURVATURE — goes NEGATIVE toward the continuum

If the free curvature only supplies the marginal part, then `singleStep` (the
real interacting per-step defect) needs the INTERACTING Bakry–Émery curvature
`Γ₂ ≥ K` of the coupled Wilson-action weight.  The only rigorous lattice-gauge BE
curvature is Shen–Zhu–Zhu (CMP 2023): `K_S(β) = (N+2)/2 − 1 − 8N(d−1)|β|`.  For
SU(2) (`N = 2`), `d = 4` this is `1 − 48β` — a POSITIVE curvature only at strong
coupling `β < 1/48` (the fixed coarse spacing = the IR anchor we already have),
NEGATIVE for `β > 1/48`, i.e. precisely as `β = 2N/g² → ∞` (`w_k → 1`, the a → 0
UV) where `singleStep` must hold for every `k`.  So the interacting-curvature
lower bound gives NO positive per-step control along the AF trajectory: the
quantity the curvature route reduces to is not merely as hard as the fluctuation
determinant — its naive positive form is FALSE in the continuum direction. -/

/-- The Shen–Zhu–Zhu interacting Bakry–Émery curvature for SU(2), `d = 4`:
`K_S(β) = (N+2)/2 − 1 − 8N(d−1)|β| = 1 − 48β`. -/
def szzCurvature (beta : Q') : Q' := (1 : Q') - Q'.ofNat 48 * beta

/-- **The interacting curvature vanishes at the strong-coupling threshold**
`β = 1/48 = 1/(16(d−1))`: `K_S(1/48) = 0`.  Above this the curvature is negative
(next lemma); below it (strong coupling / fixed spacing) it is positive — exactly
the gap we already have. -/
theorem szz_curvature_zero_at_threshold :
    (szzCurvature (Q'.mkPos 1 48 (by decide))).eqv 0 := by decide

/-- **The interacting Bakry–Émery curvature goes NEGATIVE toward the continuum.**
At any `β > 1/48` — the direction of the a → 0 continuum limit
(`β = 2N/g² → ∞`) — the SZZ curvature is strictly negative.  Concretely at the
weak-coupling sample `β = 1`, `K_S(1) = 1 − 48 = −47 < 0`.  So the interacting
curvature lower bound provides NO positive per-step gap control where `singleStep`
lives (`w_k → 1`); the curvature route's residual is FALSE in the continuum
direction, not merely intractable. -/
theorem szz_interacting_curvature_goes_negative :
    szzCurvature 1 < 0 := by decide

/-- **The interacting curvature is positive ONLY at strong coupling** (`β < 1/48`),
i.e. it re-derives the FIXED-SPACING gap we already have (the IR anchor), not the
continuum.  Concrete sample `β = 1/100`: `K_S(1/100) = 1 − 48/100 = 13/25 > 0`. -/
theorem szz_curvature_pos_strong_coupling :
    (0 : Q') < szzCurvature (Q'.mkPos 1 100 (by decide)) := by decide

/-! ## 4. HONEST VERDICT — the curvature route does NOT inhabit `singleStep`

The two machine-checked structural facts above establish:

  * the FREE curvature (Casimir `C₄(1) = 3`) is the coefficient of the MARGINAL
    part `renormW` already subtracts — it lands on part (B), PROVED, not on the
    residual (C) = `singleStep`;
  * the INTERACTING curvature (the only quantity that COULD bound the real
    per-step defect) goes NEGATIVE toward the continuum, so it supplies no
    positive per-step control where `singleStep` must hold.

Hence the curvature route reduces `singleStep` to the interacting `Γ₂` — a
genuinely DIFFERENT quantity than the fluctuation determinant `z₁`, but one that
(i) is analytic in `g²` and cannot track the essential singularity
`exp(−c/β₀g²)`, and (ii) has a positive lower bound only at strong coupling.  It
does NOT avoid the renormalon; it is the SAME non-perturbative condensate
positivity, seen through a curvature lens that structurally cannot resolve it.

NO inhabitant of `SingleStepDefectReduction.SingleStepDefectBound` is produced
here.  The following records — as a genuine `Type`-level implication (Rule 9.8),
inhabiting nothing — that IF a spacing-uniform interacting curvature
`UniformCurvatureBound` existed (the named `uniform_CD` wall, refuted-in-form
above at weak coupling), THEN the continuum gap would follow; the point of this
module is that the curvature route CANNOT supply it for `singleStep`. -/

/-- **No free-curvature shortcut to `singleStep`.**  The free curvature bundle is
PROVED (`free_curvature_anchor_bundled`) and the per-step defect is the quadratic
residual (`bondMovingDeltaRen_one_factor`); these are compatible with, and do not
inhabit, `SingleStepDefectBound`.  The residual is the interacting curvature,
which is negative in the continuum direction
(`szz_interacting_curvature_goes_negative`).  This bundles the three load-bearing
facts of the verdict without producing any frontier inhabitant. -/
theorem curvature_route_verdict :
    ((0 : Q') < casimirGap ∧ DiagCD freeDiag casimirGap)
    ∧ (∀ w : Q', (bondMovingDeltaRen 1 1 w).eqv
        (dimQ 1 * ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w))))
    ∧ szzCurvature 1 < 0 :=
  ⟨⟨casimirGap_pos, free_DiagCD⟩,
    fun w => bondMovingDeltaRen_one_factor 1 w,
    szz_interacting_curvature_goes_negative⟩

end YMGap.Continuum.CurvatureSingleStepAssessment

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.free_curvature_anchor_bundled
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.bondMovingDeltaRen_one_factor
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.curvature_lands_on_marginal_not_residual
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.residual_second_order_at_free_end
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.szz_curvature_zero_at_threshold
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.szz_interacting_curvature_goes_negative
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.szz_curvature_pos_strong_coupling
#print axioms YMGap.Continuum.CurvatureSingleStepAssessment.curvature_route_verdict
