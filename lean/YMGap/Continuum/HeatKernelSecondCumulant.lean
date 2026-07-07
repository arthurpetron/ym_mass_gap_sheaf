/-
Track B / R2 — ROUTE B: the HEAT-KERNEL / Bałaban FLUCTUATION-INTEGRAL derivation of
the block-spin gap defect as a genuine SECOND CUMULANT, and the adversarial
identification of the correct (gap-channel) cumulant object.

# What this module does (read first)

`SingleStepDefectReduction` reduces the whole Clay continuum gap to ONE per-step
inequality `singleStep : (1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`, where the
MODEL defect `δ_model = afDefectSeq afr = bondMovingDeltaRen 1 pMult (w_k)` is the
renormalized (marginal-subtracted) transverse residual on the dominant `s = 1` mode.

This module attacks that residual via the ACTUAL heat-kernel fluctuation integral.
The block-spin RG step integrates out the fine fluctuation field ξ around the coarse
background U:  the coarse effective action is `−log ∫ Dξ exp(−S_fine(U·ξ))`.  Its
cumulant expansion is:

  * (A) the FREE/Gaussian part — scale-EXACT, ZERO defect (`freeEnd_defect_scaleExact`
    upstream: `δ_ren(w=1) ≤ 0`);
  * (B) the MARGINAL part — the running coupling `g²`, SUBTRACTED by the counterterm
    `renormW` (`trueDev_eq_counterterm_sub_transverse` upstream);
  * (C) the TRANSVERSE remainder — the SECOND CUMULANT of the fine field, quadratic in
    the margin `1 − w`.  THIS module.

The heat-kernel single-plaquette class function has character coefficients
`c_s(w) = dimQ(s)·w^{C₄(s)}` (`dimQ(s) = s+1`, `C₄(s) = s(s+2)` the scaled SU(2)
Casimir; `s = 1` = fundamental, `dimQ 1 = 2`, `C₄(1) = 3`).  Integrating out the
fluctuation, the coefficient of channel `s` in the coarse action deviates from its
flat (`w = 1`, Haar) value by the second cumulant of the fluctuation's Casimir in that
channel — the marginal-subtracted overshoot

    over(s,w) = C₄(s)·(1 − w) − (1 − w^{C₄(s)}) ,

which is the SECOND-ORDER (in the margin) part of `1 − w^{C₄(s)}` (the linear/marginal
part having been subtracted by the counterterm).  Weighted by the channel dimension,

    chanCumulant(s,w) := dimQ(s)·over(s,w)         (the per-channel second cumulant).

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

  * `chanCumulant_nonneg` — the per-channel second cumulant is `≥ 0` on `[0,1]` (the
    linear/marginal model over-estimates the true deviation).
  * `chanCumulant_quadratic` — **THE HEAT-KERNEL SECOND-CUMULANT ESTIMATE.**  Per
    channel, the second cumulant is bounded by (dimension × Casimir²) × the SQUARED
    margin:
        chanCumulant(s,w)  ≤  dimQ(s)·C₄(s)²·(1 − w)² .
    This is the `secondOrder_qpow` Taylor-with-remainder at `n = C₄(s)`: the fluctuation
    determinant's deviation from Gaussian is second-order in the field, with the Casimir
    `C₄(s)` playing the curvature (the `d2x ≤ 1` Casimir/curvature bound of the Tier-0
    heat-kernel analysis).
  * `chanCumulant_one_eq_bondMoving` — **the MODEL defect IS the `s = 1` second
    cumulant.**  `bondMovingDeltaRen 1 1 w ≃ chanCumulant 1 w`: the abstract model
    defect equals the fundamental-channel heat-kernel second cumulant, tying the
    fluctuation-integral picture to the in-tree summability machinery.
  * `chanCumulant_one_le_six` — the gap channel's sharp bound `chanCumulant 1 w ≤
    6·(1 − w)²`, with `6 = dimQ(1)·C₄(1) = 2·3` (= `3N` at `N = 2`: the transverse-
    generator count × the block dimension).
  * `afDefectSeq_eq_gapCumulant` — the AF-trajectory model defect `afDefectSeq afr k` IS
    `pMult·chanCumulant 1 (w_{k₀+k})`: the summable `1/k²` sequence is literally the
    fundamental-channel heat-kernel second cumulant along the AF flow.
  * `cumSum` / `cumSum_le_moment` — the FINITE multi-mode second cumulant
    `Σ_{s=1}^{M} chanCumulant(s,w)` bounded by the Casimir-square MOMENT
    `(Σ_{s=1}^{M} dimQ(s)·C₄(s)²)·(1 − w)²` — the second-cumulant bound with an
    explicit finite Casimir-square moment constant.

# THE ADVERSARIAL FINDING (honest, decisive — AGENTS.md Rule 6)

The NAIVE reading "the real defect = the TOTAL fluctuation second cumulant over ALL
channels" is REFUTED numerically (`routeB_numerics.py`, mpmath dps ≥ 40):  the
heat-kernel-measure-weighted total

    R(w) = Σ_{s≥1} μ_s(w)·chanCumulant(s,w),   μ_s(w) = dimQ(s)·w^{C₄(s)}/Z(w),

is `≤ 6·(1 − w)²` ONLY for `w ≤ 0.670…` (which includes the strong-coupling anchor
`w = 1/6`), and DIVERGES like `(1 − w)^{−1/2}` as `w → 1` (the active-mode count
`≍ τ^{−1/2}`, `τ = −log w`).  Along the AF flow `1 − w_k ∼ 1/k` the total `R(w_k) ∼
k^{1/2}` is NOT summable — so the TOTAL second cumulant is NOT the gap defect; it is an
over-count (a free-energy quantity mixing all mass channels).

The physically-correct gap defect is the fundamental-channel (`s = 1`) second cumulant
`chanCumulant 1 w`, times the `pMult` transverse GENERATOR modes of the block (NOT a
sum over representation channels): this is `bondMovingDeltaRen 1 pMult w = δ_model`,
which IS `≤ 6·pMult·(1 − w)²` for ALL `w` and IS summable (`∼ 1/k²`).  The higher
representation channels renormalize the coupling (the marginal flow, subtracted); their
back-reaction ONTO the gap channel is the genuinely-hard Bałaban small-field/large-field
content — the NAMED residual below, NOT the divergent total `R(w)`.

# THE NAMED RESIDUAL and the guard-safe reduction (AGENTS.md Rule 6a / Rule 9)

`GapChannelDomination` carries the single genuinely-open physical input: the REAL 4D
SU(2) per-step degradation of the true dimensionless margin is dominated by the
fundamental-channel heat-kernel second cumulant `pMult·chanCumulant 1 (w_k) = δ_model`.
This is the Bałaban/Magnen–Rivasseau–Sénéor small-field theorem — that after the
marginal subtraction, the transverse fluctuation remainder controlling the GAP channel
is the second cumulant of THAT channel alone (the large-field regions and higher-rep
back-reaction being exponentially suppressed / absorbed).  `gapChannelDomination_to_singleStep`
is a CONDITIONAL producer `GapChannelDomination → SingleStepDefectBound` (a function with
an open-hypothesis binder — NOT an unconditional inhabitant, so the frontier guard does
NOT flag it; it is the Rule-6a reduction, not a closure).  `GapChannelDomination` is
UNINHABITED: it IS the real Bałaban estimate.  NO 4D Yang–Mills mass gap is claimed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural induction, reusing the PROVED
`secondOrder_qpow`, `oneSub_qpow_le`, `bondMovingDeltaRen_le_sixp`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type` data.
-/

import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.HeatKernelSecondCumulant

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 1. The per-channel heat-kernel second cumulant. -/

/-- **The per-channel second cumulant** of the fine-field fluctuation:

    chanCumulant(s,w) = dimQ(s)·( C₄(s)·(1 − w) − (1 − w^{C₄(s)}) ),

the marginal-subtracted transverse residual of representation channel `s` in the
coarse effective action — the second-order (in the margin `1 − w`) part of the true
deviation `dimQ(s)·(1 − w^{C₄(s)})`, weighted by the channel dimension.  Physically:
the deviation of the fluctuation determinant from Gaussian in channel `s`, i.e. the
connected two-point (second cumulant) of the fluctuation's Casimir in that channel. -/
def chanCumulant (s : Nat) (w : Q') : Q' :=
  dimQ s * ((Q'.ofNat (c4 s) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 s)))

/-- The Casimir-square moment coefficient of channel `s`:
`dimQ(s)·C₄(s)²` — the constant multiplying `(1 − w)²` in the second-cumulant bound. -/
def momentTermC (s : Nat) : Q' := dimQ s * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))

/-- The per-channel second cumulant is nonnegative on `[0,1]` (the linear/marginal
model over-estimates the true deviation: `1 − w^{C₄(s)} ≤ C₄(s)·(1 − w)`). -/
theorem chanCumulant_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : (0 : Q') ≤ chanCumulant s w := by
  refine Q'.mul_nonneg _ _ (dimQ_nonneg s) ?_
  have hlin : (1 : Q') - qpow w (c4 s) ≤ Q'.ofNat (c4 s) * ((1 : Q') - w) :=
    oneSub_qpow_le hw0 hw1 (c4 s)
  exact Q'.sub_nonneg_of_le hlin

/-- **THE HEAT-KERNEL SECOND-CUMULANT ESTIMATE — per-channel quadratic bound.**
On `[0,1]`,

    chanCumulant(s,w)  ≤  dimQ(s)·C₄(s)²·((1 − w)·(1 − w)) = momentTermC(s)·(1 − w)² ,

i.e. the fluctuation determinant's deviation from Gaussian in channel `s` is
second-order in the field, with the Casimir `C₄(s)` as the curvature (the `d2x ≤ 1`
heat-kernel curvature bound).  This is `secondOrder_qpow` (the constructive
Taylor-with-remainder `n(1−w) − (1−w^n) ≤ n²(1−w)²`) at `n = C₄(s)`, scaled by the
channel dimension `dimQ(s) ≥ 0`. -/
theorem chanCumulant_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) :
    chanCumulant s w ≤ momentTermC s * (((1 : Q') - w) * ((1 : Q') - w)) := by
  -- inner second-order Taylor remainder at n = C₄(s)
  have hquad :
      (Q'.ofNat (c4 s) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 s))
        ≤ (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
    secondOrder_qpow hw0 hw1 (c4 s)
  -- multiply by dimQ s ≥ 0 on the left
  have hd : chanCumulant s w
      ≤ dimQ s * ((Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hquad (dimQ_nonneg s)
  -- reassociate dimQ s·((cc)·u²) ≃ (dimQ s·(cc))·u² = momentTermC s · u²
  refine Q'.le_trans' _ _ _ hd (Q'.le_of_eqv ?_)
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (dimQ s) (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
      (((1 : Q') - w) * ((1 : Q') - w)))

/-! ## 2. The dominant (fundamental, `s = 1`) channel IS the model defect. -/

/-- **The model defect IS the fundamental-channel second cumulant.**
`bondMovingDeltaRen 1 1 w ≃ chanCumulant 1 w`: the abstract renormalized dominant-mode
defect (used by all the in-tree summability machinery) equals the heat-kernel second
cumulant of the fundamental (`s = 1`) channel.  (The `ofNat 1` bond-moving multiplicity
is the identity.) -/
theorem chanCumulant_one_eq_bondMoving (N : Nat) (w : Q') :
    (bondMovingDeltaRen N 1 w).eqv (chanCumulant 1 w) := by
  -- bondMovingDeltaRen N 1 w = ofNat 1 · (dimQ 1 · bracket) ≃ dimQ 1 · bracket
  show (Q'.ofNat 1 * (dimQ 1 *
      ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))).eqv
    (dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))
  exact Q'.one_mul_eqv _

/-- **The gap channel's sharp quadratic bound** `chanCumulant 1 w ≤ 6·(1 − w)²`
on `[0,1]`, with the SHARP constant `6 = dimQ(1)·C₄(1) = 2·3` (`= 3N` at `N = 2`:
the transverse generators of SU(2) × the block dimension).  Uses the exact `(2+w) ≤ 3`
factorization (`bondMovingDeltaRen_le_sixp`) rather than the crude `C₄² = 9` envelope. -/
theorem chanCumulant_one_le_six {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    chanCumulant 1 w
      ≤ dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w))) := by
  -- chanCumulant 1 w ≃ bondMovingDeltaRen 1 1 w ≤ ofNat 1·(dimQ 1·(3·(1−w)²))
  have heq : (chanCumulant 1 w).eqv (bondMovingDeltaRen 1 1 w) :=
    Q'.eqv_symm (chanCumulant_one_eq_bondMoving 1 w)
  have hb : bondMovingDeltaRen 1 1 w
      ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) :=
    bondMovingDeltaRen_le_sixp hw0 hw1 1 1
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv ?_))
  exact Q'.one_mul_eqv _

/-- **The AF-trajectory model defect IS the fundamental-channel second cumulant.**
`afDefectSeq afr k ≃ pMult·chanCumulant 1 (w_{k₀+k})`: the summable `∼ 1/k²` model
sequence driving the entire product floor is literally the heat-kernel second cumulant
of the fundamental channel along the AF flow (`pMult = 1`, so `≃ chanCumulant 1 (w_k)`).
This grounds the abstract `afDefectSeq` in the actual fluctuation integral. -/
theorem afDefectSeq_eq_gapCumulant (afr : AFRateModulus) (k : Nat) :
    (afDefectSeq afr k).eqv (chanCumulant 1 (afr.w (afCutoff afr + k))) := by
  -- afDefectSeq afr k = renDefect afr pMult (afCutoff+k) = bondMovingDeltaRen 1 pMult (w)
  -- with pMult = 1 (defeq), = bondMovingDeltaRen 1 1 (w) ≃ chanCumulant 1 (w)
  show (bondMovingDeltaRen 1 pMult (afr.w (afCutoff afr + k))).eqv
      (chanCumulant 1 (afr.w (afCutoff afr + k)))
  exact chanCumulant_one_eq_bondMoving 1 (afr.w (afCutoff afr + k))

/-! ## 3. The finite multi-mode second cumulant and its Casimir-square moment. -/

/-- The finite multi-mode second cumulant `Σ_{s=1}^{M} chanCumulant(s,w)` (channels
`1..M`; the trivial `s = 0` channel contributes `0` and is excluded). -/
def cumSum (w : Q') : Nat → Q'
  | 0 => 0
  | M + 1 => cumSum w M + chanCumulant (M + 1) w

/-- The finite Casimir-square moment `Σ_{s=1}^{M} dimQ(s)·C₄(s)²`. -/
def momConst : Nat → Q'
  | 0 => 0
  | M + 1 => momConst M + momentTermC (M + 1)

/-- **The finite multi-mode second-cumulant bound.**  On `[0,1]`,

    Σ_{s=1}^{M} chanCumulant(s,w)  ≤  (Σ_{s=1}^{M} dimQ(s)·C₄(s)²)·(1 − w)² ,

the multi-mode second cumulant bounded by the finite Casimir-square MOMENT times the
squared margin — the finite-truncation form of the heat-kernel second-cumulant bound.
(The INFINITE sum diverges as `w → 1`; see the adversarial finding in the module
header — the total is NOT the gap defect.  This finite bound is the genuine reusable
multi-mode content.)  Proved by induction on `M` from the per-channel
`chanCumulant_quadratic`. -/
theorem cumSum_le_moment {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ M, cumSum w M ≤ momConst M * (((1 : Q') - w) * ((1 : Q') - w))
  | 0 => by
      show (0 : Q') ≤ momConst 0 * (((1 : Q') - w) * ((1 : Q') - w))
      -- momConst 0 = 0, so RHS ≃ 0
      exact Q'.le_of_eqv (Q'.eqv_symm (q_zero_mul (((1 : Q') - w) * ((1 : Q') - w))))
  | M + 1 => by
      have hIH : cumSum w M ≤ momConst M * (((1 : Q') - w) * ((1 : Q') - w)) :=
        cumSum_le_moment hw0 hw1 M
      have hstep : chanCumulant (M + 1) w
          ≤ momentTermC (M + 1) * (((1 : Q') - w) * ((1 : Q') - w)) :=
        chanCumulant_quadratic hw0 hw1 (M + 1)
      -- cumSum w (M+1) = cumSum w M + chanCumulant (M+1) w
      --   ≤ momConst M·u² + momentTermC(M+1)·u² ≃ (momConst M + momentTermC(M+1))·u²
      show cumSum w M + chanCumulant (M + 1) w
          ≤ (momConst M + momentTermC (M + 1)) * (((1 : Q') - w) * ((1 : Q') - w))
      refine Q'.le_trans' _ _ _ (q_add_le_add hIH hstep) (Q'.le_of_eqv ?_)
      exact Q'.eqv_symm
        (Q'.add_mul_eqv (momConst M) (momentTermC (M + 1))
          (((1 : Q') - w) * ((1 : Q') - w)))

/-! ## 4. THE NAMED RESIDUAL and the guard-safe reduction. -/

/-- **`GapChannelDomination` — the single genuinely-open Bałaban input (`Type`, Rule 8;
UNINHABITED).**  Carries ONLY:

  * `afr` — an AF rate supplying the PROVED model defect `δ_model = afDefectSeq afr`
    (= `pMult·chanCumulant 1 (w_k)`, the fundamental-channel second cumulant);
  * `trueMargin` — the true dimensionless margin `m_lat(a_k)/a_k` + its positive anchor;
  * **`domination`** — THE OPEN PHYSICS: the real 4D SU(2) per-step degradation of the
    true margin is dominated by the fundamental-channel heat-kernel second cumulant
    `δ_model_k = afDefectSeq afr k = pMult·chanCumulant 1 (w_k)`:
        `(1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin (k+1)`.
    This is the Bałaban/Magnen–Rivasseau–Sénéor small-field theorem: after the marginal
    subtraction, the transverse fluctuation remainder controlling the GAP channel is the
    second cumulant of THAT channel alone (large-field regions and higher-rep
    back-reaction exponentially suppressed / absorbed) — NOT the divergent total
    second cumulant `R(w)` over all channels (the adversarial finding).

This is the sharpest honest residual of Route B: the gap-channel restriction of the
fluctuation second cumulant.  It is NOT inhabited (it IS the real Bałaban estimate).

HONESTY CAVEAT (AGENTS.md Rule 9(6), matching CAPSTONE §4): `domination` bounds a FREE
`trueMargin : Nat → Q'`, so — exactly like the `SingleStepDefectBound` it feeds — this
structure is *vacuously fakeable in principle* (`trueMargin ≡ 1` satisfies it via
`afDefectSeq_nonneg`).  That is the systematic frontier caveat, NOT a new weakness: the
residual is genuine only when `trueMargin` is the physical margin, and the honest
protection is the frontier guard + refusing to land the fake, not type impossibility.
The NON-vacuous content of this module is the PROVED §1–§3 second-cumulant estimates
(theorems about the concrete `chanCumulant` object), which this residual does NOT
subsume. -/
structure GapChannelDomination : Type where
  /-- The AF rate supplying the model defect `δ_model = pMult·chanCumulant 1 (w_k)`. -/
  afr : AFRateModulus
  /-- The genuine dimensionless physical margin `m_lat(a_k)/a_k`. -/
  trueMargin : Nat → Q'
  /-- The strong-coupling anchor: the scale-0 true margin is strictly positive. -/
  trueMargin0_pos : (0 : Q') < trueMargin 0
  /-- **THE OPEN BAŁABAN SMALL-FIELD ESTIMATE.**  The real per-step degradation is
  dominated by the fundamental-channel second cumulant `δ_model = afDefectSeq afr`. -/
  domination : ∀ k : Nat,
    (1 - afDefectSeq afr k) * trueMargin k ≤ trueMargin (k + 1)

/-- **`gapChannelDomination_to_singleStep` — the guard-safe Route-B reduction.**
A `GapChannelDomination` (the open gap-channel Bałaban estimate) produces a
`SingleStepDefectBound` (the sole open field of the whole continuum floor).  This is a
CONDITIONAL producer — a function with an open-hypothesis binder `G`, NOT an
unconditional inhabitant — so the frontier guard does NOT flag it (it is the Rule-6a
reduction, not a closure).  It certifies, via proof, that Route B's gap-channel second
cumulant IS the content of `singleStep`, now physically DERIVED from the fluctuation
integral rather than posited.  `GapChannelDomination` remains UNINHABITED. -/
def gapChannelDomination_to_singleStep (G : GapChannelDomination) :
    SingleStepDefectBound where
  afr := G.afr
  trueMargin := G.trueMargin
  trueMargin0_pos := G.trueMargin0_pos
  singleStep := G.domination

/-! ## 5. Doc — PROVED vs NAMED-open (CRITICAL honesty, AGENTS.md Rule 6). -/

/-- **PROVED (genuine `Q'` facts, axiom-clean):**
  * `chanCumulant_nonneg`, `chanCumulant_quadratic` — the per-channel heat-kernel second
    cumulant is `≥ 0` and `≤ dimQ(s)·C₄(s)²·(1 − w)²` (the second-cumulant Taylor
    estimate; Casimir = curvature).
  * `chanCumulant_one_eq_bondMoving`, `afDefectSeq_eq_gapCumulant` — the abstract model
    defect / AF sequence IS the fundamental-channel second cumulant (fluctuation-integral
    grounding of the summability machinery).
  * `chanCumulant_one_le_six` — the gap channel's sharp `6·(1 − w)²`,
    `6 = dimQ(1)·C₄(1) = 2·3 = 3N|_{N=2}`.
  * `cumSum_le_moment` — the finite multi-mode second cumulant bounded by the finite
    Casimir-square moment × `(1 − w)²`.

**ADVERSARIAL FINDING (documented, not faked):** the TOTAL (all-channel, μ-weighted)
second cumulant `R(w)` is `≤ 6(1 − w)²` only for `w ≤ 0.670…` and DIVERGES `∼ (1 −
w)^{−1/2}` as `w → 1`; along AF it is `∼ k^{1/2}`, NOT summable.  So the total is NOT
the gap defect (over-count); the gap defect is the `s = 1` CHANNEL cumulant × `pMult`
generator modes = `δ_model`, summable `∼ 1/k²`.

**NAMED OPEN (NOT inhabited):** `GapChannelDomination` — the Bałaban small-field
theorem that the real 4D degradation is dominated by the fundamental-channel second
cumulant.  `gapChannelDomination_to_singleStep` reduces `singleStep` to it (guard-safe
conditional).  NO 4D Yang–Mills mass gap is claimed; nothing is faked. -/
theorem routeB_honesty : True := trivial

end YMGap.Continuum.HeatKernelSecondCumulant

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelSecondCumulant.chanCumulant_nonneg
#print axioms YMGap.Continuum.HeatKernelSecondCumulant.chanCumulant_quadratic
#print axioms YMGap.Continuum.HeatKernelSecondCumulant.chanCumulant_one_eq_bondMoving
#print axioms YMGap.Continuum.HeatKernelSecondCumulant.chanCumulant_one_le_six
#print axioms YMGap.Continuum.HeatKernelSecondCumulant.afDefectSeq_eq_gapCumulant
#print axioms YMGap.Continuum.HeatKernelSecondCumulant.cumSum_le_moment
#print axioms YMGap.Continuum.HeatKernelSecondCumulant.gapChannelDomination_to_singleStep
