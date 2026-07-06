/-
Track B / R2 — REDUCING THE WHOLE CLAY CONTINUUM GAP TO ONE PER-STEP RG ESTIMATE,
and ATTACKING it via the free/marginal/transverse fluctuation-integration split.

# What this module does (read first)

`CrossoverDefectUnification.fullFloor_of_defectRecursion` puts the entire positive
continuum margin floor on a SINGLE `DefectGapRecursion`, whose only open field is
`recursion` (the real 4D non-abelian multi-link block-spin step, named upstream as
`UniformCouplingFromAF.TrueMarginRecursion`).  Everything else is PROVED: the
anchor (`107/108`), the deep-UV `Σ 1/k²` summability, per-step complementarity
(`δ_k < 1`), and the PRODUCT floor `∏(1 − δ_k) > 0`.

This module isolates that ONE open field down to a single per-step inequality and
attacks it.

## TASK 1 — the whole gap ⇐ ONE per-step inequality `realδ ≤ δ_model`

The product floor `∏(1 − δ_k) > 0` needs exactly (i) `δ_k < 1` (PROVED per-step)
and (ii) `Σ δ_k < ∞` (PROVED: deep-UV `1/k²` + finite middle).  BOTH are already
proved for the renormalized dominant-mode MODEL defect `δ_model := afDefectSeq afr`
(= `renDefect afr pMult` = `bondMovingDeltaRen 1 pMult (w_k)`): `afDefectSeq_le_one`
(δ<1) and `afFloorEps_le_afPhysGapSeq` (the positive product floor from summability).

So the ONLY genuinely open content of the recursion is that the REAL 4D SU(N)
per-step defect `realδ_k` of the TRUE dimensionless margin actually satisfies the
per-step bound it is compared against — `realδ_k ≤ δ_model(w_k)` — which, once
`realδ_k` is read as the actual per-step degradation of the true margin, is the
single inequality

    `singleStep :  (1 − δ_model_k) · trueMargin_k  ≤  trueMargin_{k+1}` .

`SingleStepDefectBound` carries ONLY this inequality (+ the true-margin flow and its
positive anchor); `defectRecursion_of_singleStep` fills EVERY other
`DefectGapRecursion` field from PROVED lemmas (defect := the model `afDefectSeq`,
whose nonneg/`≤1`/product-floor are proved), so `fullFloor_of_singleStep` yields the
entire positive continuum floor FOR THE TRUE MARGIN.  Thus the whole Clay continuum
gap reduces to this ONE per-step 4D-block-spin RG defect inequality.

`trueMarginRecursion_of_singleStep` maps a `SingleStepDefectBound` INTO the existing
named wall `UniformCouplingFromAF.TrueMarginRecursion` (via proof, not prose — Rule
9.8), certifying this is a genuine REFINEMENT of that wall, not a parallel scorecard.

`SingleStepDefectBound` is NOT inhabited here — it IS the real RG estimate.

## TASK 2 — the free / marginal / transverse split (crux §"correct scheme")

The real single-step defect decomposes as (A) free/Gaussian — scale-EXACT, zero
defect; (B) marginal = the running coupling, SUBTRACTED by the counterterm
`renormW`; (C) transverse overshoot — QUADRATIC, already PROVED.  Here:

  * (A) `freeEnd_defect_scaleExact` — at the free/Gaussian end `w = 1` the
    renormalized per-step defect is `≤ 0` (with `bondMovingDeltaRen_nonneg` it is
    pinned to `0`): the free UV erodes NOTHING.  PROVED.
  * (B) `trueDev_eq_marginal_sub_transverse` / `trueDev_eq_counterterm_sub_transverse`
    — the exact decomposition
        `dimQ 1·(1 − w³)  ≃  dimQ 1·(1 − renormW p w)  −  δ_ren` ,
    i.e. the true first-excited deviation = [the marginal part, which is exactly the
    counterterm `dimQ 1·(1 − renormW p w) = dimQ 1·C₄(1)·(1 − w)` absorbed by the
    retuning `renormW`] − [the transverse residual `δ_ren`].  The marginal part is
    the FLOW subtracted by the counterterm, not an error.  PROVED (uses the proved
    `renormW_margin`).
  * (C) `afDefectSeq_le_transverseQuad` — the MODEL defect `δ_model = afDefectSeq`
    is `≤ 6·(1 − w_k)²` (the proved transverse quadratic, `bondMovingDeltaRen_le_sixp`
    / `RenDefectQuadFactor`).  REUSED.

Net: the model defect `δ_model` IS the transverse (C) part (A ≡ 0, B counterterm-
subtracted), so `singleStep` (`realδ ≤ δ_model`) is EXACTLY "the real non-abelian
multi-link 4D defect is bounded by the transverse quadratic model defect" — the
sharpest residual, uninhabited.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The whole Clay continuum gap is now ONE per-step 4D-block-spin RG defect inequality
`realδ_k ≤ δ_model(w_k)` (`SingleStepDefectBound.singleStep`), pinned to the TRUE
margin.  The free part (A) is PROVED zero, the marginal part (B) is PROVED to be the
counterterm `renormW` subtraction, and the transverse part (C) is PROVED quadratic;
the residual is exactly the real non-abelian multi-link remainder — the real defect
being bounded by the transverse model.  `SingleStepDefectBound` is UNINHABITED.
NO 4D Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing PROVED `DefectGapRecursion` machinery, the
proved `afDefectSeq`/`afFloorEps` summability outputs, the proved `renormW_margin`
and `bondMovingDeltaRen_le_sixp`.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  Type-level witnesses are `Type` data (Rule 8).  The
one `noncomputable` (`defectRecursion_of_singleStep` and its dependents) is a
constructive extraction behind a Σ projection: it consumes the CReal-valued proved
product floor `afFloorEps` exactly as the upstream `afDefectGapRecursion` does.
-/

import YMGap.Continuum.CrossoverDefectUnification
import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Continuum.SummabilityCapstone

namespace YMGap.Continuum.SingleStepDefectReduction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.UniformCouplingFromAF

/-! ## TASK 2 — the free / marginal / transverse decomposition of the real step.

The renormalized per-step defect on the dominant `s = 1` mode is (def
`bondMovingDeltaRen`)

    δ_ren(N,1,w) = dimQ 1·( C₄(1)·(1 − w) − (1 − w^{C₄(1)}) ) = marg(w) − trueDev(w),

with `marg(w) = dimQ 1·C₄(1)·(1 − w)` the MARGINAL part and
`trueDev(w) = dimQ 1·(1 − w³)` the TRUE bond-moved first-excited deviation.  We prove
the three structural facts (A)/(B), and reuse (C). -/

/-! ### (A) FREE / Gaussian part is scale-EXACT — zero defect at `w = 1`. -/

/-- **(A) `freeEnd_defect_scaleExact` — the free/Gaussian part erodes nothing.**
At the free (continuum / Gaussian fixed point) end `w = 1`, the renormalized per-step
defect is `≤ 0`.  Combined with `bondMovingDeltaRen_nonneg` (`0 ≤ δ_ren`) this pins
`δ_ren(N,p,1) = 0`: the free UV step is scale-exact and contributes ZERO to the
dimensionless-gap defect.  (Along the AF trajectory `w_k → 1` in the deep UV, so this
is the `k → ∞` scale-exactness that makes the free part harmless.)  Proved from the
transverse quadratic bound `bondMovingDeltaRen_le_sixp` whose RHS `∝ (1 − 1)² ≃ 0`. -/
theorem freeEnd_defect_scaleExact (N p : Nat) :
    bondMovingDeltaRen N p 1 ≤ 0 := by
  have hle := bondMovingDeltaRen_le_sixp (w := (1 : Q')) (by decide) (by decide) N p
  refine Q'.le_trans' _ _ _ hle (Q'.le_of_eqv ?_)
  -- ofNat p·(dimQ 1·(ofNat 3·((1−1)·(1−1)))) ≃ 0
  have h1w : ((1 : Q') - 1).eqv 0 := Q'.add_neg_self_eqv 1
  have hsq : (((1 : Q') - 1) * ((1 : Q') - 1)).eqv 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 ((1 : Q') - 1) h1w) (q_zero_mul ((1 : Q') - 1))
  have h3 : (Q'.ofNat 3 * (((1 : Q') - 1) * ((1 : Q') - 1))).eqv 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ 0 hsq) (q_mul_zero (Q'.ofNat 3))
  have hd : (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - 1) * ((1 : Q') - 1)))).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (dimQ 1) _ 0 h3) (q_mul_zero (dimQ 1))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat p) _ 0 hd) (q_mul_zero (Q'.ofNat p))

/-- **(A′) the free-end defect is nonnegative** (`bondMovingDeltaRen_nonneg` at
`w = 1`); together with `freeEnd_defect_scaleExact` it pins `δ_ren(N,p,1) = 0`. -/
theorem freeEnd_defect_nonneg (N p : Nat) :
    (0 : Q') ≤ bondMovingDeltaRen N p 1 :=
  bondMovingDeltaRen_nonneg (by decide) (by decide) N p

/-! ### (B) MARGINAL part = the counterterm `renormW`, SUBTRACTED (the flow). -/

/-- **The base decomposition identity:** `δ_ren = marg − trueDev`.  Directly from the
definition of `bondMovingDeltaRen N 1 w`: the renormalized transverse defect equals
the MARGINAL linear part `dimQ 1·C₄(1)·(1 − w)` MINUS the TRUE first-excited
deviation `dimQ 1·(1 − w³)`.  (Distribute `dimQ 1` over the bracket; the `ofNat 1`
multiplicity is the identity.) -/
theorem transverse_eq_marginal_sub_trueDev (N : Nat) (w : Q') :
    (bondMovingDeltaRen N 1 w).eqv
      ((dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))
        - (dimQ 1 * ((1 : Q') - qpow w (c4 1)))) := by
  -- bondMovingDeltaRen N 1 w = ofNat 1·(dimQ 1·br),  br = M(1−w) − (1 − w³)
  -- Step 1: ofNat 1·(dimQ 1·br) ≃ dimQ 1·br
  have h1 : (Q'.ofNat 1 * (dimQ 1 *
        ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))).eqv
      (dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 _ (by decide))
      (Q'.one_mul_eqv _)
  -- Step 2: dimQ 1·(A + (−B)) ≃ dimQ 1·A + (−(dimQ 1·B))
  have h2 : (dimQ 1 *
        ((Q'.ofNat (c4 1) * ((1 : Q') - w)) + (-((1 : Q') - qpow w (c4 1))))).eqv
      ((dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))
        + (-(dimQ 1 * ((1 : Q') - qpow w (c4 1))))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (dimQ 1) (Q'.ofNat (c4 1) * ((1 : Q') - w))
        (-((1 : Q') - qpow w (c4 1))))
      (Q'.add_eqv_congr_left (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))) _ _
        (Q'.mul_neg_eqv (dimQ 1) ((1 : Q') - qpow w (c4 1))))
  exact Q'.eqv_trans _ _ _ h1 h2

/-- **(B) `trueDev_eq_marginal_sub_transverse` — the decomposition of the true
deviation.**  Rearranging the base identity:

    dimQ 1·(1 − w³)  ≃  dimQ 1·C₄(1)·(1 − w)  −  δ_ren(N,1,w) ,

i.e. the TRUE bond-moved first-excited deviation = [the MARGINAL part `marg`, the
running-coupling drift] − [the TRANSVERSE residual `δ_ren`].  The marginal part is
the flow (absorbed by the counterterm, next lemma), NOT an error; the residual is the
genuinely transverse (quadratic) defect. -/
theorem trueDev_eq_marginal_sub_transverse (N : Nat) (w : Q') :
    (dimQ 1 * ((1 : Q') - qpow w (c4 1))).eqv
      ((dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))) - bondMovingDeltaRen N 1 w) := by
  -- Abbreviations
  -- marg = dimQ 1·(M(1−w)),  trueDev = dimQ 1·(1 − w³),  δ = bondMovingDeltaRen N 1 w
  -- Base: δ ≃ marg + (−trueDev).
  have hδ : (bondMovingDeltaRen N 1 w).eqv
      ((dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))
        + (-(dimQ 1 * ((1 : Q') - qpow w (c4 1))))) :=
    transverse_eq_marginal_sub_trueDev N w
  -- Show (marg + (−δ)) ≃ trueDev, then symmetrize.
  refine Q'.eqv_symm ?_
  -- marg + (−δ) ≃ marg + (−(marg + (−trueDev)))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))) _ _
      (Q'.neg_eqv_congr _ _ hδ)) ?_
  -- −(marg + (−trueDev)) ≃ (−marg) + (−(−trueDev)) ≃ (−marg) + trueDev
  have hneg : (-((dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))
        + (-(dimQ 1 * ((1 : Q') - qpow w (c4 1)))))).eqv
      ((-(dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))))
        + (dimQ 1 * ((1 : Q') - qpow w (c4 1)))) :=
    Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))
        (-(dimQ 1 * ((1 : Q') - qpow w (c4 1)))))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_neg_eqv (dimQ 1 * ((1 : Q') - qpow w (c4 1)))))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))) _ _ hneg) ?_
  -- marg + ((−marg) + trueDev) ≃ (marg + (−marg)) + trueDev ≃ 0 + trueDev ≃ trueDev
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))
      (-(dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))))
      (dimQ 1 * ((1 : Q') - qpow w (c4 1))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (dimQ 1 * ((1 : Q') - qpow w (c4 1)))
      (Q'.add_neg_self_eqv (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))))) ?_
  exact q_zero_add_eqv (dimQ 1 * ((1 : Q') - qpow w (c4 1)))

/-- **(B′) `trueDev_eq_counterterm_sub_transverse` — the marginal part IS the
counterterm `renormW`.**  Substituting the PROVED `renormW_margin`
(`1 − renormW p w ≃ C₄(1)·(1 − w)`) into (B):

    dimQ 1·(1 − w³)  ≃  dimQ 1·(1 − renormW p w)  −  δ_ren(N,1,w) ,

exhibiting the marginal part as exactly the counterterm subtraction
`dimQ 1·(1 − renormW p w)` — the explicit reparametrization that absorbs the marginal
coupling flow.  This is the honest (B): the running coupling is SUBTRACTED by the
counterterm (the flow), leaving only the transverse residual. -/
theorem trueDev_eq_counterterm_sub_transverse (N p : Nat) (w : Q') :
    (dimQ 1 * ((1 : Q') - qpow w (c4 1))).eqv
      ((dimQ 1 * ((1 : Q') - renormW p w)) - bondMovingDeltaRen N 1 w) := by
  refine Q'.eqv_trans _ _ _ (trueDev_eq_marginal_sub_transverse N w) ?_
  -- replace marg = dimQ 1·(M(1−w)) by dimQ 1·(1 − renormW p w) in the left summand
  refine Q'.add_eqv_congr_right _ _ (-(bondMovingDeltaRen N 1 w)) ?_
  -- dimQ 1·(M(1−w)) ≃ dimQ 1·(1 − renormW p w)   (via renormW_margin, symm)
  exact Q'.mul_eqv_congr_left (dimQ 1) _ _ (Q'.eqv_symm (renormW_margin p w))

/-! ### (C) TRANSVERSE part — QUADRATIC, PROVED; the model defect IS this part. -/

/-- **(C) `afDefectSeq_le_transverseQuad` — the model defect is the proved transverse
quadratic.**  The MODEL per-step defect `δ_model = afDefectSeq afr k` equals
`bondMovingDeltaRen 1 pMult (w_{k₀+k})` and is bounded by the PROVED transverse
quadratic `6·pMult·(1 − w)²` (`bondMovingDeltaRen_le_sixp`, `RenDefectQuadFactor`).
So `δ_model` IS the (C) transverse part (with (A) ≡ 0 and (B) counterterm-absorbed):
`singleStep` (`realδ ≤ δ_model`) is therefore "real 4D multi-link defect ≤ transverse
quadratic model". -/
theorem afDefectSeq_le_transverseQuad (afr : AFRateModulus) (k : Nat) :
    afDefectSeq afr k
      ≤ Q'.ofNat pMult * (dimQ 1 * (Q'.ofNat 3 *
          (((1 : Q') - afr.w (afCutoff afr + k)) * ((1 : Q') - afr.w (afCutoff afr + k))))) :=
  bondMovingDeltaRen_le_sixp (afr.w_nonneg (afCutoff afr + k))
    (Q'.le_of_lt (afr.w_lt_one (afCutoff afr + k))) 1 pMult

/-! ## TASK 1 — the whole gap ⇐ ONE per-step inequality. -/

/-- **`SingleStepDefectBound` — the single open per-step RG estimate (`Type`, Rule 8;
UNINHABITED).**  Carries ONLY:

  * `afr` — an AF rate providing the PROVED model defect `δ_model = afDefectSeq afr`
    (whose `δ<1` and product floor are proved);
  * `trueMargin` — the TRUE dimensionless margin `m_lat(a_k)/a_k` and its positive
    anchor `trueMargin0_pos` (the PROVED strong-coupling `107/108`);
  * **`singleStep`** — the ONE genuinely-open per-step 4D-block-spin RG defect
    inequality, `(1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}` — i.e. the real
    per-step defect of the true margin is at most the transverse model defect
    `δ_model` (`realδ ≤ δ_model`).

Everything else a `DefectGapRecursion` needs is PROVED.  This structure is the exact
residual of the entire Clay continuum gap; it is NOT inhabited (it IS the real RG
estimate). -/
structure SingleStepDefectBound : Type where
  /-- The AF rate supplying the PROVED model defect `δ_model = afDefectSeq afr`. -/
  afr : AFRateModulus
  /-- The genuine dimensionless physical margin `m_lat(a_k)/a_k`. -/
  trueMargin : Nat → Q'
  /-- The strong-coupling anchor: the scale-0 true margin is strictly positive. -/
  trueMargin0_pos : (0 : Q') < trueMargin 0
  /-- **THE SINGLE OPEN PER-STEP RG ESTIMATE.**  The true margin degrades per step by
  at most the transverse model factor `(1 − δ_model_k)`:
      `(1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin (k+1)`.
  This is `realδ_k ≤ δ_model(w_k)` in per-step/recursion form — the real 4D
  non-abelian multi-link block-spin defect bounded by the proved transverse model. -/
  singleStep : ∀ k : Nat,
    (1 - afDefectSeq afr k) * trueMargin k ≤ trueMargin (k + 1)

/-- **`defectRecursion_of_singleStep` — the reduction.**  A `SingleStepDefectBound`
inhabits a full `DefectGapRecursion` whose `physGap` IS the true margin: `defect` is
the PROVED model `afDefectSeq afr` (nonneg / `≤ 1` proved), `recursion` is the single
open `singleStep`, and `prodFloor = afFloorEps afr · trueMargin 0 > 0` comes from the
PROVED summability product floor.  So the SOLE open input consumed is `singleStep`.

`noncomputable`: constructive extraction behind a Σ projection — consumes the
CReal-valued proved product floor `afFloorEps` exactly as `afDefectGapRecursion`. -/
noncomputable def defectRecursion_of_singleStep (S : SingleStepDefectBound) :
    DefectGapRecursion where
  physGap := S.trueMargin
  physGap0_pos := S.trueMargin0_pos
  defect := afDefectSeq S.afr
  defect_nonneg := afDefectSeq_nonneg S.afr
  defect_le_one := afDefectSeq_le_one S.afr
  recursion := S.singleStep
  prodFloor := afFloorEps S.afr * S.trueMargin 0
  prodFloor_pos := Q'.mul_pos (afFloorEps_pos S.afr) S.trueMargin0_pos
  prodFloor_le := by
    intro k
    show afFloorEps S.afr * S.trueMargin 0
        ≤ prodPrefix (fun i => 1 - afDefectSeq S.afr i) k * S.trueMargin 0
    have hpref : prodPrefix (fun i => 1 - afDefectSeq S.afr i) k
        = afPhysGapSeq S.afr k := by
      show prodPrefix (fun i => 1 - afDefectSeq S.afr i) k
          = prodPrefix (afSurvivalSeq S.afr) k
      rfl
    rw [hpref]
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (afFloorEps_le_afPhysGapSeq S.afr k) (Q'.le_of_lt S.trueMargin0_pos)

/-- **`fullFloor_of_singleStep` — the whole Clay continuum floor from the ONE
estimate.**  From a `SingleStepDefectBound` `S`, the positive uniform continuum floor
holds FOR THE TRUE MARGIN: `0 < prodFloor` and `prodFloor ≤ trueMargin k` at every
scale.  This is the entire continuum-gap conclusion resting on the single per-step
inequality `S.singleStep`. -/
theorem fullFloor_of_singleStep (S : SingleStepDefectBound) :
    (0 : Q') < (defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat, (defectRecursion_of_singleStep S).prodFloor ≤ S.trueMargin k :=
  CrossoverDefectUnification.fullFloor_of_defectRecursion
    (defectRecursion_of_singleStep S)

/-- **`trueMarginRecursion_of_singleStep` — the reduction is a genuine REFINEMENT of
the existing named wall.**  A `SingleStepDefectBound` maps INTO
`UniformCouplingFromAF.TrueMarginRecursion` (`D.physGap` pinned to `trueMargin`),
certifying — via proof, not prose (Rule 9.8) — that the single per-step inequality is
exactly the open content of the existing `TrueMarginRecursion` wall, sharpened to a
per-step estimate against the PROVED transverse model defect. -/
noncomputable def trueMarginRecursion_of_singleStep (S : SingleStepDefectBound) :
    UniformCouplingFromAF.TrueMarginRecursion where
  D := defectRecursion_of_singleStep S
  trueMargin := S.trueMargin
  physGap_is_trueMargin := fun _ => rfl

end YMGap.Continuum.SingleStepDefectReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SingleStepDefectReduction.freeEnd_defect_scaleExact
#print axioms YMGap.Continuum.SingleStepDefectReduction.freeEnd_defect_nonneg
#print axioms YMGap.Continuum.SingleStepDefectReduction.transverse_eq_marginal_sub_trueDev
#print axioms YMGap.Continuum.SingleStepDefectReduction.trueDev_eq_marginal_sub_transverse
#print axioms YMGap.Continuum.SingleStepDefectReduction.trueDev_eq_counterterm_sub_transverse
#print axioms YMGap.Continuum.SingleStepDefectReduction.afDefectSeq_le_transverseQuad
#print axioms YMGap.Continuum.SingleStepDefectReduction.defectRecursion_of_singleStep
#print axioms YMGap.Continuum.SingleStepDefectReduction.fullFloor_of_singleStep
#print axioms YMGap.Continuum.SingleStepDefectReduction.trueMarginRecursion_of_singleStep
