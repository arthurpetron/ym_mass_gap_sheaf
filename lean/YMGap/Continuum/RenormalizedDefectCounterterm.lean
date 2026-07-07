/-
Track B / R2 — ROUTE H (RENORMALIZATION / COUNTERTERM): the EXACT counterterm
decomposition of the raw fused-character defect, and the UNIFORM (full-range, incl.
`w → 1`) bound for the RENORMALIZED (counterterm-subtracted) defect — the analytic
half of `RouteADefectCharacter.FullRangeFusedDefect`, the sole residual of the whole
continuum floor.

# The problem (read first)

The RAW fused-character first-excited/vacuum ratio is `coeffW w 1 = dimQ 1·w³ = 2·w³`
(RouteA/RouteF: the block-spin margin degradation `Δ − Δ' = coeffW w 1`).  It is
bounded by the transverse quadratic `6·(1 − w)²` ONLY for `w ≤ 0.6778…`; as `w → 1`
(the deep-UV/continuum end the AF trajectory drives toward) the raw ratio `→ 2` while
`6·(1 − w)² → 0`, so the RAW bound FAILS (`RouteADefectCharacter.raw_ratio_exceeds_at_weak`
proves `¬ (coeffW (9/10) 1 ≤ 6·(1 − 9/10)²)`).

RENORMALIZATION fixes this.  Under one block-spin RG step the coupling is renormalized
`w ↦ w_ren` — the marginal/relevant part of the flow is absorbed by the counterterm
(the heat-kernel-time retuning `renormW`).  The genuine per-step defect of the
DIMENSIONLESS margin is NOT the raw excited weight `2w³` but the counterterm-subtracted
TRANSVERSE residual.  This module makes that precise and proves the bound holds
uniformly for the renormalized defect.

# The EXACT counterterm decomposition (proved here)

With `pMult`-inert counterterm `CT(w) := dimQ 1 · renormW p w` (`= 6w − 4`, the marginal
renormalization = `dimQ 1 ·` the retuned weight), the RAW ratio splits EXACTLY:

    coeffW w 1        =  bondMovingDeltaRen N 1 w   +   dimQ 1 · renormW p w
    (raw = 2w³)          (renormalized δ_ren)           (counterterm CT = 6w − 4)

`coeffW_eqv_renDefect_add_counterterm` — an EXACT `Q'` identity for ALL `w`.  Hence the
RENORMALIZED defect

    renormalizedDefect N p w  :=  coeffW w 1  −  CT(w)   ≃   bondMovingDeltaRen N 1 w
                              =  2w³ − (6w − 4)  =  2·(1 − w)²·(2 + w)

is the transverse residual `δ_ren`, which vanishes to SECOND order at the free
fixed point `w = 1` (the linear/marginal part is exactly what CT absorbs).

# The UNIFORM bound (proved here — the analytic core, holds at `w → 1`)

`renormalizedDefect_le_transverseQuad` / `renormalizedDefect_le_six`:

    renormalizedDefect N p w  ≤  6·(1 − w)²        for ALL `0 ≤ w ≤ 1`,

with NO `w ≤ 1/2` restriction (via `bondMovingDeltaRen_le_sixp`, since
`2·(1 − w)²·(2 + w) ≤ 6·(1 − w)² ⇔ 2 + w ≤ 3 ⇔ w ≤ 1`).  The numeric contrast is
machine-checked at the RouteA witness `w = 9/10` (`renorm_fixes_weak`): the RENORMALIZED
defect satisfies `≤ 6·(1 − w)²` (`= 29/500 ≤ 3/50`) exactly where the RAW ratio
`= 1458/1000` violates it.  So renormalization CLOSES the analytic (full-range envelope)
half of `FullRangeFusedDefect`.

# What of `FullRangeFusedDefect` reduces — and the LOUD honesty (Rule 9)

The analytic content of `FullRangeFusedDefect` (that SOME per-step leakage obeying the
transverse envelope exists at every scale) is now PROVED for the renormalized defect
`afDefectSeq afr` — but that already holds (`afDefectSeq_le_transverseQuad`).  The
GENUINE, still-open content is the IDENTIFICATION: that the REAL physical per-step
block-spin leakage of the true dimensionless margin actually EQUALS (is `≤`) the
renormalized transverse defect `afDefectSeq afr`, i.e. that the counterterm/retuning is
the physically-implementable one.  `fullRangeFusedDefect_of_identification` is a
CONDITIONAL producer discharging `FullRangeFusedDefect` from exactly that open
identification hypothesis (`physLeak k ≤ afDefectSeq afr k`), via the proved uniform
bound — NOTHING is unconditionally inhabited.

LOUD honesty (AGENTS.md Rule 9): `FullRangeFusedDefect` carries `realLeak` as a FREE
field, so it is TRIVIALLY (vacuously) inhabitable by `realLeak := afDefectSeq afr` — that
would be the Rule-9(1) vacuous closure and is REFUSED here.  The genuine wall is the
identification `physLeak = δ_ren` pinned to the PHYSICAL true margin, which is exactly
`SingleStepDefectReduction.SingleStepDefectBound.singleStep` /
`UniformCouplingFromAF.TrueMarginRecursion` — NOT inhabited.  NO 4D Yang–Mills mass gap
is claimed; the counterterm subtraction is the PHYSICAL marginal renormalization (the
EXACT identity `raw = δ_ren + CT` is not a fudge), but the physical identification
`realLeak = δ_ren` remains the open residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing PROVED facts (`bondMovingDeltaRen_le_sixp`,
`renormW`, `afDefectSeq_le_transverseQuad`, `transverseQuad_pMult1_eqv`).  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level `Q'` data.
-/

import YMGap.Continuum.RouteADefectCharacter

namespace YMGap.Continuum.RenormalizedDefectCounterterm

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.RouteADefectCharacter

/-! ## 0. The pure additive cancellation lemma (the heart of the decomposition).

`(M − (1 − x)) + (1 − M) ≃ x` for arbitrary `M, x : Q'` — the `M` and the constant `1`
cancel, leaving `x`.  Instantiated at `M = C₄(1)·(1 − w)` (`= renormTau`) and
`x = w^{C₄(1)}` it collapses the counterterm decomposition to the raw ratio. -/
theorem inner_cancel (M x : Q') :
    ((M - ((1 : Q') - x)) + ((1 : Q') - M)).eqv x := by
  -- e1 : −(1 − x) ≃ (−1) + x
  have e1 : (-((1 : Q') - x)).eqv ((-1 : Q') + x) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-x)) ?_
    exact Q'.add_eqv_congr_left (-1 : Q') _ _ (Q'.neg_neg_eqv x)
  -- e2 : M − (1 − x) ≃ M + ((−1) + x)
  have e2 : (M - ((1 : Q') - x)).eqv (M + ((-1 : Q') + x)) :=
    Q'.add_eqv_congr_left M _ _ e1
  -- e3 : LHS ≃ (M + ((−1) + x)) + (1 − M)
  have e3 : ((M - ((1 : Q') - x)) + ((1 : Q') - M)).eqv
      ((M + ((-1 : Q') + x)) + ((1 : Q') - M)) :=
    Q'.add_eqv_congr_right _ _ _ e2
  -- e4 : reassociate  (A + (1 + (−M))) ≃ ((A + 1) + (−M))   with A = M + ((−1)+x)
  have e4 : ((M + ((-1 : Q') + x)) + ((1 : Q') + (-M))).eqv
      (((M + ((-1 : Q') + x)) + (1 : Q')) + (-M)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (M + ((-1 : Q') + x)) (1 : Q') (-M))
  -- e5a : ((−1) + x) + 1 ≃ x
  have e5a : (((-1 : Q') + x) + (1 : Q')).eqv x := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-1 : Q') x (1 : Q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1 : Q') _ _ (Q'.add_comm_eqv x (1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-1 : Q') (1 : Q') x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ x (by decide : ((-1 : Q') + (1 : Q')).eqv 0)) ?_
    exact q_zero_add_eqv x
  -- e5 : (M + ((−1) + x)) + 1 ≃ M + x
  have e5 : ((M + ((-1 : Q') + x)) + (1 : Q')).eqv (M + x) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv M ((-1 : Q') + x) (1 : Q')) ?_
    exact Q'.add_eqv_congr_left M _ _ e5a
  -- e6 : ((M + ((−1)+x)) + 1) + (−M) ≃ (M + x) + (−M)
  have e6 : (((M + ((-1 : Q') + x)) + (1 : Q')) + (-M)).eqv ((M + x) + (-M)) :=
    Q'.add_eqv_congr_right _ _ (-M) e5
  -- e7 : (M + x) + (−M) ≃ x
  have e7 : ((M + x) + (-M)).eqv x := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-M) (Q'.add_comm_eqv M x)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x M (-M)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left x _ _ (Q'.add_neg_self_eqv M)) ?_
    exact q_add_zero_eqv x
  exact Q'.eqv_trans _ _ _ e3 (Q'.eqv_trans _ _ _ e4 (Q'.eqv_trans _ _ _ e6 e7))

/-! ## 1. The counterterm and the renormalized defect. -/

/-- **The marginal counterterm** `CT(w) = dimQ 1 · renormW p w` (`= 6w − 4`).  This is
`dimQ 1 ·` the retuned heat-kernel weight `renormW` that absorbs the marginal coupling
drift; `p` is inert (`renormTau` ignores `p`).  It is the part SUBTRACTED from the raw
excited weight `coeffW w 1 = 2w³` to leave the transverse residual. -/
def counterterm (p : Nat) (w : Q') : Q' := dimQ 1 * renormW p w

/-- **The renormalized (counterterm-subtracted) defect** `= coeffW w 1 − CT(w)`.  The
truncation degree `N` is carried for interface uniformity (the value does not depend on
it). -/
def renormalizedDefect (_N : Nat) (p : Nat) (w : Q') : Q' :=
  coeffW w 1 - counterterm p w

/-! ## 2. The EXACT counterterm decomposition `raw = δ_ren + CT`. -/

/-- **`coeffW_eqv_renDefect_add_counterterm` — the exact counterterm decomposition.**

    coeffW w 1  ≃  bondMovingDeltaRen N 1 w  +  dimQ 1 · renormW p w
    (raw 2w³)      (renormalized δ_ren)          (counterterm CT = 6w − 4)

An EXACT `Q'` identity for ALL `w`: the RAW fused-character excited/vacuum weight splits
into the renormalized TRANSVERSE defect `δ_ren = bondMovingDeltaRen N 1 w` plus the
MARGINAL counterterm `CT = dimQ 1 · renormW`.  Proved by factoring `dimQ 1` and the pure
additive cancellation `inner_cancel` — the marginal linear part is exactly the
counterterm, NOT an error. -/
theorem coeffW_eqv_renDefect_add_counterterm (N p : Nat) (w : Q') :
    (coeffW w 1).eqv (bondMovingDeltaRen N 1 w + dimQ 1 * renormW p w) := by
  -- coeffW w 1 = dimQ 1 · w^{C₄(1)} ;  renormW p w = 1 − (C₄(1)·(1−w))  (renormTau, defeq)
  show (dimQ 1 * qpow w (c4 1)).eqv
    (Q'.ofNat 1 * (dimQ 1 *
        ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))
      + dimQ 1 * ((1 : Q') - (Q'.ofNat (c4 1) * ((1 : Q') - w))))
  refine Q'.eqv_symm ?_
  -- Step 1: drop the `ofNat 1` multiplicity.
  have s1 : (Q'.ofNat 1 * (dimQ 1 *
        ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))).eqv
      (dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 _ (by decide))
      (Q'.one_mul_eqv _)
  -- Step 2: factor `dimQ 1` out of the sum.
  have s2 : (dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))
        + dimQ 1 * ((1 : Q') - (Q'.ofNat (c4 1) * ((1 : Q') - w)))).eqv
      (dimQ 1 * (((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))
        + ((1 : Q') - (Q'.ofNat (c4 1) * ((1 : Q') - w))))) :=
    Q'.eqv_symm (Q'.mul_add_eqv (dimQ 1)
      ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))
      ((1 : Q') - (Q'.ofNat (c4 1) * ((1 : Q') - w))))
  -- Step 3: inner cancellation → `dimQ 1 · w^{C₄(1)}`.
  have s3 : (dimQ 1 * (((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))
        + ((1 : Q') - (Q'.ofNat (c4 1) * ((1 : Q') - w))))).eqv
      (dimQ 1 * qpow w (c4 1)) :=
    Q'.mul_eqv_congr_left (dimQ 1) _ _
      (inner_cancel (Q'.ofNat (c4 1) * ((1 : Q') - w)) (qpow w (c4 1)))
  -- Assemble.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (dimQ 1 * ((1 : Q') - (Q'.ofNat (c4 1) * ((1 : Q') - w)))) s1)
    ?_
  exact Q'.eqv_trans _ _ _ s2 s3

/-- **`renormalizedDefect_eqv` — the renormalized defect IS the transverse `δ_ren`.**
`renormalizedDefect N p w = coeffW w 1 − CT(w) ≃ bondMovingDeltaRen N 1 w`.  Directly
from the exact decomposition: subtracting the counterterm from the raw ratio recovers the
transverse residual. -/
theorem renormalizedDefect_eqv (N p : Nat) (w : Q') :
    (renormalizedDefect N p w).eqv (bondMovingDeltaRen N 1 w) := by
  show (coeffW w 1 - dimQ 1 * renormW p w).eqv (bondMovingDeltaRen N 1 w)
  -- coeffW − CT ≃ (δ_ren + CT) − CT ≃ δ_ren
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(dimQ 1 * renormW p w))
      (coeffW_eqv_renDefect_add_counterterm N p w)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (bondMovingDeltaRen N 1 w) (dimQ 1 * renormW p w)
      (-(dimQ 1 * renormW p w))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (dimQ 1 * renormW p w))) ?_
  exact q_add_zero_eqv (bondMovingDeltaRen N 1 w)

/-! ## 3. THE UNIFORM (full-range) bound for the renormalized defect. -/

/-- **`renormalizedDefect_le_transverseQuad` — the UNIFORM full-range bound.**  For ALL
`0 ≤ w ≤ 1` (no `w ≤ 1/2` restriction, INCLUDING `w → 1`),

    renormalizedDefect N p w  ≤  ofNat 1 · (dimQ 1 · (ofNat 3 · (1 − w)²))   ( = 6·(1 − w)² ).

Since `renormalizedDefect ≃ bondMovingDeltaRen N 1 w` (`renormalizedDefect_eqv`) and the
latter is `≤ 6·(1 − w)²` on all of `[0,1]` (`bondMovingDeltaRen_le_sixp`).  This is the
analytic content the RAW ratio `2w³` FAILS at `w → 1`. -/
theorem renormalizedDefect_le_transverseQuad {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N p : Nat) :
    renormalizedDefect N p w
      ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (renormalizedDefect_eqv N p w))
    (bondMovingDeltaRen_le_sixp hw0 hw1 N 1)

/-- **`renormalizedDefect_le_six` — the `6·(1 − w)²` form.**  The uniform bound in the
compact `6·(1 − w)²` shape (via `transverseQuad_pMult1_eqv`). -/
theorem renormalizedDefect_le_six {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N p : Nat) :
    renormalizedDefect N p w
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
  Q'.le_trans' _ _ _ (renormalizedDefect_le_transverseQuad hw0 hw1 N p)
    (Q'.le_of_eqv (transverseQuad_pMult1_eqv w))

/-! ## 4. Numeric-in-Lean validation at `w = 9/10` — renormalization FIXES the raw failure. -/

/-- **`renormalizedDefect_value_at_weak` — the exact renormalized value at `w = 9/10`.**
`renormalizedDefect 0 1 (9/10) = 2·(1/10)²·(2 + 9/10) = 29/500`.  (Contrast the RAW ratio
`coeffW (9/10) 1 = 2·(9/10)³ = 1458/1000`.) -/
theorem renormalizedDefect_value_at_weak :
    (renormalizedDefect 0 1 (Q'.mkPos 9 10 (by decide))).eqv
      (Q'.mkPos 29 500 (by decide)) := by decide

/-- **`renormalizedDefect_holds_at_weak` — the renormalized bound HOLDS at `w = 9/10`.**
`renormalizedDefect N 1 (9/10) ≤ 6·(1 − 9/10)² = 6/100` (`29/500 = 58/1000 ≤ 60/1000`),
EXACTLY where the RAW ratio violates it. -/
theorem renormalizedDefect_holds_at_weak (N : Nat) :
    renormalizedDefect N 1 (Q'.mkPos 9 10 (by decide))
      ≤ Q'.ofNat 6 * (((1 : Q') - Q'.mkPos 9 10 (by decide))
          * ((1 : Q') - Q'.mkPos 9 10 (by decide))) :=
  renormalizedDefect_le_six (by decide) (by decide) N 1

/-- **`renorm_fixes_weak` — the decisive numeric contrast (machine-checked).**  At the
weak-coupling witness `w = 9/10`: the RENORMALIZED defect satisfies the transverse
envelope `≤ 6·(1 − w)²`, WHILE the RAW ratio `coeffW w 1` does NOT
(`raw_ratio_exceeds_at_weak`).  The counterterm subtraction genuinely converts the
diverging raw weight into the vanishing transverse residual. -/
theorem renorm_fixes_weak (N : Nat) :
    (renormalizedDefect N 1 (Q'.mkPos 9 10 (by decide))
        ≤ Q'.ofNat 6 * (((1 : Q') - Q'.mkPos 9 10 (by decide))
            * ((1 : Q') - Q'.mkPos 9 10 (by decide))))
      ∧ ¬ (coeffW (Q'.mkPos 9 10 (by decide)) 1
        ≤ Q'.ofNat 6 * (((1 : Q') - Q'.mkPos 9 10 (by decide))
            * ((1 : Q') - Q'.mkPos 9 10 (by decide)))) :=
  ⟨renormalizedDefect_holds_at_weak N, raw_ratio_exceeds_at_weak⟩

/-! ## 5. The guard-safe reduction of `FullRangeFusedDefect` (NOTHING inhabited).

`FullRangeFusedDefect` carries `realLeak : Nat → Q'` as a FREE field.  Its analytic
content — a per-scale leakage obeying the transverse envelope — is discharged by the
RENORMALIZED model defect `afDefectSeq afr` (proved uniform bound above /
`afDefectSeq_le_transverseQuad`).  The GENUINE residual is the physical IDENTIFICATION
that the REAL leakage IS `≤` that renormalized defect (the counterterm-validity /
retuning-implementable content) — carried below as an OPEN hypothesis. -/

/-- **`fullRangeFusedDefect_of_identification` — the CONDITIONAL reduction.**  Given the
open physical IDENTIFICATION `physLeak k ≤ afDefectSeq afr k` (the real per-step
block-spin leakage is bounded by the renormalized transverse model defect — the
counterterm validity), `FullRangeFusedDefect` follows, via the PROVED uniform transverse
bound `afDefectSeq_le_transverseQuad`.

This is a CONDITIONAL producer (open-hypothesis binders `physLeak`, `physLeak_nonneg`,
`physLeak_le_renDefect`, none of which is an argument of `FullRangeFusedDefect afr`), so
it does NOT unconditionally inhabit the bundle — it is the machine-checked reduction
`FullRangeFusedDefect ⇐ identification`, showing the whole analytic residual collapses onto
the single identification `physLeak ≤ afDefectSeq`, which IS
`SingleStepDefectBound.singleStep` pinned to the physical margin.

HONESTY (Rule 9): the identification is NOT discharged here.  Instantiating `physLeak :=
afDefectSeq afr` (with `physLeak_le_renDefect := le_refl`) would inhabit
`FullRangeFusedDefect` UNCONDITIONALLY, but that is the Rule-9(1) VACUOUS closure (the
free `realLeak` is not the pinned physical margin) and is DELIBERATELY NOT written. -/
def fullRangeFusedDefect_of_identification (afr : AFRateModulus)
    (physLeak : Nat → Q')
    (physLeak_nonneg : ∀ k, (0 : Q') ≤ physLeak k)
    (physLeak_le_renDefect : ∀ k, physLeak k ≤ afDefectSeq afr k) :
    FullRangeFusedDefect afr where
  realLeak := physLeak
  realLeak_nonneg := physLeak_nonneg
  fullRange := fun k =>
    Q'.le_trans' _ _ _ (physLeak_le_renDefect k)
      (model_defect_le_transverseQuad afr k)

end YMGap.Continuum.RenormalizedDefectCounterterm

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.inner_cancel
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.coeffW_eqv_renDefect_add_counterterm
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.renormalizedDefect_eqv
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.renormalizedDefect_le_transverseQuad
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.renormalizedDefect_le_six
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.renormalizedDefect_value_at_weak
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.renormalizedDefect_holds_at_weak
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.renorm_fixes_weak
#print axioms YMGap.Continuum.RenormalizedDefectCounterterm.fullRangeFusedDefect_of_identification
