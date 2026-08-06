/-
Track 11.7-fusion / R2r -- a symbolic dyadic envelope for the physical p=2 gap.

The all-cutoff campaign should not evaluate a growing table of rational powers.
This module instead fixes the explicit coupled schedule

    N_k = (k+2)^2,
    u_k = (1/12) * (1/2)^k,
    w_k = 1-u_k,

and proves its elementary properties once.  A `DyadicP2CoeffTailData` contains
only the remaining division-free adjacent coefficient-tail inequality at each
scale.  Everything else needed to build the reviewed `CanonicalBulkControl`
family is derived.

The refined reference gap is controlled without expanding `retEig2`: compare
it with the unrefined retune, use the proved one-sided Lipschitz square bridge,
and charge both retune displacements to `u_k`.  The result is the uniform
pointwise envelope

    refined(k+1)^2 - refined(k) <= 6*u_k.

This is proof about computation: the certificate size is independent of the
cutoff and no large cross-product normalization is performed.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionReferenceGap
import YMGap.Continuum.DerivedCoupledCutoffSchedule
import YMGap.Continuum.LargeFieldSuppression

namespace YMGap.Continuum.P2DyadicFusionGapEnvelope

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CutoffTailRefinedCarrier
open YMGap.Continuum.DerivedCoupledCutoffSchedule
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.FusedNextScaleRetune
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionReferenceGap
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact dyadic cutoff and weight schedule -/

/-- Geometric heat-time margin `u_k = (1/12)*(1/2)^k`. -/
def dyadicMargin (k : Nat) : Q' := q112 * qpow half k

/-- Near-continuum weight `w_k = 1-u_k`. -/
def dyadicWeight (k : Nat) : Q' := (1 : Q') - dyadicMargin k

theorem dyadicMargin_nonneg (k : Nat) : (0 : Q') <= dyadicMargin k :=
  Q'.mul_nonneg _ _ (by decide) (qpow_nonneg half half_nonneg k)

theorem dyadicMargin_le_q112 (k : Nat) : dyadicMargin k <= q112 := by
  have hp : qpow half k <= (1 : Q') :=
    qpow_le_one half_nonneg (by decide) k
  have h := Q'.mul_le_mul_of_nonneg_left _ _ q112 hp
    (by decide : (0 : Q') <= q112)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv q112))

theorem dyadicMargin_le_one (k : Nat) : dyadicMargin k <= (1 : Q') :=
  Q'.le_trans' _ _ _ (dyadicMargin_le_q112 k) (by decide)

theorem dyadicWeight_nonneg (k : Nat) : (0 : Q') <= dyadicWeight k :=
  Q'.sub_nonneg_of_le (dyadicMargin_le_one k)

theorem dyadicWeight_le_one (k : Nat) : dyadicWeight k <= (1 : Q') :=
  BondMovingRetuneFix.oneSub_le_one (dyadicMargin_nonneg k)

theorem one_sub_dyadicWeight_eqv_margin (k : Nat) :
    ((1 : Q') - dyadicWeight k) ≈ dyadicMargin k := by
  unfold dyadicWeight
  exact one_sub_one_sub_eqv (dyadicMargin k)

theorem dyadicWeight_near_continuum (k : Nat) :
    (1 : Q') - dyadicWeight k <= q112 :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (one_sub_dyadicWeight_eqv_margin k))
    (dyadicMargin_le_q112 k)

/-- The margin decreases geometrically. -/
theorem dyadicMargin_succ_le (k : Nat) :
    dyadicMargin (k + 1) <= dyadicMargin k := by
  have hpow : qpow half (k + 1) <= qpow half k := by
    show qpow half k * half <= qpow half k
    have h := Q'.mul_le_mul_of_nonneg_left half (1 : Q')
      (qpow half k) (by decide) (qpow_nonneg half half_nonneg k)
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_one_eqv (qpow half k)))
  exact Q'.mul_le_mul_of_nonneg_left _ _ q112 hpow (by decide)

/-- Add two scalar multiples without normalizing the variable-dependent
cross product. -/
theorem add_scaled_eqv (a b : Nat) (x : Q') :
    Q'.ofNat a * x + Q'.ofNat b * x ≈ Q'.ofNat (a + b) * x := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (RingNormaliser.q_add_mul (Q'.ofNat a) (Q'.ofNat b) x)) ?_
  exact Q'.mul_eqv_congr_right _ _ x (Q'.eqv_symm (Q'.ofNat_add_eqv a b))

/-! ## 2. The honest all-scale coefficient-tail carrier -/

/-- The sole residual needed to instantiate the all-scale dyadic p=2 control
family.  It is division-free and compares adjacent raw coefficients. -/
structure DyadicP2CoeffTailData : Type where
  coeffTailRatio : forall k,
    P2RetunedCoeffTailRatio (Ncut k) (dyadicWeight k)
      (dyadicWeight_nonneg k) (dyadicWeight_le_one k)

/-- Compile the dyadic schedule and the one honest residual into the preferred
raw-coefficient all-scale interface. -/
def DyadicP2CoeffTailData.toCoeffControlFamily
    (D : DyadicP2CoeffTailData) : P2RetunedCoeffControlFamily where
  N := Ncut
  w := dyadicWeight
  hN := fun k => by have := Ncut_pos k; omega
  hw0 := dyadicWeight_nonneg
  hw1 := dyadicWeight_le_one
  hnc := dyadicWeight_near_continuum
  coeffTailRatio := D.coeffTailRatio

/-- The reviewed normalized `CanonicalBulkControl` family on the exact dyadic
schedule. -/
def DyadicP2CoeffTailData.toControlFamily
    (D : DyadicP2CoeffTailData) : P2RetunedControlFamily :=
  D.toCoeffControlFamily.toTailFamily

/-! ## 3. Symbolic reference-gap envelope -/

/-- The unrefined mode-one retune used only as a comparison sequence. -/
def unrefinedModeOneQ (k : Nat) : Q' :=
  retEig 2 (by decide) (dyadicWeight k) 1

theorem unrefinedModeOne_range (k : Nat) :
    ((0 : Q') <= unrefinedModeOneQ k) /\
      (unrefinedModeOneQ k <= (1 : Q')) :=
  ⟨retEig_nonneg (dyadicWeight_nonneg k) 2 (by decide) 1,
    retEig_le_one (dyadicWeight_nonneg k) (dyadicWeight_le_one k)
      2 (by decide) 1⟩

/-- The unrefined retuned mode-one deficit costs at most `3*u_k`.
The proof uses Bernoulli at Casimir `c4 1 = 3` and the exact p=2 retune
identity; it does not evaluate the cube. -/
theorem one_sub_unrefinedModeOne_le_three_margin (k : Nat) :
    (1 : Q') - unrefinedModeOneQ k <=
      Q'.ofNat 3 * dyadicMargin k := by
  let r := renormWFix 2 (by decide) (dyadicWeight k)
  have hr0 : (0 : Q') <= r :=
    renormWFix_nonneg (dyadicWeight_nonneg k) 2 (by decide)
  have hr1 : r <= (1 : Q') :=
    renormWFix_le_one (dyadicWeight_le_one k) 2 (by decide)
  have hbern : (1 : Q') - qpow r (c4 1) <=
      Q'.ofNat (c4 1) * ((1 : Q') - r) :=
    oneSub_qpow_le hr0 hr1 (c4 1)
  have hbase0 : (0 : Q') <= (1 : Q') - r := Q'.sub_nonneg_of_le hr1
  have hbase_le : (1 : Q') - r <= dyadicMargin k := by
    have hscale : (1 : Q') - r <= Q'.ofNat 2 * ((1 : Q') - r) := by
      have h := Q'.mul_le_mul_of_nonneg_right (1 : Q') (Q'.ofNat 2)
        ((1 : Q') - r) (by decide) hbase0
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.one_mul_eqv ((1 : Q') - r))) h
    exact Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (twice_retuned_base_margin (dyadicWeight k))
        (one_sub_dyadicWeight_eqv_margin k)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (c4 1))
    hbase_le (by decide)
  exact Q'.le_trans' _ _ _ hbern
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ (dyadicMargin k)
        (by decide : Q'.ofNat (c4 1) ≈ Q'.ofNat 3))))

/-- The unrefined fine-square-minus-coarse gap is controlled solely by the
coarse heat-time margin. -/
theorem unrefined_squareGap_le_three_margin (k : Nat) :
    unrefinedModeOneQ (k + 1) * unrefinedModeOneQ (k + 1) +
        -(unrefinedModeOneQ k) <= Q'.ofNat 3 * dyadicMargin k := by
  have hf := unrefinedModeOne_range (k + 1)
  have hsq : unrefinedModeOneQ (k + 1) * unrefinedModeOneQ (k + 1) <=
      (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg hf.2 hf.2 (by decide) hf.1
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hadd := Q'.add_le_add_right _ _ (-(unrefinedModeOneQ k)) hsq
  exact Q'.le_trans' _ _ _ hadd
    (one_sub_unrefinedModeOne_le_three_margin k)

/-- The refined retune stays within one dyadic margin of the unrefined mode. -/
theorem refined_unrefined_displacement_le (k : Nat) :
    absQ
      (retEig2 2 (by decide) (refineCoeff 2 (by decide))
          (dyadicWeight k) 1 + -unrefinedModeOneQ k) <= dyadicMargin k := by
  have h := refined_retune_displacement_le_margin
    (dyadicWeight_nonneg k) (dyadicWeight_le_one k)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (absQ_sub_comm_eqv
        (unrefinedModeOneQ k)
        (retEig2 2 (by decide) (refineCoeff 2 (by decide))
          (dyadicWeight k) 1)))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (one_sub_dyadicWeight_eqv_margin k)))

/-- **Dyadic refined-reference envelope.**  The corrected reference square
gap is bounded by `6*u_k` at every scale.  The constant is assembled from
`3*u_k` for the unrefined gap, `2*u_(k+1)` for the fine square transport, and
`u_k` for the coarse transport. -/
theorem refined_squareGap_le_six_margin (k : Nat) :
    retEig2 2 (by decide) (refineCoeff 2 (by decide))
          (dyadicWeight (k + 1)) 1 *
        retEig2 2 (by decide) (refineCoeff 2 (by decide))
          (dyadicWeight (k + 1)) 1 +
      -(retEig2 2 (by decide) (refineCoeff 2 (by decide))
          (dyadicWeight k) 1) <=
        Q'.ofNat 6 * dyadicMargin k := by
  have hf := corrected_carrier_range
    (dyadicWeight_nonneg (k + 1)) (dyadicWeight_le_one (k + 1)) 1
  have href := unrefinedModeOne_range (k + 1)
  have htransport := squareGap_le_referenceSquareGap_add_errors
    hf.1 hf.2 href.1 href.2
      (refined_unrefined_displacement_le (k + 1))
      (refined_unrefined_displacement_le k)
  have herrors :
      Q'.ofNat 2 * dyadicMargin (k + 1) + dyadicMargin k <=
        Q'.ofNat 2 * dyadicMargin k + Q'.ofNat 1 * dyadicMargin k := by
    exact Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
        (dyadicMargin_succ_le k) (by decide))
      (Q'.ge_of_eqv (Q'.one_mul_eqv (dyadicMargin k)))
  have hsum := Q'.add_le_add (unrefined_squareGap_le_three_margin k) herrors
  have hcollapse :
      Q'.ofNat 3 * dyadicMargin k +
          (Q'.ofNat 2 * dyadicMargin k + Q'.ofNat 1 * dyadicMargin k) ≈
        Q'.ofNat 6 * dyadicMargin k := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv
        (Q'.ofNat 3 * dyadicMargin k)
        (Q'.ofNat 2 * dyadicMargin k)
        (Q'.ofNat 1 * dyadicMargin k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (Q'.ofNat 1 * dyadicMargin k)
        (add_scaled_eqv 3 2 (dyadicMargin k))) ?_
    exact add_scaled_eqv 5 1 (dyadicMargin k)
  exact Q'.le_trans' _ _ _ htransport
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcollapse))

/-- The same reference envelope on the normalized all-scale control family
compiled from the honest dyadic coefficient-tail residual. -/
theorem control_refined_squareGap_le_six_margin
    (D : DyadicP2CoeffTailData) (k : Nat) :
    refinedModeOneQ D.toControlFamily (k + 1) *
        refinedModeOneQ D.toControlFamily (k + 1) +
      -(refinedModeOneQ D.toControlFamily k) <=
        Q'.ofNat 6 * dyadicMargin k := by
  simpa only [refinedModeOneQ, DyadicP2CoeffTailData.toControlFamily,
    DyadicP2CoeffTailData.toCoeffControlFamily,
    P2RetunedCoeffControlFamily.toTailFamily] using
      refined_squareGap_le_six_margin k

end YMGap.Continuum.P2DyadicFusionGapEnvelope

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicFusionGapEnvelope.dyadicMargin_succ_le
#print axioms YMGap.Continuum.P2DyadicFusionGapEnvelope.DyadicP2CoeffTailData.toControlFamily
#print axioms YMGap.Continuum.P2DyadicFusionGapEnvelope.one_sub_unrefinedModeOne_le_three_margin
#print axioms YMGap.Continuum.P2DyadicFusionGapEnvelope.refined_squareGap_le_six_margin
#print axioms YMGap.Continuum.P2DyadicFusionGapEnvelope.control_refined_squareGap_le_six_margin
