/-
# Ordinary square positivity for the original spatial-union Wilson product

The ordinary vacuum mean of a supported square is nonnegative on the
existing fixed-nome completed carrier. The proof uses the original finite
window expectation and its explicit three-regulator spatial limit. It does
not assert multiplication on the OS-null quotient or the completion.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionProduct
import YMGap.Continuum.BF4WilsonSpatialUnionPairingData
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

namespace YMGap.Continuum.BF4WilsonSpatialUnionProductPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionProduct
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (embedStage completedUnit)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner completedInner_embedStage)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
  (HaarCarrierEqv haarCarrier_polyOne_left)

local infix:50 " ≈ " => Q'.eqv

private theorem chartScalar_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (g : WindowExpression base)
    (r stage t : Nat) :
    (0 : Q') ≤ chartScalar hw0 hw1 H
      (.mul (.mul (mirror H g) (mirror H g)) .one) r stage t := by
  let q := mirror H g
  let e : WindowExpression base := .mul (.mul q q) .one
  have he : Within (2*H) e := ⟨⟨mirror_within H g, mirror_within H g⟩, True.intro⟩
  have hp := chartScalar_original_pin hw0 hw1 H e he r stage t
  have hr : Within (2*H) (centeredExpression r e) :=
    (centered_within r (2*H) e).mpr he
  have hq := originalWindowScalar_pin hw0 hw1 (2*H) (centeredExpression r e)
    hr stage t t
  let p := sourcePolynomial (centeredExpression r q)
  have hsupport :
      SupportedQuaternionBlocks (((2*H)+1)*
        (BF4ExactSlabFixedSpatialSliceCarrier.baseLinks (BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth base r)).length) p :=
    source_supported (2*H) (centeredExpression r q)
      ((centered_within r (2*H) q).mpr (mirror_within H g))
  have hcoeff : HaarCarrierEqv (((2*H)+1)*
      (BF4ExactSlabFixedSpatialSliceCarrier.baseLinks
        (BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth base r)).length)
      (sourcePolynomial (centeredExpression r e)) (polyMul p p) := by
    change HaarCarrierEqv _ (polyMul (polyMul p p) polyOne) (polyMul p p)
    exact (BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.mul_comm (polyMul p p) polyOne)).trans
      (haarCarrier_polyOne_left _ _)
  have hcongr := windowRatio_carrier_congr hw0 hw1 (headCutoff w+stage)
    (BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth base r)
    (Nat.le_add_right _ _) t (2*H) t hcoeff
  have hfinite := windowRatio_square_nonnegative hw0 hw1 (headCutoff w+stage)
    (BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth base r)
    (Nat.le_add_right _ _) t (2*H) t hsupport
  have horiginal : (0 : Q') ≤
      originalWindowScalar hw0 hw1 (2*H) (centeredExpression r e) stage t t :=
    Q'.le_trans' _ _ _ hfinite
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcongr) (Q'.ge_of_eqv hq))
  exact Q'.le_trans' _ _ _ horiginal (Q'.ge_of_eqv hp)

private theorem spatial_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0 < base) (H : Nat) (g : WindowExpression base) :
    leEv (ofQ' 0) (spatialLimit hw0 hw1 H
      (.mul (.mul (mirror H g) (mirror H g)) .one)
      ⟨⟨mirror_within H g, mirror_within H g⟩, True.intro⟩ hsmall hd hs hb) := by
  let e : WindowExpression base := .mul (.mul (mirror H g) (mirror H g)) .one
  let he : Within (2*H) e := ⟨⟨mirror_within H g, mirror_within H g⟩, True.intro⟩
  let c := spatialCauchy hw0 hw1 H e he hsmall hd hs hb
  exact leEv_ofQ'_of_approx_ge (fun k => chartScalar_square_nonnegative hw0 hw1 H g
    (QMhat _ c k) (QMhat _ c k) (QMhat _ c k))

/-- Ordinary square positivity for every original supported stage, at the
same fixed-nome completed Wilson carrier and its original vacuum unit. -/
theorem product_square_vacuum_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (x : Stage) :
    RCnonneg (completedInner hw0 hw1 hsmall hd hs
      (embedStage hw0 hw1 hsmall hd hs (productStage x x))
      (completedUnit hw0 hw1 hsmall hd hs)) := by
  let H := x.value.radius
  let g := chart H x.value
  have hbase : (productStage x x).base ≤ x.base := by
    change max x.base x.base ≤ x.base
    exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hrad : (product x.value x.value).radius ≤ H := by
    change max x.value.radius x.value.radius ≤ x.value.radius
    exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hproduct : atBase (productStage x x) hbase =
      product x.value x.value := by
    simpa only [atBase_self] using
      atBase_product x x (Nat.le_refl _) (Nat.le_refl _)
  have hpair := pairing_at_base hw0 hw1 hsmall hd hs (productStage x x)
    unitStage x.base hbase
    (Nat.succ_le_of_lt x.positive)
  have hchart := intrinsicForm_chart hw0 hw1 hsmall hd hs x.positive
    (product x.value x.value) (unit x.base) H
    hrad (Nat.zero_le _)
  rw [hproduct, atBase_unit] at hpair
  have hprodChart := chart_product H x.value x.value (Nat.le_refl _) (Nat.le_refl _)
  have hunitChart := chart_unit x.base H
  simp only [hprodChart, hunitChart] at hchart
  have hEq : Equiv (pairing hw0 hw1 hsmall hd hs (productStage x x) unitStage)
      (form hw0 hw1 hsmall hd hs x.positive H
        (.mul g g) .one
        ⟨chart_within H x.value (Nat.le_refl _),
          chart_within H x.value (Nat.le_refl _)⟩ True.intro) := by
    exact hpair.trans hchart
  have hpos := spatial_square_nonnegative hw0 hw1 hsmall hd hs x.positive H g
  have hform : leEv czero
      (form hw0 hw1 hsmall hd hs x.positive H (.mul g g) .one
        ⟨chart_within H x.value (Nat.le_refl _),
          chart_within H x.value (Nat.le_refl _)⟩ True.intro) := by
    change leEv czero (spatialLimit hw0 hw1 H
      (.mul (.mul (mirror H g) (mirror H g)) .one)
      ⟨⟨mirror_within H g, mirror_within H g⟩, True.intro⟩ hsmall hd hs x.positive)
    exact hpos
  have hpairPos : leEv czero (pairing hw0 hw1 hsmall hd hs (productStage x x) unitStage) :=
    leEv_trans hform (leEv_of_equiv hEq.symm)
  rw [completedUnit, completedInner_embedStage]
  exact hpairPos

end YMGap.Continuum.BF4WilsonSpatialUnionProductPositivity

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionProductPositivity.product_square_vacuum_nonnegative
