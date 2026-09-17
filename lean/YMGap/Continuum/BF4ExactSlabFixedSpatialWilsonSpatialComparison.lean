/-
# Same-action spatial comparison for actual signed Wilson windows

The original source expression is recentered by r+1 into the existing
padded spatial chart. Ordered-word translation pins its literal polynomial
to the aligned larger chart. The separately proved fixed-box locality and
placement-independent interval cap instantiate the existing signed original
action comparison, retaining both partitions and every selected action factor.

The resulting geometric error is uniform in heat stage and external time
depth, not in nome or source expression. The explicit small-nome guards
remain. No OS quotient norm, old-carrier embedding or continuum gap follows.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality
import YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize boxAmplitude)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftLink)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def centeredExpression {base : Nat} (r : Nat) (e : WindowExpression base) :
    WindowExpression (paddedWidth base r) :=
  recenterExpression (space := r+1) (by unfold paddedWidth; omega) e

theorem centered_within {base : Nat} (r L : Nat) (e : WindowExpression base) :
    Within L (centeredExpression r e) ↔ Within L e := recenter_within _ L e

theorem centered_step {base : Nat} (r d : Nat) (e : WindowExpression base) :
    recenterExpression (space := d)
      (by unfold paddedWidth; omega : paddedWidth base r+d ≤ paddedWidth base (r+d))
      (centeredExpression r e) = centeredExpression (r+d) e := by
  have hshift : r+1+d = r+d+1 := by omega
  simpa only [centeredExpression, hshift] using
    recenterExpression_comp (first := r+1) (second := d)
      (middle := paddedWidth base r) (targetWidth := paddedWidth base (r+d))
      (by unfold paddedWidth; omega) (by unfold paddedWidth; omega) e

theorem windowCap_recenter {base targetWidth space : Nat}
    (hroom : base+space ≤ targetWidth) (e : WindowExpression base) :
    windowCap (recenterExpression hroom e) = windowCap e := by
  induction e <;> simp_all only [recenterExpression, windowCap]

def chartInsertion {base : Nat} (r H t : Nat) (e : WindowExpression base) : RatPoly :=
  placedPolynomial (chartExtent base r H t) (paddedWidth base r+1+t) (centeredExpression r e)

def chart_interval {base : Nat} (r H t : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) :
    Interval (B (chartExtent base r H t)) (chartInsertion r H t e) (windowCap e) := by
  have hw : paddedWidth base r ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+2*H ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have h := placed_interval hw ht (centeredExpression r e) ((centered_within r (2*H) e).mpr he)
  simpa only [chartInsertion, centeredExpression, windowCap_recenter] using h

theorem chart_local {base : Nat} (r H t : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) :
    LinkLocal (chartExtent base r H t)
      ((boxLinks (boxSize base (2*H))).map (shiftLink (r+1) (paddedWidth base r+1+t)))
      (chartInsertion r H t e) :=
  placed_recenter_local (space := r+1)
    (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r) (2*H) e he

/-- The exact original polynomial pin needed by the filtered-action theorem. -/
theorem aligned_chartInsertion_pin {base : Nat} (r d H t : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) :
    QuaternionPrefixPolynomialEqv (B (chartExtent base (r+d) H t))
      ((placement base r d H t).embedding.polynomial (chartInsertion r H t e))
      (chartInsertion (r+d) H t e) := by
  have hroom : paddedWidth base r+(placement base r d H t).space ≤ paddedWidth base (r+d) := by
    change paddedWidth base r+d ≤ paddedWidth base (r+d)
    unfold paddedWidth
    omega
  have hw : paddedWidth base r ≤ (placement base r d H t).source := by
    change paddedWidth base r ≤ chartExtent base r H t
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+2*H ≤ (placement base r d H t).source := by
    change paddedWidth base r+1+t+2*H ≤ chartExtent base r H t
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have h := placed_pin (placement base r d H t) hroom hw ht (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  have htime : paddedWidth base r+1+t+2*d = paddedWidth base (r+d)+1+t := by
    unfold paddedWidth
    omega
  simpa only [placement, htime, centered_step, chartInsertion] using h

/-- Every scalar is the actual full selected-chain normalized expectation. -/
def chartScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (r stage t : Nat) : Q' :=
  finiteValue w hw0 hw1 (chartExtent base r H t) (chartIds base r H t)
    (fun _ hi => chartIds_physical hi) (chartInsertion r H t e) stage

/-- Centered spatial chart and old raw time realization have one compact
source, one cutoff and one partition; ambient sizes need not agree. -/
theorem chartScalar_original_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (r stage t : Nat) :
    chartScalar hw0 hw1 H e r stage t ≈
      originalWindowScalar hw0 hw1 (2*H) (centeredExpression r e) stage t t := by
  have hw : paddedWidth base r ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+(t+(2*H+t)) ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hr := (centered_within r (2*H) e).mpr he
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (windowRatio_originalFiniteValue hw0 hw1 (m := t) (L := 2*H) (n := t)
      hw ht (centeredExpression r e) hr stage))
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 (2*H) (centeredExpression r e) hr stage t t))

def rowModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (r : Nat) (epsilon : Q') : Nat :=
  jointModulus hw0 hw1 (2*H) (centeredExpression r e) epsilon

attribute [local irreducible] chartScalar originalWindowScalar

theorem row_rectangle {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (r : Nat) (epsilon : Q') (heps : (0 : Q') < epsilon) (k t j u : Nat)
    (hk : rowModulus hw0 hw1 H e r epsilon ≤ k)
    (ht : rowModulus hw0 hw1 H e r epsilon ≤ t)
    (hj : rowModulus hw0 hw1 H e r epsilon ≤ j)
    (hu : rowModulus hw0 hw1 H e r epsilon ≤ u) :
    chartScalar hw0 hw1 H e r k t ≤ chartScalar hw0 hw1 H e r j u + epsilon ∧
      chartScalar hw0 hw1 H e r j u ≤ chartScalar hw0 hw1 H e r k t + epsilon := by
  have h := originalJoint_rectangle hw0 hw1 (2*H) (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he) epsilon heps k t j u
    (Nat.le_trans (Nat.le_max_right _ _) hk) (Nat.le_trans (Nat.le_max_left _ _) ht)
    (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hu)
  have hp := chartScalar_original_pin hw0 hw1 H e he r k t
  have hq := chartScalar_original_pin hw0 hw1 H e he r j u
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (Q'.le_trans' _ _ _ h.1
      (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hq))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hq) (Q'.le_trans' _ _ _ h.2
      (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hp)))⟩

def spatialAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (H : Nat) (e : WindowExpression base) : Q' :=
  (windowCap e+windowCap e) * boxAmplitude w hd hs (boxSize base (2*H))

theorem spatialAmplitude_nonnegative (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e) :
    (0 : Q') ≤ spatialAmplitude w hd hs H e := by
  have hc := (chart_interval 0 H 0 e he).nonnegative
  exact Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hc hc)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (probePrefactor_nonnegative w hd _)
      (ClusterCount.ofNat_nonneg _)) (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- Actual original action comparison with no caller-supplied locality, cap
or spatial-decay premise. The original small-nome guards are retained. -/
theorem chartScalar_spatial_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (r d stage t : Nat) :
    Q'.abs (chartScalar hw0 hw1 H e (r+d) stage t + -(chartScalar hw0 hw1 H e r stage t)) ≤
      spatialAmplitude w hd hs H e *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize (boxSize base (2*H))) := by
  unfold chartScalar
  have hpin := BF4ExactSlabFixedSpatialAlignedAction.finiteValue_pin hw0 hw1 base r d H t
    (chartInsertion r H t e) (chart_interval r H t e he).support
    (chartInsertion (r+d) H t e) (chart_interval (r+d) H t e he).support
    (aligned_chartInsertion_pin r d H t e he) stage
  have hbnd := BF4ExactSlabFixedSpatialBoxBoundary.finiteValue_bound hw0 hw1 hsmall hd hs
    base r d H t (paddedWidth base (r+d)+1+t) (boxSize base (2*H)) hb (boxSize_pos base (2*H))
    (chartInsertion (r+d) H t e) (windowCap e)
    (chart_interval (r+d) H t e he) (chart_local (r+d) H t e he) stage
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hpin)))) hbnd

theorem chartScalar_reflected_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within H e)
    (r stage t : Nat) :
    (0 : Q') ≤ chartScalar hw0 hw1 H (.mul (mirror H e) e) r stage t := by
  have hp := chartScalar_original_pin hw0 hw1 H (.mul (mirror H e) e)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e he⟩ r stage t
  have hn := originalReflectedScalar_nonnegative hw0 hw1 H (centeredExpression r e)
    ((centered_within r H e).mpr he) stage t
  apply Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hp)
  simpa only [centeredExpression, recenterExpression, mirror, recenter_mapOffsets] using hn

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.centeredExpression
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.centered_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.centered_step
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.windowCap_recenter
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chartInsertion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chart_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chart_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.aligned_chartInsertion_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chartScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chartScalar_original_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.rowModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.row_rectangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.spatialAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.spatialAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chartScalar_spatial_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison.chartScalar_reflected_nonnegative
