/-
# Actual reflected chart scalars become insensitive to spatial boundaries

The signed probe product, selected action and original partition are the
ones in chartScalar. Both interval and link-locality data are constructed
from the fixed base presentations. Exact translation identifies the masked
larger law with the smaller original chart, and the signed core estimate
bounds their difference uniformly in heat stage and boundary-time buffer.

The amplitude retains the base observable/support and nome dependence.
Small-nome guards are explicit. This is spatial comparison of the actual
reflected moments, not a temporal decay rate or a continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
import YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize boxAmplitude)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

def spatialAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base H : Nat) (x y : PhysicalSpan base) : Q' :=
  (pairCap x.val y.val+pairCap x.val y.val) * boxAmplitude w hd hs (boxSize base H)

theorem rate_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ entropyRate 625 (adjustedCoreRate w hd) :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg 625) (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

theorem spatialAmplitude_nonnegative (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base H : Nat) (x y : PhysicalSpan base) (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    (0 : Q') ≤ spatialAmplitude w hd hs base H x y := by
  have hc := (chartProbe_interval base 0 H 0 x y hx hy).nonnegative
  exact Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hc hc)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (probePrefactor_nonnegative w hd _)
        (ClusterCount.ofNat_nonneg _)) (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- The actual reflected product, with no caller-supplied interval/locality
or spatial-decay premise. The original radius and coupling guards remain. -/
theorem chartScalar_spatial_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r d H t stage : Nat) (hb : 0<base) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Q'.abs (chartScalar hw0 hw1 (paddedWidth base (r+d)) stage H
      (recenter (r+d) x) (recenter (r+d) y) t +
      -(chartScalar hw0 hw1 (paddedWidth base r) stage H (recenter r x) (recenter r y) t)) ≤
      spatialAmplitude w hd hs base H x y *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize (boxSize base H)) := by
  have hn : 0 < boxSize base H := by unfold boxSize; omega
  have hpin := BF4ExactSlabFixedSpatialAlignedAction.finiteValue_pin hw0 hw1 base r d H t
    (chartProbe base r H t x y) (chartProbe_interval base r H t x y hx hy).support
    (chartProbe base (r+d) H t x y) (chartProbe_interval base (r+d) H t x y hx hy).support
    (BF4ExactSlabFixedSpatialTranslatedProbe.aligned_chartInsertion_pin base r d H t x y hx hy) stage
  have hbnd := BF4ExactSlabFixedSpatialBoxBoundary.finiteValue_bound hw0 hw1 hsmall hd hs
    base r d H t (paddedWidth base (r+d)+1+t) (boxSize base H) hb hn
    (chartProbe base (r+d) H t x y) (pairCap x.val y.val)
    (chartProbe_interval base (r+d) H t x y hx hy)
    (chartProbe_local base (r+d) H t x y hx hy) stage
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hpin)))) hbnd

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison.spatialAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison.rate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison.spatialAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison.chartScalar_spatial_bound
