/-
# Spatial limits of the actual cutoff-removed reflected pairings

The raw three-index diagonal uses the original chartScalar with spatial
margin, heat stage and boundary-time buffer all equal to the displayed
index. A computed spatial pivot combines the actual geometric cross-width
bound with the existing joint cutoff/time modulus at one fixed width.
The resulting CReal and QCauchy data require no width-uniform temporal
mixing rate and no choice of subsequence.

The already constructed, cutoff/time-removed jointPairing in each
recentered box converges to this SAME scalar. This does not identify the
separate completed vector carriers, prove a width-independent physical
gap, or construct a continuum quantum field theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
import YMGap.Continuum.SpatialPivotCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter recenter_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing jointPairing_chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl (boxSize)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (base H : Nat) (x y : PhysicalSpan base)
  (hx : radius x.val ≤ H) (hy : radius y.val ≤ H)

def recenteredScalar (r stage t : Nat) : Q' :=
  chartScalar hw0 hw1 (paddedWidth base r) stage H (recenter r x) (recenter r y) t

def rowModulus (r : Nat) (epsilon : Q') : Nat :=
  chartJointModulus hw0 hw1 (paddedWidth base r) H (recenter r x) (recenter r y)
    (Nat.le_trans (Nat.le_of_eq (recenter_radius r x)) hx)
    (Nat.le_trans (Nat.le_of_eq (recenter_radius r y)) hy) epsilon

theorem row_rectangle (r : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (k t j u : Nat)
    (hk : rowModulus hw0 hw1 base H x y hx hy r epsilon ≤ k)
    (ht : rowModulus hw0 hw1 base H x y hx hy r epsilon ≤ t)
    (hj : rowModulus hw0 hw1 base H x y hx hy r epsilon ≤ j)
    (hu : rowModulus hw0 hw1 base H x y hx hy r epsilon ≤ u) :
    recenteredScalar hw0 hw1 base H x y r k t ≤ recenteredScalar hw0 hw1 base H x y r j u+epsilon ∧
      recenteredScalar hw0 hw1 base H x y r j u ≤ recenteredScalar hw0 hw1 base H x y r k t+epsilon :=
  chartJoint_rectangle hw0 hw1 (paddedWidth base r) H (recenter r x) (recenter r y)
    (Nat.le_trans (Nat.le_of_eq (recenter_radius r x)) hx)
    (Nat.le_trans (Nat.le_of_eq (recenter_radius r y)) hy) epsilon he k t j u
    (Nat.le_trans (Nat.le_max_right _ _) hk) (Nat.le_trans (Nat.le_max_left _ _) ht)
    (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hu)

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

/-- Explicit Cauchy data for the actual unmodified three-regulator diagonal. -/
def spatialCauchy : QCauchy (fun n => recenteredScalar hw0 hw1 base H x y n n n) :=
  SpatialPivotCauchy.diagonalCauchy (recenteredScalar hw0 hw1 base H x y)
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs base H x y)
    (carrierSize (boxSize base H)) (rowModulus hw0 hw1 base H x y hx hy)
    (rate_nonnegative hw0 hd) hs (spatialAmplitude_nonnegative w hd hs base H x y hx hy)
    (fun r d k t => chartScalar_spatial_bound hw0 hw1 hsmall hd hs base r d H t k hb x y hx hy)
    (row_rectangle hw0 hw1 base H x y hx hy)

/-- A witnessed constructive real, not an existential subsequential limit. -/
def spatialLimit : CReal :=
  ofQ'CauchySeq _ (spatialCauchy hw0 hw1 base H x y hx hy hsmall hd hs hb)

theorem spatial_diagonal_converges :
    ConvergesTo (fun n => ofQ' (recenteredScalar hw0 hw1 base H x y n n n))
      (spatialLimit hw0 hw1 base H x y hx hy hsmall hd hs hb) :=
  convergesTo_ofQ'CauchySeq _ (spatialCauchy hw0 hw1 base H x y hx hy hsmall hd hs hb)

/-- The actual cutoff/time-removed reflected pairings converge across widths.
No cross-width vector identification or common Hilbert carrier is assumed. -/
theorem jointPairing_spatial_converges :
    ConvergesTo (fun r => jointPairing hw0 hw1 (paddedWidth base r) (recenter r x) (recenter r y))
      (spatialLimit hw0 hw1 base H x y hx hy hsmall hd hs hb) := by
  have h := SpatialPivotCauchy.rowLimits_converge (recenteredScalar hw0 hw1 base H x y)
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs base H x y)
    (carrierSize (boxSize base H)) (rowModulus hw0 hw1 base H x y hx hy)
    (rate_nonnegative hw0 hd) hs (spatialAmplitude_nonnegative w hd hs base H x y hx hy)
    (fun r d k t => chartScalar_spatial_bound hw0 hw1 hsmall hd hs base r d H t k hb x y hx hy)
    (row_rectangle hw0 hw1 base H x y hx hy)
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro r
  exact (jointPairing_chart hw0 hw1 (paddedWidth base r) H (recenter r x) (recenter r y)
    (Nat.le_trans (Nat.le_of_eq (recenter_radius r x)) hx)
    (Nat.le_trans (Nat.le_of_eq (recenter_radius r y)) hy)).symm

/-- The chosen observation chart changes the modulus, not the limiting scalar. -/
theorem spatialLimit_chart_independent (H' : Nat)
    (hx' : radius x.val ≤ H') (hy' : radius y.val ≤ H') :
    Equiv (spatialLimit hw0 hw1 base H x y hx hy hsmall hd hs hb)
      (spatialLimit hw0 hw1 base H' x y hx' hy' hsmall hd hs hb) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl _)
    (jointPairing_spatial_converges hw0 hw1 base H x y hx hy hsmall hd hs hb)
    (jointPairing_spatial_converges hw0 hw1 base H' x y hx' hy' hsmall hd hs hb)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.recenteredScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.rowModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.row_rectangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.spatialCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.spatialLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.spatial_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.jointPairing_spatial_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit.spatialLimit_chart_independent
