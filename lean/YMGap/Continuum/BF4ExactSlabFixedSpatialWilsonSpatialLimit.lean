/-
# Original Wilson-window expectations after three lattice regulators recede

The unmodified diagonal uses spatial margin, heat stage and symmetric
external time depth all equal to its displayed index. The actual spatial
comparison and the joint time/cutoff modulus at one computed spatial pivot
give explicit Cauchy data. Previously constructed joint limits converge to
the SAME CReal. Complete reflected products remain nonnegative.

This is fixed-spacing small-nome SU(2). Individual observable limits and
their reflected positivity are not yet a consistent full OS state, its
quotient/completion, full observable coverage or the strict estimate on
that enlarged carrier. Physical spacing and the continuum target remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
import YMGap.Continuum.SpatialPivotCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality (boxSize)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

theorem rate_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ entropyRate 625 (adjustedCoreRate w hd) :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg 625) (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)

/-- The generic row construction is the already constructed original joint
time/cutoff limit, by exact same-source finite pins, not a new chosen state. -/
theorem rowLimit_pin (r : Nat) :
    Equiv (SpatialPivotCauchy.rowLimit (chartScalar hw0 hw1 H e) (rowModulus hw0 hw1 H e)
      (row_rectangle hw0 hw1 H e he) r)
      (originalJointLimit hw0 hw1 (2*H) (centeredExpression r e)
        ((centered_within r (2*H) e).mpr he)) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_original_pin hw0 hw1 H e he r n n))
    (convergesTo_ofQ'CauchySeq _ (SpatialPivotCauchy.rowCauchy
      (chartScalar hw0 hw1 H e) (rowModulus hw0 hw1 H e) (row_rectangle hw0 hw1 H e he) r))
    (originalJoint_diagonal_converges hw0 hw1 (2*H) (centeredExpression r e)
      ((centered_within r (2*H) e).mpr he))

attribute [local irreducible] chartScalar rowModulus originalJointLimit

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

/-- Actual original expectation on the literal three-regulator diagonal. -/
def spatialCauchy : QCauchy (fun n => chartScalar hw0 hw1 H e n n n) :=
  SpatialPivotCauchy.diagonalCauchy (chartScalar hw0 hw1 H e)
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs H e)
    (carrierSize (boxSize base (2*H))) (rowModulus hw0 hw1 H e)
    (rate_nonnegative hw0 hd) hs (spatialAmplitude_nonnegative w hd hs H e he)
    (fun r d k t => chartScalar_spatial_bound hw0 hw1 hsmall hd hs hb H e he r d k t)
    (row_rectangle hw0 hw1 H e he)

theorem spatialCauchy_modulus (epsilon : Q') :
    (spatialCauchy hw0 hw1 H e he hsmall hd hs hb).M epsilon =
      SpatialPivotCauchy.diagonalModulus (entropyRate 625 (adjustedCoreRate w hd))
        (spatialAmplitude w hd hs H e) (carrierSize (boxSize base (2*H)))
        (rowModulus hw0 hw1 H e) epsilon := rfl

def spatialLimit : CReal := ofQ'CauchySeq _ (spatialCauchy hw0 hw1 H e he hsmall hd hs hb)

theorem spatial_diagonal_converges :
    ConvergesTo (fun n => ofQ' (chartScalar hw0 hw1 H e n n n))
      (spatialLimit hw0 hw1 H e he hsmall hd hs hb) :=
  convergesTo_ofQ'CauchySeq _ (spatialCauchy hw0 hw1 H e he hsmall hd hs hb)

/-- The previous cutoff/time-removed original Wilson expectations converge
to this SAME spatial diagonal, with no uniform-in-width time modulus. -/
theorem jointLimits_spatial_converge :
    ConvergesTo (fun r => originalJointLimit hw0 hw1 (2*H) (centeredExpression r e)
      ((centered_within r (2*H) e).mpr he)) (spatialLimit hw0 hw1 H e he hsmall hd hs hb) := by
  have h := SpatialPivotCauchy.rowLimits_converge (chartScalar hw0 hw1 H e)
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs H e)
    (carrierSize (boxSize base (2*H))) (rowModulus hw0 hw1 H e)
    (rate_nonnegative hw0 hd) hs (spatialAmplitude_nonnegative w hd hs H e he)
    (fun r d k t => chartScalar_spatial_bound hw0 hw1 hsmall hd hs hb H e he r d k t)
    (row_rectangle hw0 hw1 H e he)
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro r
  exact rowLimit_pin hw0 hw1 H e he r

/-- Independent spatial margin, cutoff and symmetric time depth are
controlled by one computed spatial pivot and its explicit inner modulus. -/
theorem spatial_approx (epsilon : Q') (heps : (0 : Q') < epsilon) (r k t i : Nat)
    (hr : SpatialPivotCauchy.pivot (entropyRate 625 (adjustedCoreRate w hd))
      (spatialAmplitude w hd hs H e) (carrierSize (boxSize base (2*H))) epsilon ≤ r)
    (hk : rowModulus hw0 hw1 H e
      (SpatialPivotCauchy.pivot (entropyRate 625 (adjustedCoreRate w hd))
        (spatialAmplitude w hd hs H e) (carrierSize (boxSize base (2*H))) epsilon)
      (SpatialPivotCauchy.quarter epsilon) ≤ k)
    (ht : rowModulus hw0 hw1 H e
      (SpatialPivotCauchy.pivot (entropyRate 625 (adjustedCoreRate w hd))
        (spatialAmplitude w hd hs H e) (carrierSize (boxSize base (2*H))) epsilon)
      (SpatialPivotCauchy.quarter epsilon) ≤ t)
    (hi : (spatialCauchy hw0 hw1 H e he hsmall hd hs hb).M epsilon ≤ i) :
    chartScalar hw0 hw1 H e r k t ≤ (spatialLimit hw0 hw1 H e he hsmall hd hs hb).approx i+epsilon ∧
      (spatialLimit hw0 hw1 H e he hsmall hd hs hb).approx i ≤ chartScalar hw0 hw1 H e r k t+epsilon :=
  SpatialPivotCauchy.diagonal_approx (chartScalar hw0 hw1 H e)
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs H e)
    (carrierSize (boxSize base (2*H))) (rowModulus hw0 hw1 H e)
    (rate_nonnegative hw0 hd) hs (spatialAmplitude_nonnegative w hd hs H e he)
    (fun r d k t => chartScalar_spatial_bound hw0 hw1 hsmall hd hs hb H e he r d k t)
    (row_rectangle hw0 hw1 H e he) epsilon heps r k t i hr hk ht hi

/-- Full signed reflected products remain nonnegative after all THREE
lattice regulators recede. Physical spacing and nome are not varied. -/
theorem spatial_reflected_nonnegative (hlower : Within H e) :
    leEv (ofQ' 0) (spatialLimit hw0 hw1 H (.mul (mirror H e) e)
      ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e hlower⟩ hsmall hd hs hb) := by
  let c := spatialCauchy hw0 hw1 H (.mul (mirror H e) e)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e hlower⟩ hsmall hd hs hb
  exact leEv_ofQ'_of_approx_ge (fun k => chartScalar_reflected_nonnegative hw0 hw1 H e hlower
    (QMhat _ c k) (QMhat _ c k) (QMhat _ c k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.rate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.rowLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.spatialCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.spatialCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.spatialLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.spatial_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.jointLimits_spatial_converge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.spatial_approx
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit.spatial_reflected_nonnegative
