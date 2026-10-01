/-
# Second order in the SAME signed-family energy and variance

Expose the mixed-minus-diagonal quadratic coefficient, cubic correction and
actual omitted-mode debt inside the EXISTING original odd-marginal formula.
Keep both the angular change-of-weight defect and the COMPLETE-weight Ward
residual, including its original center. Nothing here bounds that combined
interaction correction relative to variance or supplies physical scaling.
-/

import YMGap.Continuum.SU2QuaternionCyclicSecondOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySecondOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor (signedRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance wardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  angularWeightDefect wardResidual

/-- All sources remain the original projected endpoints. Projection here is
the EXISTING fringe join, not a new law or an assumed degree-below-K bound. -/
def quadraticCoefficient (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  sourceSecondMoment (N width-1) q f + sourceFirstOrder (N width-1) q f

def cubicCorrection (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  sourceCubic (N width-1) w q f

def cutoffCorrection (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  sourceOmitted (N width-1) w K q f

/-- The correction uses the SAME partition and original mean. No constituent
is assigned a useful sign, and neither source nor variance is inverted. -/
def secondOrderVarianceRemainder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*quadraticCoefficient w K width n f +
    cubicCorrection w K width n f - cutoffCorrection w K width n f -
    ((1 : Q')-w)*angularWeightDefect w K width n f -
    ((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f) *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

/-- Exact join to the existing correction, not a new remainder assumption. -/
theorem varianceRemainder_secondOrder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    varianceRemainder hw0 hw1 K width hK n f ≈
      secondOrderVarianceRemainder hw0 hw1 K width hK n f := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  have hr := sourceRemainder_secondOrder (N width-1) w K q f
  have hraw : signedRemainder w K width n f ≈
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*quadraticCoefficient w K width n f +
        cubicCorrection w K width n f-cutoffCorrection w K width n f -
        ((1 : Q')-w)*angularWeightDefect w K width n f :=
    Q'.add_eqv_congr' hr (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ (varianceRemainder_raw hw0 hw1 K width hK n f)
    (Q'.mul_eqv_congr_right _ _ _ (Q'.add_eqv_congr' hraw (Q'.eqv_refl _)))

/-- The whole signed family's original energy now carries the explicit second
order and actual cutoff payment. All repeated-face cross terms remain. -/
theorem padded_family_energy_secondOrder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≈
      12*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)) +
        secondOrderVarianceRemainder hw0 hw1 K width hK n (spatialSpan width c qs) :=
  Q'.eqv_trans _ _ _ (padded_family_energy_variance hw0 hw1 K hwidth hK n qs c hqs)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (varianceRemainder_secondOrder hw0 hw1 K width hK n (spatialSpan width c qs)))

/-- This explicit ceiling pays cubic and cutoff coefficients but keeps the
quadratic coefficient and BOTH interacting derivative corrections signed.
It is not claimed small relative to the SAME variance. -/
def secondOrderVarianceCeiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*quadraticCoefficient w K width n f +
    sourceErrorBudget (N width-1) w K q f -
    ((1 : Q')-w)*angularWeightDefect w K width n f -
    ((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f) *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem varianceRemainder_le_secondOrder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    varianceRemainder hw0 hw1 K width hK n f ≤
      secondOrderVarianceCeiling hw0 hw1 K width hK n f := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let c := (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*quadraticCoefficient w K width n f
  have he := sourceError_bound (N width-1) (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K q f
  have hraw : c+sourceCubic (N width-1) w q f-sourceOmitted (N width-1) w K q f ≤
      c+sourceErrorBudget (N width-1) w K q f :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _))
      (Q'.add_le_add_left c _ _ he)
  have hcorrected := Q'.add_le_add_right _ _
    (-(((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f))
    (Q'.add_le_add_right _ _ (-(((1 : Q')-w)*angularWeightDefect w K width n f)) hraw)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)) hcorrected
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (varianceRemainder_secondOrder hw0 hw1 K width hK n f)) hscaled

/-- Actual original signed-family energy bound. This changes no source,
mean, odd marginal or partition, and retains the useful quadratic sign. -/
theorem padded_family_energy_le_secondOrder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      12*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)) +
        secondOrderVarianceCeiling hw0 hw1 K width hK n (spatialSpan width c qs) :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_family_energy_variance hw0 hw1 K hwidth hK n qs c hqs))
    (Q'.add_le_add_left _ _ _
      (varianceRemainder_le_secondOrder hw0 hw1 K width hK n (spatialSpan width c qs)))

#print axioms quadraticCoefficient
#print axioms cubicCorrection
#print axioms cutoffCorrection
#print axioms secondOrderVarianceRemainder
#print axioms varianceRemainder_secondOrder
#print axioms padded_family_energy_secondOrder
#print axioms secondOrderVarianceCeiling
#print axioms varianceRemainder_le_secondOrder
#print axioms padded_family_energy_le_secondOrder

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySecondOrder
