/-
# Observable curvature inside the original signed-family variance estimate

The literal quadratic cancellation applies to the EXISTING projected
terminal source. Its two negative squares can be retained or dropped for
an upper bound. Only the observable-curvature insertion then remains at
second order; actual cubic/cutoff payments and BOTH interacting corrections
are unchanged. No bound relative to variance on a scaling family is proved.
-/

import YMGap.Continuum.SU2QuaternionSecondOrderCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySecondOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare (activeCasimirPolynomial)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma)
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceSecondMoment sourceErrorBudget)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance wardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySecondOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  angularWeightDefect wardResidual

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem projected_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

/-- The signed insertion has only observable derivatives; the source is still
the entire original projected terminal source, with no altered density. -/
def curvatureMoment (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  quaternionHaar (N width) (polyMul (polyMul q q)
    (activeCasimirPolynomial (List.range (N width))
      (activeGamma (List.range (N width)) f f)))

/-- The two constructed negative squares justify this bound on the actual
quadratic coefficient. The remaining curvature moment has no assumed sign. -/
theorem quadraticCoefficient_le_curvature (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    quadraticCoefficient w K width n f ≤
      -curvatureMoment w K width n f +
        sourceFirstOrder (N width-1)
          (projectedEndpointSource w K width (terminalMessage w K width n)) f := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width-1+1) q := by
    simpa only [hN] using projected_supported w K width n
  have hf' : SupportedQuaternionBlocks (N width-1+1) f := by simpa only [hN] using hf
  have h : sourceSecondMoment (N width-1) q f ≤ -curvatureMoment w K width n f := by
    simpa only [hN, curvatureMoment, q] using
      sourceSecondMoment_le_curvature (N width-1) q f hq hf'
  exact Q'.add_le_add_right _ _ (sourceFirstOrder (N width-1) q f) h

/-- Only D2 changes to its proved upper bound. Cubic and actual cutoff payment,
angular weight defect, complete Ward residual and original odd mass remain. -/
def curvatureVarianceCeiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
      (-curvatureMoment w K width n f + sourceFirstOrder (N width-1) q f) +
    sourceErrorBudget (N width-1) w K q f -
    ((1 : Q')-w)*angularWeightDefect w K width n f -
    ((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f) *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem secondOrderVarianceCeiling_le_curvature {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    secondOrderVarianceCeiling hw0 hw1 K width hK n f ≤
      curvatureVarianceCeiling hw0 hw1 K width hK n f := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hc : (0 : Q') ≤ HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)) :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg (Q'.mul_nonneg _ _ hh hh)
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ _
    (quadraticCoefficient_le_curvature w K width n f hf) hc
  have hraw := Q'.add_le_add_right _ _
    (-(((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f))
    (Q'.add_le_add_right _ _ (-(((1 : Q')-w)*angularWeightDefect w K width n f))
      (Q'.add_le_add_right _ _ (sourceErrorBudget (N width-1) w K q f) hquad))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem varianceRemainder_le_curvature {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    varianceRemainder hw0 hw1 K width hK n f ≤
      curvatureVarianceCeiling hw0 hw1 K width hK n f :=
  Q'.le_trans' _ _ _ (varianceRemainder_le_secondOrder hw0 hw1 K width hK n f)
    (secondOrderVarianceCeiling_le_curvature hw0 hw1 K width hK n f hf)

/-- Concrete consumer for the WHOLE signed padded family and its SAME original
interacting variance. This ceiling is not proved scaling-small. -/
theorem padded_family_energy_le_curvature {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      12*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)) +
        curvatureVarianceCeiling hw0 hw1 K width hK n (spatialSpan width c qs) :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_family_energy_variance hw0 hw1 K hwidth hK n qs c hqs))
    (Q'.add_le_add_left _ _ _
      (varianceRemainder_le_curvature hw0 hw1 K width hK n (spatialSpan width c qs)
        (spatialSpan_supported width c qs)))

#print axioms curvatureMoment
#print axioms quadraticCoefficient_le_curvature
#print axioms curvatureVarianceCeiling
#print axioms secondOrderVarianceCeiling_le_curvature
#print axioms varianceRemainder_le_curvature
#print axioms padded_family_energy_le_curvature

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCurvature
