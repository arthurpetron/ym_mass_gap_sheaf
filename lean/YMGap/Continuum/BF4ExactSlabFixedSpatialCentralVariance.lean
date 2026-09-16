/-
# A uniform finite central-character variance in the SAME original chain

The certified density is exactly V*(T^(t+1)1)^2. Its normalized moments
are pinned by coefficient algebra to the already constructed middle ratios,
retaining the central potential and the same positive partition function.
The actual source character's bare Haar moments then give a positive
variance floor independent of boundary depth and late heat cutoff.

The final inequality is about the literal original common-chart scalars,
with identical stage, chart, buffer and action in its first/second moments.
Nome and positive spatial width remain explicit. No limiting nonconstant
vector, spatial-uniform floor, or continuum conclusion is claimed here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter
import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

-- The proof rearranges whole factors, never their coordinate ledgers.
attribute [local irreducible] spatialWeight terminalMessage baseLinks character

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Both reciprocals belong to the identical central partition. No support
guard is needed for this unconditional signed coefficient identity. -/
theorem normalizedMoment_middleRatio {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) (p : RatPoly) :
    normalizedMoment (N width) (centralDensity w K width t) p
        (centralMass_positive hw0 hw1 K width hK t) ≈
      middleRatio hw0 hw1 K width hK (t+1) (t+1) p := by
  have hnum : quaternionHaar (N width) (polyMul (centralDensity w K width t) p) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width (t+1)) p)
          (terminalMessage w K width (t+1))) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 1)))
      (by decide) (fun
        | 0 => spatialWeight w K width
        | 1 => terminalMessage w K width (t+1)
        | _ => p))
  unfold normalizedMoment middleRatio massRatio
  exact qmul hnum (Q'.recipPos_eqv_congr _ _ _ _ (Q'.eqv_refl _))

/-- The floor is computed from the SAME density and the bare Haar moments
of this actual valid face; no interacting variance premise is supplied. -/
theorem centralVariance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (hwidth : 0 < width) (t : Nat) :
    centralFraction hw0 hw1 width ≤
      normalizedVariance (N width) (centralDensity w K width t) (character width)
        (centralMass_positive hw0 hw1 K width hK t) :=
  normalized_variance_floor (centralMass_positive hw0 hw1 K width hK t)
    (Q'.le_of_lt (centralFraction_positive hw0 hw1 width))
    (centralDensity_normalizedFloor hw0 hw1 K width hK t)
    (character_supported width) (character_mean_zero hwidth) (character_square_one hwidth)

/-- Positive lower variance in the original finite common chart. The
two moments share every regulator and their actual normalization. -/
theorem chart_variance_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (hwidth : 0 < width) (stage t : Nat) :
    centralFraction hw0 hw1 width ≤
      chartScalar hw0 hw1 width stage 0 (span width hwidth) (span width hwidth) (t+1) +
        -(chartScalar hw0 hw1 width stage 0 (span width hwidth) (unit width) (t+1) *
          chartScalar hw0 hw1 width stage 0 (span width hwidth) (unit width) (t+1)) := by
  have hmean := Q'.eqv_trans _ _ _
    (normalizedMoment_middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t
      (character width))
    (Q'.eqv_symm (chartScalar_mean_pin hw0 hw1 width hwidth stage (t+1)))
  have hsquare := Q'.eqv_trans _ _ _
    (normalizedMoment_middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t
      (polyMul (character width) (character width)))
    (Q'.eqv_symm (chartScalar_square_pin hw0 hw1 width hwidth stage (t+1)))
  exact Q'.le_trans' _ _ _
    (centralVariance_floor hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) hwidth t)
    (Q'.le_of_eqv (Q'.add_eqv_congr' hsquare (Q'.neg_eqv_congr _ _ (qmul hmean hmean))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance.normalizedMoment_middleRatio
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance.centralVariance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance.chart_variance_floor
