/-
# Finite positive linear laws for the actual interior ratio

For fixed nome, width, late heat cutoff and two boundary lengths, the
actual middle ratio is a normalized rational-linear functional of its
inserted polynomial. Every law retains the SAME positive denominator
ell((T^m 1)*(T^n 1)), independent of the probe. Signed homogeneity and
coefficient/Haar-carrier congruence need no support assumption.

Positivity uses the actual terminal-message certificates and a supplied
polynomial certificate; supported squares give the particular
positive-functional law. These finite laws feed the constructed interior
time limit on the supported polynomial algebra. No stationary cylinder
law, reflected OS positivity, cutoff removal or physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_congr weightedMass_add weightedMass_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

-- Use scalar laws without expanding the original finite transfer iterates.
attribute [local irreducible] weightedMass spatialWeight baseLinks terminalMessage

/-- Coefficient equality of the insertion preserves the actual normalized
ratio; no support guard is needed for this algebraic identity. -/
theorem middleRatio_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    middleRatio hw0 hw1 K width hK m n p ≈ middleRatio hw0 hw1 K width hK m n q :=
  massRatio_congr w K width (terminalPair_positive hw0 hw1 K width hK m n)
    (terminalPair_positive hw0 hw1 K width hK m n)
    (weightedMass_congr w K width
      ((RatPolyCoeffEqv.mul_left (terminalMessage w K width m) h).mul_right
        (terminalMessage w K width n)))
    (Q'.eqv_refl _)

/-- Equality under every Haar insertion survives the actual two terminal
messages and spatial weight, with the denominator unchanged. -/
theorem middleRatio_carrier_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p q : RatPoly}
    (h : HaarCarrierEqv (N width) p q) :
    middleRatio hw0 hw1 K width hK m n p ≈ middleRatio hw0 hw1 K width hK m n q := by
  apply massRatio_congr w K width (terminalPair_positive hw0 hw1 K width hK m n)
    (terminalPair_positive hw0 hw1 K width hK m n)
  · unfold weightedMass
    exact (HaarCarrierEqv.mul_right (terminalMessage w K width n)
      (h.mul_left (terminalMessage w K width m))) (spatialWeight w K width)
  · exact Q'.eqv_refl _

/-- The unit cancels the SAME positive middle partition. -/
theorem middleRatio_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    middleRatio hw0 hw1 K width hK m n polyOne ≈ 1 := by
  unfold middleRatio massRatio
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (weightedMass_congr w K width
        ((RatPolyCoeffEqv.mul_one (terminalMessage w K width m)).mul_right
          (terminalMessage w K width n))))
    (Q'.mul_recipPos_eqv _ (terminalPair_positive hw0 hw1 K width hK m n))

/-- Additivity of the actual finite middle functional. -/
theorem middleRatio_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (p q : RatPoly) :
    middleRatio hw0 hw1 K width hK m n (polyAdd p q) ≈
      middleRatio hw0 hw1 K width hK m n p + middleRatio hw0 hw1 K width hK m n q := by
  have he : RatPolyCoeffEqv
      (polyMul (polyMul (terminalMessage w K width m) (polyAdd p q)) (terminalMessage w K width n))
      (polyAdd
        (polyMul (polyMul (terminalMessage w K width m) p) (terminalMessage w K width n))
        (polyMul (polyMul (terminalMessage w K width m) q) (terminalMessage w K width n))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
        (.mul (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
      (fun | 0 => terminalMessage w K width m | 1 => p | 2 => q | _ => terminalMessage w K width n)
  unfold middleRatio massRatio
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (weightedMass_congr w K width he) (weightedMass_add w K width _ _)))
    (Q'.add_mul_eqv _ _ _)

/-- Rational homogeneity retains negative as well as nonnegative scales. -/
theorem middleRatio_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (c : Q') (p : RatPoly) :
    middleRatio hw0 hw1 K width hK m n (polySmul c p) ≈
      c * middleRatio hw0 hw1 K width hK m n p := by
  have he := ((RatPolyCoeffEqv.polyMul_smul_right c (terminalMessage w K width m) p).mul_right
      (terminalMessage w K width n)).trans
    (RatPolyCoeffEqv.polyMul_smul_left c (polyMul (terminalMessage w K width m) p)
      (terminalMessage w K width n))
  unfold middleRatio massRatio
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (weightedMass_congr w K width he) (weightedMass_smul w K width c _)))
    (Q'.mul_assoc_eqv _ _ _)

/-- Certified positivity is preserved under both actual terminal messages,
the spatial weight, and the SAME positive reciprocal partition. -/
theorem middleRatio_certificate_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p : RatPoly}
    (P : Certificate (N width) p) :
    (0 : Q') ≤ middleRatio hw0 hw1 K width hK m n p := by
  unfold middleRatio massRatio
  exact Q'.mul_nonneg _ _
    (weightedMass_nonnegative hw0 hw1 K width hK
      (((terminalMessage_certificate hw0 hw1 K width hK m).mul P).mul
        (terminalMessage_certificate hw0 hw1 K width hK n)))
    (Q'.le_of_lt (Q'.recipPos_pos _ (terminalPair_positive hw0 hw1 K width hK m n)))

/-- Positive-functional law for every supported square on the slice. -/
theorem middleRatio_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    (0 : Q') ≤ middleRatio hw0 hw1 K width hK m n (polyMul p p) :=
  middleRatio_certificate_nonnegative hw0 hw1 K width hK m n (.square p hp)

end YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws.middleRatio_square_nonnegative
