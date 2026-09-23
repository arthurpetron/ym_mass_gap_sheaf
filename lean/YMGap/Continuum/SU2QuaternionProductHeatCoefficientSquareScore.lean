/-
# Coefficient-square control of the original product-heat score

The multiplicity bound is LOCAL to each selected block. Repeated heat factors
remain in the sum, and repeated angular terms are counted by the explicit
local multiplicity. No unproved grouping, orthogonality, or discarded mixed
term is used. This is a normalized response bound, not a Wilson jump-energy
comparison or a physical spectral gap.
-/

import YMGap.Continuum.SU2QuaternionProductHeatDualScore
import YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget

namespace YMGap.Continuum.SU2QuaternionProductHeatCoefficientSquareScore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature
open YMGap.Continuum.SU2QuaternionProductHeatDualScore
open YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative

/-- Nonnegativity of the computed cap, without an assumed analytic bound. -/
theorem logCurvatureCap_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ logCurvatureCap w hw0 hw1 := by
  have hsecond : (0 : Q') ≤ heatSecondDerivativeCap w 32 32 64 :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide)
        (SU2HeatPolynomialPrefixBound.prefixBudget_nonnegative hw0 6))
      (Q'.mul_nonneg _ _ (by decide)
        (SU2HeatPolynomialPrefixBound.prefixBudget_nonnegative hw0 4))
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hsecond (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (SumOfSquares.q_mul_self_nonneg _)

/-- The WHOLE original normalized score with an explicit local coefficient
square cost. The same positive edge mass normalizes both sides. -/
theorem productHeat_normalized_coefficientSquare_score_bound
    (n : Nat) (terms : List (AngularTerm n)) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (m : Nat)
    (hlocal : ∀ i, i ∈ ids →
      (terms.filter (fun t => decide (t.block.val = i))).length ≤ m)
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (A : Certificate n a) (hf : SupportedQuaternionBlocks (n+n) f)
    (hZ : (0 : Q') < quaternionHaar (n+n)
      (polyMul (polyMul a (liftBoundary n a)) (productHeat n w K ids))) :
    let W := productHeat n w K ids
    let d := signedAngularDirection (upperTerms terms) W
    let R := polyMul a (liftBoundary n a)
    let r := Q'.recipPos (quaternionHaar (n+n) (polyMul R W)) hZ
    (r*quaternionHaar (n+n) (polyMul R (polyMul d f))) *
        (r*quaternionHaar (n+n) (polyMul R (polyMul d f))) ≤
      ((Q'.ofNat m * logCurvatureCap w hw0 hw1) *
        productCoefficientSquareSum terms ids) *
        (r*quaternionHaar (n+n) (polyMul R (polyMul W (polyMul f f)))) := by
  let W := productHeat n w K ids
  let R := polyMul a (liftBoundary n a)
  let r := Q'.recipPos (quaternionHaar (n+n) (polyMul R W)) hZ
  have hW : Certificate (n+n) W := productHeatCertificate n hw0 hw1 K
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) ids hids
  have hR : Certificate (n+n) R :=
    (certificate_extend n ha A).mul (lift_certificate n A)
  have htest : (0 : Q') ≤
      r * quaternionHaar (n+n) (polyMul R (polyMul W (polyMul f f))) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _))
      (hR.mul (hW.mul (Certificate.square f hf))).haar_nonnegative
  exact Q'.le_trans' _ _ _
    (productHeat_normalized_dual_score_bound n terms hw0 hw1 K hK ids hids a f ha A hf hZ)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (productCurvatureCost_le_coefficientSquares terms _
        (logCurvatureCap_nonnegative hw0 hw1) m ids hlocal) htest)

end YMGap.Continuum.SU2QuaternionProductHeatCoefficientSquareScore

#print axioms YMGap.Continuum.SU2QuaternionProductHeatCoefficientSquareScore.logCurvatureCap_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCoefficientSquareScore.productHeat_normalized_coefficientSquare_score_bound
