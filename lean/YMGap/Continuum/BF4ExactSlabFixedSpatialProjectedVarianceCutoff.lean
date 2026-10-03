/-
# ORIGINAL projected active variance under a controlled reference cutoff

The source, action, incoming depths and output score use the ORIGINAL K.
Only the auxiliary conditional kernel in the reference variance uses L.
An explicit source-independent cutoff makes the variance comparison cost
one near-unit factor. Actual Haar normalization is proved under every
surviving insertion, never asserted as a free-polynomial identity.

This pays a representation-cutoff comparison leg. It does not supply the
reference conditional Poincare estimate, a surviving-norm bound, a justified
changing family, or any continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
import YMGap.Continuum.SU2QuaternionConditionalVarianceOrder
import YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVarianceCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_one)
open YMGap.Continuum.SU2QuaternionProductHeatRelativeCutoff
open YMGap.Continuum.SU2QuaternionConditionalVarianceOrder
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- The ORIGINAL kinetic layer has unit conditional mass under arbitrary
surviving insertions. No positivity guard or action normalization is used. -/
theorem kinetic_conditional_unit (w : Q') (K width : Nat) :
    HaarCarrierEqv (N width)
      (partialHaarHeads (N width) (kineticWeight w K width)) polyOne := by
  rw [kineticWeight_eq_indexedProduct]
  let ids := activeBlocks width
  have hone := carrier_of_supported
    (productMap_supported (N width) w K ids (activeBlocks_lt width)
      (supported_one (N width))) (supported_one (N width))
    (productMap_one (N width) w K ids (activeBlocks_nodup width) (activeBlocks_lt width))
  exact (RatPolyCoeffEqv.haarCarrier
    (partialHaarHeads_congr (N width)
      (RatPolyCoeffEqv.mul_one (productHeat (N width) w K ids)))).symm.trans hone

/-- Only the selected kinetic-factor count enters this computed cutoff.
It depends on nome and tolerance; no scaling-uniformity is claimed. -/
def projectedVarianceCutoff (w eta : Q') (width : Nat) : Nat :=
  productRelativeCutoff w eta (activeBlocks width).length

/-- Remaining ORIGINAL conditional Jensen debt after fringe integration. -/
def projectedActiveVariance (w : Q') (K width s i j : Nat) (a c : RatPoly) : RatPoly :=
  let S := conditionalScore (4*s+i) (4*s+j)
    (transferStep w K width a) (transferStep w K width c)
  polyAdd (lastStepProjectedDerivativeBudget w K width s i j a c)
    (polyNeg (polyMul S S))

/-- The source Q is kept at ORIGINAL K, including its original action and
output transfer. Only the auxiliary conditional kernel uses L. -/
def projectedReferenceVariance (w : Q') (K L width s i j : Nat)
    (a c : RatPoly) : RatPoly :=
  determinant (N width) (kineticWeight w L width)
    (lastStepProjectedDerivative w K width s i j a c)

private theorem variance_pin (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    HaarCarrierEqv (N width) (projectedActiveVariance w K width s i j a c)
      (determinant (N width) (kineticWeight w K width)
        (lastStepProjectedDerivative w K width s i j a c)) := by
  have h := lastStep_projectedDerivative_carrier w K width s i j hs hi hj ha hc
  exact HaarCarrierEqv.add
    (HaarCarrierEqv.refl (N width)
      (lastStepProjectedDerivativeBudget w K width s i j a c))
    (HaarCarrierEqv.neg (HaarCarrierEqv.mul h h))

/-- Constructed near-unit comparison for the actual ORIGINAL Jensen debt.
Both cutoffs may be arbitrarily late; neither source nor mass is inverted. -/
def projected_variance_cutoff_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (eta : Q')
    (he : (0 : Q') < eta) (he1 : eta ≤ 1) (K L width : Nat)
    (hK : projectedVarianceCutoff w eta width ≤ K)
    (hL : projectedVarianceCutoff w eta width ≤ L)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    Certificate (N width)
      (polyAdd (polySmul (1+eta) (projectedReferenceVariance w K L width s i j a c))
        (polyNeg (projectedActiveVariance w K width s i j a c))) := by
  have O : Certificate (N width+N width)
      (polyAdd (polySmul (1+eta) (kineticWeight w L width))
        (polyNeg (kineticWeight w K width))) := by
    simpa only [kineticWeight_eq_indexedProduct, productHeat] using
      productHeat_relative_upperCertificate (N width) hw0 hw1 eta he he1
        K L (activeBlocks width) (activeBlocks_lt width) hK hL
  have C := conditional_variance_order_certificate (N width) (N width)
    (kineticWeight w K width) (kineticWeight w L width)
    (lastStepProjectedDerivative w K width s i j a c) (1+eta)
    (kineticWeight_supported w K width) (kineticWeight_supported w L width)
    (lastStepProjectedDerivative_supported w K width s i j hs hi hj ha hc)
    (kinetic_conditional_unit w K width) (kinetic_conditional_unit w L width) O
  exact .transport (HaarCarrierEqv.add
    (HaarCarrierEqv.refl (N width)
      (polySmul (1+eta) (projectedReferenceVariance w K L width s i j a c)))
    (HaarCarrierEqv.neg (variance_pin w K width s i j hs hi hj ha hc))) C

/-- Arbitrary certified output W survives the cutoff comparison. In
particular the original Vbar^2*G^2 can be inserted without independence. -/
theorem projected_variance_cutoff_weighted_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (eta : Q')
    (he : (0 : Q') < eta) (he1 : eta ≤ 1) (K L width : Nat)
    (hK : projectedVarianceCutoff w eta width ≤ K)
    (hL : projectedVarianceCutoff w eta width ≤ L)
    (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4) {a c W : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (PW : Certificate (N width) W) :
    quaternionHaar (N width) (polyMul W (projectedActiveVariance w K width s i j a c)) ≤
      (1+eta)*quaternionHaar (N width)
        (polyMul W (projectedReferenceVariance w K L width s i j a c)) := by
  have H := SU2QuaternionProductHeatPositiveOrder.haar_order
    (projected_variance_cutoff_certificate hw0 hw1 eta he he1 K L width hK hL
      s i j hs hi hj ha hc) PW
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm W _)))
    (Q'.le_trans' _ _ _ H (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (haar_of_coeff
      (RatPolyCoeffEqv.polyMul_smul_left (1+eta) _ W))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (1+eta) _)
        (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ W)))))))

#print axioms kinetic_conditional_unit
#print axioms projectedVarianceCutoff
#print axioms projectedActiveVariance
#print axioms projectedReferenceVariance
#print axioms projected_variance_cutoff_certificate
#print axioms projected_variance_cutoff_weighted_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVarianceCutoff
