/-
# Exact north-chart weight carried by the global Cayley denominator

The denominator-cleared plaquette vector jet is not the pure ORIGINAL vector
jet.  This leaf identifies its exact multiplicative weight on the actual
unit-quaternion Haar carrier: the global denominator is a product of four
nonnegative north-chart factors, and the cleared observable is four times the
square of that product times the pure vector jet.

This is the exact interface required by any later multi-chart or southern-tail
payment.  It does not divide by the weight, which vanishes at the Cayley south
pole, and it does not identify the cleared response with the milestone-384
unweighted pure-jet response.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Product of the four explicit north-chart scalar factors attached to the
oriented plaquette links. -/
def globalCayleyNorthFactorProduct
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul
      (polyMul
        (northCayleyFactorPolynomial (faceCayleyQuaternion0 extent face)
          (faceCayleyComplement0 extent face))
        (northCayleyFactorPolynomial (faceCayleyQuaternion1 extent face)
          (faceCayleyComplement1 extent face)))
      (northCayleyFactorPolynomial (faceCayleyQuaternion2 extent face)
        (faceCayleyComplement2 extent face)))
    (northCayleyFactorPolynomial (faceCayleyQuaternion3 extent face)
      (faceCayleyComplement3 extent face))

/-- The literal global Cayley denominator is exactly the four-factor north
chart product on the complete slab Haar carrier. -/
theorem globalCayleyDenominatorPolynomial_carrier_northFactorProduct
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyDenominatorPolynomial extent face)
      (globalCayleyNorthFactorProduct extent face) := by
  let blocks := (boundaryCompleteSlabLinks extent).length
  have hdenominator : HaarCarrierEqv blocks
      (globalCayleyDenominatorPolynomial extent face)
      (faceCayleyScaleProduct extent face) :=
    RatPolyCoeffEqv.haarCarrier
      (faceCayleyScaleProduct_coeff_globalDenominator extent face).symm
  have h0 := clearedCayleyFactorPolynomial_carrier_north
    (faceCayleyQuaternion0 extent face) (faceCayleyComplement0 extent face)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
  have h1 := clearedCayleyFactorPolynomial_carrier_north
    (faceCayleyQuaternion1 extent face) (faceCayleyComplement1 extent face)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
  have h2 := clearedCayleyFactorPolynomial_carrier_north
    (faceCayleyQuaternion2 extent face) (faceCayleyComplement2 extent face)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
  have h3 := clearedCayleyFactorPolynomial_carrier_north
    (faceCayleyQuaternion3 extent face) (faceCayleyComplement3 extent face)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))
  change HaarCarrierEqv blocks
    (globalCayleyDenominatorPolynomial extent face)
    (globalCayleyNorthFactorProduct extent face)
  refine hdenominator.trans ?_
  simpa [faceCayleyScaleProduct, globalCayleyNorthFactorProduct] using
    (HaarCarrierEqv.mul
      (HaarCarrierEqv.mul (HaarCarrierEqv.mul h0 h1) h2) h3)

/-- The denominator-cleared vector jet is the pure ORIGINAL vector jet
multiplied by four times the square of the explicit north-chart product. -/
theorem globalCayleyVectorJetClearedPolynomial_carrier_northWeight
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetClearedPolynomial extent face)
      (polyMul
        (polyMul (polyConst 4)
          (polyMul
            (globalCayleyNorthFactorProduct extent face)
            (globalCayleyNorthFactorProduct extent face)))
        (globalPlaquetteVectorJet extent face)) := by
  have hdenominator :=
    globalCayleyDenominatorPolynomial_carrier_northFactorProduct extent face
  unfold globalCayleyVectorJetClearedPolynomial
  exact HaarCarrierEqv.mul
    (HaarCarrierEqv.mul
      (HaarCarrierEqv.refl _ (polyConst 4))
      (HaarCarrierEqv.mul hdenominator hdenominator))
    (HaarCarrierEqv.refl _ (globalPlaquetteVectorJet extent face))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight.globalCayleyNorthFactorProduct
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight.globalCayleyDenominatorPolynomial_carrier_northFactorProduct
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight.globalCayleyVectorJetClearedPolynomial_carrier_northWeight
