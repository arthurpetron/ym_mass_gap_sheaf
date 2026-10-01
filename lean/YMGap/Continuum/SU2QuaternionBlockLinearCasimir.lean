/-
# The degree-one Casimir at an arbitrary quaternion block

The head-block linear eigenaction transports through the explicit head swap.
All equalities are on the same finite Haar carrier, under arbitrary polynomial
insertions. The source support and in-range guards make the reindexing honest.
-/

import YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
import YMGap.Continuum.BF4ExactSlabSelectedFaceFold

namespace YMGap.Continuum.SU2QuaternionBlockLinearCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier

/-- On any in-range block, a polynomial of exact block degree one has
positive Casimir eigenvalue three on the original arbitrary-insertion Haar
carrier. No harmonicity or heat-eigenfunction hypothesis is required. -/
theorem blockCasimir_linear {blocks block : Nat} (hblock : block < blocks)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hdegree : HasQuaternionBlockDegree block 1 p) :
    HaarCarrierEqv blocks (blockAngularLaplacian block p)
      (polySmul (-3) p) := by
  let s := headSwapBlockInvolution blocks block hblock
  let q := reindexQuaternionPolynomial s p
  have hzero : 0 < blocks := by omega
  have hs0 : s.map 0 = block :=
    headSwapBlockInvolution_map_zero blocks block hblock
  have hsb : s.map block = 0 :=
    headSwapBlockInvolution_map_selected blocks block hblock
  have hq : SupportedQuaternionBlocks blocks q := reindex_supported s p
  have hdq : HasQuaternionBlockDegree 0 1 q :=
    blockDegree_reindex s hzero hs0 hdegree
  have hhead : HaarCarrierEqv blocks
      (blockAngularLaplacian 0 q) (polySmul (-3) q) := by
    have he := linear_angularLaplacian hzero q hdq
    exact (RatPolyCoeffEqv.haarCarrier
      (blockAngularLaplacian_eq_six 0 q)).trans (by
        simpa only [angularLaplacian, six, blockAngularDerivative,
          Nat.mul_zero, Nat.zero_add] using he)
  have hback : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s q) p :=
    carrierOfPrefix (reindex_supported s q) hp (reindex_twice_prefix s p)
  have htransport : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s (blockAngularLaplacian 0 q))
      (blockAngularLaplacian block (reindexQuaternionPolynomial s q)) := by
    simpa only [hsb] using
      (reindex_blockAngularLaplacian_carrier s hblock q hq)
  have hlinear := reindex_carrier s
    (blockAngularLaplacian_supported hzero hq)
    (polySmul_supported hq (-3)) hhead
  have hright : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s (polySmul (-3) q))
      (polySmul (-3) p) := by
    rw [reindexQuaternionPolynomial_smul]
    exact HaarCarrierEqv.smul (-3) hback
  exact (blockAngularLaplacian_carrier hblock hback).symm.trans
    (htransport.symm.trans (hlinear.trans hright))

end YMGap.Continuum.SU2QuaternionBlockLinearCasimir

#print axioms YMGap.Continuum.SU2QuaternionBlockLinearCasimir.blockCasimir_linear
