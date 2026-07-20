/-
# Exact outward elementary-cube trace network

The preceding face-product bridge identifies, for every opaque vertex-major
Boolean assignment, the product of six orientation-specific plaquette trace
summands with the exact twelve-link Schur-delta value after finite-product
Haar.  This leaf lifts that pointwise theorem through the structural
depth-twenty-four Boolean sum and obtains the exact value `1/16`.

The recursive sum is never unfolded at depth twenty four.  This network is
the honest outward-oriented sum of the fixed-assignment trace products;
identifying it with a product of six four-binder trace expansions, and then
replacing the three reversed faces by canonical-standard representatives,
remain separate tasks.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge
import YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution

namespace YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceNetwork

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge
open YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

/-- The honest outward-oriented cube network, summed in the established
vertex-major tag assignment.  Keep this definition opaque at depth twenty
four. -/
def radiusZeroElementaryCubeOutwardTraceNetwork : ComplexRatPoly :=
  complexRatPolyBoolSum 24
    radiusZeroElementaryCubeOutwardFaceTraceProduct

/-- Haar linearity and the pointwise six-face theorem reduce the outward
network to the already resolved symbolic delta sum. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_schurDeltaSum :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceNetwork)
      (rationalComplexBoolSum 24
        radiusZeroElementaryCubeSchurDeltaValue) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_boolSum
      (adjacentEvenActiveLinks 0).length 24
      radiusZeroElementaryCubeOutwardFaceTraceProduct)
    (rationalComplexBoolSum_congr 24 (fun assignment =>
      finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_schurDeltaValue
        assignment))

/-- The honest outward trace network and the earlier right-local paired
network have the same exact finite-product Haar value. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_pairedTraceNetwork :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceNetwork)
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubePairedTraceNetwork) :=
  rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_schurDeltaSum
    (rationalComplexEqv_symm
      finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork)

/-- **Exact outward cube-network integral.**  The fully summed six-face
outward fundamental trace network defined above has finite-product Haar value
`1/16`.  This is not yet the canonical-standard production representative. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_exact :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceNetwork)
      (Q'.mkPos 1 16 (by decide), 0) :=
  rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_schurDeltaSum
    rationalComplexBoolSum_radiusZeroElementaryCubeSchurDeltaValue_exact

#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_schurDeltaSum
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_pairedTraceNetwork
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_exact

end YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceNetwork
