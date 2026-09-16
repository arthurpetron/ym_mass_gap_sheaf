/-
# Positive order bounds for the actual fixed-spatial potential

The literal width-only ordered plaquette words are supported and Haar-unit
in every product-quaternion carrier with room for the source slice. In
particular these witnesses apply directly to the head potential on the
N+N pair carrier, without a separate certificate-lifting assumption.

The existing all-nome heat certificates supply positivity at every late
cutoff and the cutoff-independent cap prefixCap^numberOfSpatialFaces.
All factors use their original shared coordinates. These are finite Haar
certificate bounds, not pointwise evaluation claims, a stationary measure,
an OS operator bound, or width- or spacing-uniform control.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem link_supported (width blocks : Nat) (hroom : N width ≤ blocks)
    (l : Z4Link) : Supported blocks (link width l) := by
  unfold link
  split
  · have hi := List.idxOf_lt_length_of_mem ‹l ∈ baseLinks width›
    exact Supported.coordinate (Nat.lt_of_lt_of_le hi hroom)
  · exact Supported.one blocks

private theorem oriented_supported (width blocks : Nat) (hroom : N width ≤ blocks)
    (entry : OrientedBF4Link) : Supported blocks (orientedLink width entry) := by
  unfold orientedLink
  split
  · exact (link_supported width blocks hroom entry.link).conj
  · exact link_supported width blocks hroom entry.link

private theorem word_supported (width blocks : Nat) (hroom : N width ≤ blocks) :
    ∀ (entries : List OrientedBF4Link) (initial : PolyQuaternion),
      Supported blocks initial → Supported blocks
        (entries.foldl (fun total entry => PolyQuaternion.mul total (orientedLink width entry)) initial)
  | [], _, h => h
  | entry::entries, _, h => word_supported width blocks hroom entries _
      (h.mul (oriented_supported width blocks hroom entry))

/-- Support of the source's literal ordered word in any carrier with enough room.
The defined identity fallback is included, so no extra face premise is needed. -/
theorem plaquette_supported (width blocks : Nat) (hroom : N width ≤ blocks)
    (face : Z4Plaq) : Supported blocks (plaquette width face) :=
  word_supported width blocks hroom (orientedPlaquetteBoundary face)
    PolyQuaternion.one (Supported.one blocks)

private theorem link_unit (width blocks : Nat) (hroom : N width ≤ blocks)
    (l : Z4Link) : HaarCarrierEqv blocks (polyQuaternionNorm (link width l)) polyOne := by
  unfold link
  split
  · have hi := List.idxOf_lt_length_of_mem ‹l ∈ baseLinks width›
    exact haarNorm_coordinate (Nat.lt_of_lt_of_le hi hroom)
  · exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one

private theorem oriented_unit (width blocks : Nat) (hroom : N width ≤ blocks)
    (entry : OrientedBF4Link) :
    HaarCarrierEqv blocks (polyQuaternionNorm (orientedLink width entry)) polyOne := by
  unfold orientedLink
  split
  · exact HaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
      (link_unit width blocks hroom entry.link)
  · exact link_unit width blocks hroom entry.link

/-- Unit norm under every Haar insertion on the same enlarged source carrier.
The noncommutative ordered word is unchanged. -/
theorem plaquette_unit (width blocks : Nat) (hroom : N width ≤ blocks)
    (face : Z4Plaq) : HaarCarrierEqv blocks (polyQuaternionNorm (plaquette width face)) polyOne :=
  haarNorm_fold (orientedLink width) (orientedPlaquetteBoundary face)
    (fun entry _ => oriented_unit width blocks hroom entry)
    PolyQuaternion.one (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one)

def faceCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width blocks : Nat) (hroom : N width ≤ blocks) (face : Z4Plaq)
    (hK : headCutoff w ≤ K) :
    Certificate blocks (heatPrefix w K (plaquette width face).scalar) :=
  QuaternionHaarAllNomeHeatCertificate.prefixCertificate hw0 hw1
    (plaquette_supported width blocks hroom face) (plaquette_unit width blocks hroom face) K hK

/-- The absolute face cap needs no lower bound on the finite cutoff. -/
def faceInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width blocks : Nat) (hroom : N width ≤ blocks) (face : Z4Plaq) :
    Interval blocks (heatPrefix w K (plaquette width face).scalar) (prefixCap w) :=
  QuaternionHaarAllNomeHeatCertificate.prefixInterval hw0 hw1
    (SquareBound.scalar (plaquette_supported width blocks hroom face)
      (plaquette_unit width blocks hroom face)) K

private def productCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width blocks : Nat) (hroom : N width ≤ blocks) (hK : headCutoff w ≤ K) :
    (faces : List Z4Plaq) → Certificate blocks
      (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces)
  | [] => .one blocks
  | face::faces => (faceCertificate hw0 hw1 K width blocks hroom face hK).mul
      (productCertificate hw0 hw1 K width blocks hroom hK faces)

/-- Positivity of the complete actual spatial potential, including on the
two-slice head carrier. The threshold is exactly the existing headCutoff. -/
def spatialCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width blocks : Nat) (hroom : N width ≤ blocks) (hK : headCutoff w ≤ K) :
    Certificate blocks (spatialWeight w K width) :=
  productCertificate hw0 hw1 K width blocks hroom hK (spatialFaces width)

/-- Cutoff-independent absolute cap with the literal spatial-face count.
Overlapping links are retained by the product certificate. -/
def spatialInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width blocks : Nat) (hroom : N width ≤ blocks) :
    Interval blocks (spatialWeight w K width) ((prefixCap w)^(spatialFaces width).length) :=
  Interval.productUniform _ (prefixCap w) (spatialFaces width)
    (fun face _ => faceInterval hw0 hw1 K width blocks hroom face)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder.plaquette_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder.plaquette_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder.faceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder.faceInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder.spatialCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder.spatialInterval
