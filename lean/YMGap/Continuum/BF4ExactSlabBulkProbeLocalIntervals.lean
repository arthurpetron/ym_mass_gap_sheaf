/-
# Sharp local intervals on the original probe and reflected scalar loop

A square cap of one gives a linear interval of one by the existing cross
certificate, with no square-root construction. Products of actual scalar
link coordinates keep that cap. The fundamental plaquette character has
cap two, both below and above the reflection plane. The explicit upper
scalar product is pinned to the reflection of the original lower product.
These are local Haar certificates, not interacting amplitude estimates.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
import YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

/-- The existing cross certificate gives the sharp cap, without a root oracle. -/
def unitSquareInterval {blockCount : Nat} {p : RatPoly} (P : SquareBound blockCount p 1) :
    Interval blockCount p 1 where
  support := P.support
  nonnegative := Q'.zero_le_one
  upper := .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_one p).symm))
    (P.cross (.one blockCount))
  lower := .ofCoeff ((RatPolyCoeffEqv.refl _).add
    ((coeffEvalExpr_eqv_of_normalize_eq (.var 0) (.neg (.neg (.var 0))) (by decide) (fun _ => p)).trans
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_one (polyNeg p)).symm)))
    (P.neg.cross (.one blockCount))

def scalarProductInterval (extent : Nat) : (links : List Z4Link) →
    Interval (boundaryCompleteSlabLinks extent).length (scalarProduct extent links) 1
  | [] => .one _
  | link :: links => ((unitSquareInterval (.scalar (supported_slabLink extent link)
      (slabLink_haar_unit extent link))).mul (scalarProductInterval extent links)).changeCap (by decide)

def upperScalar (half : Nat) : RatPoly :=
  scalarProduct (centralExtent half) ((probeLinks half).map (timeReflectLink (centralExtent half)))

def bulkScalarInterval (half : Nat) : Interval (blocks half) (bulkScalar half) 1 := scalarProductInterval _ _
def upperScalarInterval (half : Nat) : Interval (blocks half) (upperScalar half) 1 := scalarProductInterval _ _

theorem probeLinks_physical {half : Nat} {link : Z4Link} (hi : link ∈ probeLinks half) :
    link ∈ boundaryCompleteSlabLinks (centralExtent half) := by
  rw [← crossingIds_links] at hi
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hi
  exact faceLinkA_physical (slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp (crossingIds_fixed hid)).1)

theorem probeLinks_spatial {half : Nat} {link : Z4Link} (hi : link ∈ probeLinks half) : link.2 ≠ .x3 := by
  rw [← crossingIds_links] at hi
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp hi
  exact faceLinkA_spatial _

theorem scalarProduct_reflection (extent : Nat) : ∀ links : List Z4Link,
    (∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) →
    (∀ link, link ∈ links → link.2 ≠ .x3) →
    ReflectionImage extent (scalarProduct extent links) (scalarProduct extent (links.map (timeReflectLink extent)))
  | [], _, _ => ReflectionImage.one _
  | link :: links, hp, hs =>
      ReflectionImage.mul (spatial_link_reflection (hp link List.mem_cons_self) (hs link List.mem_cons_self)).scalar
        (scalarProduct_reflection extent links (fun l hl => hp l (List.mem_cons_of_mem link hl))
          (fun l hl => hs l (List.mem_cons_of_mem link hl)))

theorem upperScalar_image (half : Nat) : ReflectionImage (centralExtent half) (bulkScalar half) (upperScalar half) :=
  scalarProduct_reflection _ _ (fun _ hi => probeLinks_physical hi) (fun _ hi => probeLinks_spatial hi)

def fundamentalInterval (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar 1) 2 :=
  (Interval.smul 2 (by decide) (unitSquareInterval (.scalar (supported_slabPlaquette extent _)
    (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi))))).changeCap (by decide)

def probeInterval (half : Nat) : Interval (blocks half) (lower (bulkProbe half)) 2 :=
  fundamentalInterval (centralExtent half) (translatedId half 0)
    (mem_centralLowerFaceIds.mp (probeId_translated_lower half)).1

def upperProbeInterval (half : Nat) : Interval (blocks half) (upper (bulkProbe half)) 2 :=
  fundamentalInterval (centralExtent half) (slabFaceReflectId (centralExtent half) (translatedId half 0))
    (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp (probeId_translated_lower half)).1)

end YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.unitSquareInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.scalarProductInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.upperScalar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.bulkScalarInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.upperScalarInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.probeLinks_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.probeLinks_spatial
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.scalarProduct_reflection
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.upperScalar_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.fundamentalInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.probeInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals.upperProbeInterval
