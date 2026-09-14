/-
# Ordinary positive certificates for the actual spatial Gram heat product

Each original reflected spatial Gram character is the character of the
literal two-link unit quaternion word, under EVERY Haar insertion. The
small-nome heat certificate therefore transports to the actual Gram heat
factor. Multiplication retains all shared variables and all spectator faces.

This is stronger than nonnegativity of reflected pairings: arbitrary
positive-certificate insertions may be used. The explicit nome guards
remain. No collar perturbation or normalized excitation floor is asserted.
-/

import YMGap.Continuum.QuaternionHaarHeatCertificate
import YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization

namespace YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep

/-- Original lower link times the conjugate of its actual reflected link. -/
def spatialWord (extent : Nat) (link : Z4Link) : PolyQuaternion :=
  PolyQuaternion.mul (correctedSlabLinkPolynomial extent link)
    (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (timeReflectLink extent link)))

theorem spatialWord_supported (extent : Nat) (link : Z4Link) :
    Supported (boundaryCompleteSlabLinks extent).length (spatialWord extent link) :=
  (supported_slabLink extent link).mul (supported_slabLink extent _).conj

theorem spatialWord_unit (extent : Nat) (link : Z4Link) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (spatialWord extent link)) polyOne :=
  haarNorm_mul (slabLink_haar_unit extent link)
    (QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
      (slabLink_haar_unit extent _))

def spatialScalarBound (extent : Nat) (link : Z4Link) :
    SquareBound (boundaryCompleteSlabLinks extent).length (spatialWord extent link).scalar 1 :=
  .scalar (spatialWord_supported extent link) (spatialWord_unit extent link)

/-- All representation degrees, arbitrary insertions, same link coordinates. -/
theorem spatialCharacter_pin (extent : Nat) (link : Z4Link) (n : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (spatialWord extent link).scalar n)
      (reflectedSpatialLinkGram extent link n).1 := by
  have h := character_haar_gram_of_unit_radii
    (asRepresentationQuaternion (correctedSlabLinkPolynomial extent (timeReflectLink extent link)))
    (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link))
    (slabLink_haar_unit extent (timeReflectLink extent link))
    (slabLink_haar_unit extent link) n
  have hs := characterPolynomial_coeffEqv (pathProduct_scalar
      (correctedSlabLinkPolynomial extent (timeReflectLink extent link))
      (correctedSlabLinkPolynomial extent link)) n
  exact QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier hs) h.1

private theorem sum_row {A : Type} {blocks : Nat} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionHaarCarrierEqv blocks (f a) (g a)) →
    QuaternionHaarCarrierEqv blocks (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => QuaternionHaarCarrierEqv.refl _ _
  | a :: xs, h => QuaternionHaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem faceHeat_pin (w : Q') (K half id : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (faceHeatPolynomial w K half id)
      (heatPrefix w K (spatialWord (centralExtent half)
        (faceLinkA (slabPlaquetteAt (centralExtent half) id))).scalar) := by
  apply sum_row
  intro n hn
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hn)]
  exact QuaternionHaarCarrierEqv.smul _ (QuaternionHaarCarrierEqv.symm (spatialCharacter_pin _ _ n))

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)

/-- Positivity of the actual original Gram heat factor at every cutoff. -/
def spatialFaceCertificate (K half id : Nat) :
    Certificate (boundaryCompleteSlabLinks (centralExtent half)).length (faceHeatPolynomial w K half id) :=
  .transport (faceHeat_pin w K half id)
    (prefixCertificate hw0 hw1 hsmall hdelta (spatialScalarBound _ _) K)

def spatialProductCertificate (K half : Nat) : (ids : List Nat) →
    Certificate (boundaryCompleteSlabLinks (centralExtent half)).length
      (polynomialProduct (faceHeatPolynomial w K half) ids)
  | [] => .one _
  | id :: ids => (spatialFaceCertificate hw0 hw1 hsmall hdelta K half id).mul
      (spatialProductCertificate K half ids)

/-- Every unselected face retains its FULL heat prefix and shared links. -/
def spectatorCertificate (K half : Nat) :
    Certificate (boundaryCompleteSlabLinks (centralExtent half)).length (spectatorInterface w K half) :=
  spatialProductCertificate hw0 hw1 hsmall hdelta K half (spectatorIds half)

end YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate

#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialWord
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialWord_supported
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialWord_unit
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialScalarBound
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialCharacter_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.faceHeat_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialFaceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spatialProductCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate.spectatorCertificate
