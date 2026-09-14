/-
# Positive integration against the SAME full spectator OS background

Reflecting the detached lower physical face list produces an explicit upper
heat product with an ordinary positive certificate. Its product with Lfar
and the full spectator interface is pinned to theta(Lfar)*Lfar*Isp.
Consequently signed interval insertions are bounded relative to the SAME
Zsp, not a different squared-half partition. All nome guards are explicit.
No local-collar error or volume-uniform excitation floor is assumed here.
-/

import YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate
import YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
import YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def upperSpectatorHeat (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half))
    ((lowerSpectators half).map (slabFaceReflectId (centralExtent half)))

theorem lowerSpectators_physical {half id : Nat} (hi : id ∈ lowerSpectators half) :
    id ∈ slabPhysicalFaceEdges (centralExtent half) := (mem_centralLowerFaceIds.mp (detached_mem hi)).1

private theorem reflected_product (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    ReflectionImage extent (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polynomialProduct (fun id => faceHeatPolynomial w K extent (slabFaceReflectId extent id)) ids)
  | [], _ => ReflectionImage.one extent
  | id :: ids, hi => (faceHeat_reflection w K (hi id List.mem_cons_self)).mul
      (reflected_product w K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

theorem upperSpectatorHeat_image (w : Q') (K half : Nat) :
    ReflectionImage (centralExtent half) (spectatorHeat w K half) (upperSpectatorHeat w K half) := by
  simpa only [spectatorHeat, upperSpectatorHeat, polynomialProduct, List.foldr_map] using
    (reflected_product w K (centralExtent half) (lowerSpectators half) (fun _ hi => lowerSpectators_physical hi))

theorem upperSpectatorHeat_supported (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (upperSpectatorHeat w K half) := heatProduct_supported w K _ _

/-- Original integrand defining Zsp, before any reflection recoding. -/
def originalBackground (w : Q') (K half : Nat) : RatPoly :=
  polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (spectatorHeat w K half))
    (spectatorHeat w K half)) (spectatorInterface w K half)

/-- Coefficient-pinned positive presentation, not a replacement partition. -/
def positiveBackground (w : Q') (K half : Nat) : RatPoly :=
  polyMul (polyMul (upperSpectatorHeat w K half) (spectatorHeat w K half)) (spectatorInterface w K half)

theorem background_image (w : Q') (K half : Nat) :
    PaddedPolynomialCoeffEqv (blocks half) (originalBackground w K half) (positiveBackground w K half) :=
  PaddedPolynomialCoeffEqv.mul
    (PaddedPolynomialCoeffEqv.mul (upperSpectatorHeat_image w K half)
      (PaddedPolynomialCoeffEqv.refl (blocks half) (spectatorHeat w K half)))
    (PaddedPolynomialCoeffEqv.refl (blocks half) (spectatorInterface w K half))

variable {w : Q'} (hw0 : (0 : Q') ≤ w)

include hw0

theorem originalBackground_supported (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (originalBackground w K half) :=
  supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _)
    (spectatorHeat_supported w K half)) (spectatorExpansion hw0 K half).polynomialSupported

theorem positiveBackground_supported (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (positiveBackground w K half) :=
  supported_polyMul (supported_polyMul (upperSpectatorHeat_supported w K half)
    (spectatorHeat_supported w K half)) (spectatorExpansion hw0 K half).polynomialSupported

theorem background_integral_pin (K half : Nat) :
    quaternionHaar (blocks half) (positiveBackground w K half) ≈ backgroundMass w K half :=
  (background_image w K half).symm.haar (positiveBackground_supported hw0 K half)
    (originalBackground_supported hw0 K half)

variable (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)

def lowerCertificate (K half : Nat) : Certificate (blocks half) (spectatorHeat w K half) :=
  faceProductCertificate hw0 hw1 hsmall hdelta K _ _ (fun _ hi => lowerSpectators_physical hi)

def upperCertificate (K half : Nat) : Certificate (blocks half) (upperSpectatorHeat w K half) :=
  faceProductCertificate hw0 hw1 hsmall hdelta K _ _ (fun _ hi => by
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hi
    exact slabFaceReflectId_physical (lowerSpectators_physical hid))

def backgroundCertificate (K half : Nat) : Certificate (blocks half) (positiveBackground w K half) :=
  ((upperCertificate hw0 hw1 hsmall hdelta K half).mul
    (lowerCertificate hw0 hw1 hsmall hdelta K half)).mul (spectatorCertificate hw0 hw1 hsmall hdelta K half)

include hw0 hw1 hsmall hdelta

/-- Relative signed-insertion bound with the exact background of the reference minor. -/
theorem background_weighted_bound (K half : Nat) {r : RatPoly} {d : Q'} (R : Interval (blocks half) r d) :
    Q'.abs (quaternionHaar (blocks half) (polyMul (originalBackground w K half) r)) ≤
      d * backgroundMass w K half := by
  have he := ((background_image w K half).mul (.refl _ r)).haar
    (supported_polyMul (originalBackground_supported hw0 K half) R.support)
    (supported_polyMul (positiveBackground_supported hw0 K half) R.support)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ (R.weighted_haar_bound (backgroundCertificate hw0 hw1 hsmall hdelta K half))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (background_integral_pin hw0 K half))))

end YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.upperSpectatorHeat
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.lowerSpectators_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.upperSpectatorHeat_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.upperSpectatorHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.originalBackground
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.positiveBackground
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.background_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.originalBackground_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.positiveBackground_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.background_integral_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.upperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.backgroundCertificate
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground.background_weighted_bound
