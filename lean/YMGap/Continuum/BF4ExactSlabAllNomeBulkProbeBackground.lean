/-
# All-nome integration against the original bulk-probe spectator background

For every rational 0 < w < 1 and K >= headCutoff(w), the original lower
spectator heat product, its reflected upper product, and the unchanged
spatial spectator interface all have positive Haar certificates. Their
product is the existing positiveBackground, coefficient-pinned to the
existing originalBackground and its exact backgroundMass.

The signed-insertion estimate below therefore removes the old small-nome
guards from this background step. It neither changes the reference law
nor supplies collar perturbation smallness, centered decay, or an OS gap.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate
import YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground

namespace YMGap.Continuum.BF4ExactSlabAllNomeBulkProbeBackground

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Original lower physical spectators, at the explicit all-nome cutoff. -/
def lowerCertificate (K half : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (spectatorHeat w K half) :=
  headProduct_certificate hw0 hw1 K _ hK _ (fun _ hi => lowerSpectators_physical hi)

/-- Literal reflected upper spectators, with the same nome and cutoff. -/
def upperCertificate (K half : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (upperSpectatorHeat w K half) :=
  headProduct_certificate hw0 hw1 K _ hK _ (fun _ hi => by
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hi
    exact slabFaceReflectId_physical (lowerSpectators_physical hid))

/-- The existing full positive presentation, not a replacement background. -/
def backgroundCertificate (K half : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (positiveBackground w K half) :=
  ((upperCertificate hw0 hw1 K half hK).mul
    (lowerCertificate hw0 hw1 K half hK)).mul
      (BF4ExactSlabAllNomeSpatialHeatCertificate.spectatorCertificate hw0 hw1 K half hK)

include hw0 hw1 in
/-- Relative signed insertion against the SAME exact background mass. The
interval's radius is supplied explicitly; no collar smallness is asserted. -/
theorem background_weighted_bound (K half : Nat) (hK : headCutoff w ≤ K)
    {r : RatPoly} {d : Q'} (R : Interval (blocks half) r d) :
    Q'.abs (quaternionHaar (blocks half) (polyMul (originalBackground w K half) r)) ≤
      d * backgroundMass w K half := by
  have he := ((background_image w K half).mul (.refl _ r)).haar
    (supported_polyMul (originalBackground_supported (Q'.le_of_lt hw0) K half) R.support)
    (supported_polyMul (positiveBackground_supported (Q'.le_of_lt hw0) K half) R.support)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ (R.weighted_haar_bound (backgroundCertificate hw0 hw1 K half hK))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (background_integral_pin (Q'.le_of_lt hw0) K half))))

end YMGap.Continuum.BF4ExactSlabAllNomeBulkProbeBackground

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeBulkProbeBackground.lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeBulkProbeBackground.upperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeBulkProbeBackground.backgroundCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeBulkProbeBackground.background_weighted_bound
