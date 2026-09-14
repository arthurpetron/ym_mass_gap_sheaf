/-
# Retain the exact scalar-square mass in the positive spectator background

The lower scalar square stays inside the positive integration certificate.
Its mass is exactly Zsp/256 by the original spectator factorization, at
every cutoff and translated volume. Signed interval insertions are bounded
relative to this smaller mass, preserving the scalar signal's normalization.
No interacting determinant sign or thermodynamic excitation is asserted.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
import YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference

namespace YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

private def env4 (a b c d : RatPoly) : Nat → RatPoly
  | 0 => a | 1 => b | 2 => c | _ => d

private theorem reorder (a b c d : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul a b) c) d) (polyMul (polyMul a (polyMul d b)) c) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
    (.mul (.mul (.var 0) (.mul (.var 3) (.var 1))) (.var 2)) (by decide) (env4 a b c d)

variable {w : Q'} (hw : (0 : Q') ≤ w)
include hw

/-- Every supported local lower insertion factors against the SAME positive presentation. -/
theorem background_local_moment (K half : Nat) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (blocks half) q) (hlq : LinkLocal (centralExtent half) (probeLinks half) q) :
    quaternionHaar (blocks half) (polyMul (positiveBackground w K half) q) ≈
      quaternionHaar (blocks half) q * backgroundMass w K half := by
  have hp := ((background_image w K half).symm.mul (PaddedPolynomialCoeffEqv.refl (blocks half) q)).haar
    (supported_polyMul (positiveBackground_supported hw K half) hq)
    (supported_polyMul (originalBackground_supported hw K half) hq)
  have hr : quaternionHaar (blocks half) (polyMul (originalBackground w K half) q) ≈
      spectatorPair w K half (spectatorHeat w K half) (polyMul q (spectatorHeat w K half)) :=
    haar_of_coeff (reorder _ _ _ _)
  have hf := Q'.eqv_trans _ _ _
    (spectatorPair_coeff w K half (RatPolyCoeffEqv.one_mul (spectatorHeat w K half)).symm (RatPolyCoeffEqv.refl _))
    (detached_pair_factor hw K half (supported_one _) hq (BlockLocal.one _ _) hlq)
  have hc : (quaternionHaar (blocks half) polyOne * quaternionHaar (blocks half) q) ≈ quaternionHaar (blocks half) q :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (haar_one _)) (Q'.one_mul_eqv _)
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ hr
    (Q'.eqv_trans _ _ _ hf (Q'.mul_eqv_congr_right _ _ _ hc)))

def scalarBackground (w : Q') (K half : Nat) : RatPoly :=
  polyMul (positiveBackground w K half) (polyMul (bulkScalar half) (bulkScalar half))

theorem scalarBackground_supported (K half : Nat) : SupportedQuaternionBlocks (blocks half) (scalarBackground w K half) :=
  supported_polyMul (positiveBackground_supported hw K half)
    (supported_polyMul (bulkScalar_supported half) (bulkScalar_supported half))

theorem scalarBackground_mass (K half : Nat) :
    quaternionHaar (blocks half) (scalarBackground w K half) ≈ Q'.invSucc 255 * backgroundMass w K half :=
  Q'.eqv_trans _ _ _
    (background_local_moment hw K half (supported_polyMul (bulkScalar_supported half) (bulkScalar_supported half))
      ((bulkScalar_local half).mul (bulkScalar_local half)))
    (Q'.mul_eqv_congr_right _ _ _ (bulkScalar_square_haar half))

variable (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)

def scalarBackgroundCertificate (K half : Nat) : Certificate (blocks half) (scalarBackground w K half) :=
  (backgroundCertificate hw hw1 hsmall hdelta K half).mul (.square (bulkScalar half) (bulkScalar_supported half))

include hw1 hsmall hdelta

/-- The exact 1/256 survives before any absolute bound on the remaining insertion. -/
theorem scalar_weighted_bound (K half : Nat) {r : RatPoly} {d : Q'} (R : Interval (blocks half) r d) :
    Q'.abs (quaternionHaar (blocks half) (polyMul (scalarBackground w K half) r)) ≤
      d * (Q'.invSucc 255 * backgroundMass w K half) :=
  Q'.le_trans' _ _ _ (R.weighted_haar_bound (scalarBackgroundCertificate hw hw1 hsmall hdelta K half))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (scalarBackground_mass hw K half)))

end YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground.background_local_moment
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground.scalarBackground
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground.scalarBackground_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground.scalarBackground_mass
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground.scalarBackgroundCertificate
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground.scalar_weighted_bound
