/-
# Positive conditional heat after actual finite-input saturation

A fixed prefix need not be a positive kernel near nome one. For a supported
polynomial whose finite modes are retained, its actual conditional image is
unchanged on passing to a computed larger positive prefix. Integrating that
prefix's concrete certificate constructs a certificate of the ORIGINAL
image, including arbitrary dependence on the already-existing output link.
This is pointwise at a strict nome; no uniform positive prefix up to one,
conditional variance inequality or changing-source cutoff is asserted.
-/

import YMGap.Continuum.SU2QuaternionConditionalHeatSaturation
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension

namespace YMGap.Continuum.SU2QuaternionConditionalHeatPositiveSaturation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData (relativeHeat_supported)
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction (relativeHeat_certificate)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion (modeCutoff)
open YMGap.Continuum.SU2QuaternionConditionalHeatSaturation
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHead_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate

/-- Computed strict-nome prefix: every source mode and the positive-kernel
onset are retained. It can depend on nome, and is not bounded up to one. -/
def positivePrefix (u : Q') (K : Nat) : Nat := max (headCutoff u) K

/-- Concrete positivity of the actual saturated conditional map. The input
certificate is transported only through equality under EVERY surviving
insertion, not through a fresh-output identification. -/
def conditionalHeat_saturated_certificate (tail : Nat) (ht : 0 < tail)
    (u : Q') (hu0 : (0 : Q') < u) (hu1 : u < (1 : Q'))
    (K : Nat) {p : RatPoly} (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : modeCutoff (tail+1) p ≤ K) (P : Certificate (tail+1) p) :
    Certificate tail (conditionalHeat u K p) := by
  let L := positivePrefix u K
  have hlarge : headCutoff u ≤ L := Nat.le_max_left _ _
  have hsource : modeCutoff (tail+1) p ≤ L := Nat.le_trans hK (Nat.le_max_right _ _)
  have hb : 2+(tail-1) = tail+1 := by omega
  have H : Certificate (tail+1) (relativeHeat u L) := by
    simpa only [hb] using certificate_extend (tail-1)
      (relativeHeat_supported u L) (relativeHeat_certificate hu0 hu1 L hlarge)
  have C : Certificate tail (conditionalHeat u L p) :=
    partialHaarHead_certificate tail (H.mul P)
  exact .transport (conditionalHeat_cutoff_stable tail ht u K L p hp hK hsource) C

end YMGap.Continuum.SU2QuaternionConditionalHeatPositiveSaturation

#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatPositiveSaturation.positivePrefix
#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatPositiveSaturation.conditionalHeat_saturated_certificate
