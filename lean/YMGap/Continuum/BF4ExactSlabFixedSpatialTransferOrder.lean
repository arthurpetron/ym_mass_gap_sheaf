/-
# The actual fixed-spatial transfer preserves certified polynomial order

Enlarge only supported input messages to the actual two-slice carrier,
multiply by the original positive K*V weight, and integrate its head blocks.
Both enlargement and Haar certificate preservation are proved constructions.
The same result iterates with the exact original finite-time ordering.

This is preservation of the polynomial positive cone, not a positive
semidefinite operator, strict contraction, stationary law or OS identification.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Original T preserves actual certificates; support is essential for enlargement. -/
def transferStep_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (F : Certificate (N width) f) :
    Certificate (N width) (transferStep w K width f) :=
  Certificate.ofCoeff (transferStep_kernelMap w K width f)
    (partialHaarHeads_certificate (N width) (N width)
      ((stepWeightCertificate hw0 hw1 K width hK).mul (certificate_extend (N width) hf F)))

private theorem support_smul {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c f) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hf s hs

/-- The existing same-carrier order comparison is preserved, without a scalar inequality oracle. -/
def transferStep_monotone {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (F : Certificate (N width) (polyAdd g (polySmul (-1) f))) :
    Certificate (N width)
      (polyAdd (transferStep w K width g) (polySmul (-1) (transferStep w K width f))) :=
  Certificate.ofCoeff
    ((transferStep_add w K width g (polySmul (-1) f)).trans
      ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width (-1) f))).symm
    (transferStep_certificate hw0 hw1 K width hK (supported_add hg (support_smul hf (-1))) F)

/-- Every actual finite K/V iterate remains certified positive on the same slice carrier. -/
def iterateStep_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (steps : Nat) → (f : RatPoly) → SupportedQuaternionBlocks (N width) f →
      Certificate (N width) f → Certificate (N width)
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps f)
  | 0, _, _, F => F
  | steps+1, f, hf, F =>
      iterateStep_certificate hw0 hw1 K width hK steps (transferStep w K width f)
        (transferStep_supported w K width hf) (transferStep_certificate hw0 hw1 K width hK hf F)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder.transferStep_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder.transferStep_monotone
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder.iterateStep_certificate
