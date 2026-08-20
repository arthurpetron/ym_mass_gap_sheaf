/-
M2e -- connect the existing non-abelian physical-rate bridge to the exact
constructive logarithmic rate layer.

`NonAbelianGapChain.PhysicalRateBridge` already carries a physical separator,
positive spacing, gauge-invariant correlator control, and a two-sided rational
margin-rate bound.  `PhysicalSeparatorLogRate` turns exactly those data into a
finite positive band for `-log(q_j)/a_j`, provided the currently direct artanh
window is supplied.

This file records that composition.  It does not prove the sharp rate fields in
`PhysicalRateBridge`, construct its uniform LSI datum, or remove the named log
window/range-reduction input.
-/

import YMGap.Continuum.NonAbelianGapChain
import YMGap.Continuum.PhysicalSeparatorLogRate

namespace YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate

/-- The spacing component of a non-abelian physical-rate bridge, packaged for
the exact logarithmic layer. -/
def exactPhysicalSpacing (B : PhysicalRateBridge) : PhysicalSpacing where
  spacing := B.spacing
  spacing_pos := B.spacing_pos

/-- The exact constructive rate family `-log(q_j)/a_j` attached to the same
physical separator and spacing already carried by the bridge. -/
def exactLogRateFamily (B : PhysicalRateBridge)
    (W : PhysicalLogWindow B.physicalSeparator) :
    ExactPhysicalLogRateFamily B.physicalSeparator :=
  exactRateFamilyOfPhysicalData
    B.physicalSeparator B.spacing B.spacing_pos W

/-- A `PhysicalRateBridge` with the direct log window supplies the complete
exact M2 separator certificate.  The lower constant remains `floorConst`; the
constructive logarithm comparison enlarges the upper constant by `9/4`. -/
def exactPhysicalSeparatorCertificate (B : PhysicalRateBridge)
    (W : PhysicalLogWindow B.physicalSeparator) :
    ExactPhysicalSeparatorCertificate :=
  exactPhysicalSeparatorCertificateOfPhysicalGapFloor
    B.physicalSeparator B.spacing B.spacing_pos W B.physicalGapFloor

@[simp] theorem exactPhysicalSeparatorCertificate_separator
    (B : PhysicalRateBridge)
    (W : PhysicalLogWindow B.physicalSeparator) :
    (B.exactPhysicalSeparatorCertificate W).separator =
      B.physicalSeparator :=
  rfl

@[simp] theorem exactPhysicalSeparatorCertificate_floor
    (B : PhysicalRateBridge)
    (W : PhysicalLogWindow B.physicalSeparator) :
    (B.exactPhysicalSeparatorCertificate W).uniformBand.floor =
      B.floorConst :=
  rfl

@[simp] theorem exactPhysicalSeparatorCertificate_ceiling
    (B : PhysicalRateBridge)
    (W : PhysicalLogWindow B.physicalSeparator) :
    (B.exactPhysicalSeparatorCertificate W).uniformBand.ceiling =
      YMGap.Continuum.EffMassConvergence.c94 * B.ceilConst :=
  rfl

end YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge

#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.exactPhysicalSpacing
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.exactLogRateFamily
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.exactPhysicalSeparatorCertificate
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.exactPhysicalSeparatorCertificate_separator
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.exactPhysicalSeparatorCertificate_floor
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.exactPhysicalSeparatorCertificate_ceiling
