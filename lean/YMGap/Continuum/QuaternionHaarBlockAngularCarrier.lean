/-
# Angular derivatives at arbitrary quaternion blocks in the Haar carrier

The reindex equality is a prefix-polynomial equality only. Both sides are
supported before it is promoted to equality under every Haar insertion.
-/

import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.QuaternionHaarBlockAngularCarrier

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.QuaternionHaarAngularCarrier

/-- A derivative at any in-range quaternion block stays in the finite
carrier. -/
theorem blockAngularDerivative_supported {blocks block i j : Nat}
    (hb : block < blocks) (hi : i < 4) (hj : j < 4)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (blockAngularDerivative block i j p) := by
  unfold blockAngularDerivative
  exact angularDerivative_supported_at (by omega) (by omega) hp

/-- Tangential differentiation at an arbitrary block preserves equality
under every insertion in the original Haar carrier. -/
theorem blockAngularDerivative_carrier {blocks block i j : Nat}
    (hb : block < blocks) (hi : i < 4) (hj : j < 4)
    {p q : RatPoly} (_hp : SupportedQuaternionBlocks blocks p)
    (_hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (blockAngularDerivative block i j p)
      (blockAngularDerivative block i j q) := by
  exact angularDerivative_carrier_at hb hi hj h

/-- Padded-safe angular transport through an explicit quaternion-block
involution. This is not a raw coefficient equality. -/
theorem reindex_blockAngularDerivative_carrier {blocks block i j : Nat}
    (s : QuaternionBlockInvolution blocks) (hb : block < blocks)
    (hi : i < 4) (hj : j < 4) (p : RatPoly)
    (_hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularDerivative (s.map block) i j p))
      (blockAngularDerivative block i j (reindexQuaternionPolynomial s p)) := by
  apply carrierOfPrefix
  · exact reindex_supported s _
  · exact blockAngularDerivative_supported hb hi hj (reindex_supported s p)
  · exact reindex_blockAngularDerivative_prefix s hb hi hj p

end YMGap.Continuum.QuaternionHaarBlockAngularCarrier

#print axioms YMGap.Continuum.QuaternionHaarBlockAngularCarrier.blockAngularDerivative_supported
#print axioms YMGap.Continuum.QuaternionHaarBlockAngularCarrier.blockAngularDerivative_carrier
#print axioms YMGap.Continuum.QuaternionHaarBlockAngularCarrier.reindex_blockAngularDerivative_carrier
