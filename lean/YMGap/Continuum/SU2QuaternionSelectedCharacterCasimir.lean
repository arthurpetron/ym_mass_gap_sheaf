/-
# Selected-block transport for the relative-character Casimir

The reindexing API gives a prefix identity for one angular derivative.  After
support is checked, that identity is an arbitrary-insertion Haar carrier; the
selected-block integration-by-parts carrier theorem differentiates it a
second time.  Summing the six planes transports the literal block Laplacian.
-/

import YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
import YMGap.Continuum.SU2QuaternionChannelCasimirLocality
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier

private theorem six_carrier {blocks : Nat} {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → HaarCarrierEqv blocks (f i j) (g i j)) :
    HaarCarrierEqv blocks (six f) (six g) := by
  unfold six
  exact HaarCarrierEqv.add (h 0 1 (by decide) (by decide))
    (HaarCarrierEqv.add (h 0 2 (by decide) (by decide))
      (HaarCarrierEqv.add (h 0 3 (by decide) (by decide))
        (HaarCarrierEqv.add (h 1 2 (by decide) (by decide))
          (HaarCarrierEqv.add (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

/-- Literal selected-block Laplacians preserve arbitrary-insertion carrier
equality. -/
theorem blockAngularLaplacian_carrier {blocks block : Nat}
    (hblock : block < blocks) {p q : RatPoly}
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (blockAngularLaplacian block p)
      (blockAngularLaplacian block q) := by
  have hs : HaarCarrierEqv blocks
      (six fun i j => blockAngularDerivative block i j
        (blockAngularDerivative block i j p))
      (six fun i j => blockAngularDerivative block i j
        (blockAngularDerivative block i j q)) :=
    six_carrier (fun i j hi hj =>
      angularDerivative_carrier_at hblock hi hj
        (angularDerivative_carrier_at hblock hi hj h))
  exact (RatPolyCoeffEqv.haarCarrier
      (blockAngularLaplacian_eq_six block p)).trans
    (hs.trans (RatPolyCoeffEqv.haarCarrier
      (blockAngularLaplacian_eq_six block q).symm))

private theorem reindex_secondAngular_carrier
    {blocks block i j : Nat} (s : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) (hi : i < 4) (hj : j < 4)
    (p : RatPoly) (_hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularDerivative (s.map block) i j
          (blockAngularDerivative (s.map block) i j p)))
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j
          (reindexQuaternionPolynomial s p))) := by
  have hpOuter := reindex_blockAngularDerivative_prefix s hblock hi hj
    (blockAngularDerivative (s.map block) i j p)
  have hcOuter : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularDerivative (s.map block) i j
          (blockAngularDerivative (s.map block) i j p)))
      (blockAngularDerivative block i j
        (reindexQuaternionPolynomial s
          (blockAngularDerivative (s.map block) i j p))) := by
    apply carrierOfPrefix
    · exact reindex_supported s _
    · exact angularDerivative_supported_at (by omega) (by omega)
        (reindex_supported s _)
    · exact hpOuter
  have hpInner := reindex_blockAngularDerivative_prefix s hblock hi hj p
  have hcInner : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularDerivative (s.map block) i j p))
      (blockAngularDerivative block i j
        (reindexQuaternionPolynomial s p)) := by
    apply carrierOfPrefix
    · exact reindex_supported s _
    · exact angularDerivative_supported_at (by omega) (by omega)
        (reindex_supported s p)
    · exact hpInner
  exact hcOuter.trans
    (angularDerivative_carrier_at hblock hi hj hcInner)

/-- A block involution transports the literal Laplacian from the source block
to its selected target, under every insertion in the same supported carrier. -/
theorem reindex_blockAngularLaplacian_carrier
    {blocks block : Nat} (s : QuaternionBlockInvolution blocks)
    (hblock : block < blocks) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (blockAngularLaplacian (s.map block) p))
      (blockAngularLaplacian block
        (reindexQuaternionPolynomial s p)) := by
  have hleft := RatPolyCoeffEqv.reindex s
    (blockAngularLaplacian_eq_six (s.map block) p)
  have hright := blockAngularLaplacian_eq_six block
    (reindexQuaternionPolynomial s p)
  have hsix : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (six fun i j => blockAngularDerivative (s.map block) i j
          (blockAngularDerivative (s.map block) i j p)))
      (six fun i j => blockAngularDerivative block i j
        (blockAngularDerivative block i j
          (reindexQuaternionPolynomial s p))) := by
    simpa only [six, reindexQuaternionPolynomial_add] using
      (six_carrier (blocks := blocks) (fun i j hi hj =>
        reindex_secondAngular_carrier s hblock hi hj p hp))
  exact (RatPolyCoeffEqv.haarCarrier hleft).trans
    (hsix.trans (RatPolyCoeffEqv.haarCarrier hright.symm))

private theorem applyChain_carrier {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly},
      SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks q →
      HaarCarrierEqv blocks p q →
      HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q)
  | [], _, _, _, _, h => h
  | s::steps, p, q, hp, hq, h =>
      applyChain_carrier steps (reindex_supported s p) (reindex_supported s q)
        (reindex_carrier s hp hq h)

/-- A whole exposure chain transports the literal Laplacian from its
contravariant source block to the displayed target block. -/
theorem applyChain_blockAngularLaplacian_carrier
    {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks))
      (block : Nat), block < blocks → ∀ (p : RatPoly),
      SupportedQuaternionBlocks blocks p →
      HaarCarrierEqv blocks
        (applyQuaternionBlockSwapChain steps
          (blockAngularLaplacian
            (quaternionBlockSwapChainSource steps block) p))
        (blockAngularLaplacian block
          (applyQuaternionBlockSwapChain steps p))
  | [], block, hblock, p, hp => HaarCarrierEqv.refl _ _
  | s::steps, block, hblock, p, hp => by
      let sourceRest := quaternionBlockSwapChainSource steps block
      have hsourceRest : sourceRest < blocks :=
        quaternionBlockSwapChainSource_lt steps hblock
      have hs := reindex_blockAngularLaplacian_carrier s hsourceRest p hp
      have hsApplied := applyChain_carrier steps
        (reindex_supported s
          (blockAngularLaplacian (s.map sourceRest) p))
        (blockAngularLaplacian_supported hsourceRest (reindex_supported s p)) hs
      have hrest := applyChain_blockAngularLaplacian_carrier steps block hblock
        (reindexQuaternionPolynomial s p) (reindex_supported s p)
      exact hsApplied.trans hrest

end YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir

#print axioms YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir.reindex_blockAngularLaplacian_carrier
#print axioms YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir.applyChain_blockAngularLaplacian_carrier
#print axioms YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir.blockAngularLaplacian_carrier
