/- Exact selected-endpoint Casimir eigenaction for normalized characters. -/

import YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
import YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionSelectedCharacterEigenaction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
open YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

private theorem chain_smul {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (c : Q') (p : RatPoly) :
    applyQuaternionBlockSwapChain steps (polySmul c p) =
      polySmul c (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s steps ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_smul, ih]

private theorem chain_carrier {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly},
      SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks q →
      HaarCarrierEqv blocks p q →
      HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q)
  | [], _, _, _, _, h => h
  | s::steps, p, q, hp, hq, h =>
      chain_carrier steps (reindex_supported s p) (reindex_supported s q)
        (reindex_carrier s hp hq h)

private theorem reflect_chain_carrier {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
      (applyQuaternionBlockSwapChain steps q)) : HaarCarrierEqv blocks p q := by
  have hr := chain_carrier steps.reverse
    (applyQuaternionBlockSwapChain_supported steps p hp)
    (applyQuaternionBlockSwapChain_supported steps q hq) h
  have hpInv : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps p)) p := by
    apply carrierOfPrefix
    · exact applyQuaternionBlockSwapChain_supported steps.reverse _
        (applyQuaternionBlockSwapChain_supported steps p hp)
    · exact hp
    · exact reverse_apply_inverse_prefix steps p
  have hqInv : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps q)) q := by
    apply carrierOfPrefix
    · exact applyQuaternionBlockSwapChain_supported steps.reverse _
        (applyQuaternionBlockSwapChain_supported steps q hq)
    · exact hq
    · exact reverse_apply_inverse_prefix steps q
  exact hpInv.symm.trans (hr.trans hqInv)

private theorem normalized_exposed_prefix {blocks : Nat} (hb : 1 < blocks)
    (a b : Fin blocks) (hab : a.val ≠ b.val) (degree : Nat) :
    QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain (pairSteps hb a b)
        (normalizedCharacterAt a.val b.val degree))
      (normalizedCharacterAt 0 1 degree) := by
  unfold normalizedCharacterAt
  rw [chain_smul]
  exact ((applyQuaternionBlockSwapChain_character_prefix (pairSteps hb a b)
    (scalarAt a.val b.val) degree).trans
      ((scalar_exposed hb a b hab).character degree)).smul _

/-- The normalized relative character is a Casimir eigenfunction at either
chosen endpoint: order that endpoint first in `(a,b)`. -/
theorem normalizedCharacterAt_blockAngularLaplacian
    {blocks : Nat} (hb : 1 < blocks) (a b : Fin blocks)
    (hab : a.val ≠ b.val) (degree : Nat) :
    HaarCarrierEqv blocks
      (blockAngularLaplacian a.val
        (normalizedCharacterAt a.val b.val degree))
      (polySmul (-(Q'.ofNat degree * (Q'.ofNat degree + 2)))
        (normalizedCharacterAt a.val b.val degree)) := by
  let P := normalizedCharacterAt a.val b.val degree
  let N := normalizedCharacterAt 0 1 degree
  let steps := pairSteps hb a b
  let eigenvalue := -(Q'.ofNat degree * (Q'.ofNat degree + 2))
  have hP : SupportedQuaternionBlocks blocks P :=
    normalizedCharacterAt_supported a.isLt b.isLt
  have hc : HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps P) N := by
    apply carrierOfPrefix
    · exact applyQuaternionBlockSwapChain_supported steps P hP
    · exact normalizedCharacterAt_supported (by omega) (by omega)
    · exact normalized_exposed_prefix hb a b hab degree
  have htransport := applyChain_blockAngularLaplacian_carrier
    steps 0 (by omega) P hP
  rw [pair_zero hb a b hab] at htransport
  have hlap := blockAngularLaplacian_carrier (by omega : 0 < blocks) hc
  have hhead : HaarCarrierEqv blocks (blockAngularLaplacian 0 N)
      (polySmul eigenvalue N) := by
    have he := normalizedCharacterAt_zero_one_angularCasimir blocks degree hb
    have hshape : HaarCarrierEqv blocks (blockAngularLaplacian 0 N)
        (six fun i j => blockAngularDerivative 0 i j
          (blockAngularDerivative 0 i j N)) :=
      RatPolyCoeffEqv.haarCarrier (blockAngularLaplacian_eq_six 0 N)
    change HaarCarrierEqv blocks (blockAngularLaplacian 0 N)
      (angularLaplacian N) at hshape
    exact hshape.trans he
  have hrhs : HaarCarrierEqv blocks
      (polySmul eigenvalue N)
      (applyQuaternionBlockSwapChain steps (polySmul eigenvalue P)) := by
    rw [chain_smul]
    exact (HaarCarrierEqv.smul eigenvalue hc).symm
  exact reflect_chain_carrier steps
    (blockAngularLaplacian_supported a.isLt hP)
    (polySmul_supported hP eigenvalue)
    (htransport.trans (hlap.trans (hhead.trans hrhs)))

end YMGap.Continuum.SU2QuaternionSelectedCharacterEigenaction

#print axioms YMGap.Continuum.SU2QuaternionSelectedCharacterEigenaction.normalizedCharacterAt_blockAngularLaplacian
