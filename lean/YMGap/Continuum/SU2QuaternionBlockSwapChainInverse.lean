/-
# Inverting a finite quaternion-block swap chain

Every entry in a block-swap chain is an explicit involution.  Reversing the
list therefore gives its inverse.  The identities below retain prefix padding;
their Haar corollary requires support only where the finite Haar functional
actually needs it.
-/

import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.SU2QuaternionBlockSwapChainInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local infix:50 " ≈ " => Q'.eqv

private theorem apply_chain_append {blocks : Nat}
    (first second : List (QuaternionBlockInvolution blocks)) (p : RatPoly) :
    applyQuaternionBlockSwapChain (first ++ second) p =
      applyQuaternionBlockSwapChain second
        (applyQuaternionBlockSwapChain first p) := by
  induction first generalizing p with
  | nil => rfl
  | cons swap rest ih =>
      change applyQuaternionBlockSwapChain (rest ++ second)
          (reindexQuaternionPolynomial swap p) = _
      exact ih (reindexQuaternionPolynomial swap p)

/-- Applying a chain after its reversed chain is prefix-identical. -/
theorem apply_reverse_inverse_prefix {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly),
      QuaternionPrefixPolynomialEqv blocks
        (applyQuaternionBlockSwapChain steps
          (applyQuaternionBlockSwapChain steps.reverse p)) p
  | [], p => QuaternionPrefixPolynomialEqv.refl blocks p
  | swap :: rest, p => by
      rw [List.reverse_cons, apply_chain_append]
      change QuaternionPrefixPolynomialEqv blocks
        (applyQuaternionBlockSwapChain rest
          (reindexQuaternionPolynomial swap
            (reindexQuaternionPolynomial swap
              (applyQuaternionBlockSwapChain rest.reverse p)))) p
      exact (applyQuaternionBlockSwapChain_prefix rest
        (reindex_twice_prefix swap
          (applyQuaternionBlockSwapChain rest.reverse p))).trans
        (apply_reverse_inverse_prefix rest p)

/-- The reverse chain also cancels a preceding forward chain. -/
theorem reverse_apply_inverse_prefix {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps p)) p := by
  simpa using apply_reverse_inverse_prefix steps.reverse p

theorem apply_reverse_inverse_padded {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly) :
    PaddedPolynomialCoeffEqv blocks
      (applyQuaternionBlockSwapChain steps
        (applyQuaternionBlockSwapChain steps.reverse p)) p :=
  PaddedPolynomialCoeffEqv.of_prefix
    (apply_reverse_inverse_prefix steps p)

theorem reverse_apply_inverse_padded {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly) :
    PaddedPolynomialCoeffEqv blocks
      (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps p)) p :=
  PaddedPolynomialCoeffEqv.of_prefix
    (reverse_apply_inverse_prefix steps p)

/-- Reversing the swap list preserves the declared finite carrier. -/
theorem reverse_chain_supported {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks
      (applyQuaternionBlockSwapChain steps.reverse p) :=
  applyQuaternionBlockSwapChain_supported steps.reverse p hp

/-- Arbitrary supported insertions see the reverse/forward composite as the
identity on the same full Haar carrier. -/
theorem apply_reverse_inverse_haar {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p insertion : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hi : SupportedQuaternionBlocks blocks insertion) :
    quaternionHaar blocks
      (polyMul insertion
        (applyQuaternionBlockSwapChain steps
          (applyQuaternionBlockSwapChain steps.reverse p))) ≈
      quaternionHaar blocks (polyMul insertion p) := by
  exact quaternionHaar_prefixPolynomialEqv blocks
    ((QuaternionPrefixPolynomialEqv.refl blocks insertion).mul
      (apply_reverse_inverse_prefix steps p))
    (supported_polyMul hi
      (applyQuaternionBlockSwapChain_supported steps _
        (reverse_chain_supported steps p hp)))
    (supported_polyMul hi hp)

end YMGap.Continuum.SU2QuaternionBlockSwapChainInverse

#print axioms YMGap.Continuum.SU2QuaternionBlockSwapChainInverse.apply_reverse_inverse_prefix
#print axioms YMGap.Continuum.SU2QuaternionBlockSwapChainInverse.reverse_apply_inverse_prefix
#print axioms YMGap.Continuum.SU2QuaternionBlockSwapChainInverse.apply_reverse_inverse_padded
#print axioms YMGap.Continuum.SU2QuaternionBlockSwapChainInverse.reverse_apply_inverse_padded
#print axioms YMGap.Continuum.SU2QuaternionBlockSwapChainInverse.reverse_chain_supported
#print axioms YMGap.Continuum.SU2QuaternionBlockSwapChainInverse.apply_reverse_inverse_haar
