/-
# Literal paired angular frame at an arbitrary original block

All first and ordered second generators travel through the SAME finite
block chart. These are supported Haar-carrier pins, not raw coefficient
identities and not derivatives of the polynomial frozen coefficients.
The consumer is the local original-prefix curvature at an OUTPUT block.
No conditional, OS, scaling or physical gap is asserted here.
-/

import YMGap.Continuum.QuaternionHaarMixedAngularTransport
import YMGap.Continuum.SU2QuaternionPairedFrameScalarJets

namespace YMGap.Continuum.SU2QuaternionPairedFrameAt

set_option autoImplicit false

open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarBlockAngularCarrier
open YMGap.Continuum.QuaternionHaarMixedAngularTransport
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)

/-- The same three signed pairs, at the specified physical block. -/
def pairedDerivativeAt (block : Nat) (i : Fin 3) (p : RatPoly) : RatPoly :=
  match i.val with
  | 0 => polyAdd (blockAngularDerivative block 0 1 p) (blockAngularDerivative block 2 3 p)
  | 1 => polyAdd (blockAngularDerivative block 0 2 p)
      (polyNeg (blockAngularDerivative block 1 3 p))
  | _ => polyAdd (blockAngularDerivative block 0 3 p) (blockAngularDerivative block 1 2 p)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

theorem pairedDerivativeAt_zero (i : Fin 3) (p : RatPoly) :
    pairedDerivativeAt 0 i p = pairedDerivative i p := by
  rcases direction_cases i with rfl | rfl | rfl <;> rfl

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem pairedDerivativeAt_supported {blocks block : Nat}
    (hb : block < blocks) (i : Fin 3) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (pairedDerivativeAt block i p) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact supported_add (blockAngularDerivative_supported hb (by decide) (by decide) hp)
      (blockAngularDerivative_supported hb (by decide) (by decide) hp)
  · exact supported_add (blockAngularDerivative_supported hb (by decide) (by decide) hp)
      (support_neg (blockAngularDerivative_supported hb (by decide) (by decide) hp))
  · exact supported_add (blockAngularDerivative_supported hb (by decide) (by decide) hp)
      (blockAngularDerivative_supported hb (by decide) (by decide) hp)

theorem pairedDerivativeAt_carrier {blocks block : Nat} (hb : block < blocks)
    (i : Fin 3) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (pairedDerivativeAt block i p) (pairedDerivativeAt block i q) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact HaarCarrierEqv.add
      (blockAngularDerivative_carrier (i := 0) (j := 1) hb (by decide) (by decide) hp hq h)
      (blockAngularDerivative_carrier (i := 2) (j := 3) hb (by decide) (by decide) hp hq h)
  · exact HaarCarrierEqv.add
      (blockAngularDerivative_carrier (i := 0) (j := 2) hb (by decide) (by decide) hp hq h)
      (HaarCarrierEqv.neg
        (blockAngularDerivative_carrier (i := 1) (j := 3) hb (by decide) (by decide) hp hq h))
  · exact HaarCarrierEqv.add
      (blockAngularDerivative_carrier (i := 0) (j := 3) hb (by decide) (by decide) hp hq h)
      (blockAngularDerivative_carrier (i := 1) (j := 2) hb (by decide) (by decide) hp hq h)

theorem chain_add {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (p q : RatPoly) : applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p) (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_add, ih]

theorem chain_neg {blocks : Nat} (steps : List (QuaternionBlockInvolution blocks))
    (p : RatPoly) : applyQuaternionBlockSwapChain steps (polyNeg p) =
      polyNeg (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_neg, ih]

/-- The actual first paired generator, including its middle negative term. -/
theorem chain_pairedDerivativeAt {blocks block : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (hb : block < blocks)
    (i : Fin 3) (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (pairedDerivativeAt block i (applyQuaternionBlockSwapChain steps p))
      (applyQuaternionBlockSwapChain steps
        (pairedDerivativeAt (quaternionBlockSwapChainSource steps block) i p)) := by
  rcases direction_cases i with rfl | rfl | rfl
  · simpa only [pairedDerivativeAt, chain_add] using
      HaarCarrierEqv.add (chain_blockDerivative steps block 0 1 hb (by decide) (by decide) p hp)
        (chain_blockDerivative steps block 2 3 hb (by decide) (by decide) p hp)
  · simpa only [pairedDerivativeAt, chain_add, chain_neg] using
      HaarCarrierEqv.add (chain_blockDerivative steps block 0 2 hb (by decide) (by decide) p hp)
        (HaarCarrierEqv.neg (chain_blockDerivative steps block 1 3 hb
          (by decide) (by decide) p hp))
  · simpa only [pairedDerivativeAt, chain_add] using
      HaarCarrierEqv.add (chain_blockDerivative steps block 0 3 hb (by decide) (by decide) p hp)
        (chain_blockDerivative steps block 1 2 hb (by decide) (by decide) p hp)

/-- EVERY ordered second entry travels without symmetrizing i,j or acting
on a frozen coefficient. -/
theorem chain_pairedSecondAt {blocks block : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (hb : block < blocks)
    (i j : Fin 3) (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks
      (pairedDerivativeAt block i
        (pairedDerivativeAt block j (applyQuaternionBlockSwapChain steps p)))
      (applyQuaternionBlockSwapChain steps
        (pairedDerivativeAt (quaternionBlockSwapChainSource steps block) i
          (pairedDerivativeAt (quaternionBlockSwapChainSource steps block) j p))) := by
  have hs := quaternionBlockSwapChainSource_lt steps hb
  have hj := chain_pairedDerivativeAt steps hb j p hp
  have hd := pairedDerivativeAt_supported hs j hp
  exact (pairedDerivativeAt_carrier hb i
    (pairedDerivativeAt_supported hb j
      (applyQuaternionBlockSwapChain_supported steps p hp))
    (applyQuaternionBlockSwapChain_supported steps _ hd) hj).trans
    (chain_pairedDerivativeAt steps hb i _ hd)

end YMGap.Continuum.SU2QuaternionPairedFrameAt

#print axioms YMGap.Continuum.SU2QuaternionPairedFrameAt.pairedDerivativeAt
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameAt.pairedDerivativeAt_zero
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameAt.pairedDerivativeAt_supported
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameAt.pairedDerivativeAt_carrier
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameAt.chain_pairedDerivativeAt
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameAt.chain_pairedSecondAt
