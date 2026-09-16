/-
# Literal whole-window placement in the original chronological carrier

The L+1 slices of a supported source window are placed at start+m through
start+m+L inside the original chain from start through start+m+L+n.
Every spatial block keeps its existing slice order, including box-fringe
coordinates. Lifting by m*N and embedding in the whole chain is literally
the same polynomial as embedding the window at start+m.

The ambient swept-chain Haar numerator then equals the existing observed
window pairing. No action factor or endpoint weight is removed: the final
spatial V occurs once in weightedMass. This is finite source placement,
not a claim that an arbitrary source polynomial is an original gauge
observable, nor a stationary, cutoff-limit, reflected OS or gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction (ambientChain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
  (chain_pin ambientChain_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle (middle_block)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage window_pairing)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

/-- Every block of the interior window has precisely its original ambient
placement. The empty-slice carrier requires no division assumption. -/
theorem window_block {width start m L n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent) {i : Nat}
    (hi : i < (L+1)*(N width)) :
    (embedding (m+(L+n)) hw ht).block (m*(N width)+i) =
      (embedding L (start := start+m) hw
        (show start+m+L ≤ extent by omega)).block i := by
  have hN : 0 < N width := by
    by_cases hz : N width = 0
    · rw [hz, Nat.mul_zero] at hi
      omega
    · omega
  have hrem : i % N width < N width := Nat.mod_lt i hN
  have hdivision : (i / N width)*(N width) + i % N width = i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i (N width)
  have hquot : i / N width ≤ L := by
    by_cases hq : i / N width ≤ L
    · exact hq
    · have hmul := Nat.mul_le_mul_right (N width)
        (show L+1 ≤ i / N width by omega)
      omega
  have htotal : (m+i/N width)+((L-i/N width)+n) = m+(L+n) := by omega
  have hwindow : i/N width+(L-i/N width) = L := by omega
  have htime : start+(m+i/N width) = (start+m)+i/N width := by omega
  have hindex : (m+i/N width)*(N width)+i%N width = m*(N width)+i := by
    rw [Nat.add_mul, Nat.add_assoc, hdivision]
  have hfull := middle_block (m := m+i/N width) (n := (L-i/N width)+n) hw
    (show start+((m+i/N width)+((L-i/N width)+n)) ≤ extent by omega) hrem
  have hsmall := middle_block (start := start+m) (m := i/N width) (n := L-i/N width) hw
    (show start+m+(i/N width+(L-i/N width)) ≤ extent by omega) hrem
  simp only [BlockEmbedding.block, embedding,
    BF4ExactSlabFixedSpatialSliceCarrier.embedding, htotal, htime, hindex] at hfull
  simp only [BlockEmbedding.block, embedding,
    BF4ExactSlabFixedSpatialSliceCarrier.embedding, hwindow, hdivision] at hsmall
  simpa only [BlockEmbedding.block, embedding] using hfull.trans hsmall.symm

/-- Literal whole-window polynomial placement, retaining every coefficient,
monomial and term order, rather than merely equality after Haar integration. -/
theorem window_polynomial_pin {width start m L n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    (embedding (m+(L+n)) hw ht).polynomial (liftBoundary (m*(N width)) p) =
      (embedding L (start := start+m) hw
        (show start+m+L ≤ extent by omega)).polynomial p := by
  apply BlockEmbedding.polynomial_liftBoundary
  · have h := Nat.mul_le_mul_right (N width)
      (show m+(L+1) ≤ m+(L+n)+1 by omega)
    simpa only [Nat.add_mul, Nat.one_mul] using h
  · exact fun _ hi => window_block hw ht hi
  · exact hp

/-- The complete ambient swept-chain numerator is the existing observed
window pairing, with arbitrary signed supported p and the actual final V.
No nome, cutoff-positivity or face-observable premise is needed for this
finite polynomial/Haar identity. -/
theorem swept_window_pairing {width start m L n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    quaternionHaar (B extent)
        (polyMul
          ((embedding L (start := start+m) hw
            (show start+m+L ≤ extent by omega)).polynomial p)
          (ambientChain w K extent width start (m+(L+n)))) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width m L p) (terminalMessage w K width n)) := by
  let E := embedding (m+(L+n)) hw ht
  let M := embedding L (start := start+m) hw (show start+m+L ≤ extent by omega)
  let U := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht
  let c := chain (N width) (kineticWeight w K width) (spatialWeight w K width)
    (m+(L+n)) polyOne
  let lifted := liftBoundary (m*(N width)) p
  have hunit : PaddedPolynomialCoeffEqv (B extent) (U.polynomial polyOne) polyOne :=
    .of_prefix U.polynomial_one_prefix
  have hchain : PaddedPolynomialCoeffEqv (B extent) (E.polynomial c)
      (ambientChain w K extent width start (m+(L+n))) :=
    (chain_pin hw ht w K polyOne (supported_one (N width))).trans
      (((PaddedPolynomialCoeffEqv.refl _ _).mul hunit).trans
        (.of_coeff (RatPolyCoeffEqv.mul_one _)))
  have hpin : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (polyMul lifted c))
      (polyMul (M.polynomial p) (ambientChain w K extent width start (m+(L+n)))) := by
    rw [BlockEmbedding.polynomial_mul, window_polynomial_pin hw ht p hp]
    exact (PaddedPolynomialCoeffEqv.refl _ _).mul hchain
  have hlift : SupportedQuaternionBlocks ((m+(L+n)+1)*(N width)) lifted :=
    support_mono (lift_supported hp (m*(N width))) (by
      have h := Nat.mul_le_mul_right (N width)
        (show L+1+m ≤ m+(L+n)+1 by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using h)
  have hsource : SupportedQuaternionBlocks ((m+(L+n)+1)*(N width)) (polyMul lifted c) :=
    supported_polyMul hlift
      (chain_supported (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) (m+(L+n)) (supported_one (N width)))
  have hambient := supported_polyMul (M.polynomial_supported p)
    (ambientChain_supported w K extent width start (m+(L+n)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hpin.haar (E.polynomial_supported _) hambient))
    (Q'.eqv_trans _ _ _ (E.haar _ hsource) (window_pairing w K width m L n hp))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding.window_block
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding.window_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding.swept_window_pairing
