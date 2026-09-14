/-
# Original full-tube connected numerator equals a boundary variance numerator

Both endpoint words, every full heat factor, the partition and both means
are transported by the same full original-slab permutation. Thus the exact
w^36 signal includes its vacuum subtraction, for arbitrary retained signed
boundary data. The remaining interacting plaquettes can violate the displayed
independence guard; their error is not bounded here.
-/

import YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction
import YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance

namespace YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionFullHeatTubeComposition
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" margin:max => List.length (boundaryCompleteSlabLinks (responseExtent margin))

private theorem haar_pin (margin : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N margin) p) (hq : SupportedQuaternionBlocks (N margin) q)
    (h : PaddedPolynomialCoeffEqv (N margin) ((carrierEmbedding margin).polynomial p) q) :
    quaternionHaar (N margin) q ≈ quaternionHaar (N margin) p :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (h.haar ((carrierEmbedding margin).polynomial_supported _) hq))
    ((carrierEmbedding margin).haar p hp)

/-- Four moments on the SAME mapped carrier; no normalized model is substituted. -/
theorem connected_embedding (margin : Nat) {p q r p' q' r' : RatPoly}
    (hp : SupportedQuaternionBlocks (N margin) p) (hq : SupportedQuaternionBlocks (N margin) q)
    (hr : SupportedQuaternionBlocks (N margin) r)
    (hp' : SupportedQuaternionBlocks (N margin) p') (hq' : SupportedQuaternionBlocks (N margin) q')
    (hr' : SupportedQuaternionBlocks (N margin) r')
    (pp : PaddedPolynomialCoeffEqv (N margin) ((carrierEmbedding margin).polynomial p) p')
    (pq : PaddedPolynomialCoeffEqv (N margin) ((carrierEmbedding margin).polynomial q) q')
    (pr : PaddedPolynomialCoeffEqv (N margin) ((carrierEmbedding margin).polynomial r) r') :
    connectedNumerator (N margin) p' q' r' ≈ connectedNumerator (N margin) p q r := by
  have pin1 := pp.mul pr
  have pin2 := pq.mul pr
  have pin3 := pp.mul pin2
  simp only [← (carrierEmbedding margin).polynomial_mul] at pin1 pin2 pin3
  have h0 := haar_pin margin hr hr' pr
  have h1 := haar_pin margin (supported_polyMul hp hr) (supported_polyMul hp' hr') pin1
  have h2 := haar_pin margin (supported_polyMul hq hr) (supported_polyMul hq' hr') pin2
  have h3 := haar_pin margin (supported_polyMul hp (supported_polyMul hq hr))
    (supported_polyMul hp' (supported_polyMul hq' hr')) pin3
  have mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)
  exact Q'.add_eqv_congr' (mul_congr h0 h3) (Q'.neg_eqv_congr _ _ (mul_congr h1 h2))

theorem literal_vacuum (margin : Nat) (w : Q') (K : Nat) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (N margin) r)
    (hd : ∀ slot : Nat, slot < 12 → HasQuaternionBlockDegree slot 0 r) :
    quaternionHaar (N margin) (literalChain margin w K ((carrierEmbedding margin).polynomial r)) ≈
      quaternionHaar (N margin) ((carrierEmbedding margin).polynomial r) := by
  have hsize := carrier_size margin
  have hn : N margin-1+1 = N margin := by omega
  have hs := chain_supported 0 K [w,w,w] (by change 15 < N margin; omega) r hr
  have h := chain_vacuum (N margin-1) 0 K [w,w,w] (by change 15 < N margin-1+1; omega) r
    (by simpa only [hn] using hr) (fun slot _ hl => hd slot hl)
  rw [hn] at h
  exact Q'.eqv_trans _ _ _ (haar_pin margin hs
    (literal_chain_supported margin w K _ ((carrierEmbedding margin).polynomial_supported _))
    (chain_embedding_pin margin w K r))
    (Q'.eqv_trans _ _ _ h (Q'.eqv_symm ((carrierEmbedding margin).haar r hr)))

/-- Original literal endpoints, original twelve full factors, same partition
and means. All cutoff and volume parameters remain explicit in the type. -/
theorem literal_connected_transport (margin : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (N margin) r)
    (hd : ∀ slot : Nat, slot < 12 → HasQuaternionBlockDegree slot 0 r) :
    connectedNumerator (N margin) (literalSlice margin 0) (literalSlice margin 3)
      (literalChain margin w K ((carrierEmbedding margin).polynomial r)) ≈
        qpow w 36 * connectedNumerator (N margin) (literalSlice margin 3) (literalSlice margin 3)
          ((carrierEmbedding margin).polynomial r) := by
  have hsize := carrier_size margin
  have hn : N margin-1+1 = N margin := by omega
  have hs := chain_supported 0 K [w,w,w] (by change 15 < N margin; omega) r hr
  have hp0 : SupportedQuaternionBlocks (N margin) (compactSlice 0) := slice_supported 0 (by omega)
  have hp3 : SupportedQuaternionBlocks (N margin) (compactSlice 3) := slice_supported 12 (by omega)
  have hin := connected_embedding margin hp0 hp3 hs
    (original_character_support _ _ _) (original_character_support _ _ _)
    (literal_chain_supported margin w K _ ((carrierEmbedding margin).polynomial_supported _))
    (slice_embedding_pin margin 0) (slice_embedding_pin margin 3) (chain_embedding_pin margin w K r)
  have hc := three_layer_connected (N margin-1) 0 K hK w (by omega) r
    (by simpa only [hn] using hr) (fun slot _ hl => hd slot hl)
  rw [hn] at hc
  have hout := connected_embedding margin hp3 hp3 hr
    (original_character_support _ _ _) (original_character_support _ _ _) ((carrierEmbedding margin).polynomial_supported _)
    (slice_embedding_pin margin 3) (slice_embedding_pin margin 3) (PaddedPolynomialCoeffEqv.refl _ _)
  exact Q'.eqv_trans _ _ _ hin (Q'.eqv_trans _ _ _ hc (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hout)))

end YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance

#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance.connected_embedding
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance.literal_vacuum
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance.literal_connected_transport
