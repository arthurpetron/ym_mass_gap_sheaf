/-
# The full original tube heat sub-action has connected numerator w^36

All cutoff spins and both replica means are retained. The original
ordered sub-action is swept to the full-kernel tube, then the unchanged
full carrier permutation transports it to the proved compact contraction.
The independent boundary is the unit polynomial and its upper-plaquette
variance is exactly one. No remaining ambient plaquette is discarded
from a full-action claim: this theorem evaluates only the named tubeIds.
-/

import YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep
import YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance
import YMGap.Continuum.BF4ExactSlabBareTubeEvaluation

namespace YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
open YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction
open YMGap.Continuum.BF4ExactSlabFullHeatTubeCovariance
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFullHeatTubeComposition
open YMGap.Continuum.SU2QuaternionFullHeatTubeCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" margin:max => List.length (boundaryCompleteSlabLinks (responseExtent margin))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem connected_extend {source target : Nat} (hle : source ≤ target) (p q r : RatPoly)
    (hp : SupportedQuaternionBlocks source p) (hq : SupportedQuaternionBlocks source q)
    (hr : SupportedQuaternionBlocks source r) :
    connectedNumerator target p q r ≈ connectedNumerator source p q r :=
  Q'.add_eqv_congr' (qmul (quaternionHaar_extend_supported_endpoint hle r hr)
    (quaternionHaar_extend_supported_endpoint hle _ (supported_polyMul hp (supported_polyMul hq hr))))
    (Q'.neg_eqv_congr _ _ (qmul (quaternionHaar_extend_supported_endpoint hle _ (supported_polyMul hp hr))
      (quaternionHaar_extend_supported_endpoint hle _ (supported_polyMul hq hr))))

theorem compact_upper_variance : connectedNumerator 16 (compactSlice 3) (compactSlice 3) polyOne ≈ 1 := by
  decide +kernel

theorem full_carrier_upper_variance (margin : Nat) :
    connectedNumerator (N margin) (compactSlice 3) (compactSlice 3) polyOne ≈ 1 := by
  have hn := carrier_size margin
  exact Q'.eqv_trans _ _ _ (connected_extend (by omega : 16 ≤ N margin) _ _ _
    (slice_supported 12 (by decide)) (slice_supported 12 (by decide)) (supported_one _)) compact_upper_variance

theorem literal_chain_padded_congr (margin : Nat) (w : Q') (K : Nat) {r s : RatPoly}
    (h : PaddedPolynomialCoeffEqv (N margin) r s) :
    PaddedPolynomialCoeffEqv (N margin) (literalChain margin w K r) (literalChain margin w K s) := by
  unfold literalChain
  induction sideIds with
  | nil => exact h
  | cons i ids ih => exact (PaddedPolynomialCoeffEqv.refl _ _).mul ih

theorem unit_chain_embedding (margin : Nat) (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv (N margin) ((carrierEmbedding margin).polynomial (chain 0 K [w,w,w] polyOne))
      (literalChain margin w K polyOne) :=
  (chain_embedding_pin margin w K polyOne).trans
    (literal_chain_padded_congr margin w K (.of_prefix (carrierEmbedding margin).polynomial_one_prefix))

theorem literal_connected_value (margin : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K) :
    connectedNumerator (N margin) (literalSlice margin 0) (literalSlice margin 3)
      (literalChain margin w K polyOne) ≈ RingNormaliser.qpow w 36 := by
  have hsize := carrier_size margin
  have hn : N margin-1+1 = N margin := by omega
  have hin := connected_embedding margin (slice_supported 0 (by omega)) (slice_supported 12 (by omega))
    (chain_supported 0 K [w,w,w] (by change 15 < N margin; omega) polyOne (supported_one _))
    (original_character_support _ _ _) (original_character_support _ _ _)
    (literal_chain_supported margin w K polyOne (supported_one _))
    (slice_embedding_pin margin 0) (slice_embedding_pin margin 3) (unit_chain_embedding margin w K)
  have h := three_layer_connected (N margin-1) 0 K hK w (by omega) polyOne (supported_one _)
    (fun slot _ _ => hasQuaternionBlockDegree_one slot)
  rw [hn] at h
  exact Q'.eqv_trans _ _ _ hin (Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (full_carrier_upper_variance margin)) (Q'.mul_one_eqv _)))

theorem original_tube_numerator (w : Q') (K margin : Nat) (hK : 1 ≤ K) :
    BF4ExactSlabDisconnectedHaarCancellation.connectedNumerator w K (responseExtent margin) (tubeIds margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈ RingNormaliser.qpow w 36 :=
  Q'.eqv_trans _ _ _ (original_tube_connected_sweep w K margin) (literal_connected_value margin w K hK)

end YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue

#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.connected_extend
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.compact_upper_variance
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.full_carrier_upper_variance
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.literal_chain_padded_congr
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.unit_chain_embedding
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.literal_connected_value
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue.original_tube_numerator
