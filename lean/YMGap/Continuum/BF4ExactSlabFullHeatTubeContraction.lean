/-
# Full-cutoff tube contraction on the original all-volume slab carrier

The twelve factors are the original swept face factors with their complete
heatWeights, not selected fundamental terms. One full carrier permutation
pins all of them to the proved full-kernel chain. The boundary remains on
that same carrier and is independent only of the twelve integrated links.

This is a conditional Haar identity. The remaining interacting plaquettes
may depend on those links; no positive full-response bound is inferred.
-/

import YMGap.Continuum.SU2QuaternionFullHeatTubeComposition
import YMGap.Continuum.BF4ExactSlabTubeCarrierWords

namespace YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFullHeatTubeComposition
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" margin:max => List.length (boundaryCompleteSlabLinks (responseExtent margin))

/-- The existing full-action factor, with no change to its coefficients. -/
def literalHeat (margin : Nat) (w : Q') (K : Nat) (time : Fin 3) (edge : Fin 4) : RatPoly :=
  factor (sweptCharacter (responseExtent margin) (margin+3)) (sideFace margin time edge, heatWeights w K)

theorem literalHeat_expansion (margin : Nat) (w : Q') (K : Nat) (time : Fin 3) (edge : Fin 4) :
    literalHeat margin w K time edge = finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
      (sweptCharacter (responseExtent margin) (margin+3) (sideFace margin time edge) spin)) (List.range (K+1)) := by
  unfold literalHeat factor heatWeights
  induction List.range (K+1) with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, finitePolySum, ih]

theorem side_character_embedding_pin (margin : Nat) (time : Fin 3) (edge : Fin 4) (spin : Nat) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (characterPolynomial
        (scalarAt (4*time.val+edge.val) (4*(time.val+1)+edge.val)) spin))
      (sweptCharacter (responseExtent margin) (margin+3) (sideFace margin time edge) spin) := by
  have ht := time.isLt
  have he := edge.isLt
  rw [tube_side_character_pin margin _ (sideFace_mem margin time edge) spin]
  apply PaddedPolynomialCoeffEqv.of_prefix
  apply (carrierEmbedding margin).character_of_quaternion
  rw [(carrierEmbedding margin).quaternion_mul, (carrierEmbedding margin).quaternion_conj]
  rw [(side_link_pins margin time edge).1, (side_link_pins margin time edge).2]
  exact (carrier_link_pin margin _ (by omega)).mul (carrier_link_pin margin _ (by omega)).conj

theorem side_heat_embedding_pin (margin : Nat) (w : Q') (K : Nat) (time : Fin 3) (edge : Fin 4) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (heatAt (4*time.val+edge.val) (4*(time.val+1)+edge.val) w K))
      (literalHeat margin w K time edge) := by
  rw [literalHeat_expansion]
  unfold heatAt
  induction List.range (K+1) with
  | nil => exact .refl _ _
  | cons s ss ih =>
    simp only [finitePolySum, (carrierEmbedding margin).polynomial_add, (carrierEmbedding margin).polynomial_smul]
    exact ((side_character_embedding_pin margin time edge s).smul _).add ih

/-- The existing ordered list enumerates exactly tubeSides (side_faces_pin). -/
def literalChain (margin : Nat) (w : Q') (K : Nat) (r : RatPoly) : RatPoly :=
  sideIds.foldr (fun i p => polyMul (literalHeat margin w K i.1 i.2) p) r

theorem chain_embedding_pin (margin : Nat) (w : Q') (K : Nat) (r : RatPoly) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (chain 0 K [w,w,w] r))
      (literalChain margin w K ((carrierEmbedding margin).polynomial r)) := by
  have h : chain 0 K [w,w,w] r = sideIds.foldr
      (fun i p => polyMul (heatAt (4*i.1.val+i.2.val) (4*(i.1.val+1)+i.2.val) w K) p) r := rfl
  rw [h]
  unfold literalChain
  induction sideIds with
  | nil => exact .refl _ _
  | cons i ids ih =>
    simp only [List.foldr_cons, (carrierEmbedding margin).polynomial_mul]
    exact (side_heat_embedding_pin margin w K i.1 i.2).mul ih

private theorem support_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := fun t ht => (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_smul {blocks : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem literal_heat_supported (margin : Nat) (w : Q') (K : Nat) (time : Fin 3) (edge : Fin 4) :
    SupportedQuaternionBlocks (N margin) (literalHeat margin w K time edge) := by
  rw [literalHeat_expansion]
  induction List.range (K+1) with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons s ss ih => exact support_add (support_smul _ (swept_character_supported _ _ _ s)) ih

theorem literal_chain_supported (margin : Nat) (w : Q') (K : Nat) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (N margin) r) : SupportedQuaternionBlocks (N margin) (literalChain margin w K r) := by
  unfold literalChain
  induction sideIds with
  | nil => exact hr
  | cons i ids ih => exact supported_polyMul (literal_heat_supported margin w K i.1 i.2) ih

private theorem compact_slice_supported (margin : Nat) (time : Fin 4) :
    SupportedQuaternionBlocks (N margin) (compactSlice time) := by
  have hc : ∀ time : Fin 4, (compactSlice time).all (fun t => decide (t.1.length ≤ 4*16)) = true := by decide +kernel
  have hn := carrier_size margin
  intro t ht
  have hs := of_decide_eq_true (List.all_eq_true.mp (hc time) t ht)
  omega

/-- Exact w^36 transmission through the twelve ORIGINAL full heat factors.
The input boundary may use every retained upper or spectator link. -/
theorem literal_boundary_haar (margin : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (N margin) r)
    (hd : ∀ slot : Nat, slot < 12 → HasQuaternionBlockDegree slot 0 r) :
    quaternionHaar (N margin) (polyMul (literalSlice margin 0)
      (literalChain margin w K ((carrierEmbedding margin).polynomial r))) ≈
        qpow w 36 * quaternionHaar (N margin)
          (polyMul (literalSlice margin 3) ((carrierEmbedding margin).polynomial r)) := by
  have hsize := carrier_size margin
  have hn : N margin-1+1 = N margin := by omega
  have hs := chain_supported 0 K [w,w,w] (by change 15 < N margin; omega) r hr
  have hin := (slice_embedding_pin margin 0).mul (chain_embedding_pin margin w K r)
  rw [← (carrierEmbedding margin).polynomial_mul] at hin
  have hhin := hin.haar ((carrierEmbedding margin).polynomial_supported _)
    (supported_polyMul (original_character_support _ _ _)
      (literal_chain_supported margin w K _ ((carrierEmbedding margin).polynomial_supported _)))
  have hein := (carrierEmbedding margin).haar _ (supported_polyMul (compact_slice_supported margin 0) hs)
  have hc := three_layer_haar (N margin-1) 0 K hK w (by omega) r
    (by simpa only [hn] using hr) (fun slot _ hl => hd slot hl)
  rw [hn] at hc
  have hout := (slice_embedding_pin margin 3).mul (PaddedPolynomialCoeffEqv.refl (N margin) ((carrierEmbedding margin).polynomial r))
  rw [← (carrierEmbedding margin).polynomial_mul] at hout
  have hhout := hout.haar ((carrierEmbedding margin).polynomial_supported _)
    (supported_polyMul (original_character_support _ _ _) ((carrierEmbedding margin).polynomial_supported _))
  have heout := (carrierEmbedding margin).haar _ (supported_polyMul (compact_slice_supported margin 3) hr)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hhin) (Q'.eqv_trans _ _ _ hein
    (Q'.eqv_trans _ _ _ hc (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_symm heout) hhout))))

end YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction

#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.literalHeat
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.literalHeat_expansion
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.side_character_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.side_heat_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.literalChain
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.chain_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.literal_heat_supported
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.literal_chain_supported
#print axioms YMGap.Continuum.BF4ExactSlabFullHeatTubeContraction.literal_boundary_haar
