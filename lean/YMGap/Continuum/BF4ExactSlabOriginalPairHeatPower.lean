/-
# Original two-replica heat weights have a combined exponent at least 36

Reindex the full positive-face count back to the ORIGINAL face indices.
The original packet coefficients factor as dimension product times the
sum of their SU(2) Casimir powers. The retained-pair area theorem supplies
the exponent floor. The signed amplitude retains the original Haar
four-moment term; no sign or lower bound is imposed on it.
-/

import YMGap.Continuum.SU2FiniteHeatPowerFactorization
import YMGap.Continuum.BF4ExactSlabConnectedReplicaArea

namespace YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

theorem positiveFaces_length (extent : Nat) (state : EdgeLabelling) :
    (positiveFaces extent state).length = positiveCount state (slabPhysicalFaceEdges extent) := by
  let pred := fun f => decide (0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf f))
  have he := congrArg (fun fs => (fs.filter pred).length) (slabFaceIds_map extent)
  dsimp only at he
  change ((boundaryCompleteSlabPlaquettes extent).filter pred).length = _
  rw [← he, List.filter_map, List.length_map]
  unfold positiveCount
  congr 1
  apply List.filter_congr
  intro id hi
  dsimp only [Function.comp_def, pred]
  rw [idxOf_slabPlaquetteAt hi]

private theorem packet_product_pin (w : Q') (K : Nat) (state : EdgeLabelling) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → state id ≤ K) →
      eliminateLinks (fun id => coeffAt (heatKernelPacket K w) (state id)) ids =
        eliminateLinks (fun id => coeffW w (state id)) ids
  | [], _ => rfl
  | id::ids, h => by
    rw [eliminateLinks, eliminateLinks, coeffAt_heatKernelPacket
      (Nat.lt_succ_of_le (h id List.mem_cons_self))]
    rw [packet_product_pin w K state ids (fun i hi => h i (List.mem_cons_of_mem id hi))]

theorem original_face_factor (w : Q') (K extent : Nat) (state : EdgeLabelling)
    (hb : ∀ id, id ∈ slabPhysicalFaceEdges extent → state id ≤ K) :
    slabParametricKPhysicalFaceFactor w K extent state ≈
      dimensionProduct state (slabPhysicalFaceEdges extent) *
        qpow w (casimirSum state (slabPhysicalFaceEdges extent)) := by
  unfold slabParametricKPhysicalFaceFactor
  rw [packet_product_pin w K state _ hb]
  exact coefficient_product w state _

def pairPower (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  casimirSum pair.1 (slabPhysicalFaceEdges (responseExtent margin)) +
    casimirSum pair.2 (slabPhysicalFaceEdges (responseExtent margin))

/-- Original signed Haar term with ALL original representation dimensions. -/
def signedAmplitude (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  (dimensionProduct pair.1 (slabPhysicalFaceEdges (responseExtent margin)) *
    dimensionProduct pair.2 (slabPhysicalFaceEdges (responseExtent margin))) *
      pairTerm margin pair.1 pair.2

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem original_pair_power (w : Q') (K margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hb : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → pair.1 id ≤ K ∧ pair.2 id ≤ K) :
    weightedPairTerm w K margin pair ≈ signedAmplitude margin pair * qpow w (pairPower margin pair) := by
  have hf := qmul (original_face_factor w K _ pair.1 (fun id hi => (hb id hi).1))
    (original_face_factor w K _ pair.2 (fun id hi => (hb id hi).2))
  have hp := Q'.eqv_trans _ _ _ hf (mul_shuffle _ _ _ _)
  have hs := Q'.eqv_trans _ _ _ hp (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (HeatKernelRGStep.qpow_add w _ _)))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hs) ?_
  unfold signedAmplitude
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem retained_power_minimum {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin))) :
    36 ≤ pairPower margin pair := by
  have ha := original_retained_pair_minimum_twelve hs hp
  rw [positiveFaces_length, positiveFaces_length] at ha
  have hl := three_count_le pair.1 (slabPhysicalFaceEdges (responseExtent margin))
  have hr := three_count_le pair.2 (slabPhysicalFaceEdges (responseExtent margin))
  unfold pairPower
  omega

/-- Power 36 allows exactly twelve occupied faces, all in the fundamental representation. -/
theorem retained_minimal_power_fundamental {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36) :
    (positiveFaces (responseExtent margin) pair.1).length +
        (positiveFaces (responseExtent margin) pair.2).length = 12 ∧
      ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → pair.1 id ≤ 1 ∧ pair.2 id ≤ 1 := by
  have ha := original_retained_pair_minimum_twelve hs hp
  rw [positiveFaces_length, positiveFaces_length] at ha ⊢
  have hl := casimir_decomposition pair.1 (slabPhysicalFaceEdges (responseExtent margin))
  have hr := casimir_decomposition pair.2 (slabPhysicalFaceEdges (responseExtent margin))
  unfold pairPower at he
  have zl : excessSum pair.1 (slabPhysicalFaceEdges (responseExtent margin)) = 0 := by omega
  have zr : excessSum pair.2 (slabPhysicalFaceEdges (responseExtent margin)) = 0 := by omega
  constructor
  · omega
  · intro id hi
    exact ⟨zero_excess_small pair.1 _ zl id hi,zero_excess_small pair.2 _ zr id hi⟩

/-- Explicit division-free cofactor; no sign claim about the retained amplitude. -/
def pairResidual (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  signedAmplitude margin pair * qpow w (pairPower margin pair - 36)

theorem retained_pair_factorization (w : Q') {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin))) :
    weightedPairTerm w K margin pair ≈ qpow w 36 * pairResidual w margin pair := by
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  exact Q'.eqv_trans _ _ _ (original_pair_power w K margin pair
    (fun id _ => bounded K selected pair hm id))
    (extract_floor w (signedAmplitude margin pair) 36 (pairPower margin pair) (retained_power_minimum hs hp))

end YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower

#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.positiveFaces_length
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.original_face_factor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.pairPower
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.signedAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.original_pair_power
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.retained_power_minimum
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.retained_minimal_power_fundamental
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.pairResidual
#print axioms YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower.retained_pair_factorization
