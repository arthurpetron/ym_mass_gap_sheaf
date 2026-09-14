/-
# The ORIGINAL spatial-defect remainder has an exact w^42 factor

The finite incidence parity law applies to either original connected
moment channel. Hence nonzero original pairs have even Casimir power.
The all-spin arithmetic and prior literal leading-tube uniqueness remove
every non-tube amplitude below power 42. At power 42 all fourteen replica
occupations are fundamental.

The exact cofactor of the actual spatial-defect remainder retains every
signed Haar amplitude, dimension and original detached partition square.
It is defined without division by w, for all rational nomes and K>=1.
Its magnitude, positive full response and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabPairChannelParity
import YMGap.Continuum.SU2FiniteCasimirEvenExcess
import YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
import YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound

namespace YMGap.Continuum.BF4ExactSlabSpatialHeatPower42

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2FiniteCasimirEvenExcess
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabConnectedReplicaArea
open YMGap.Continuum.BF4ExactSlabNonTubeHeatPower
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem oddFaces_length (extent : Nat) (state : EdgeLabelling) :
    (oddFaces extent state).length=parityCount state (slabPhysicalFaceEdges extent) := by
  let pred := fun f => decide (state ((boundaryCompleteSlabPlaquettes extent).idxOf f)%2=1)
  have he := congrArg (fun fs => (fs.filter pred).length) (slabFaceIds_map extent)
  dsimp only at he
  change ((boundaryCompleteSlabPlaquettes extent).filter pred).length = _
  rw [← he, List.filter_map, List.length_map, parityCount_filter_length]
  congr 1
  apply List.filter_congr
  intro id hi
  dsimp only [Function.comp_def, pred]
  rw [idxOf_slabPlaquetteAt hi]

theorem nonzero_pairPower_even (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) : pairPower margin pair%2=0 := by
  have h := (nonzero_pair_face_counts_even margin pair hne).1
  rw [oddFaces_length, oddFaces_length] at h
  unfold pairPower
  rw [Nat.add_mod, casimirSum_mod_two, casimirSum_mod_two, ← Nat.add_mod]
  exact h

theorem odd_power_pairTerm_zero (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (ho : pairPower margin pair%2=1) : pairTerm margin pair.1 pair.2 ≈ 0 := by
  by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
  · exact hz
  · have he := nonzero_pairPower_even margin pair hz
    omega

theorem nonTube_sub42_amplitude_zero {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (ht : ids ≠ tubeIds margin) (hpower : pairPower margin pair < 42) : signedAmplitude margin pair ≈ 0 := by
  by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
  · exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)
  · have ha := original_retained_pair_minimum_twelve hs hp
    rw [positiveFaces_length, positiveFaces_length] at ha
    have he := paired_even_sub42_eq36 pair.1 pair.2 _ ha hpower (nonzero_pairPower_even margin pair hz)
    exact nonTube_leading_amplitude_zero hs hp hK ht he

theorem retained_power42_fundamental {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) :
    (positiveFaces (responseExtent margin) pair.1).length+(positiveFaces (responseExtent margin) pair.2).length=14 ∧
      ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → pair.1 id ≤ 1 ∧ pair.2 id ≤ 1 := by
  have ha := original_retained_pair_minimum_twelve hs hp
  rw [positiveFaces_length, positiveFaces_length] at ha ⊢
  exact paired_power42_fundamental pair.1 pair.2 _ ha he

def pairResidual42 (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  signedAmplitude margin pair*qpow w (pairPower margin pair-42)

theorem nonTube_pair_factorization42 (w : Q') {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (ht : ids ≠ tubeIds margin) : weightedPairTerm w K margin pair ≈ qpow w 42*pairResidual42 w margin pair := by
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  refine Q'.eqv_trans _ _ _ (original_pair_power w K margin pair (fun id _ => bounded K ids pair hm id)) ?_
  by_cases hf : 42 ≤ pairPower margin pair
  · exact extract_floor w (signedAmplitude margin pair) 42 (pairPower margin pair) hf
  · have hz := nonTube_sub42_amplitude_zero hK hs hp ht (by omega)
    have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair)) hz) (Q'.zero_mul_eqv _)
    have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (qpow w 42) _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair-42)) hz) (Q'.zero_mul_eqv _)))
      (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hr)

def spatialHeatResidual42 (w : Q') (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (pairResidual42 w margin)
    ((corePairs K margin time ids).filter (spatialDefectKeep margin))*detachedSquare w K margin ids)
    (shortOtherCores 33 margin)

/-- The actual remaining signed branch, including each ORIGINAL detached partition. -/
theorem original_spatial_remainder_factorization42 (w : Q') (K margin time : Nat) (hK : 1 ≤ K) :
    spatialDefectRemainder w K margin time ≈ qpow w 42*spatialHeatResidual42 w K margin time := by
  apply Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ (shortOtherCores 33 margin) (by
    intro ids hs
    have h := listQSum_congr_on _ _ ((corePairs K margin time ids).filter (spatialDefectKeep margin))
      (fun pair hp => nonTube_pair_factorization42 w hK (shortOtherCores_connected hs)
        (List.mem_filter.mp hp).1 (shortOtherCores_window hs).2.2)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
      (Q'.eqv_trans _ _ _ h (listQSum_mul_left _ _ _))) (Q'.mul_assoc_eqv _ _ _)))
  exact listQSum_mul_left _ _ _

theorem original_numerator_lower_with_spatial_heat42 (K margin time : Nat) (hK : 1 ≤ K) :
    spatialAllowance*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) +
      qpow nome 42*spatialHeatResidual42 nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _
    (original_spatial_remainder_factorization42 nome K margin time hK)))
    (original_numerator_lower_with_spatial_remainder K margin time hK)

end YMGap.Continuum.BF4ExactSlabSpatialHeatPower42

#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.oddFaces_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.nonzero_pairPower_even
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.odd_power_pairTerm_zero
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.nonTube_sub42_amplitude_zero
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.retained_power42_fundamental
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.pairResidual42
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.nonTube_pair_factorization42
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.spatialHeatResidual42
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.original_spatial_remainder_factorization42
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeatPower42.original_numerator_lower_with_spatial_heat42
