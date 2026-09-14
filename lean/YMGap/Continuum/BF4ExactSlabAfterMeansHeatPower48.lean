/-
# The ORIGINAL remainder after means-42 absorption has an exact w^48 factor

The power-42 joint channel is excluded geometrically. Every nonzero
power-42 spatial term is therefore already in the absorbed means sector.
Every nonzero spatial pair needs fourteen positive occupations. The SU(2)
Casimir excess and original channel parity leave no other power below 48.
No division by w is used:
the remaining cofactor retains the actual signed amplitudes, dimensions,
pair enumeration and each core's own detached partition square.

This is an exact identity at every rational nome and cutoff, NOT a bound
on the cofactor. Positive full response and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabPower42JointExclusion
import YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder

namespace YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteCasimirFirstExcess
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.BF4ExactSlabPower42JointExclusion
open YMGap.Continuum.BF4ExactSlabPower42SpatialBudget
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder
open YMGap.Continuum.BF4ExactSlabPower42MeansCount
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem oddFaces_sublist_positive (extent : Nat) (state : EdgeLabelling) :
    (oddFaces extent state).Sublist (positiveFaces extent state) := by
  let pos := fun face => decide (0 < state ((Z4HalfTimeReflectionGeometry.boundaryCompleteSlabPlaquettes extent).idxOf face))
  have hs : ((oddFaces extent state).filter pos).Sublist
      ((Z4HalfTimeReflectionGeometry.boundaryCompleteSlabPlaquettes extent).filter pos) :=
    List.Sublist.filter pos List.filter_sublist
  have he : (oddFaces extent state).filter pos=oddFaces extent state := by
    apply List.filter_eq_self.mpr
    intro face hf
    have ho := of_decide_eq_true (List.mem_filter.mp hf).2
    exact decide_eq_true (by omega)
  rw [he] at hs
  exact hs

theorem original_spatial_minimum_fourteen {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hd : spatialDefectKeep margin pair=true) :
    14 ≤ (positiveFaces (responseExtent margin) pair.1).length+
      (positiveFaces (responseExtent margin) pair.2).length := by
  have hb := original_temporal_spatial_budget hs hp
  have hsp := nonzero_spatial_minimum_two margin pair hne (spatialDefectKeep_nonempty hd)
  have hl := (List.Sublist.filter (fun face => decide ((dirsOf face.2).2 ≠ Dir4.x3))
    (oddFaces_sublist_positive (responseExtent margin) pair.1)).length_le
  have hr := (List.Sublist.filter (fun face => decide ((dirsOf face.2).2 ≠ Dir4.x3))
    (oddFaces_sublist_positive (responseExtent margin) pair.2)).length_le
  change (spatialOddFaces margin pair.1).length ≤ (spatialFaces (positiveFaces _ pair.1)).length at hl
  change (spatialOddFaces margin pair.2).length ≤ (spatialFaces (positiveFaces _ pair.2)).length at hr
  unfold pairSpatial at hsp
  omega

/-- Above an even occupation floor, the first even Casimir band has only its base power. -/
theorem paired_even_first_band (floor : Nat) (left right : Nat → Nat) (ids : List Nat)
    (ha : 2*floor ≤ positiveCount left ids+positiveCount right ids)
    (hp : casimirSum left ids+casimirSum right ids < 6*floor+6)
    (he : (casimirSum left ids+casimirSum right ids)%2=0) :
    casimirSum left ids+casimirSum right ids=6*floor := by
  have hl := casimir_decomposition left ids
  have hr := casimir_decomposition right ids
  have el := excessSum_zero_or_five left ids
  have er := excessSum_zero_or_five right ids
  omega

theorem afterMeans42_power42_pairTerm_zero {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hk : afterMeans42Keep margin pair=true) :
    pairTerm margin pair.1 pair.2 ≈ 0 := by
  by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
  · exact hz
  · have hd := Bool.and_eq_true_iff.mp hk
    have hj := power42_spatial_joint_false hs hp he hz hd.1
    have hm : means42Keep margin pair=true := decide_eq_true ⟨he,hz,hd.1,hj⟩
    rw [hm] at hd
    cases hd.2

theorem afterMeans42_sub48_amplitude_zero {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (hk : afterMeans42Keep margin pair=true)
    (hpower : pairPower margin pair < 48) : signedAmplitude margin pair ≈ 0 := by
  have hz : pairTerm margin pair.1 pair.2 ≈ 0 := by
    by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
    · exact hz
    · have ha := original_spatial_minimum_fourteen hs hp hz (Bool.and_eq_true_iff.mp hk).1
      rw [positiveFaces_length,positiveFaces_length] at ha
      have he := paired_even_first_band 7 pair.1 pair.2 _ ha hpower
        (nonzero_pairPower_even margin pair hz)
      exact afterMeans42_power42_pairTerm_zero hs hp he hk
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)

def afterMeansPairResidual48 (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  signedAmplitude margin pair*qpow w (pairPower margin pair-48)

theorem afterMeans42_pair_factorization48 (w : Q') {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (hk : afterMeans42Keep margin pair=true) :
    weightedPairTerm w K margin pair ≈ qpow w 48*afterMeansPairResidual48 w margin pair := by
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  refine Q'.eqv_trans _ _ _ (original_pair_power w K margin pair (fun id _ => bounded K ids pair hm id)) ?_
  by_cases hf : 48 ≤ pairPower margin pair
  · exact extract_floor w (signedAmplitude margin pair) 48 (pairPower margin pair) hf
  · have hz := afterMeans42_sub48_amplitude_zero hs hp hk (by omega)
    have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair)) hz)
      (Q'.zero_mul_eqv _)
    have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (qpow w 48) _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair-48)) hz)
        (Q'.zero_mul_eqv _))) (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hr)

def afterMeansHeatResidual48 (w : Q') (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (afterMeansPairResidual48 w margin)
    ((corePairs K margin time ids).filter (afterMeans42Keep margin))*detachedSquare w K margin ids)
    (shortOtherCores 33 margin)

/-- Exact factorization of the actual signed complementary source, with its OWN partitions. -/
theorem original_afterMeans_remainder_factorization48 (w : Q') (K margin time : Nat) :
    afterMeans42Remainder w K margin time ≈ qpow w 48*afterMeansHeatResidual48 w K margin time := by
  apply Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ (shortOtherCores 33 margin) (by
    intro ids hs
    have h := listQSum_congr_on _ _ ((corePairs K margin time ids).filter (afterMeans42Keep margin))
      (fun pair hp => afterMeans42_pair_factorization48 w (shortOtherCores_connected hs)
        (List.mem_filter.mp hp).1 (List.mem_filter.mp hp).2)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
      (Q'.eqv_trans _ _ _ h (listQSum_mul_left _ _ _))) (Q'.mul_assoc_eqv _ _ _)))
  exact listQSum_mul_left _ _ _

theorem original_numerator_lower_with_afterMeans_heat48 (K margin time : Nat) (hK : 1 ≤ K) :
    afterMeans42Allowance*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin))+
      qpow nome 48*afterMeansHeatResidual48 nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _
    (original_afterMeans_remainder_factorization48 nome K margin time)))
    (original_numerator_lower_after_means42 K margin time hK)

end YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48

#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.oddFaces_sublist_positive
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.original_spatial_minimum_fourteen
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.paired_even_first_band
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.afterMeans42_power42_pairTerm_zero
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.afterMeans42_sub48_amplitude_zero
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.afterMeansPairResidual48
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.afterMeans42_pair_factorization48
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.afterMeansHeatResidual48
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.original_afterMeans_remainder_factorization48
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48.original_numerator_lower_with_afterMeans_heat48
