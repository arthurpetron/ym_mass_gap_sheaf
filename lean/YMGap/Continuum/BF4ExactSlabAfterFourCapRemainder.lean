/-
# Absorb the original four-face family; retain a six-face, power-54 remainder

The original signed sum splits exactly, with its OWN detached partitions.
After absorption the reference is
(1/4-2^-19-2^-26-2^-14-2^-14)*w^36*Z_full^2 at fixed nome.
Every nonzero remaining pair has at least six spatial odd faces, hence
at least eighteen positive occupations and Casimir power at least 54.
The actual remainder factors by w^54 at every rational nome, including 0.
Its aggregate bound, positive full response, continuum and Clay are OPEN.
-/

import YMGap.Continuum.BF4ExactSlabFourCapRemainderBound

namespace YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.BF4ExactSlabFourCapPairCount
open YMGap.Continuum.BF4ExactSlabFourCapPairSum
open YMGap.Continuum.BF4ExactSlabFourCapRemainderBound
open YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def afterFourCapKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  afterTwoCapKeep margin pair && !(fourCapKeep margin pair)

def afterFourCapRemainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (afterFourCapKeep margin)

theorem afterFourCap_spatial_minimum_six (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hk : afterFourCapKeep margin pair=true) :
    6 ≤ pairSpatial margin pair := by
  have hkeep := Bool.and_eq_true_iff.mp hk
  have hfour := afterTwoCap_spatial_minimum_four margin pair hne hkeep.1
  have he := (nonzero_pair_face_counts_even margin pair hne).2
  by_cases hsix : 6 ≤ pairSpatial margin pair
  · exact hsix
  · have hsp : pairSpatial margin pair=4 := by omega
    have ht : fourCapKeep margin pair=true := decide_eq_true ⟨hsp,hne,hkeep.1⟩
    rw [ht] at hkeep
    cases hkeep.2

private theorem fourCap_parent_filter (margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    (xs.filter (afterTwoCapKeep margin)).filter (fourCapKeep margin)=xs.filter (fourCapKeep margin) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro pair _
  cases hk : fourCapKeep margin pair with
  | false => rfl
  | true => exact (of_decide_eq_true hk).2.2

theorem afterTwo_pair_sum_fourCap (w : Q') (K margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) (xs.filter (afterTwoCapKeep margin)) ≈
      listQSum (weightedPairTerm w K margin) (xs.filter (fourCapKeep margin))+
        listQSum (weightedPairTerm w K margin) (xs.filter (afterFourCapKeep margin)) := by
  have hp := Q'.eqv_trans _ _ _ (listQSum_perm (weightedPairTerm w K margin)
    (List.filter_append_perm (fourCapKeep margin) (xs.filter (afterTwoCapKeep margin))).symm)
    (sum_append _ _ _)
  rw [fourCap_parent_filter] at hp
  have hr : (xs.filter (afterTwoCapKeep margin)).filter (fun pair => !(fourCapKeep margin pair))=
      xs.filter (afterFourCapKeep margin) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro pair _
    exact Bool.and_comm _ _
  rw [hr] at hp
  exact hp

theorem original_afterTwo_split_fourCap (w : Q') (K margin time : Nat) :
    afterTwoCapRemainder w K margin time ≈ fourCapRemainder w K margin time+afterFourCapRemainder w K margin time := by
  refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ids _ => ?_)) (listQSum_add _ _ _)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
    (afterTwo_pair_sum_fourCap w K margin (corePairs K margin time ids))) (Q'.add_mul_eqv _ _ _)

def afterFourCapAllowance : Q' := afterTwoCapAllowance + -fourCapAllowance

theorem afterFourCapAllowance_pos : (0 : Q') < afterFourCapAllowance := by decide

theorem original_numerator_lower_after_fourCap (K margin time : Nat) (hK : 1 ≤ K) :
    afterFourCapAllowance*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin))+afterFourCapRemainder nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  absorb_signed_branch afterTwoCapAllowance fourCapAllowance _ _ _ _ _
    (original_afterTwo_split_fourCap nome K margin time)
    (original_fourCap_remainder_bound K margin time)
    (original_numerator_lower_after_twoCap K margin time hK)

theorem afterFourCap_power_minimum54 {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hs : ids ∈ shortOtherCores 33 margin)
    (hp : pair ∈ corePairs K margin time ids) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hk : afterFourCapKeep margin pair=true) : 54 ≤ pairPower margin pair := by
  have ha := original_spatial_positive_floor hs hp
  have hsp := afterFourCap_spatial_minimum_six margin pair hne hk
  rw [positiveFaces_length,positiveFaces_length] at ha
  have hl := casimir_decomposition pair.1 (slabPhysicalFaceEdges (responseExtent margin))
  have hr := casimir_decomposition pair.2 (slabPhysicalFaceEdges (responseExtent margin))
  unfold pairPower
  omega

theorem afterFourCap_sub54_amplitude_zero {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hs : ids ∈ shortOtherCores 33 margin)
    (hp : pair ∈ corePairs K margin time ids) (hk : afterFourCapKeep margin pair=true)
    (hpower : pairPower margin pair < 54) : signedAmplitude margin pair ≈ 0 := by
  have hz : pairTerm margin pair.1 pair.2 ≈ 0 := by
    by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
    · exact hz
    · have h := afterFourCap_power_minimum54 hs hp hz hk
      omega
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)

def afterFourCapPairResidual54 (w : Q') (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  signedAmplitude margin pair*qpow w (pairPower margin pair-54)

theorem afterFourCap_pair_factorization54 (w : Q') {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hs : ids ∈ shortOtherCores 33 margin)
    (hp : pair ∈ corePairs K margin time ids) (hk : afterFourCapKeep margin pair=true) :
    weightedPairTerm w K margin pair ≈ qpow w 54*afterFourCapPairResidual54 w margin pair := by
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  refine Q'.eqv_trans _ _ _ (original_pair_power w K margin pair (fun id _ => bounded K ids pair hm id)) ?_
  by_cases hf : 54 ≤ pairPower margin pair
  · exact extract_floor w (signedAmplitude margin pair) 54 (pairPower margin pair) hf
  · have hz := afterFourCap_sub54_amplitude_zero hs hp hk (by omega)
    have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair)) hz)
      (Q'.zero_mul_eqv _)
    have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (qpow w 54) _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow w (pairPower margin pair-54)) hz)
        (Q'.zero_mul_eqv _))) (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hr)

def afterFourCapHeatResidual54 (w : Q') (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (afterFourCapPairResidual54 w margin)
    ((corePairs K margin time ids).filter (afterFourCapKeep margin))*detachedSquare w K margin ids)
    (shortOtherCores 33 margin)

theorem original_afterFourCap_factorization54 (w : Q') (K margin time : Nat) :
    afterFourCapRemainder w K margin time ≈ qpow w 54*afterFourCapHeatResidual54 w K margin time := by
  apply Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ (shortOtherCores 33 margin) (by
    intro ids hs
    have h := listQSum_congr_on _ _ ((corePairs K margin time ids).filter (afterFourCapKeep margin))
      (fun pair hp => afterFourCap_pair_factorization54 w hs (List.mem_filter.mp hp).1 (List.mem_filter.mp hp).2)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
      (Q'.eqv_trans _ _ _ h (listQSum_mul_left _ _ _))) (Q'.mul_assoc_eqv _ _ _)))
  exact listQSum_mul_left _ _ _

theorem original_numerator_lower_with_afterFourCap_heat54 (K margin time : Nat) (hK : 1 ≤ K) :
    afterFourCapAllowance*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin))+
      qpow nome 54*afterFourCapHeatResidual54 nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _
    (original_afterFourCap_factorization54 nome K margin time)))
    (original_numerator_lower_after_fourCap K margin time hK)

end YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder

#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCapKeep
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCapRemainder
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCap_spatial_minimum_six
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterTwo_pair_sum_fourCap
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.original_afterTwo_split_fourCap
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCapAllowance
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCapAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.original_numerator_lower_after_fourCap
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCap_power_minimum54
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCap_sub54_amplitude_zero
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCapPairResidual54
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCap_pair_factorization54
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.afterFourCapHeatResidual54
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.original_afterFourCap_factorization54
#print axioms YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder.original_numerator_lower_with_afterFourCap_heat54
