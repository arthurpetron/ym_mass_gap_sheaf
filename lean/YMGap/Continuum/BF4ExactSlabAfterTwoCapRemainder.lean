/-
# Absorb all remaining original two-cap terms; leave at least four spatial faces

The exact split retains the SAME original pair weights and each detached
partition square. After the two-cap bound, the fixed-nome reference is
(1/4-2^-19-2^-26-2^-14)*w^36*Z_full^2. Every nonzero retained term has
at least four spatial odd faces, and the actual remainder keeps its
exact w^48 factor. Its aggregate magnitude and positive full response
remain OPEN, as do full realization and continuum/Clay.
-/

import YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound

namespace YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.BF4ExactSlabTwoCapPairCount
open YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound
open YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder
open YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48
open YMGap.Continuum.BF4ExactSlabPairChannelParity
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
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def afterTwoCapKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  afterMeans42Keep margin pair && !(twoCapKeep margin pair)

def afterTwoCapRemainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (afterTwoCapKeep margin)

theorem afterTwoCap_spatial_minimum_four (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hk : afterTwoCapKeep margin pair=true) :
    4 ≤ pairSpatial margin pair := by
  have hkeep := Bool.and_eq_true_iff.mp hk
  have hs := (Bool.and_eq_true_iff.mp hkeep.1).1
  have htwo := nonzero_spatial_minimum_two margin pair hne (spatialDefectKeep_nonempty hs)
  have he := (nonzero_pair_face_counts_even margin pair hne).2
  by_cases hfour : 4 ≤ pairSpatial margin pair
  · exact hfour
  · have hsp : pairSpatial margin pair=2 := by omega
    have ht : twoCapKeep margin pair=true := decide_eq_true ⟨hsp,hne,hkeep.1⟩
    rw [ht] at hkeep
    cases hkeep.2

private theorem twoCap_parent_filter (margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    (xs.filter (afterMeans42Keep margin)).filter (twoCapKeep margin)=xs.filter (twoCapKeep margin) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro pair _
  cases hk : twoCapKeep margin pair with
  | false => rfl
  | true => exact (of_decide_eq_true hk).2.2

theorem afterMeans_pair_sum_twoCap (w : Q') (K margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) (xs.filter (afterMeans42Keep margin)) ≈
      listQSum (weightedPairTerm w K margin) (xs.filter (twoCapKeep margin))+
        listQSum (weightedPairTerm w K margin) (xs.filter (afterTwoCapKeep margin)) := by
  have hp := Q'.eqv_trans _ _ _ (listQSum_perm (weightedPairTerm w K margin)
    (List.filter_append_perm (twoCapKeep margin) (xs.filter (afterMeans42Keep margin))).symm)
    (sum_append _ _ _)
  rw [twoCap_parent_filter] at hp
  have hr : (xs.filter (afterMeans42Keep margin)).filter (fun pair => !(twoCapKeep margin pair))=
      xs.filter (afterTwoCapKeep margin) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro pair _
    exact Bool.and_comm _ _
  rw [hr] at hp
  exact hp

theorem original_afterMeans_split_twoCap (w : Q') (K margin time : Nat) :
    afterMeans42Remainder w K margin time ≈ twoCapRemainder w K margin time+afterTwoCapRemainder w K margin time := by
  refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ids _ => ?_)) (listQSum_add _ _ _)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
    (afterMeans_pair_sum_twoCap w K margin (corePairs K margin time ids))) (Q'.add_mul_eqv _ _ _)

def afterTwoCapAllowance : Q' := afterMeans42Allowance + -twoCapAllowance

theorem afterTwoCapAllowance_pos : (0 : Q') < afterTwoCapAllowance := by decide

/-- Reusable rational absorption; all inputs refer to the supplied exact signed split. -/
theorem absorb_signed_branch (a b Z S M R N : Q') (hs : S ≈ M+R)
    (hb : Q'.abs M ≤ b*Z) (hN : a*Z+S ≤ N) : (a + -b)*Z+R ≤ N := by
  have hl := Q'.le_trans' _ _ _ (Q'.neg_le_neg hb) (ExpNeg.neg_abs_le M)
  have he : (a + -b)*Z+R ≈ a*Z+(-(b*Z)+R) := poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (.var 3))
    (.add (.mul (.var 0) (.var 2)) (.add (.neg (.mul (.var 1) (.var 2))) (.var 3)))
    (by decide) (fun i => if i=0 then a else if i=1 then b else if i=2 then Z else R)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left (a*Z) _ _ (Q'.add_le_add_right _ _ R hl))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _ hs)) hN))

theorem original_numerator_lower_after_twoCap (K margin time : Nat) (hK : 1 ≤ K) :
    afterTwoCapAllowance*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin))+afterTwoCapRemainder nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  absorb_signed_branch afterMeans42Allowance twoCapAllowance _ _ _ _ _
    (original_afterMeans_split_twoCap nome K margin time)
    (original_twoCap_remainder_bound K margin time)
    (original_numerator_lower_after_means42 K margin time hK)

def afterTwoCapHeatResidual48 (w : Q') (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (afterMeansPairResidual48 w margin)
    ((corePairs K margin time ids).filter (afterTwoCapKeep margin))*detachedSquare w K margin ids)
    (shortOtherCores 33 margin)

theorem original_afterTwoCap_factorization48 (w : Q') (K margin time : Nat) :
    afterTwoCapRemainder w K margin time ≈ qpow w 48*afterTwoCapHeatResidual48 w K margin time := by
  apply Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ (shortOtherCores 33 margin) (by
    intro ids hs
    have h := listQSum_congr_on _ _ ((corePairs K margin time ids).filter (afterTwoCapKeep margin))
      (fun pair hp => afterMeans42_pair_factorization48 w (shortOtherCores_connected hs)
        (List.mem_filter.mp hp).1 (Bool.and_eq_true_iff.mp (List.mem_filter.mp hp).2).1)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
      (Q'.eqv_trans _ _ _ h (listQSum_mul_left _ _ _))) (Q'.mul_assoc_eqv _ _ _)))
  exact listQSum_mul_left _ _ _

theorem original_numerator_lower_with_afterTwoCap_heat48 (K margin time : Nat) (hK : 1 ≤ K) :
    afterTwoCapAllowance*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin))+
      qpow nome 48*afterTwoCapHeatResidual48 nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _
    (original_afterTwoCap_factorization48 nome K margin time)))
    (original_numerator_lower_after_twoCap K margin time hK)

end YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder

#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterTwoCapKeep
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterTwoCapRemainder
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterTwoCap_spatial_minimum_four
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterMeans_pair_sum_twoCap
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.original_afterMeans_split_twoCap
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterTwoCapAllowance
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterTwoCapAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.absorb_signed_branch
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.original_numerator_lower_after_twoCap
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.afterTwoCapHeatResidual48
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.original_afterTwoCap_factorization48
#print axioms YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder.original_numerator_lower_with_afterTwoCap_heat48
