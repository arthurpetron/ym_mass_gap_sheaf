/-
# Absorb the original power-42 means sector into the response reference

Split the SAME spatial-defect remainder into the proved means-42 sector
and its literal complementary filter. This identity holds at every rational
nome. At the unchanged nome 1/1024, absorb the signed means sector with
its own detached partitions. The positive reference coefficient becomes
1/4-2^-19-2^-26. The complementary original spatial remainder is OPEN;
no positive full response or continuum/Clay theorem is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPower42MeansBound

namespace YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.BF4ExactSlabPower42MeansCount
open YMGap.Continuum.BF4ExactSlabPower42MeansBound
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound
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

def afterMeans42Keep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  spatialDefectKeep margin pair && !(means42Keep margin pair)

def afterMeans42Remainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (afterMeans42Keep margin)

private theorem means42_spatial_filter (margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    (xs.filter (spatialDefectKeep margin)).filter (means42Keep margin)=xs.filter (means42Keep margin) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro pair _
  cases hm : means42Keep margin pair with
  | false => rfl
  | true => exact (of_decide_eq_true hm).2.2.1

theorem spatial_pair_sum_after_means42 (w : Q') (K margin : Nat)
    (xs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) (xs.filter (spatialDefectKeep margin)) ≈
      listQSum (weightedPairTerm w K margin) (xs.filter (means42Keep margin))+
        listQSum (weightedPairTerm w K margin) (xs.filter (afterMeans42Keep margin)) := by
  have hp := Q'.eqv_trans _ _ _
    (listQSum_perm (weightedPairTerm w K margin)
      (List.filter_append_perm (means42Keep margin) (xs.filter (spatialDefectKeep margin))).symm)
    (sum_append _ _ _)
  rw [means42_spatial_filter] at hp
  have hr : (xs.filter (spatialDefectKeep margin)).filter (fun pair => !(means42Keep margin pair)) =
      xs.filter (afterMeans42Keep margin) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro pair _
    exact Bool.and_comm _ _
  rw [hr] at hp
  exact hp

theorem original_spatial_split_after_means42 (w : Q') (K margin time : Nat) :
    spatialDefectRemainder w K margin time ≈
      means42Remainder w K margin time+afterMeans42Remainder w K margin time := by
  refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ids _ => ?_)) (listQSum_add _ _ _)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
    (spatial_pair_sum_after_means42 w K margin (corePairs K margin time ids))) (Q'.add_mul_eqv _ _ _)

def afterMeans42Allowance : Q' := spatialAllowance + -means42Allowance

theorem afterMeans42Allowance_pos : (0 : Q') < afterMeans42Allowance := by decide

private theorem absorb_means (a b Z S M R N : Q') (hs : S ≈ M+R)
    (hb : Q'.abs M ≤ b*Z) (hN : a*Z+S ≤ N) : (a + -b)*Z+R ≤ N := by
  have hl := Q'.le_trans' _ _ _ (Q'.neg_le_neg hb) (ExpNeg.neg_abs_le M)
  have he : (a + -b)*Z+R ≈ a*Z+(-(b*Z)+R) := poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (.var 3))
    (.add (.mul (.var 0) (.var 2)) (.add (.neg (.mul (.var 1) (.var 2))) (.var 3)))
    (by decide) (fun i => if i=0 then a else if i=1 then b else if i=2 then Z else R)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left (a*Z) _ _ (Q'.add_le_add_right _ _ R hl))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _ hs)) hN))

theorem original_numerator_lower_after_means42 (K margin time : Nat) (hK : 1 ≤ K) :
    afterMeans42Allowance*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin))+afterMeans42Remainder nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  absorb_means spatialAllowance means42Allowance _ _ _ _ _
    (original_spatial_split_after_means42 nome K margin time)
    (original_means42_remainder_bound K margin time)
    (original_numerator_lower_with_spatial_remainder K margin time hK)

end YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder

#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.afterMeans42Keep
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.afterMeans42Remainder
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.spatial_pair_sum_after_means42
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.original_spatial_split_after_means42
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.afterMeans42Allowance
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.afterMeans42Allowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder.original_numerator_lower_after_means42
