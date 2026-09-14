/-
# Bound the whole ORIGINAL zero-spatial short-core remainder

The actual original pair-weight sum is combined with the individual
short-core detached partition comparison. At nome 1/1024 the resulting
signed remainder has absolute value <=2^-19*w^36*Z_full^2, for all K>=1,
volume margins and cut times. Both replica weights, signed Haar terms
and each original detached partition are retained.

Together with the original tube reference and large-core tail this leaves
only the actual spatial-defect remainder in the numerator lower bound.
That remainder is NOT bounded here. Positive full response, its transfer
to the thermodynamic observable, and continuum/Clay closure remain open.
-/

import YMGap.Continuum.BF4ExactSlabShortDetachedPartition
import YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
import YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum

namespace YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_flatMap)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate
open YMGap.Continuum.BF4ExactSlabShortDetachedPartition
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem sum_mul_right {A : Type} (f : A → Q') (c : Q') (xs : List A) :
    listQSum (fun x => f x*c) xs ≈ listQSum f xs*c :=
  Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ xs (fun _ _ => Q'.mul_comm_eqv _ _))
    (Q'.eqv_trans _ _ _ (listQSum_mul_left c f xs) (Q'.mul_comm_eqv _ _))

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x::xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add (h x List.mem_cons_self)
        (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

theorem signedFamily_abs_bound {A B : Type} (xs : List A) (groups : A → List B)
    (weight : B → Q') (partition : A → Q') (C : Q')
    (hp : ∀ x, x ∈ xs → (0 : Q') ≤ partition x) (hc : ∀ x, x ∈ xs → partition x ≤ C) :
    Q'.abs (listQSum (fun x => listQSum weight (groups x)*partition x) xs) ≤
      listQSum (fun b => Q'.abs (weight b)) (xs.flatMap groups)*C := by
  have h := abs_sum_bound _ (fun x => listQSum (fun b => Q'.abs (weight b)) (groups x)*C) xs (by
    intro x hx
    have ha := abs_sum_bound weight (fun b => Q'.abs (weight b)) (groups x) (fun _ _ => Q'.le_refl' _)
    have habs : Q'.abs (listQSum weight (groups x)*partition x) ≤
        Q'.abs (listQSum weight (groups x))*partition x := by
      simpa only [ExpNeg.abs_of_nonneg (hp x hx)] using
        ExpNeg.abs_mul_le (listQSum weight (groups x)) (partition x)
    exact Q'.le_trans' _ _ _ habs
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (hp x hx))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (hc x hx)
          (listQSum_nonnegative_on _ _ (fun _ _ => Q'.abs_nonneg _)))))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (sum_mul_right _ C xs)
    (Q'.mul_eqv_congr_right _ _ C (Q'.eqv_symm (listQSum_flatMap _ groups xs)))))

theorem original_zeroSpatial_abs_le_pair_sum (K margin time : Nat) :
    Q'.abs (zeroSpatialRemainder nome K margin time) ≤
      listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (zeroSpatialPairs K margin time) *
        (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
  have h := signedFamily_abs_bound (shortOtherCores 33 margin)
    (fun ids => (corePairs K margin time ids).filter (zeroSpatialKeep margin))
    (weightedPairTerm nome K margin) (detachedSquare nome K margin)
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (fun _ _ => SumOfSquares.q_mul_self_nonneg _)
    (fun _ hs => original_short_detached_square_le_two K margin hs)
  simpa only [zeroSpatialPairs, shortPairs, List.filter_flatMap, corePairs] using h

def zeroSpatialAllowance : Q' := Q'.invSucc (2^19-1)*RingNormaliser.qpow nome 36

theorem zeroSpatialAllowance_pos : (0 : Q') < zeroSpatialAllowance := by decide

/-- Original signed branch, including every detached partition square. -/
theorem original_zeroSpatial_remainder_bound (K margin time : Nat) (hK : 1 ≤ K) :
    Q'.abs (zeroSpatialRemainder nome K margin time) ≤
      zeroSpatialAllowance*partitionSquare nome K (responseExtent margin)
        (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (existingNome_original_weight_abs_sum_bound K margin time hK)
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (SumOfSquares.q_mul_self_nonneg _))
  have he (W Z : Q') : (Q'.invSucc (2^20-1)*W)*(2*Z) ≈ (Q'.invSucc (2^19-1)*W)*Z := by
    have h := poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.const 2)) (.var 1)) (.var 2)) (by decide)
      (fun i => if i=0 then Q'.invSucc (2^20-1) else if i=1 then W else Z)
    exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ Z
      (Q'.mul_eqv_congr_right _ _ W (by decide : Q'.invSucc (2^20-1)*2 ≈ Q'.invSucc (2^19-1))))
  exact Q'.le_trans' _ _ _ (original_zeroSpatial_abs_le_pair_sum K margin time)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (he _ _)))

/-- Positive reference left after the large and zero-spatial branches. -/
def spatialAllowance : Q' := tailAllowance + -zeroSpatialAllowance

theorem spatialAllowance_pos : (0 : Q') < spatialAllowance := by decide

private theorem absorb_zeroSpatial (a b Z E S D N : Q') (hs : E ≈ S+D)
    (hb : Q'.abs S ≤ b*Z) (hN : a*Z+E ≤ N) : (a + -b)*Z+D ≤ N := by
  have hl := Q'.le_trans' _ _ _ (Q'.neg_le_neg hb) (ExpNeg.neg_abs_le S)
  have he : (a + -b)*Z+D ≈ a*Z+(-(b*Z)+D) := poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (.var 3))
    (.add (.mul (.var 0) (.var 2)) (.add (.neg (.mul (.var 1) (.var 2))) (.var 3)))
    (by decide) (fun i => if i=0 then a else if i=1 then b else if i=2 then Z else D)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left (a*Z) _ _ (Q'.add_le_add_right _ _ D hl))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _ hs)) hN))

/-- Only the ACTUAL spatial-defect branch remains to control in this numerator bound. -/
theorem original_numerator_lower_with_spatial_remainder (K margin time : Nat) (hK : 1 ≤ K) :
    spatialAllowance*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) +
      spatialDefectRemainder nome K margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  absorb_zeroSpatial tailAllowance zeroSpatialAllowance _ _ _ _ _
    (original_short_remainder_split nome K margin time)
    (original_zeroSpatial_remainder_bound K margin time hK)
    (original_numerator_lower_with_short_remainder K margin hK)

end YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound

#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.signedFamily_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.original_zeroSpatial_abs_le_pair_sum
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.zeroSpatialAllowance
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.zeroSpatialAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.original_zeroSpatial_remainder_bound
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.spatialAllowance
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.spatialAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound.original_numerator_lower_with_spatial_remainder
