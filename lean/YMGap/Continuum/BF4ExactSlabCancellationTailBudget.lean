/-
# Partition-relative tails after exact small-core cancellation

Small connecting cores can exist geometrically. This theorem does not
give them a false size floor: it removes them only when their ORIGINAL
connected coefficient is proved zero. Detached partition squares remain
in the exact sum. The retained subfamily inherits the existing two-probe
count, giving the existing explicit budget with the new minimum size.
The cancellation premise is algebraic; the original shifted-probe
instance is supplied separately, not assumed as an analytic frontier.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget

namespace YMGap.Continuum.BF4ExactSlabCancellationTailBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

def largeConnectingAnchors (extent : Nat) (left right : List Z4Link) (ambient : List Nat)
    (minimumSize : Nat) : List (List Nat) :=
  (connectingAnchors extent left right ambient).filter (fun ids => decide (minimumSize ≤ ids.length))

theorem large_connecting_weight_tail {rate : Q'} (hr : (0 : Q') ≤ rate) (hs : entropyRate 625 rate < 1)
    {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ambient : List Nat) (minimumSize : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    listQSum (fun ids => rate^ids.length) (largeConnectingAnchors extent left right ambient minimumSize) ≤
      tailBudget (countPrefactor P Q) 625 minimumSize rate hs := by
  apply size_sum_bound _ List.length (countPrefactor P Q) 625 minimumSize ambient.length hr hs
  · intro ids hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  · intro ids hi
    exact (selected_sublist (connecting_selected (List.mem_filter.mp hi).1)).length_le
  · intro n
    have hsub : ((largeConnectingAnchors extent left right ambient minimumSize).filter
        (fun ids => decide (n = ids.length))).Sublist
        ((connectingAnchors extent left right ambient).filter (fun ids => decide (n = ids.length))) :=
      List.Sublist.filter _ List.filter_sublist
    have he : (connectingAnchors extent left right ambient).filter (fun ids => decide (n = ids.length)) =
        (connectingAnchors extent left right ambient).filter (fun ids => decide (ids.length = n)) := by
      apply List.filter_congr
      intro ids _
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (eq_comm : n = ids.length ↔ ids.length = n)
    exact Nat.le_trans hsub.length_le (by rw [he]; exact connectingAtSize_length_le P Q extent ambient n hn hphys)

theorem resummed_large_expansion (w : Q') (K extent : Nat) (p q : RatPoly)
    (c d : Q') (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (minimumSize : Nat) (hn : ambient.Nodup)
    (hzero : ∀ ids, ids ∈ connectingAnchors extent left right ambient → ids.length < minimumSize →
      connectedCoefficient w K extent p q ids ≈ 0) :
    connectedNumerator w K extent ambient p q ≈
      listQSum (fun ids => connectedCoefficient w K extent p q ids *
        partitionSquare w K extent (detachedIds extent (left++right) ids ambient))
        (largeConnectingAnchors extent left right ambient minimumSize) := by
  refine Q'.eqv_trans _ _ _
    (connectedNumerator_connecting_expansion w K extent p q left right Ip.support Iq.support hl hr ambient hn) ?_
  apply sum_filter_zero
  intro ids hi hd
  have hnot : ¬ minimumSize ≤ ids.length := of_decide_eq_false hd
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (hzero ids hi (by omega))) (Q'.zero_mul_eqv _)

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x :: xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add (h x List.mem_cons_self) (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

/-- Same explicit budget and full partition square, now with proved zeros instead of a false geometric floor. -/
theorem connectedNumerator_tail_of_small_zero {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K extent : Nat) (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (minimumSize : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hzero : ∀ ids, ids ∈ connectingAnchors extent left right ambient → ids.length < minimumSize →
      connectedCoefficient w K extent p q ids ≈ 0) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤
      twoProbeBudget P Q w hd hs c d minimumSize * partitionSquare w K extent ambient := by
  let r := adjustedCoreRate w hd
  let A := (c*d+c*d)*probePrefactor w hd (left++right).length
  let Z := partitionSquare w K extent ambient
  let anchors := largeConnectingAnchors extent left right ambient minimumSize
  have hsum : Q'.abs (listQSum (fun ids => connectedCoefficient w K extent p q ids *
      partitionSquare w K extent (detachedIds extent (left++right) ids ambient)) anchors) ≤
      listQSum (fun ids => (A*r^ids.length)*Z) anchors := by
    apply abs_sum_bound
    intro ids hi
    exact resummed_geometric_bound hw0 hw1 hsmall hd K extent p q c d (left++right) Ip Iq
      (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      (hr.mono (fun _ h => List.mem_append.mpr (Or.inr h))) ambient ids hn hphys
      (connecting_selected (List.mem_filter.mp hi).1)
  have hfactor : listQSum (fun ids => (A*r^ids.length)*Z) anchors ≈
      (A*listQSum (fun ids => r^ids.length) anchors)*Z :=
    Q'.eqv_trans _ _ _ (listQSum_mul_right _ Z anchors)
      (Q'.mul_eqv_congr_right _ _ Z (listQSum_mul_left A _ anchors))
  have ha : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)
      (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)) (probePrefactor_nonnegative w hd _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (resummed_large_expansion w K extent p q c d Ip Iq left right hl hr ambient minimumSize hn hzero)))
    (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.mul_le_mul_of_nonneg_right _ _ Z (Q'.mul_le_mul_of_nonneg_left _ _ A
        (large_connecting_weight_tail (adjustedCoreRate_nonnegative hw0 hd) hs P Q extent ambient minimumSize hn hphys) ha)
        (SumOfSquares.q_mul_self_nonneg _))))

end YMGap.Continuum.BF4ExactSlabCancellationTailBudget

#print axioms YMGap.Continuum.BF4ExactSlabCancellationTailBudget.largeConnectingAnchors
#print axioms YMGap.Continuum.BF4ExactSlabCancellationTailBudget.large_connecting_weight_tail
#print axioms YMGap.Continuum.BF4ExactSlabCancellationTailBudget.resummed_large_expansion
#print axioms YMGap.Continuum.BF4ExactSlabCancellationTailBudget.connectedNumerator_tail_of_small_zero
