/-
# Original partition-relative bound for an actual subfamily of cores

The retained list is a sublist of the existing connecting anchors. It
inherits the original size count, without replacing multiplicities or
requiring a size floor on the omitted cores. Each summand keeps its own
original detached partition square. This bounds a remainder subfamily,
not merely the full numerator.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget

namespace YMGap.Continuum.BF4ExactSlabResummedSubfamilyBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem subfamily_weight_tail {rate : Q'} (hr : (0 : Q') ≤ rate) (hs : entropyRate 625 rate < 1)
    {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ambient : List Nat) (minimumSize : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (family : List (List Nat)) (hsub : family.Sublist (connectingAnchors extent left right ambient))
    (hsize : ∀ ids, ids ∈ family → minimumSize ≤ ids.length) :
    listQSum (fun ids => rate^ids.length) family ≤
      tailBudget (countPrefactor P Q) 625 minimumSize rate hs := by
  apply size_sum_bound family List.length (countPrefactor P Q) 625 minimumSize ambient.length hr hs hsize
  · intro ids hi
    exact (selected_sublist (connecting_selected (hsub.subset hi))).length_le
  · intro n
    have he : (connectingAnchors extent left right ambient).filter (fun ids => decide (n = ids.length)) =
        (connectingAnchors extent left right ambient).filter (fun ids => decide (ids.length = n)) := by
      apply List.filter_congr
      intro ids _
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (eq_comm : n = ids.length ↔ ids.length = n)
    have h := (hsub.filter (fun ids => decide (n = ids.length))).length_le
    rw [he] at h
    exact Nat.le_trans h (connectingAtSize_length_le P Q extent ambient n hn hphys)

private theorem abs_sum_bound {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → Q'.abs (f x) ≤ g x) → Q'.abs (listQSum f xs) ≤ listQSum g xs
  | [], _ => by change Q'.abs (0 : Q') ≤ 0; decide
  | x::xs, h => Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
    (Q'.add_le_add (h x List.mem_cons_self) (abs_sum_bound f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))))

/-- A tail of the original resummed list with the SAME full partition square. -/
theorem resummed_subfamily_tail {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K extent : Nat) (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ambient : List Nat) (minimumSize : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (family : List (List Nat)) (hsub : family.Sublist (connectingAnchors extent left right ambient))
    (hsize : ∀ ids, ids ∈ family → minimumSize ≤ ids.length) :
    Q'.abs (listQSum (fun ids => connectedCoefficient w K extent p q ids *
      partitionSquare w K extent (detachedIds extent (left++right) ids ambient)) family) ≤
      twoProbeBudget P Q w hd hs c d minimumSize * partitionSquare w K extent ambient := by
  let r := adjustedCoreRate w hd
  let A := (c*d+c*d)*probePrefactor w hd (left++right).length
  let Z := partitionSquare w K extent ambient
  have hsum : Q'.abs (listQSum (fun ids => connectedCoefficient w K extent p q ids *
      partitionSquare w K extent (detachedIds extent (left++right) ids ambient)) family) ≤
      listQSum (fun ids => (A*r^ids.length)*Z) family := by
    apply abs_sum_bound
    intro ids hi
    exact resummed_geometric_bound hw0 hw1 hsmall hd K extent p q c d (left++right) Ip Iq
      (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      (hr.mono (fun _ h => List.mem_append.mpr (Or.inr h))) ambient ids hn hphys
      (connecting_selected (hsub.subset hi))
  have hfactor : listQSum (fun ids => (A*r^ids.length)*Z) family ≈
      (A*listQSum (fun ids => r^ids.length) family)*Z :=
    Q'.eqv_trans _ _ _ (listQSum_mul_right _ Z family)
      (Q'.mul_eqv_congr_right _ _ Z (listQSum_mul_left A _ family))
  have ha : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)
      (Q'.mul_nonneg _ _ Ip.nonnegative Iq.nonnegative)) (probePrefactor_nonnegative w hd _)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ Z (Q'.mul_le_mul_of_nonneg_left _ _ A
      (subfamily_weight_tail (adjustedCoreRate_nonnegative hw0 hd) hs P Q extent ambient minimumSize
        hn hphys family hsub hsize) ha) (SumOfSquares.q_mul_self_nonneg _)))

end YMGap.Continuum.BF4ExactSlabResummedSubfamilyBound

#print axioms YMGap.Continuum.BF4ExactSlabResummedSubfamilyBound.subfamily_weight_tail
#print axioms YMGap.Continuum.BF4ExactSlabResummedSubfamilyBound.resummed_subfamily_tail
